#!/usr/bin/env python3
"""How often does the rounding test of correctly rounded Ozaki-I and Ozaki-II succeed on an entry?

A CPU simulation of the correctly rounded schemes of `Ozaki/Correct.lean`, in exact arithmetic.
For one output entry `x . y` each scheme computes an exact value `H` and a proven bound
`B >= |x . y - H|`, and accepts when `H - B` and `H + B` round to the same value (`roundEnclosure`,
`roundingTest`); otherwise it tries the next enclosure and finally takes the exact fallback. The
matrix multiplier is exact (the Lean proofs show it is on slices and residues), so the slice and
residue products are computed exactly here; every `H`, `B`, `x . y` is an exact dyadic rational,
rounded with round to nearest even (`roundRNE`) by integer arithmetic.

Ozaki-I (`Ozaki/Split.lean`, `Ozaki/Ozaki1.lean`): `b = 11`, slices by round to nearest even on the
grid `2^(ceil(log2 max|r|) - b)` of what is left (`split`, `sliceGrid`), the `s(s+1)/2` slice products
`t + u < s` added exactly (`exactTerms`), and the bounds

* `normwise`   `(s+1) k 2^(E+F-s(b+1))`                (`exactTerms_error`, `ozaki1Bound`);
* `entrywise`  `(s+1) sum_i min(2|x_i y_i|, 2^(E+F-s(b+1)))` (`exactTerms_error_sharp`);
* `overlap`    `(s+1) N 2^(E+F-s(b+1))`, `N` the support overlap (`exactTerms_error_overlap`,
               `ozaki1BoundZ`; one extra product on the matrix multiplier per entry);
* `normwise_w96`, `overlap_w96`: the same with a `W = 96`-bit truncated sum
               (`Ozaki/TruncatedSum.lean` `ozaki1TruncatedEnclosure`, `ozaki1TruncatedEnclosureZ`).

Exact fallback (`ozaki1ExactFallback`): all `s_e^2` slice products, `s_e` the smallest `s >= 1`
leaving no residual in `x` or `y` (`residualsVanish`). Slice products of one split are prefixes of
the next (`split_prefix`), so the model reuses them: testing at `ss = [5, 6]` and falling back
costs `21 + s_e^2 - (reused pairs)` products on the matrix multiplier.

Ozaki-II (`Ozaki/Ozaki2.lean`): shift to `P` bits and truncate (`scaleShift`, `scaleTrunc`), one
product on the matrix multiplier per modulus, CRT reconstruction (exact when `2 k 4^P < M`), with
the moduli `fp64Moduli` of `Ozaki/BoundedChecked2.lean` (greedy pairwise coprime moduli <= 4096,
extended to 13 and 14) and `P = ozaki2Bits k M`. Bounds:

* `rational`  `max|x - x~| sum|y| + max|y - y~| sum|x~|` (`ozaki2Bound`, `dot_approx_error`);
* `integer`   `K 2^(-s_x-s_y)`, `K = boundK` (`Ozaki/BoundedOzaki2.lean`, `ozaki2K`).

Exact fallback: Ozaki-I's (`ozaki2CRE`). Configurations are tried in order (12, 13, 14 moduli for
binary64; 6, 7, 8 for binary32); a new `P` changes the scaled integers, so nothing is reused.

The cost model counts products on the matrix multiplier (one low-precision dot product of length
`k`) per entry; it is not GPU time. Every entry is also checked: `|x . y - H| <= B` for every
enclosure, and every result the rounding test accepts equals the rounding of the exact product
(both must never fail).

With `--rules`, each configuration also tries the slice counts of the rule for correct rounding
(`Ozaki/SliceRuleCR.lean` `slicesForCR`, `Ozaki/Adaptive.lean` `crSlices`): from
`s0 = slicesFor b (t + ceil(log2 k))`, the lists `[s0, s0+1]` and `[s0, s0+1, s0+2]`, with `t` the
output precision; every list also reports the adaptive shortcut (`cost_mean_adaptive`,
`ozaki1CRA`: straight to the exact fallback when `s_e^2` is at most the first test's cost). The
results go to `data/fallback-sim-rules.json` unless `--out` is given; the plain run's file is
untouched.

Usage (numpy from the local uv cache, no network):

    uv run --offline --no-project --python 3.12 --with numpy \
        python scripts/fallback_sim.py --out data/fallback-sim.json
    uv run --offline --no-project --python 3.12 --with numpy \
        python scripts/fallback_sim.py --rules --datasets \
        uniform,spread8,spread40,cancel1e2,cancel1e6,cancel1e10,sparse90,block4,fp16,int27,int12
    uv run --offline --no-project --python 3.12 --with numpy \
        python scripts/fallback_sim.py --summary data/fallback-sim.json   # markdown tables

The second command reproduces data/fallback-sim-rules.json (54 configurations).
"""
import argparse
import json
import math
import sys
import time
import zlib
from fractions import Fraction
from itertools import accumulate

import numpy as np

SLICE_BITS = 11          # b: slices are b-bit integers, |q| <= 2^b (Split.lean)
TRUNCATED_SUM_BITS = 96  # W of TruncatedSum.lean
MODULUS_CAP = 4096       # moduli <= 2^(b+1)
FORMATS = {'binary64': (53, -1022, 1023), 'binary32': (24, -126, 127)}
LIMB = 20                # limb width for the exact Ozaki-II integer products

# Settings per output format.
SETTINGS = {
    'binary64': {'ss_lists': [[5, 6], [4, 5, 6, 7]], 'oz2_counts': [12, 13, 14],
                 'datasets': ['uniform', 'uniform_rng', 'spread8', 'spread40', 'cancel1e2', 'cancel1e6',
                              'cancel1e10', 'cancel1e14', 'gendot1e2', 'gendot1e6',
                              'gendot1e10', 'gendot1e14', 'sparse90', 'block4', 'fp16', 'int8',
                              'int27']},
    'binary32': {'ss_lists': [[3, 4], [2, 3, 4, 5]], 'oz2_counts': [6, 7, 8],
                 'datasets': ['uniform', 'uniform_rng', 'spread8', 'cancel1e2', 'cancel1e6', 'gendot1e2',
                              'gendot1e6', 'sparse90', 'block4', 'fp16', 'int8', 'int12']},
}
BOUNDS1 = ['normwise', 'entrywise', 'overlap', 'normwise_w96', 'overlap_w96']
BOUNDS2 = ['rational', 'integer']
DESCRIPTIONS = {
    'uniform': 'U(-1,1) with full significands (uniform_full), independent A (64 x k) and B (k x 64)',
    'uniform_rng': 'numpy uniform(-1,1): values on the grid 2^-52 (few significant bits when small), GEMM',
    'spread8': 'sign * U[1,2) * 2^e, e uniform in [-8, 8], GEMM',
    'spread40': 'sign * U[1,2) * 2^e, e uniform in [-40, 40], GEMM',
    'cancel1e2': 'x, y ~ U(-1,1), partial sum cancelled on ~3 sqrt(k) slots with |x|, |y| <= 1, '
                 'last y set for kappa = sum|x_i y_i| / |x.y| = 1e2; one pair per entry',
    'cancel1e6': 'as cancel1e2, kappa = 1e6',
    'cancel1e10': 'as cancel1e2, kappa = 1e10',
    'cancel1e14': 'as cancel1e2, kappa = 1e14',
    'gendot1e2': 'GenDot (Ogita-Rump-Oishi 2005, Alg. 6.1) with c = 2|x|.|y|/|x.y| = 2e2 (exponents '
                 'spread over 2^(log2 c / 2); the achieved kappa grows with k), one pair per entry',
    'gendot1e6': 'GenDot, c = 2e6',
    'gendot1e10': 'GenDot, c = 2e10',
    'gendot1e14': 'GenDot, c = 2e14',
    'sparse90': 'U(-1,1) (full significands) with 90% zeros (independent), GEMM',
    'block4': 'k split in 4 blocks; each row of A and column of B dense U(-1,1) on one random block '
              '(about 75% of entries have disjoint supports: exact zeros)',
    'fp16': 'U(-1,1) (full significands) rounded to binary16, GEMM',
    'int8': 'integers uniform in [-128, 127], GEMM (exactly representable results)',
    'int27': 'integers uniform in [-2^26, 2^26], GEMM (results beyond 2^53: exact ties)',
    'int12': 'integers uniform in [-2^11, 2^11], GEMM (results beyond 2^24: exact ties)',
}


# ---------------------------------------------------------------- dyadic rationals n * 2^e

def dy_add(a, b):
    n1, e1 = a
    n2, e2 = b
    if n1 == 0:
        return b
    if n2 == 0:
        return a
    if e1 <= e2:
        return (n1 + (n2 << (e2 - e1)), e1)
    return ((n1 << (e1 - e2)) + n2, e2)


def dy_sub(a, b):
    return dy_add(a, (-b[0], b[1]))


def dy_mul(a, b):
    return (a[0] * b[0], a[1] + b[1])


def dy_le(a, b):
    return dy_sub(b, a)[0] >= 0


def dy_float(f):
    """A binary64 value as an exact dyadic."""
    if f == 0:
        return (0, 0)
    m, e = math.frexp(f)
    return (int(m * (1 << 53)), e - 53)


def dy_frac(a):
    n, e = a
    return Fraction(n) * Fraction(2) ** e


def rne(a, fmt):
    """`roundRNE p emin emax`: round n 2^e to nearest, ties to even; None on overflow. The result is
    canonical (odd mantissa, or (0, 0)), so two roundings agree iff the tuples are equal."""
    p, emin, emax = fmt
    n, e = a
    if n == 0:
        return (0, 0)
    m = -n if n < 0 else n
    grid = max(m.bit_length() - 1 + e, emin) - (p - 1)
    sh = grid - e
    if sh > 0:
        q = m >> sh
        r = m - (q << sh)
        h = 1 << (sh - 1)
        if r > h or (r == h and q & 1):
            q += 1
        if q == 0:
            return (0, 0)
        m, e = q, grid
    tz = (m & -m).bit_length() - 1
    m >>= tz
    e += tz
    if m.bit_length() + e > emax + 1:
        return None
    return (-m if n < 0 else m, e)


def classify(a, fmt):
    """(tie, representable, ulp exponent) of a nonzero exact value in the format."""
    p, emin, _ = fmt
    n, e = a
    m = abs(n)
    grid = max(m.bit_length() - 1 + e, emin) - (p - 1)
    sh = grid - e
    if sh <= 0:
        return False, True, grid
    r = m & ((1 << sh) - 1)
    return r == (1 << (sh - 1)), r == 0, grid


def check(H, B, fmt):
    """`roundEnclosure`: the common rounding of H - B and H + B, or None."""
    lo = rne(dy_sub(H, B), fmt)
    hi = rne(dy_add(H, B), fmt)
    return lo if (lo is not None and lo == hi) else None


def wide(B, ulp_exp):
    """4 B >= ulp: the enclosure is too wide for the format at this magnitude."""
    return B[0] != 0 and abs(B[0]).bit_length() - 1 + B[1] >= ulp_exp - 2


# ---------------------------------------------------------------- slicing (Split.lean)

def ceil_log2(a):
    """`ceilLog2` of positive binary64 values."""
    m, e = np.frexp(a)
    return (e - (m == 0.5)).astype(np.int64)


def split_rows(V, b, smin):
    """`split b s` of every row of V, for s up to max(smin, the last nonzero residual).

    Slice t: grid g = ceil(log2 max|r|) - b (or prev - (b+1) for a zero r, starting from prev = b),
    q = rne(r / 2^g), r <- r - q 2^g. In binary64 the scaling, the rounding (np.rint is ties to
    even) and the subtraction are exact (the residual of a binary64 value on a coarser grid is a
    binary64 value). Returns the slices (int16), the grids (nv x T) and, per row, the smallest s
    with a zero residual (0 for a zero row)."""
    nv = V.shape[0]
    R = V.copy()
    prev = np.full(nv, b, dtype=np.int64)
    Qs, Gs = [], []
    sv = np.zeros(nv, dtype=np.int64)
    done = ~(R != 0).any(axis=1)
    t = 0
    while t < smin or not done.all():
        A = np.abs(R).max(axis=1)
        g = prev - (b + 1)
        nz = A > 0
        if nz.any():
            g[nz] = ceil_log2(A[nz]) - b
        Q = np.rint(np.ldexp(R, -g[:, None]))
        assert np.abs(Q).max() <= 2 ** b
        R -= np.ldexp(Q, g[:, None])
        Qs.append(Q.astype(np.int16))
        Gs.append(g)
        prev = g
        t += 1
        alive = (R != 0).any(axis=1)
        sv[~done & ~alive] = t
        done |= ~alive
        if t > 300:
            raise RuntimeError('slicing does not terminate')
    return Qs, np.stack(Gs, axis=1), sv


def exact_abs_sums(V):
    """Exact sum_i |V_i| of every row, as dyadics: slice |V| on wide grids and add the integers."""
    Qs, G, _ = split_rows(np.abs(V), 14, 0)
    nv = V.shape[0]
    if not Qs:
        return [(0, 0)] * nv
    S = np.stack([Q.sum(axis=1, dtype=np.int64) for Q in Qs], axis=1).tolist()
    G = G.tolist()
    out = []
    for i in range(nv):
        acc = (0, 0)
        for s, g in zip(S[i], G[i]):
            if s:
                acc = dy_add(acc, (s, g))
        out.append(acc)
    return out


class Side:
    """The rows of A, the columns of B (as rows), or the x / y vectors of the pairs."""

    def __init__(self, V, smin):
        self.V = V
        self.Q, G, sv = split_rows(V, SLICE_BITS, smin)
        self.G = G.tolist()
        self.sv = sv.tolist()
        self.E = (G[:, 0] + SLICE_BITS).tolist()          # splitExp
        self.absV = np.abs(V)
        m, e = np.frexp(self.absV)
        self.M = (m * 2.0 ** 53).astype(np.int64)         # |V| = M 2^X exactly
        self.X = (e - 53).astype(np.int64)
        self.nz = V != 0
        self.abssum = exact_abs_sums(V)


# ---------------------------------------------------------------- the entrywise bound

def capsum_block(P, xM, xe, yM, ye, TE):
    """For each entry (row of P = |x| |y| in binary64) and threshold exponent te:
    sum_i min(|x_i y_i|, 2^te), exactly (half of `capSum` at M = 2^(te+1)).

    Rounding is monotone and 2^te is a binary64 value, so fl(p) < 2^te implies p < 2^te and
    fl(p) > 2^te implies p > 2^te; only fl(p) = 2^te needs the exact product. The exact products of
    the small terms are summed as integers. Also returns the overlap count and sum |x_i y_i|."""
    r = P.shape[0]
    pos = P > 0
    nnz = pos.sum(axis=1)
    sabs = P.sum(axis=1)
    tmax = TE.max(axis=1)
    assert tmax.min() > -1000 and tmax.max() < 1000
    G = pos & (P <= np.ldexp(1.0, tmax)[:, None])
    need = G.any(axis=1)
    out = []
    for e in range(r):
        tes = TE[e].tolist()
        nz = int(nnz[e])
        if not need[e]:
            out.append([(nz, te) for te in tes])
            continue
        idx = np.flatnonzero(G[e])
        vals = P[e, idx]
        order = np.argsort(vals, kind='stable')
        idx = idx[order]
        vals = vals[order]
        pe = xe[e, idx] + ye[e, idx]
        emin = int(pe.min())
        ints = [a * c << s for a, c, s in
                zip(xM[e, idx].tolist(), yM[e, idx].tolist(), (pe - emin).tolist())]
        pref = [0]
        pref.extend(accumulate(ints))
        res = []
        for te in tes:
            thr = math.ldexp(1.0, te)
            lo = int(np.searchsorted(vals, thr, 'left'))
            hi = int(np.searchsorted(vals, thr, 'right'))
            acc = pref[lo]
            nthr = nz - hi
            for l in range(lo, hi):
                if te >= emin and ints[l] <= (1 << (te - emin)):
                    acc += ints[l]
                else:
                    nthr += 1
            res.append(dy_add((acc, emin), (nthr, te)))
        out.append(res)
    return out, nnz, sabs


# ---------------------------------------------------------------- Ozaki-II

def coprime_moduli(count, cap=MODULUS_CAP):
    """Greedy pairwise coprime moduli from `cap` down; the first 12 are `fp64Moduli`."""
    ms = []
    m = cap
    while len(ms) < count:
        if all(math.gcd(m, o) == 1 for o in ms):
            ms.append(m)
        m -= 1
    return ms


def ozaki2_bits(k, M, fuel=400):
    """`ozaki2Bits k M`: the largest P with 2 k 2^(2P) < M."""
    for P in range(fuel, 0, -1):
        if 2 * k * 4 ** P < M:
            return P
    return 0


def sym_mod(x, m):
    r = x % m
    return r - m if 2 * r > m else r


def crt_reconstruct(ms, rs):
    """`crt (crtBasis ms) rs`."""
    M = math.prod(ms)
    acc = 0
    for m, r in zip(ms, rs):
        Mi = M // m
        acc += Mi * pow(Mi, -1, m) * r
    return sym_mod(acc, M)


def oz2_side(V, P):
    """`scaleShift P`, `scaleTrunc`, the truncation data of the bounds, and limbs of the integers."""
    nv = V.shape[0]
    A = np.abs(V).max(axis=1)
    sh = np.zeros(nv, dtype=np.int64)
    nz = A > 0
    sh[nz] = P - ceil_log2(A[nz])
    S = np.ldexp(V, sh[:, None])                  # exact
    a = np.trunc(S)                               # exact; |a| <= 2^P
    frac = S - a                                  # exact
    drops = (frac != 0).any(axis=1)
    maxdiff = np.ldexp(np.abs(frac).max(axis=1), -sh)   # max |x - x~|, exact
    absa = np.abs(a)
    sg = np.sign(a)
    nl = (P + 1 + LIMB - 1) // LIMB
    limbs = []
    suma = [0] * nv
    for j in range(nl):
        L = np.mod(np.floor(np.ldexp(absa, -LIMB * j)), 2.0 ** LIMB)
        limbs.append(L * sg)
        for i, sj in enumerate(L.sum(axis=1).tolist()):
            suma[i] += int(sj) << (LIMB * j)
    return {'sh': sh.tolist(), 'drops': drops.tolist(),
            'maxdiff': [dy_float(f) for f in maxdiff.tolist()], 'suma': suma, 'limbs': limbs,
            'a': a}


# ---------------------------------------------------------------- data

def stable_seed(*parts):
    return zlib.crc32('/'.join(map(str, parts)).encode())


def two_prod(a, b):
    p = a * b
    c = 134217729.0
    t = c * a
    ah = t - (t - a)
    al = a - ah
    t = c * b
    bh = t - (t - b)
    bl = b - bh
    return p, ((ah * bh - p) + ah * bl + al * bh) + al * bl


def dd_add_prod(hi, lo, a, b):
    p, pe = two_prod(a, b)
    s = hi + p
    bb = s - hi
    se = (hi - (s - bb)) + (p - bb)
    se = se + (lo + pe)
    h2 = s + se
    return h2, se - (h2 - s)


def gendot(rng, N, n, c, f32):
    """GenDot (Ogita, Rump, Oishi 2005, Algorithm 6.1), vectorized over N pairs; the partial dot
    products are accumulated in double-double. Entries are binary32 values when f32."""
    def cast(a):
        return a.astype(np.float32).astype(np.float64) if f32 else a
    b = math.log2(c)
    n2 = round(n / 2)
    X = np.empty((N, n))
    Y = np.empty((N, n))
    e = np.round(rng.random((N, n2)) * b / 2)
    e[:, 0] = round(b / 2) + 1
    e[:, -1] = 0
    X[:, :n2] = cast((2 * rng.random((N, n2)) - 1) * 2.0 ** e)
    Y[:, :n2] = cast((2 * rng.random((N, n2)) - 1) * 2.0 ** e)
    hi = np.zeros(N)
    lo = np.zeros(N)
    for i in range(n2):
        hi, lo = dd_add_prod(hi, lo, X[:, i], Y[:, i])
    e2 = np.round(np.linspace(b / 2, 0, n - n2))
    for i in range(n2, n):
        xi = cast((2 * rng.random(N) - 1) * 2.0 ** e2[i - n2])
        xi[xi == 0] = 1.0
        ri = cast((2 * rng.random(N) - 1) * 2.0 ** e2[i - n2])
        if f32:
            yi = ((ri.astype(np.float32) - hi.astype(np.float32)) / xi.astype(np.float32))
            yi = yi.astype(np.float64)
        else:
            yi = (ri - hi) / xi
        X[:, i] = xi
        Y[:, i] = yi
        hi, lo = dd_add_prod(hi, lo, xi, yi)
    perm = np.argsort(rng.random((N, n)), axis=1)
    return np.take_along_axis(X, perm, 1), np.take_along_axis(Y, perm, 1)


def uniform_full(rng, shape):
    """U(-1, 1) with a full 53-bit significand at every magnitude: the binade of a uniform draw,
    a uniform significand in [1/2, 1). (numpy's uniform(-1, 1) lies on the grid 2^-52, so its small
    entries have few significant bits; that is `uniform_rng`.)"""
    u = rng.uniform(-1, 1, shape)
    _, e = np.frexp(u)
    return np.sign(u) * np.ldexp(rng.uniform(0.5, 1, shape), e)


def cancel(rng, N, n, kappa, f32):
    """x, y ~ U(-1, 1), then the partial sum is cancelled with the last components, keeping every
    entry at most about 1 in magnitude: about 3 sqrt(n) slots with x in +-[1/2, 1) take
    y = clip(-S / x, -1, 1) while |S| > 1, and the last y is set so that x . y is about
    +-sum|x_i y_i| / kappa (the achieved kappa is measured exactly afterwards)."""
    def cast(a):
        return a.astype(np.float32).astype(np.float64) if f32 else a
    m = 3 * math.isqrt(n) + 4
    X = cast(uniform_full(rng, (N, n)))
    Y = cast(uniform_full(rng, (N, n)))
    X[:, n - m:] = cast(rng.uniform(0.5, 1, (N, m)) * rng.choice([-1.0, 1.0], (N, m)))
    hi = np.zeros(N)
    lo = np.zeros(N)
    for c in range(n - m):
        hi, lo = dd_add_prod(hi, lo, X[:, c], Y[:, c])
    for c in range(n - m, n - 1):
        yc = cast(np.clip(-hi / X[:, c], -1, 1))
        Y[:, c] = np.where(np.abs(hi) > 1, yc, Y[:, c])
        hi, lo = dd_add_prod(hi, lo, X[:, c], Y[:, c])
    sabs = (np.abs(X[:, :-1]) * np.abs(Y[:, :-1])).sum(axis=1) + np.abs(hi)
    t = rng.choice([-1.0, 1.0], N) * sabs / kappa
    Y[:, -1] = cast(((t - hi) - lo) / X[:, -1])
    perm = np.argsort(rng.random((N, n)), axis=1)
    return np.take_along_axis(X, perm, 1), np.take_along_axis(Y, perm, 1)


def gen_gemm(name, rng, m, n, k, f32):
    def U(shape):
        return uniform_full(rng, shape)

    def make(shape):
        if name == 'uniform':
            return U(shape)
        if name == 'uniform_rng':
            return rng.uniform(-1, 1, shape)
        if name.startswith('spread'):
            r = int(name[6:])
            return np.ldexp(rng.uniform(1, 2, shape) * rng.choice([-1.0, 1.0], shape),
                            rng.integers(-r, r + 1, shape))
        if name == 'sparse90':
            return U(shape) * (rng.random(shape) < 0.1)
        if name == 'block4':
            V = np.zeros(shape)
            w = shape[1] // 4
            for i, blk in enumerate(rng.integers(0, 4, shape[0])):
                V[i, blk * w:(blk + 1) * w] = U(w)
            return V
        if name == 'fp16':
            return U(shape).astype(np.float16).astype(np.float64)
        if name == 'int8':
            return rng.integers(-128, 128, shape).astype(np.float64)
        if name.startswith('int'):
            r = int(name[3:]) - 1
            return rng.integers(-2 ** r, 2 ** r + 1, shape).astype(np.float64)
        raise ValueError(name)

    A, Bt = make((m, k)), make((n, k))
    if f32:
        A = A.astype(np.float32).astype(np.float64)
        Bt = Bt.astype(np.float32).astype(np.float64)
    return A, Bt


# ---------------------------------------------------------------- one block of entries

def tri(s):
    return s * (s + 1) // 2


def clog2(k):
    """The least c with k <= 2^c (`clog2`)."""
    return 0 if k <= 1 else (k - 1).bit_length()


def slices_for_cr(b, t, k):
    """`slicesForCR b t k = slicesFor b (t + clog2 k)`: the least s >= 1 (up to 199) with
    (s + 1) 2^(t' + 2) <= 2^(s (b + 1)), t' = t + clog2 k; 0 if none."""
    tp = t + clog2(k)
    for s in range(1, 200):
        if (s + 1) * 2 ** (tp + 2) <= 2 ** (s * (b + 1)):
            return s
    return 0


def cr_lists(fmt_name, k):
    s0 = slices_for_cr(SLICE_BITS, FORMATS[fmt_name][0], k)
    return [[s0, s0 + 1], [s0, s0 + 1, s0 + 2]]


def process_block(mode, Xv, Yv, fmt_name, cfg, rec, stats, nvalidate):
    """All entries of one GEMM (mode 'gemm': Xv rows of A, Yv columns of B) or of one chunk of pairs
    (mode 'pairs': entry e is Xv[e] . Yv[e]); appends per-entry records to `rec`."""
    fmt = FORMATS[fmt_name]
    b = SLICE_BITS
    k = Xv.shape[1]
    s_check = cfg['s_check']
    smax = max(s_check)
    t0 = time.time()
    X = Side(Xv, smax)
    Y = Side(Yv, smax)
    nx, ny = Xv.shape[0], Yv.shape[0]
    if mode == 'gemm':
        entries = [(i, j) for i in range(nx) for j in range(ny)]
    else:
        entries = [(i, i) for i in range(nx)]
    nE = len(entries)
    stats['time_slice'] += time.time() - t0

    # Ozaki-I slice products: the triangle t + u < smax and the exact fallback's t < s_x, u < s_y.
    t0 = time.time()
    mx, my = max(X.sv), max(Y.sv)
    pairs = {(t, u) for t in range(smax) for u in range(smax - t)}
    pairs |= {(t, u) for t in range(mx) for u in range(my)}
    T = {}
    if mode == 'gemm':
        QX = [q.astype(np.float64) for q in X.Q]
        QY = [q.astype(np.float64) for q in Y.Q]
        for (t, u) in pairs:
            T[(t, u)] = (QX[t] @ QY[u].T).astype(np.int64).ravel().tolist()   # exact: < 2^53
    else:
        for (t, u) in pairs:
            T[(t, u)] = np.einsum('ij,ij->i', X.Q[t], Y.Q[u], dtype=np.int64).tolist()
    stats['mm_products_simulated'] += len(pairs)
    stats['time_products'] += time.time() - t0

    # The entrywise bound: sum min(|x_i y_i|, 2^(E+F-s(b+1)-1)) for every s; overlap counts.
    t0 = time.time()
    caps, nov, sabs = [None] * nE, [0] * nE, [0.0] * nE
    sarr = np.array(s_check)
    if mode == 'gemm':
        Fy = np.array(Y.E)
        for i in range(nx):
            P = X.absV[i][None, :] * Y.absV
            assert ((P > 0) == (X.nz[i][None, :] & Y.nz)).all()
            TE = (X.E[i] + Fy)[:, None] - sarr[None, :] * (b + 1) - 1
            xM = np.broadcast_to(X.M[i], P.shape)
            xe = np.broadcast_to(X.X[i], P.shape)
            out, nn, sa = capsum_block(P, xM, xe, Y.M, Y.X, TE)
            for j in range(ny):
                caps[i * ny + j] = out[j]
                nov[i * ny + j] = int(nn[j])
                sabs[i * ny + j] = float(sa[j])
    else:
        P = X.absV * Y.absV
        assert ((P > 0) == (X.nz & Y.nz)).all()
        TE = (np.array(X.E) + np.array(Y.E))[:, None] - sarr[None, :] * (b + 1) - 1
        out, nn, sa = capsum_block(P, X.M, X.X, Y.M, Y.X, TE)
        caps, nov, sabs = out, nn.tolist(), sa.tolist()
        del P
    stats['time_capsum'] += time.time() - t0

    # Ozaki-II: per configuration, the exact integer product a . c from 20-bit limbs.
    t0 = time.time()
    oz2 = []
    for (ms, P2) in cfg['oz2_cfgs']:
        sx = oz2_side(Xv, P2)
        sy = oz2_side(Yv, P2)
        nl = len(sx['limbs'])
        N2 = [0] * nE
        for j in range(nl):
            for l in range(nl):
                if mode == 'gemm':
                    Tl = (sx['limbs'][j] @ sy['limbs'][l].T).ravel()
                else:
                    Tl = np.einsum('ij,ij->i', sx['limbs'][j], sy['limbs'][l])
                assert np.abs(Tl).max(initial=0) < 2.0 ** 53
                sh = LIMB * (j + l)
                for e, v in enumerate(Tl.tolist()):
                    if v:
                        N2[e] += int(v) << sh
        # Validate the limb product and the CRT reconstruction on a few entries.
        M = math.prod(ms)
        assert 2 * k * 4 ** P2 < M
        for e in range(min(nvalidate, nE)):
            i, j = entries[e]
            a = [int(v) for v in sx['a'][i].tolist()]
            c = [int(v) for v in sy['a'][j].tolist()]
            exact = sum(p * q for p, q in zip(a, c))
            rs = []
            for m in ms:
                ra = [sym_mod(z, m) for z in a]
                rc = [sym_mod(z, m) for z in c]
                assert max(map(abs, ra + rc)) <= 2 ** b
                rs.append(sum(p * q for p, q in zip(ra, rc)) % m)
            ok = exact == N2[e] and crt_reconstruct(ms, rs) == exact
            stats['validate_oz2'] += 1
            stats['validate_oz2_fail'] += 0 if ok else 1
        for key in ('a', 'limbs'):
            del sx[key], sy[key]
        oz2.append((sx, sy, N2))
    stats['time_oz2'] += time.time() - t0

    # Per entry: exact value, Ozaki-I and Ozaki-II enclosures, rounding tests.
    t0 = time.time()
    for e, (i, j) in enumerate(entries):
        g, h = X.G[i], Y.G[j]
        sx_, sy_ = X.sv[i], Y.sv[j]
        se = max(1, sx_, sy_)
        E, F = X.E[i], Y.E[j]
        base = g[-1] + h[-1]          # grids decrease, so every exponent used is >= base
        vi = 0
        for t in range(sx_):
            gt = g[t] - base
            for u in range(sy_):
                Tv = T[(t, u)][e]
                if Tv:
                    vi += Tv << (gt + h[u])
        v = (vi, base)
        if e < nvalidate:
            xf = [Fraction(p) for p in Xv[i].tolist()]
            yf = [Fraction(p) for p in Yv[j].tolist()]
            exact = sum(p * q for p, q in zip(xf, yf))
            stats['validate_exact'] += 1
            stats['validate_exact_fail'] += 0 if exact == dy_frac(v) else 1
            # The entrywise bound's capSum, directly from its definition.
            for si, s in enumerate(s_check):
                Mf = Fraction(2) ** (E + F - s * (b + 1))
                cap = sum(min(2 * abs(p * q), Mf) for p, q in zip(xf, yf))
                stats['validate_capsum'] += 1
                stats['validate_capsum_fail'] += 0 if cap == 2 * dy_frac(caps[e][si]) else 1
            # Ozaki-II's rational bound and boundK, directly from truncVals.
            for (sx, sy, _), (ms, P2) in zip(oz2, cfg['oz2_cfgs']):
                shx, shy = sx['sh'][i], sy['sh'][j]
                xt = [Fraction(int(p * Fraction(2) ** shx)) / Fraction(2) ** shx for p in xf]
                yt = [Fraction(int(p * Fraction(2) ** shy)) / Fraction(2) ** shy for p in yf]
                brat = (max(abs(p - q) for p, q in zip(xf, xt)) * sum(map(abs, yf)) +
                        max(abs(p - q) for p, q in zip(yf, yt)) * sum(map(abs, xt)))
                a = [int(p * Fraction(2) ** shx) for p in xf]
                c = [int(p * Fraction(2) ** shy) for p in yf]
                dx, dy = xt != xf, yt != yf
                K = ((sum(map(abs, c)) + k) if dx else 0) + (sum(map(abs, a)) if dy else 0)
                mine = dy_add(dy_mul(sx['maxdiff'][i], Y.abssum[j]),
                              dy_mul(sy['maxdiff'][j], (sx['suma'][i], -shx)))
                mineK = ((sy['suma'][j] + k) if sx['drops'][i] else 0) + \
                    (sx['suma'][i] if sy['drops'][j] else 0)
                stats['validate_oz2_bounds'] += 1
                stats['validate_oz2_bounds_fail'] += 0 if (brat == dy_frac(mine) and K == mineK) else 1
        rv = rne(v, fmt)
        zero = vi == 0
        if zero:
            tie, rep, ulp = False, True, None
        else:
            tie, rep, ulp = classify(v, fmt)
        rec['se'].append(se)
        rec['sxsy'].append(max(sx_, 1) * max(sy_, 1))
        rec['zero'].append(zero)
        rec['tie'].append(tie)
        rec['repr'].append(rep)
        rec['kappa'].append(math.inf if zero else sabs[e] / abs(float(dy_frac(v))))

        # Triangle sums, exact (H) and truncated (TruncatedSum.lean), by anti-diagonals.
        q = E + F - TRUNCATED_SUM_BITS
        Hs, Ws, Ns = [0], [0], [0]
        H = WS = nzt = 0
        for d in range(smax):
            for t in range(d + 1):
                Tv = T[(t, d - t)][e]
                if Tv:
                    ex = g[t] + h[d - t]
                    H += Tv << (ex - base)
                    WS += (Tv << (ex - q)) if ex >= q else (Tv >> (q - ex))
                    nzt += 1
            Hs.append(H)
            Ws.append(WS)
            Ns.append(nzt)
        N = nov[e]
        for si, s in enumerate(s_check):
            mexp = E + F - s * (b + 1)
            Hd, Wd = (Hs[s], base), (Ws[s], q)
            cs = caps[e][si]
            encl = {
                'normwise': (Hd, ((s + 1) * k, mexp)),
                'entrywise': (Hd, ((s + 1) * 2 * cs[0], cs[1])),
                'overlap': (Hd, ((s + 1) * N, mexp)),
                'normwise_w96': (Wd, dy_add(((s + 1) * k, mexp), (tri(s), q))),
                'overlap_w96': (Wd, dy_add(((s + 1) * N, mexp), (Ns[s], q))),
            }
            for name, (Hc, Bc) in encl.items():
                if not dy_le((abs(dy_sub(v, Hc)[0]), dy_sub(v, Hc)[1]), Bc):
                    stats['violations_bound'] += 1
                w = check(Hc, Bc, fmt)
                if w is not None and w != rv:
                    stats['violations_result'] += 1
                rec['ok1'][name][s].append(w is not None)
                rec['wide1'][name][s].append((not zero) and wide(Bc, ulp))
            rec['hex1'][s].append(Hs[s] == vi)

        for c, (sx, sy, N2) in enumerate(oz2):
            shx, shy = sx['sh'][i], sy['sh'][j]
            q2 = -(shx + shy)
            H2 = (N2[e], q2)
            brat = dy_add(dy_mul(sx['maxdiff'][i], Y.abssum[j]),
                          dy_mul(sy['maxdiff'][j], (sx['suma'][i], -shx)))
            K = ((sy['suma'][j] + k) if sx['drops'][i] else 0) + \
                (sx['suma'][i] if sy['drops'][j] else 0)
            for name, Bc in (('rational', brat), ('integer', (K, q2))):
                d = dy_sub(v, H2)
                if not dy_le((abs(d[0]), d[1]), Bc):
                    stats['violations_bound'] += 1
                w = check(H2, Bc, fmt)
                if w is not None and w != rv:
                    stats['violations_result'] += 1
                rec['ok2'][name][c].append(w is not None)
                rec['wide2'][name][c].append((not zero) and wide(Bc, ulp))
            rec['hex2'][c].append(dy_sub(v, H2)[0] == 0)
            rec['b0'][c].append(brat[0] == 0)
    stats['time_entries'] += time.time() - t0
    stats['entries'] += nE


# ---------------------------------------------------------------- summaries

def frac(mask, n):
    return round(float(np.count_nonzero(mask)) / n, 6) if n else 0.0


def hist(values):
    u, c = np.unique(values, return_counts=True)
    return {str(int(a)): int(b) for a, b in zip(u, c)}


def fallback_mix(fb, zero, tie, rep, wide_last, hexact_last):
    nf = int(np.count_nonzero(fb))
    near = fb & ~zero & ~tie & ~wide_last
    return {
        'count': nf,
        'exact_zero': int(np.count_nonzero(fb & zero)),
        'tie': int(np.count_nonzero(fb & tie)),
        'wide_bound': int(np.count_nonzero(fb & ~zero & ~tie & wide_last)),
        'near_boundary': int(np.count_nonzero(near)),
        'representable': int(np.count_nonzero(fb & rep & ~zero)),
        'H_already_exact': int(np.count_nonzero(fb & hexact_last)),
    }


def summarize(rec, cfg):
    n = len(rec['se'])
    se = np.array(rec['se'])
    sxsy = np.array(rec['sxsy'])
    zero = np.array(rec['zero'])
    tie = np.array(rec['tie'])
    rep = np.array(rec['repr'])
    kap = np.array(rec['kappa'])
    base = se ** 2
    smax_e = int(se.max())
    out = {'entries': n,
           'exact_fallback_slices_hist': hist(se),
           'exact_fallback_cost_mean': round(float(base.mean()), 3),
           'full_split_sxsy_cost_mean': round(float(sxsy.mean()), 3),
           'frac_exact_zero': frac(zero, n), 'frac_tie': frac(tie, n),
           'frac_representable': frac(rep & ~zero, n)}
    fin = kap[np.isfinite(kap)]
    if fin.size:
        lk = np.log10(fin)
        out['kappa_log10_p10_p50_p90'] = [round(float(np.percentile(lk, p)), 2)
                                          for p in (10, 50, 90)]

    o1 = {}
    for ss in cfg['ss_lists']:
        key = ','.join(map(str, ss))
        sl = ss[-1]
        # reuse[e]: pairs t + u < sl with t, u < s_e, already computed by the rounding tests.
        reuse = np.array([sum(1 for t in range(sl) for u in range(sl - t)
                              if t < s and u < s) for s in range(smax_e + 1)])
        o1[key] = {}
        for bound in BOUNDS1:
            succeeded_at = np.full(n, -1)
            for idx, s in enumerate(ss):
                m = (succeeded_at < 0) & np.array(rec['ok1'][bound][s])
                succeeded_at[m] = idx
            fb = succeeded_at < 0
            extra = 1 if bound.startswith('overlap') else 0
            tris = np.array([tri(s) for s in ss])
            cum_noreuse = np.cumsum(tris)
            cost = np.where(fb, tri(sl) + base - reuse[se], tris[np.maximum(succeeded_at, 0)]) + extra
            cost_noreuse = np.where(fb, cum_noreuse[-1] + base,
                                    cum_noreuse[np.maximum(succeeded_at, 0)]) + extra
            # Adaptive: s_e is known after splitting; go straight to the exact fallback when it is
            # no dearer than the first test.
            direct = base <= tri(ss[0]) + extra
            cost_adapt = np.where(direct, base, cost)
            wl = np.array(rec['wide1'][bound][sl])
            hx = np.array(rec['hex1'][sl])
            o1[key][bound] = {
                'test_succeeded_frac': {str(s): frac(succeeded_at == idx, n) for idx, s in enumerate(ss)},
                'exact_frac': frac(fb, n),
                'exact_fallback_slices_mean': round(float(se[fb].mean()), 3) if fb.any() else None,
                'exact_fallback_slices_hist': hist(se[fb]) if fb.any() else {},
                'cost_mean': round(float(cost.mean()), 3),
                'cost_mean_no_reuse': round(float(cost_noreuse.mean()), 3),
                'cost_mean_adaptive': round(float(cost_adapt.mean()), 3),
                'cost_ratio_vs_exact_fallback': round(float(cost.mean() / base.mean()), 4),
                'fallbacks': fallback_mix(fb, zero, tie, rep, wl, hx),
            }
    o2 = {}
    counts = [len(ms) for ms, _ in cfg['oz2_cfgs']]
    cum = np.cumsum(counts)
    for bound in BOUNDS2:
        succeeded_at = np.full(n, -1)
        for c in range(len(counts)):
            m = (succeeded_at < 0) & np.array(rec['ok2'][bound][c])
            succeeded_at[m] = c
        fb = succeeded_at < 0
        cost = np.where(fb, cum[-1] + base, cum[np.maximum(succeeded_at, 0)])
        wl = np.array(rec['wide2'][bound][len(counts) - 1])
        hx = np.array(rec['hex2'][len(counts) - 1])
        o2[bound] = {
            'test_succeeded_frac': {str(cnt): frac(succeeded_at == c, n) for c, cnt in enumerate(counts)},
            'exact_frac': frac(fb, n),
            'exact_fallback_slices_mean': round(float(se[fb].mean()), 3) if fb.any() else None,
            'exact_fallback_slices_hist': hist(se[fb]) if fb.any() else {},
            'cost_mean': round(float(cost.mean()), 3),
            'cost_ratio_vs_exact_fallback': round(float(cost.mean() / base.mean()), 4),
            'fallbacks': fallback_mix(fb, zero, tie, rep, wl, hx),
        }
    out['ozaki1'] = o1
    out['ozaki2'] = o2
    # How often the enclosure's H is already the exact product (Ozaki-II: the truncation dropped
    # nothing, so B = 0 and the rounding test succeeds whatever the rounding boundary).
    out['ozaki1_H_exact_frac'] = {str(s): frac(np.array(rec['hex1'][s]), n)
                                  for s in cfg['s_check']}
    out['ozaki2_H_exact_frac'] = {str(cnt): frac(np.array(rec['hex2'][c]), n)
                                  for c, cnt in enumerate(counts)}
    out['ozaki2_truncation_lossless_frac'] = {str(cnt): frac(np.array(rec['b0'][c]), n)
                                              for c, cnt in enumerate(counts)}
    return out


# ---------------------------------------------------------------- driver

def new_rec(cfg):
    return {'se': [], 'sxsy': [], 'zero': [], 'tie': [], 'repr': [], 'kappa': [],
            'ok1': {bd: {s: [] for s in cfg['s_check']} for bd in BOUNDS1},
            'wide1': {bd: {s: [] for s in cfg['s_check']} for bd in BOUNDS1},
            'hex1': {s: [] for s in cfg['s_check']},
            'ok2': {bd: {c: [] for c in range(len(cfg['oz2_cfgs']))} for bd in BOUNDS2},
            'wide2': {bd: {c: [] for c in range(len(cfg['oz2_cfgs']))} for bd in BOUNDS2},
            'hex2': {c: [] for c in range(len(cfg['oz2_cfgs']))},
            'b0': {c: [] for c in range(len(cfg['oz2_cfgs']))}}


def run_dataset(name, k, fmt_name, args):
    st = SETTINGS[fmt_name]
    ss_lists = [list(ss) for ss in st['ss_lists']]
    if getattr(args, 'rules', False):
        for ss in cr_lists(fmt_name, k):
            if ss not in ss_lists:
                ss_lists.append(ss)
    s_check = sorted(set(s for ss in ss_lists for s in ss))
    oz2_cfgs = []
    for cnt in st['oz2_counts']:
        ms = coprime_moduli(cnt)
        oz2_cfgs.append((ms, ozaki2_bits(k, math.prod(ms))))
    cfg = {'s_check': s_check, 'ss_lists': ss_lists, 'oz2_cfgs': oz2_cfgs}
    rng = np.random.default_rng(stable_seed(name, k, fmt_name))
    f32 = fmt_name == 'binary32'
    rec = new_rec(cfg)
    stats = {key: 0 for key in ('entries', 'violations_bound', 'violations_result',
                                'validate_exact', 'validate_exact_fail', 'validate_capsum',
                                'validate_capsum_fail', 'validate_oz2', 'validate_oz2_fail',
                                'validate_oz2_bounds', 'validate_oz2_bounds_fail',
                                'mm_products_simulated')}
    for key in ('time_slice', 'time_products', 'time_capsum', 'time_oz2', 'time_entries'):
        stats[key] = 0.0
    t0 = time.time()
    if name.startswith('gendot') or name.startswith('cancel'):
        kappa = float(name[6:])
        left = args.entries
        while left > 0:
            nb = min(args.chunk, left)
            if name.startswith('gendot'):
                Xv, Yv = gendot(rng, nb, k, 2 * kappa, f32)
            else:
                Xv, Yv = cancel(rng, nb, k, kappa, f32)
            first = left == args.entries
            process_block('pairs', Xv, Yv, fmt_name, cfg, rec, stats,
                          args.validate if first else 0)
            left -= nb
        mode = 'pairs'
    else:
        side = int(round(math.sqrt(args.entries)))
        A, Bt = gen_gemm(name, rng, side, side, k, f32)
        process_block('gemm', A, Bt, fmt_name, cfg, rec, stats, args.validate)
        mode = 'gemm'
    res = {'dataset': name, 'description': DESCRIPTIONS[name], 'k': k, 'format': fmt_name,
           'mode': mode, 'ss_lists': ss_lists,
           'ozaki2_configs': [{'moduli_count': len(ms), 'P': P2, 'log2_M': round(math.log2(math.prod(ms)), 2)}
                              for ms, P2 in oz2_cfgs]}
    res.update(summarize(rec, cfg))
    stats['seconds'] = round(time.time() - t0, 2)
    for key in list(stats):
        if key.startswith('time_'):
            stats[key] = round(stats[key], 2)
    res['checks'] = stats
    return res


def main():
    ap = argparse.ArgumentParser(description=__doc__.split('\n')[0])
    ap.add_argument('--out', default='data/fallback-sim.json')
    ap.add_argument('--sizes', default='256,1024,4096')
    ap.add_argument('--formats', default='binary64,binary32')
    ap.add_argument('--datasets', default='', help='comma list; default: all per format')
    ap.add_argument('--entries', type=int, default=4096)
    ap.add_argument('--chunk', type=int, default=256, help='pairs per block (memory)')
    ap.add_argument('--validate', type=int, default=4,
                    help='entries per block checked against Fraction arithmetic and the CRT')
    ap.add_argument('--summary', metavar='JSON', help='print markdown tables from a results file')
    ap.add_argument('--rules', action='store_true',
                    help='also try the slice counts of the correct-rounding rule (slicesForCR); '
                         'writes data/fallback-sim-rules.json unless --out is given')
    args = ap.parse_args()
    if args.rules and args.out == 'data/fallback-sim.json':
        args.out = 'data/fallback-sim-rules.json'

    if args.summary:
        print_summary(json.load(open(args.summary)))
        return
    sizes = [int(s) for s in args.sizes.split(',')]
    only = set(filter(None, args.datasets.split(',')))
    results = []
    meta = {
        'script': 'scripts/fallback_sim.py',
        'slice_bits_b': SLICE_BITS, 'truncated_sum_bits_W': TRUNCATED_SUM_BITS,
        'entries_per_configuration': args.entries,
        'moduli': coprime_moduli(14),
        'settings': {f: {'ss_lists': SETTINGS[f]['ss_lists'],
                         'ozaki2_moduli_counts': SETTINGS[f]['oz2_counts']} for f in SETTINGS},
        'cost_model': 'products on the matrix multiplier (low-precision dot products of length k) '
                      'per output entry; Ozaki-I reuses slice products across slice counts '
                      '(split_prefix) and in the exact fallback; the overlap bound adds one '
                      'product (support indicators); Ozaki-II configurations cost one product '
                      'per modulus, without reuse; the exact fallback costs s_e^2 '
                      '(ozaki1ExactFallback). Not GPU time.',
        'fallback_categories': 'exact_zero: x.y = 0; tie: x.y exactly halfway between two '
                               'neighbours in the output format; wide_bound: 4B >= ulp(x.y) at '
                               'the last rounding test; near_boundary: the rest (x.y within 2B of a '
                               'rounding boundary with 4B < ulp); representable: x.y a format '
                               'value (overlaps the others); H_already_exact: H = x.y at the '
                               'last rounding test yet B > 0.',
    }
    t_all = time.time()
    for fmt_name in args.formats.split(','):
        for k in sizes:
            for name in SETTINGS[fmt_name]['datasets']:
                if only and name not in only:
                    continue
                r = run_dataset(name, k, fmt_name, args)
                results.append(r)
                o1 = r['ozaki1'][','.join(map(str, SETTINGS[fmt_name]['ss_lists'][0]))]
                ex = ','.join('%s=%.3f' % (bd, o1[bd]['exact_frac'])
                              for bd in ('normwise', 'entrywise', 'overlap'))
                print(f"{fmt_name} k={k:5d} {name:11s} {r['checks']['seconds']:7.1f}s exact[{ex}] "
                      f"oz2={r['ozaki2']['rational']['exact_frac']:.3f} "
                      f"viol={r['checks']['violations_bound']}/{r['checks']['violations_result']} "
                      f"valfail={sum(v for kk, v in r['checks'].items() if kk.endswith('_fail'))}",
                      file=sys.stderr, flush=True)
                meta['total_seconds'] = round(time.time() - t_all, 1)
                with open(args.out, 'w') as fh:
                    json.dump({'meta': meta, 'results': results}, fh, indent=1)
                    fh.write('\n')


# ---------------------------------------------------------------- markdown summary

def pct(x):
    return f'{100 * x:.1f}' if x is not None else '-'


def print_summary(data):
    res = data['results']
    for fmt_name in ('binary64', 'binary32'):
        rows = [r for r in res if r['format'] == fmt_name]
        if not rows:
            continue
        st = data['meta']['settings'][fmt_name]
        ssa = ','.join(map(str, st['ss_lists'][0]))
        ssb = ','.join(map(str, st['ss_lists'][1]))
        s1, s2 = st['ss_lists'][0]
        print(f'\n### {fmt_name}: Ozaki-I, ss = [{ssa}] (% of entries decided at s={s1} / s={s2} / '
              f'exact fallback)\n')
        print('| data | k | kappa p50 | normwise | entrywise | nonzero-position | s_e (fallback) | '
              'cost / exact fallback (normwise, nonzero-position) |')
        print('|---|---|---|---|---|---|---|---|')
        for r in rows:
            o = r['ozaki1'][ssa]
            cells = []
            for bd in ('normwise', 'entrywise', 'overlap'):
                d = o[bd]
                cells.append(f"{pct(d['test_succeeded_frac'][str(s1)])} / {pct(d['test_succeeded_frac'][str(s2)])}"
                             f" / **{pct(d['exact_frac'])}**")
            kp = r.get('kappa_log10_p10_p50_p90', [None] * 3)[1]
            sef = o['normwise']['exact_fallback_slices_mean']
            print(f"| {r['dataset']} | {r['k']} | {('1e%.1f' % kp) if kp is not None else '-'} | "
                  + ' | '.join(cells) +
                  f" | {sef if sef is not None else '-'} | "
                  f"{o['normwise']['cost_mean']:.1f} / {o['overlap']['cost_mean']:.1f} vs "
                  f"{r['exact_fallback_cost_mean']:.1f} |")
        print(f'\n### {fmt_name}: Ozaki-I, ss = [{ssb}], exact-fallback % (normwise / entrywise / '
              f'nonzero-position / nonzero-position + W=96 truncated sum) and mean cost\n')
        print('| data | k | exact % | cost (normwise / nonzero-position) | adaptive cost (nonzero-position) | exact fallback |')
        print('|---|---|---|---|---|---|')
        for r in rows:
            o = r['ozaki1'][ssb]
            ex = ' / '.join(pct(o[bd]['exact_frac']) for bd in
                            ('normwise', 'entrywise', 'overlap', 'overlap_w96'))
            print(f"| {r['dataset']} | {r['k']} | {ex} | {o['normwise']['cost_mean']:.1f} / "
                  f"{o['overlap']['cost_mean']:.1f} | {o['overlap']['cost_mean_adaptive']:.1f} | "
                  f"{r['exact_fallback_cost_mean']:.1f} |")
        counts = [c['moduli_count'] for c in rows[0]['ozaki2_configs']]
        print(f'\n### {fmt_name}: Ozaki-II, {counts} moduli in turn (% decided at each / exact fallback)\n')
        print('| data | k | P | rational bound | integer bound (boundK) | cost (rational) vs exact fallback |')
        print('|---|---|---|---|---|---|')
        for r in rows:
            o = r['ozaki2']
            cells = []
            for bd in ('rational', 'integer'):
                d = o[bd]
                cells.append(' / '.join(pct(d['test_succeeded_frac'][str(c)]) for c in counts) +
                             f" / **{pct(d['exact_frac'])}**")
            Ps = ','.join(str(c['P']) for c in r['ozaki2_configs'])
            print(f"| {r['dataset']} | {r['k']} | {Ps} | " + ' | '.join(cells) +
                  f" | {o['rational']['cost_mean']:.1f} vs {r['exact_fallback_cost_mean']:.1f} |")
        print(f'\n### {fmt_name}: what the fallbacks are (Ozaki-I ss = [{ssa}], nonzero-position bound; '
              f'Ozaki-II rational)\n')
        print('| data | k | O-I fallbacks | zero | tie | near | wide | H exact | O-II fallbacks | '
              'zero | tie | near | wide |')
        print('|---|---|---|---|---|---|---|---|---|---|---|---|---|')
        for r in rows:
            a = r['ozaki1'][ssa]['overlap']['fallbacks']
            c = r['ozaki2']['rational']['fallbacks']
            print(f"| {r['dataset']} | {r['k']} | {a['count']} | {a['exact_zero']} | {a['tie']} | "
                  f"{a['near_boundary']} | {a['wide_bound']} | {a['H_already_exact']} | "
                  f"{c['count']} | {c['exact_zero']} | {c['tie']} | {c['near_boundary']} | "
                  f"{c['wide_bound']} |")


if __name__ == '__main__':
    main()
