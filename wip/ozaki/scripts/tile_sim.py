#!/usr/bin/env python3
"""Tile-level cost model of correctly rounded Ozaki-I and Ozaki-II GEMMs (binary64 output).

`fallback_sim.py` counts products on the matrix multiplier per output entry. A matrix multiplier
works on output tiles, so entries of one tile that need different slice counts, or the exact
fallback, cannot stop separately. This script simulates whole GEMMs `C = A B` (`m x n` output, inner
dimension `k`) entry by entry with the same exact arithmetic as `fallback_sim.py` (it imports its
slicing, Ozaki-II truncation, CRT, rounding and data generators), records at which level the rounding
test of each entry succeeds, and then charges the work under explicit tile policies.

Schemes (as in `fallback_sim.py`, binary64 output, `b = 11`-bit slices):

* Ozaki-I, slice lists `[5, 6]` (plain) and `[6, 7]` (the k-dependent rule `slicesForCR`, which is
  `[6, 7]` for k = 256 .. 4096), bounds `normwise` and `overlap` (zero-aware: one extra product on
  the matrix multiplier, the support-indicator GEMM). Exact fallback: `s_e^2` slice products,
  reusing the triangle.
* Ozaki-II, 12, 13, 14 moduli in turn (nothing reused between configurations), bounds `rational`
  and `integer` (boundK); exact fallback: Ozaki-I's `s_e^2`.

Cost unit on the matrix multiplier: a *tile product* is one output tile (TM x TN entries) times one
slice (or residue) product of full inner dimension k. On a Tensor Core variant with 11-bit slices,
split-K runs chunks of `2^(24-2b) = 4` products per exact call, so one tile product of a 16 x 8 tile
is `ceil(k / 4)` `mma.m16n8k16` instructions (`SliceRun.blocks` of `OzakiTC/SplitChoice.lean`);
every scheme uses the same k, so this factor does not change any ratio. Results are also given as
*dot products of length k per output entry* (tile products x TM TN / (m n)), the unit of
`fallback_sim.py`.

Policies (per tile shape TM x TN):

* C  per entry: each entry pays its own count (fallback_sim's cost); tiles = sum / (TM TN), a lower
     bound that no tiled schedule beats.
* A  uniform per tile: the tile runs a level for all its entries; if the rounding test of any entry
     fails at that level, the whole tile runs the next level (entries whose test succeeded keep
     their value, masked). A tile in the exact fallback runs `S^2` products with `S` the largest
     `s_e` in the tile.
* B  masked + compaction: level 0 runs on every tile; the entries whose test failed are compacted
     across tiles into new tiles for the next level and for the exact fallback.
     - B_ideal: perfect packing, `ceil(count / (TM TN))` tiles per level (exact fallback: entries
       sorted by `s_e`, a packed tile pays its largest `s_e`). A tile of 3 entries costs a whole
       tile. It ignores that an MMA tile is an outer product, so it is optimistic.
     - B_gather: a tile is any TM gathered rows x TN gathered columns (an outer product); it covers
       only the entries in that row x column set whose test failed. Greedy schedule: group the
       distinct columns (or rows) of those entries in index order into groups of TN (TM), then cut
       the rows (columns) they touch into chunks of TM (TN); the cheaper orientation is used, and
       for the exact fallback the cheaper of packing per `s_e` class or all together. This charges
       the loss of data reuse: scattered entries fill only min(TM, TN) of a tile's TM TN slots.
* A at coarse granularity (64 x 64 warp tile, 128 x 128 thread-block tile): the decision to run the
  next level is made per coarse tile. A_shuffled: A on tiles of randomly drawn entries (no
  correlation inside a tile).
* Adaptive shortcut (Ozaki-I): a tile (A, B) or entry (C) whose exact fallback costs no more than
  the first rounding test (`S^2 <= tri(s1) + extra`) takes the exact fallback at once (`ozaki1CRA`).

Baselines: `exact_tile` every tile in the exact fallback (S^2 per tile, S its largest s_e);
`exact_entry` per entry (s_e^2, fallback_sim's baseline); `exact_global` one slice count for the
whole GEMM.

Work off the matrix multiplier (counted separately, never folded into the count of products on the
matrix multiplier), as event counts and in 64-bit integer operations with the weights in `WEIGHTS`:

* slicing: slices of A and B are computed once per matrix and reused by every tile: (rows of A +
  columns of B) x k elements per slice, to the depth some issued tile needs (slices past an
  operand's last nonzero residual cost nothing); the exact fallback needs `s_x`, `s_y` slices;
* Ozaki-II conversion: scale/truncate per element per configuration and one residue per element per
  modulus, for the rows/columns involved;
* accumulation of slice products into the entry's accumulator (a 2-word truncated sum for the
  rounding tests, a 5-word exact register for the exact fallback), and split-K chunk results (one
  convert + add per entry per chunk, proportional to the count of products on the matrix
  multiplier);
* rounding tests: one test per entry per level tested (A tests whole tiles);
* Ozaki-II reconstruction: CRT per entry per modulus with 3-word integers, plus a final reduction;
* final rounding of the exact fallback's sum;
* compaction (policy B): each entry moved to a later level writes its index and accumulator state.
  The memory traffic of gathers is not modelled.

Soundness is checked as in `fallback_sim.py`: every enclosure contains the exact product and every
result that a rounding test accepts equals the round to nearest even of the exact product (violation
counters over all entries and levels); the exact product from the slices is compared with an
independent exact product (20-bit limbs on each row's own grid) for every entry and with `Fraction`
arithmetic on a few entries per block of rows; Ozaki-II's limb product and CRT reconstruction on a
few entries per block of rows. Every policy returns, per entry, either a value accepted by a
rounding test or the rounding of the exact product, so these counters cover all policies.

This is a model, not GPU time: it counts instructions issued and integer operations; memory
traffic, latency, occupancy and scheduling overheads of compaction are not modelled.

Usage (numpy from the local uv cache, no network):

    uv run --offline --no-project --python 3.12 --with numpy \\
        python scripts/tile_sim.py --out data/tile-sim.json
    uv run --offline --no-project --python 3.12 --with numpy \\
        python scripts/tile_sim.py --summary data/tile-sim.json [--all]
"""
import argparse
import json
import math
import os
import sys
import time
from concurrent.futures import ProcessPoolExecutor, as_completed
from fractions import Fraction

import numpy as np

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import fallback_sim as fs  # noqa: E402

FMT_NAME = 'binary64'
FMT = fs.FORMATS[FMT_NAME]
BITS = fs.SLICE_BITS                      # b = 11
LIMB = fs.LIMB                            # 20-bit limbs for exact integer products
SPLITK_CHUNK = 2 ** (24 - 2 * BITS)       # 4 products per exact call of the matrix multiplier (11-bit slices)
PLAIN = [5, 6]
OZ2_COUNTS = [12, 13, 14]
BOUNDS1 = ['normwise', 'overlap']
BOUNDS2 = ['rational', 'integer']
MMA_SHAPES = [(16, 8), (16, 16)]
COARSE_SHAPES = [(64, 64), (128, 128)]
INF = 10 ** 6
DATASETS = ['uniform', 'spread8', 'spread40', 'cancel1e2', 'cancel1e6', 'cancel1e10', 'sparse90',
            'block4', 'fp16', 'int8']
DESCRIPTIONS = dict(fs.DESCRIPTIONS)
for _kap in ('1e2', '1e6', '1e10'):
    DESCRIPTIONS['cancel' + _kap] = (
        'GEMM form of the cancel family (fallback_sim builds independent pairs, which share no rows '
        'or columns): A = [U U], B^T = [V fl(D - V)] with U, V ~ U(-1,1) full significands, '
        'D = delta U(-1,1), columns permuted at random, so C = U (V + fl(D - V))^T cancels; delta '
        'calibrated so that the median entry condition number sum|a_l b_l| / |c| is ' + _kap +
        ' (it varies by entry; percentiles reported)')

# Weights in 64-bit integer operations per event (stated model, not measured).
WEIGHTS = {
    'slice_element': 5,      # per element per slice: max-reduction share 1, shift 1, RNE 2, residual 1
    'oz2_convert_element': 3,  # per element per Ozaki-II configuration: scale + truncate to 2 words
    'oz2_residue': 4,        # per element per modulus: 2-word integer mod a 12-bit modulus
    'accumulate_truncated_sum': 2,  # per entry per slice product into the 96-bit (2-word) truncated sum
    'accumulate_exact': 5,   # per entry per slice product into the 263-bit (5-word) exact register
    'splitk_chunk_add': 2,   # per entry per split-K chunk: convert the binary32 chunk result + add
    'rounding_test_ozaki1': 20,  # per entry per test: bound 2, H -/+ B on 2 words 4, two RNEs 12, compare 2
    'rounding_test_ozaki2': 26,  # as Ozaki-I plus forming the bound from row/column sums (6)
    'crt_modulus': 6,        # per entry per modulus: 12-bit residue x 3-word CRT basis constant, add
    'crt_final': 12,         # per entry per configuration: reduce mod M (3 words), symmetric, scale
    'round_exact': 10,       # per entry in the exact fallback: RNE of a 5-word value
    'compact_entry': 4,      # policy B, per entry per later level: write its index and 2-word state
}


def tri(s):
    return s * (s + 1) // 2


def rule_list(k):
    return fs.cr_lists(FMT_NAME, k)[0]


def dy_float(n, e):
    sh = max(n.bit_length() - 60, 0)
    return math.ldexp(float(n >> sh), e + sh)


# ---------------------------------------------------------------- data

def cancel_gemm(m, n, k, kappa):
    seed = fs.stable_seed('tile-cancel', kappa, m, n, k)

    def build(delta):
        rng = np.random.default_rng(seed)
        h = k // 2
        U = fs.uniform_full(rng, (m, h))
        V = fs.uniform_full(rng, (n, h))
        D = fs.uniform_full(rng, (n, h)) * delta
        A = np.concatenate([U, U], axis=1)
        Bt = np.concatenate([V, D - V], axis=1)
        perm = rng.permutation(k)
        return A[:, perm], Bt[:, perm]

    # median |c| ~ 0.6745 delta sqrt(k/2) / 3, sum|a b| ~ k / 4: an analytic start, then two
    # binary64 estimates of the median condition number (relative error < k u kappa, ample here).
    delta = 1.112 * math.sqrt(2 * k) / kappa
    for _ in range(2):
        A, Bt = build(delta)
        with np.errstate(divide='ignore'):
            med = float(np.median((np.abs(A) @ np.abs(Bt).T) / np.abs(A @ Bt.T)))
        delta *= med / kappa
    return build(delta)


def make_gemm(name, m, n, k):
    if name.startswith('cancel'):
        return cancel_gemm(m, n, k, float(name[6:]))
    rng = np.random.default_rng(fs.stable_seed('tile', name, m, n, k))
    return fs.gen_gemm(name, rng, m, n, k, False)


def int_limbs(V):
    """Each row of V as an integer on the row's finest grid, in signed 20-bit limbs:
    V_i = 2^base_i sum_l L_l[i] 2^(20 l). Independent of the slicing."""
    absV = np.abs(V)
    mant, ex = np.frexp(absV)
    X = (ex - 53).astype(np.int64)
    nz = absV > 0
    base = np.where(nz, X, np.iinfo(np.int64).max).min(axis=1)
    base[~nz.any(axis=1)] = 0
    S = np.ldexp(absV, -base[:, None])            # exact integers
    top = np.where(nz, ex - base[:, None], 0).max()
    nl = max(1, -(-int(top) // LIMB))
    sg = np.sign(V)
    limbs = [np.mod(np.floor(np.ldexp(S, -LIMB * l)), 2.0 ** LIMB) * sg for l in range(nl)]
    return limbs, base.tolist()


# ---------------------------------------------------------------- the GEMM, entry by entry

def build_context(A, Bt, k, smax):
    ctx = {'A': A, 'Bt': Bt, 'k': k, 'smax': smax}
    ctx['Xs'] = fs.Side(A, smax)
    ctx['Ys'] = fs.Side(Bt, smax)
    ctx['QY'] = [q.astype(np.float64) for q in ctx['Ys'].Q]
    ctx['GX'] = np.array(ctx['Xs'].G, dtype=np.int64)
    ctx['GY'] = np.array(ctx['Ys'].G, dtype=np.int64)
    ctx['sx'] = np.array(ctx['Xs'].sv, dtype=np.int64)
    ctx['sy'] = np.array(ctx['Ys'].sv, dtype=np.int64)
    ctx['nzY'] = ctx['Ys'].nz.astype(np.float64)
    ctx['absBt'] = np.abs(Bt)
    oz2 = []
    for cnt in OZ2_COUNTS:
        ms = fs.coprime_moduli(cnt)
        P2 = fs.ozaki2_bits(k, math.prod(ms))
        sy2 = fs.oz2_side(Bt, P2)
        oz2.append((ms, P2, sy2))
    ctx['oz2'] = oz2
    ctx['ylimbs'], ctx['ybase'] = int_limbs(Bt)
    return ctx


def exact_from_limbs(xl, yl, r, n):
    nd = len(xl) + len(yl) - 1
    diag = [np.zeros((r, n), dtype=np.int64) for _ in range(nd)]
    for a, X in enumerate(xl):
        for c, Y in enumerate(yl):
            T = X @ Y.T
            assert np.abs(T).max(initial=0) < 2.0 ** 53
            diag[a + c] += T.astype(np.int64)
    acc = np.zeros((r, n), dtype=object)
    for d, D in enumerate(diag):
        if D.any():
            acc = acc + (D.astype(object) << (LIMB * d))
    return acc.ravel().tolist()


def process_block(ctx, i0, i1, s_test, rec, stats, nvalidate):
    """Entries (i, j), i0 <= i < i1, all j: exact value, every rounding test, Ozaki-II enclosures."""
    A, Bt, k, smax = ctx['A'], ctx['Bt'], ctx['k'], ctx['smax']
    Xs, Ys = ctx['Xs'], ctx['Ys']
    n = Bt.shape[0]
    r = i1 - i0
    Xb = A[i0:i1]
    sx = ctx['sx'][i0:i1]
    sy = ctx['sy']
    gX = ctx['GX'][i0:i1]
    gY = ctx['GY']
    base = gX[:, -1][:, None] + gY[:, -1][None, :]

    # Ozaki-I slice products (exact on the matrix multiplier), the exact value and the triangle sums.
    t0 = time.time()
    mx, my = max(1, int(sx.max())), max(1, int(sy.max()))
    pairs = {(t, u) for t in range(smax) for u in range(smax - t)}
    pairs |= {(t, u) for t in range(mx) for u in range(my)}
    QXb = [Xs.Q[t][i0:i1].astype(np.float64) for t in range(len(Xs.Q))]
    V = np.zeros((r, n), dtype=object)
    diag = [np.zeros((r, n), dtype=object) for _ in range(smax)]
    for (t, u) in sorted(pairs):
        T = QXb[t] @ ctx['QY'][u].T
        assert np.abs(T).max(initial=0) < 2.0 ** 53
        Ti = T.astype(np.int64)
        if not Ti.any():
            continue
        sh = gX[:, t][:, None] + gY[:, u][None, :] - base
        assert sh.min() >= 0
        term = Ti.astype(object) << sh.astype(object)
        if t < mx and u < my:
            V = V + term
        if t + u < smax:
            diag[t + u] = diag[t + u] + term
    Hs = {}
    acc = np.zeros((r, n), dtype=object)
    for d in range(smax):
        acc = acc + diag[d]
        if d + 1 in s_test:
            Hs[d + 1] = acc.ravel().tolist()
    del diag, acc
    stats['mm_products_simulated'] += len(pairs)
    Vl = V.ravel().tolist()
    Bl = base.ravel().tolist()
    del V
    Nov = (Xs.nz[i0:i1].astype(np.float64) @ ctx['nzY'].T).astype(np.int64).ravel().tolist()
    sabs = (np.abs(Xb) @ ctx['absBt'].T).ravel().tolist()
    stats['time_ozaki1_products'] += time.time() - t0

    # Independent exact product (limbs on each row's own grid).
    t0 = time.time()
    xl, xbase = int_limbs(Xb)
    indep = exact_from_limbs(xl, ctx['ylimbs'], r, n)
    ybase = ctx['ybase']
    del xl
    stats['time_independent_exact'] += time.time() - t0

    # Ozaki-II: exact integer products of the truncated operands, per configuration.
    t0 = time.time()
    oz2b = []
    for (ms, P2, sy2) in ctx['oz2']:
        sx2 = fs.oz2_side(Xb, P2)
        N2 = exact_from_limbs(sx2['limbs'], sy2['limbs'], r, n)
        M = math.prod(ms)
        assert 2 * k * 4 ** P2 < M
        for e in range(min(nvalidate, r * n)):
            ii, j = divmod(e, n)
            a = [int(v) for v in sx2['a'][ii].tolist()]
            c = [int(v) for v in sy2['a'][j].tolist()]
            exact = sum(p * q for p, q in zip(a, c))
            rs = []
            for mod in ms:
                ra = [fs.sym_mod(z, mod) for z in a]
                rc = [fs.sym_mod(z, mod) for z in c]
                assert max(map(abs, ra + rc)) <= 2 ** BITS
                rs.append(sum(p * q for p, q in zip(ra, rc)) % mod)
            stats['validate_oz2'] += 1
            stats['validate_oz2_fail'] += 0 if (exact == N2[e] and fs.crt_reconstruct(ms, rs) == exact) else 1
        oz2b.append((sx2['sh'], sx2['drops'], sx2['maxdiff'], sx2['suma'], N2, sy2))
    stats['time_ozaki2_products'] += time.time() - t0

    # Per entry: rounding tests.
    t0 = time.time()
    XE, YE = Xs.E, Ys.E
    Yabssum = Ys.abssum
    sxl, syl = sx.tolist(), sy.tolist()
    ok1 = rec['ok1']
    ok2 = rec['ok2']
    rne, rounding_test = fs.rne, fs.check
    dy_sub, dy_le, dy_add, dy_mul = fs.dy_sub, fs.dy_le, fs.dy_add, fs.dy_mul
    vb = vr = 0
    for e in range(r * n):
        ii, j = divmod(e, n)
        i = i0 + ii
        vi, bs = Vl[e], Bl[e]
        v = (vi, bs)
        # independent exact product
        if dy_sub(v, (indep[e], xbase[ii] + ybase[j]))[0] != 0:
            stats['validate_independent_fail'] += 1
        stats['validate_independent'] += 1
        if e < nvalidate:
            xf = [Fraction(p) for p in Xb[ii].tolist()]
            yf = [Fraction(p) for p in Bt[j].tolist()]
            stats['validate_fraction'] += 1
            stats['validate_fraction_fail'] += 0 if sum(p * q for p, q in zip(xf, yf)) == fs.dy_frac(v) else 1
        rv = rne(v, FMT)
        zero = vi == 0
        rec['zero'].append(zero)
        rec['tie'].append(False if zero else fs.classify(v, FMT)[0])
        rec['kappa'].append(math.inf if zero else sabs[e] / abs(dy_float(vi, bs)))
        rec['se'].append(max(1, sxl[ii], syl[j]))
        E, F = XE[i], YE[j]
        N = Nov[e]
        for s in s_test:
            Hd = (Hs[s][e], bs)
            mexp = E + F - s * (BITS + 1)
            d = dy_sub(v, Hd)
            ad = (abs(d[0]), d[1])
            for bname, Bc in (('normwise', ((s + 1) * k, mexp)), ('overlap', ((s + 1) * N, mexp))):
                if not dy_le(ad, Bc):
                    vb += 1
                w = rounding_test(Hd, Bc, FMT)
                if w is not None and w != rv:
                    vr += 1
                ok1[bname][s].append(w is not None)
        for c, (shxl, dropx, mdx, sumax, N2, sy2) in enumerate(oz2b):
            shx, shy = shxl[ii], sy2['sh'][j]
            q2 = -(shx + shy)
            H2 = (N2[e], q2)
            brat = dy_add(dy_mul(mdx[ii], Yabssum[j]), dy_mul(sy2['maxdiff'][j], (sumax[ii], -shx)))
            K = ((sy2['suma'][j] + k) if dropx[ii] else 0) + (sumax[ii] if sy2['drops'][j] else 0)
            d = dy_sub(v, H2)
            ad = (abs(d[0]), d[1])
            for bname, Bc in (('rational', brat), ('integer', (K, q2))):
                if not dy_le(ad, Bc):
                    vb += 1
                w = rounding_test(H2, Bc, FMT)
                if w is not None and w != rv:
                    vr += 1
                ok2[bname][c].append(w is not None)
    stats['violations_bound'] += vb
    stats['violations_result'] += vr
    stats['rounding_tests_evaluated'] += r * n * (len(s_test) * len(BOUNDS1) +
                                                  len(OZ2_COUNTS) * len(BOUNDS2))
    stats['entries'] += r * n
    stats['time_entries'] += time.time() - t0


# ---------------------------------------------------------------- tile policies

def tile_view(a, TM, TN):
    m, n = a.shape
    return a.reshape(m // TM, TM, n // TN, TN).swapaxes(1, 2)


def tile_max(a, TM, TN):
    return tile_view(a, TM, TN).max(axis=(2, 3))


def cover_orientations(I, J, TM, TN):
    """Greedy gather schedules for entries (I, J): per orientation, (tiles, tile id per entry)."""
    out = []
    if I.size == 0:
        return [(0, np.zeros(0, dtype=np.int64))]
    big = int(max(I.max(), J.max())) + 2
    for a, b, ta, tb in ((J, I, TN, TM), (I, J, TM, TN)):
        _, ia = np.unique(a, return_inverse=True)
        grp = (ia // ta).astype(np.int64)
        key = grp * big + b
        uk, ik = np.unique(key, return_inverse=True)
        ug = uk // big
        rank = np.arange(len(uk)) - np.searchsorted(ug, ug, side='left')
        tkey = ug * big + rank // tb
        ut, it = np.unique(tkey, return_inverse=True)
        out.append((len(ut), it[ik]))
    return out


def gather_cost(I, J, S, TM, TN, cost_of):
    """Cheapest greedy gather schedule for entries (I, J) whose tile costs cost_of[max S in tile]."""
    best = None
    for nt, tid in cover_orientations(I, J, TM, TN):
        if nt == 0:
            return 0, 0
        tmax = np.zeros(nt, dtype=np.int64)
        np.maximum.at(tmax, tid, S)
        c = int(cost_of[tmax].sum())
        if best is None or c < best[0]:
            best = (c, nt)
    return best


def ideal_cost(S, TT, cost_of):
    """Perfect packing: entries sorted by S, chunks of TT, each paying its largest S."""
    if S.size == 0:
        return 0, 0
    Ss = np.sort(S)
    tops = Ss[TT - 1::TT]
    if Ss.size % TT:
        tops = np.append(tops, Ss[-1])
    return int(cost_of[tops].sum()), int(tops.size)


def scheme_specs(k, se_max):
    specs = {}
    for ss in (PLAIN, rule_list(k)):
        reuse = np.array([sum(1 for t in range(ss[-1]) for u in range(ss[-1] - t) if t < S and u < S)
                          for S in range(se_max + 1)])
        for bound in BOUNDS1:
            extra = 1 if bound == 'overlap' else 0
            inc = [tri(ss[0]) + extra] + [tri(ss[l]) - tri(ss[l - 1]) for l in range(1, len(ss))]
            specs['ozaki1[%s]/%s' % (','.join(map(str, ss)), bound)] = {
                'scheme': 'ozaki1', 'levels': list(ss), 'bound': bound, 'inc': inc,
                'exact_inc': np.array([S * S - reuse[S] for S in range(se_max + 1)]),
                'extra': extra}
    for bound in BOUNDS2:
        specs['ozaki2[%s]/%s' % (','.join(map(str, OZ2_COUNTS)), bound)] = {
            'scheme': 'ozaki2', 'levels': list(OZ2_COUNTS), 'bound': bound, 'inc': list(OZ2_COUNTS),
            'exact_inc': np.array([S * S for S in range(se_max + 1)]), 'extra': 0}
    return specs


def r4(x):
    return None if x is None else round(float(x), 4)


def analyze(spec, lvl, se, svx, svy, k, rng_seed):
    """Tile products on the matrix multiplier and the counts of work off it, for every policy and
    one scheme configuration."""
    m, n = lvl.shape
    L = len(spec['inc'])
    inc = np.array(spec['inc'])
    cum = np.cumsum(inc)
    ex_inc = spec['exact_inc']
    is1 = spec['scheme'] == 'ozaki1'
    W = WEIGHTS
    chunks = -(-k // SPLITK_CHUNK)

    def cost(lv, S):
        return cum[np.minimum(lv, L - 1)] + np.where(lv == L, ex_inc[S], 0)

    cost_e = cost(lvl, se)
    direct_e = (se ** 2 <= inc[0]) if is1 else np.zeros_like(se, dtype=bool)
    cost_e_ad = np.where(direct_e, se ** 2, cost_e)
    out = {'per_entry': {
        'test_succeeded_frac': {str(s): r4((lvl == l).mean()) for l, s in enumerate(spec['levels'])},
        'exact_frac': r4((lvl == L).mean()),
        'products_per_entry_C': r4(cost_e.mean()),
        'products_per_entry_C_adaptive': r4(cost_e_ad.mean()) if is1 else None,
        'exact_fallback_products_per_entry': r4((se ** 2).mean()),
        'saving_C_vs_exact_entry': r4(1 - cost_e.mean() / (se ** 2).mean()),
    }}

    # Counts off the matrix multiplier shared by every policy (per entry, useful work).
    test_prods = cum[np.minimum(lvl, L - 1)] - spec['extra']
    exact_prods = np.where(lvl == L, ex_inc[se], 0)
    n_exact = int((lvl == L).sum())

    def off_mm(issued_dot_products, slices_x, slices_y, tests, recon, conv_rows, compacted=0):
        """Counts and weighted 64-bit integer operations; slices_* per row of A / column of B."""
        c = {}
        c['slice_elements'] = int(k * (np.sum(slices_x) + np.sum(slices_y)))
        if is1:
            c['accumulate_truncated_sum'] = int(test_prods.sum())
            c['accumulate_exact'] = int(exact_prods.sum())
            c['rounding_tests'] = int(tests)
        else:
            c['oz2_convert_elements'] = int(k * sum(conv_rows))
            c['oz2_residues'] = int(k * sum(rw * cnt for rw, cnt in zip(conv_rows, spec['levels'])))
            c['crt_entry_moduli'] = int(sum(rc * cnt for rc, cnt in zip(recon, spec['levels'])))
            c['crt_entry_configs'] = int(sum(recon))
            c['rounding_tests'] = int(tests)
            c['accumulate_exact'] = int(exact_prods.sum())
        c['splitk_chunk_adds'] = int(issued_dot_products * chunks)
        c['exact_roundings'] = n_exact
        c['compacted_entries'] = int(compacted)
        ops = {'slicing': c['slice_elements'] * W['slice_element']}
        if is1:
            ops['accumulate'] = (c['accumulate_truncated_sum'] * W['accumulate_truncated_sum'] +
                                 c['accumulate_exact'] * W['accumulate_exact'])
            ops['rounding_tests'] = c['rounding_tests'] * W['rounding_test_ozaki1']
        else:
            ops['oz2_conversion'] = (c['oz2_convert_elements'] * W['oz2_convert_element'] +
                                     c['oz2_residues'] * W['oz2_residue'])
            ops['oz2_reconstruct'] = (c['crt_entry_moduli'] * W['crt_modulus'] +
                                      c['crt_entry_configs'] * W['crt_final'])
            ops['rounding_tests'] = c['rounding_tests'] * W['rounding_test_ozaki2']
            ops['accumulate'] = c['accumulate_exact'] * W['accumulate_exact']
        ops['splitk_chunks'] = c['splitk_chunk_adds'] * W['splitk_chunk_add']
        ops['exact_rounding'] = n_exact * W['round_exact']
        ops['compaction'] = c['compacted_entries'] * W['compact_entry']
        total = sum(ops.values())
        macs = issued_dot_products * k
        return {'counts': c, 'int64_ops': ops, 'int64_ops_total': int(total),
                'int64_ops_per_entry': round(total / (m * n), 1),
                'int64_ops_per_mm_mac': round(total / macs, 5) if macs else None,
                'int64_ops_per_mm_mac_excl_splitk': round((total - ops['splitk_chunks']) / macs, 6)
                if macs else None}

    lv_cap = np.minimum(lvl, L - 1)
    if is1:
        depth = np.array(spec['levels'] + [INF])
        dep_e = depth[lvl]
        sl_x_C = np.minimum(dep_e.max(axis=1), svx)
        sl_y_C = np.minimum(dep_e.max(axis=0), svy)
        tests_C = int((lv_cap + 1).sum())
        recon_C = None
        conv_C = None
    else:
        ex_rows = (lvl == L).any(axis=1)
        ex_cols = (lvl == L).any(axis=0)
        sl_x_C = np.where(ex_rows, svx, 0)
        sl_y_C = np.where(ex_cols, svy, 0)
        tests_C = int((lv_cap + 1).sum())
        recon_C = [int((lvl >= c).sum()) for c in range(L)]
        conv_C = [int((lvl >= c).any(axis=1).sum() + (lvl >= c).any(axis=0).sum()) for c in range(L)]

    # The work off the matrix multiplier of the always-exact baseline (exact fallback per entry).
    exact_base = {'slice_elements': int(k * (svx.sum() + svy.sum())),
                  'accumulate_exact': int((se ** 2).sum()), 'exact_roundings': int(m * n)}
    eb_ops = (exact_base['slice_elements'] * W['slice_element'] +
              exact_base['accumulate_exact'] * W['accumulate_exact'] +
              exact_base['exact_roundings'] * W['round_exact'] +
              int((se ** 2).sum()) * chunks * W['splitk_chunk_add'])
    out['exact_entry_off_mm'] = {'counts': exact_base, 'int64_ops_total': int(eb_ops),
                                 'int64_ops_per_entry': round(eb_ops / (m * n), 1)}

    perm = np.random.default_rng(rng_seed).permutation(m * n)
    out['tiles'] = {}
    for (TM, TN) in MMA_SHAPES + COARSE_SHAPES:
        TT = TM * TN
        nt = (m // TM) * (n // TN)
        mma = (TM, TN) in MMA_SHAPES
        res = {'tiles_per_level0': nt}
        LT = tile_max(lvl, TM, TN)
        ST = tile_max(se, TM, TN)
        cT = cost(LT, ST)
        A_prod = int(cT.sum())
        E_T = int((ST ** 2).sum())
        E_C = (se ** 2).sum() / TT
        E_G = nt * int(se.max()) ** 2
        C_prod = cost_e.sum() / TT
        res['exact_tile'] = E_T
        res['exact_entry'] = r4(E_C)
        res['exact_global'] = E_G
        res['C'] = r4(C_prod)
        res['A'] = A_prod
        lvl_sh = lvl.ravel()[perm].reshape(m, n)
        se_sh = se.ravel()[perm].reshape(m, n)
        res['A_shuffled'] = int(cost(tile_max(lvl_sh, TM, TN), tile_max(se_sh, TM, TN)).sum())
        res['A_tile_level_hist'] = {str(l): int((LT == l).sum()) for l in range(L + 1)}
        if is1:
            dT = ST ** 2 <= inc[0]
            res['A_adaptive'] = int(np.where(dT, ST ** 2, cT).sum())
            res['C_adaptive'] = r4(cost_e_ad.sum() / TT)
        if mma:
            # B: level 0 on every tile, then compaction.
            I, J = np.indices((m, n))
            bi = nt * int(inc[0])
            bg = nt * int(inc[0])
            used_g = []
            for l in range(1, L):
                msk = lvl >= l
                cnt = int(msk.sum())
                bi += -(-cnt // TT) * int(inc[l])
                ntg = cover_orientations(I[msk], J[msk], TM, TN)
                ntg = min(x[0] for x in ntg)
                bg += ntg * int(inc[l])
                used_g.append((cnt, ntg))
            mskx = lvl == L
            ci, nti = ideal_cost(se[mskx], TT, ex_inc)
            bi += ci
            # exact fallback, gather: all together or per s_e class
            cg_all, ntg_all = gather_cost(I[mskx], J[mskx], se[mskx], TM, TN, ex_inc)
            cg_cls, ntg_cls = 0, 0
            for s in np.unique(se[mskx]):
                mm = mskx & (se == s)
                c1, n1 = gather_cost(I[mm], J[mm], se[mm], TM, TN, ex_inc)
                cg_cls += c1
                ntg_cls += n1
            cg, ntgx = (cg_all, ntg_all) if cg_all <= cg_cls else (cg_cls, ntg_cls)
            bg += cg
            used_g.append((int(mskx.sum()), ntgx))
            res['B_ideal'] = bi
            res['B_gather'] = bg
            res['B_gather_density'] = [{'entries': a, 'tiles': b,
                                        'fill': r4(a / (b * TT)) if b else None} for a, b in used_g]
            if is1:
                # adaptive B: tiles whose exact fallback is no dearer than the first rounding test go
                # straight to it.
                dT = ST ** 2 <= inc[0]
                dE = np.repeat(np.repeat(dT, TM, axis=0), TN, axis=1)
                act = ~dE
                bga = int((ST[dT] ** 2).sum()) + int((~dT).sum()) * int(inc[0])
                for l in range(1, L):
                    msk = (lvl >= l) & act
                    bga += min(x[0] for x in cover_orientations(I[msk], J[msk], TM, TN)) * int(inc[l])
                mskx = (lvl == L) & act
                c_all = gather_cost(I[mskx], J[mskx], se[mskx], TM, TN, ex_inc)[0]
                c_cls = sum(gather_cost(I[mskx & (se == s)], J[mskx & (se == s)],
                                        se[mskx & (se == s)], TM, TN, ex_inc)[0]
                            for s in np.unique(se[mskx]))
                res['B_gather_adaptive'] = bga + min(c_all, c_cls)
        # ratios and savings
        sav_C = 1 - C_prod / E_C
        res['dot_products_per_entry'] = {
            key: r4(res[key] * TT / (m * n)) for key in
            ('exact_tile', 'exact_entry', 'exact_global', 'C', 'A', 'A_shuffled', 'B_ideal', 'B_gather',
             'A_adaptive', 'C_adaptive', 'B_gather_adaptive') if key in res}
        rel = {}
        for key in ('A', 'A_shuffled', 'B_ideal', 'B_gather'):
            if key not in res:
                continue
            x = res[key]
            # survival: the fraction of the per-entry (policy C) absolute saving that policy x keeps,
            # against the tiled exact fallback (like for like) or the per-entry one (conservative)
            rel[key] = {'vs_exact_tile': r4(x / E_T), 'vs_exact_entry': r4(x / E_C),
                        'vs_C': r4(x / C_prod),
                        'saving_vs_exact_tile': r4(1 - x / E_T), 'saving_vs_exact_entry': r4(1 - x / E_C),
                        'survival_like_for_like': r4((E_T - x) / (E_T - C_prod))
                        if E_T - C_prod > 0.005 * E_T else None,
                        'survival_conservative': r4((E_C - x) / (E_C - C_prod))
                        if E_C - C_prod > 0.005 * E_C else None}
        rel['C'] = {'vs_exact_tile': r4(C_prod / E_T), 'vs_exact_entry': r4(C_prod / E_C),
                    'saving_vs_exact_entry': r4(sav_C), 'saving_vs_exact_tile': r4(1 - C_prod / E_T)}
        res['relative'] = rel
        if (TM, TN) == (16, 8):
            res['mma_m16n8k16_per_tile_product'] = chunks
            res['mma_m16n8k16_instructions'] = {
                key: int(round(res[key] * chunks)) for key in
                ('exact_tile', 'exact_entry', 'C', 'A', 'B_ideal', 'B_gather') if key in res}
        # counts off the matrix multiplier, per policy, for the 16 x 8 MMA shape
        if (TM, TN) == MMA_SHAPES[0]:
            oe = {}
            compacted = int(sum((lvl >= l).sum() for l in range(1, L + 1)))
            iss = {key: res[key] * TT for key in ('A', 'B_ideal', 'B_gather') if key in res}
            iss['C'] = C_prod * TT
            if is1:
                DT = np.where(LT < L, depth[np.minimum(LT, L - 1)], INF)
                sl_x_A = np.minimum(np.repeat(DT.max(axis=1), TM), svx)
                sl_y_A = np.minimum(np.repeat(DT.max(axis=0), TN), svy)
                tests_A = int(((np.minimum(LT, L - 1) + 1) * TT).sum())
                oe['A'] = off_mm(iss['A'], sl_x_A, sl_y_A, tests_A, None, None)
                for key in ('B_ideal', 'B_gather', 'C'):
                    oe[key] = off_mm(iss[key], sl_x_C, sl_y_C, tests_C, None, None,
                                        compacted if key != 'C' else 0)
            else:
                exT = LT == L
                sl_x_A = np.where(np.repeat(exT.any(axis=1), TM), svx, 0)
                sl_y_A = np.where(np.repeat(exT.any(axis=0), TN), svy, 0)
                recon_A = [int((LT >= c).sum()) * TT for c in range(L)]
                conv_A = [int((LT >= c).any(axis=1).sum() * TM + (LT >= c).any(axis=0).sum() * TN)
                          for c in range(L)]
                tests_A = int(((np.minimum(LT, L - 1) + 1) * TT).sum())
                oe['A'] = off_mm(iss['A'], sl_x_A, sl_y_A, tests_A, recon_A, conv_A)
                for key in ('B_ideal', 'B_gather', 'C'):
                    oe[key] = off_mm(iss[key], sl_x_C, sl_y_C, tests_C, recon_C, conv_C,
                                        compacted if key != 'C' else 0)
            res['off_mm'] = oe
        out['tiles']['%dx%d' % (TM, TN)] = res
    return out


# ---------------------------------------------------------------- driver

def run_one(name, k, m, n, block, nvalidate):
    t_start = time.time()
    A, Bt = make_gemm(name, m, n, k)
    plain, rule = PLAIN, rule_list(k)
    s_test = sorted(set(plain) | set(rule))
    smax = max(s_test)
    ctx = build_context(A, Bt, k, smax)
    rec = {'se': [], 'zero': [], 'tie': [], 'kappa': [],
           'ok1': {bd: {s: [] for s in s_test} for bd in BOUNDS1},
           'ok2': {bd: {c: [] for c in range(len(OZ2_COUNTS))} for bd in BOUNDS2}}
    stats = {key: 0 for key in ('entries', 'rounding_tests_evaluated', 'violations_bound',
                                'violations_result',
                                'validate_independent', 'validate_independent_fail',
                                'validate_fraction', 'validate_fraction_fail', 'validate_oz2',
                                'validate_oz2_fail', 'mm_products_simulated')}
    for key in ('time_ozaki1_products', 'time_independent_exact', 'time_ozaki2_products', 'time_entries'):
        stats[key] = 0.0
    for i0 in range(0, m, block):
        process_block(ctx, i0, min(m, i0 + block), s_test, rec, stats, nvalidate)
    svx = np.array(ctx['Xs'].sv, dtype=np.int64)
    svy = np.array(ctx['Ys'].sv, dtype=np.int64)
    oz2_cfgs = [{'moduli_count': len(ms), 'P': P2, 'log2_M': round(math.log2(math.prod(ms)), 2)}
                for ms, P2, _ in ctx['oz2']]
    del ctx
    se = np.array(rec['se'], dtype=np.int64).reshape(m, n)
    zero = np.array(rec['zero']).reshape(m, n)
    tie = np.array(rec['tie']).reshape(m, n)
    kap = np.array(rec['kappa'])
    res = {'dataset': name, 'description': DESCRIPTIONS[name], 'm': m, 'n': n, 'k': k,
           'ss_plain': plain, 'ss_rule': rule, 'ozaki2_configs': oz2_cfgs,
           'frac_exact_zero': r4(zero.mean()), 'frac_tie': r4(tie.mean()),
           'se_hist': {str(int(a)): int(b) for a, b in zip(*np.unique(se, return_counts=True))},
           'sx_rows_hist': {str(int(a)): int(b) for a, b in zip(*np.unique(svx, return_counts=True))},
           'sy_cols_hist': {str(int(a)): int(b) for a, b in zip(*np.unique(svy, return_counts=True))}}
    fin = kap[np.isfinite(kap)]
    if fin.size:
        res['kappa_log10_p10_p50_p90'] = [round(float(np.percentile(np.log10(fin), p)), 2)
                                          for p in (10, 50, 90)]
    specs = scheme_specs(k, int(se.max()))
    res['schemes'] = {}
    nonmono = {}
    for key, spec in specs.items():
        if spec['scheme'] == 'ozaki1':
            oks = [np.array(rec['ok1'][spec['bound']][s]).reshape(m, n) for s in spec['levels']]
        else:
            oks = [np.array(rec['ok2'][spec['bound']][c]).reshape(m, n) for c in range(len(OZ2_COUNTS))]
        L = len(oks)
        lvl = np.full((m, n), L, dtype=np.int64)
        for l in range(L - 1, -1, -1):
            lvl[oks[l]] = l
        nonmono[key] = int(sum(int((oks[l] & ~oks[l + 1]).sum()) for l in range(L - 1)))
        res['schemes'][key] = analyze(spec, lvl, se, svx, svy, k,
                                      fs.stable_seed('shuffle', name, k, key))
    stats['nonmonotone_succeeded_then_failed'] = nonmono
    stats['seconds'] = round(time.time() - t_start, 1)
    for key in list(stats):
        if key.startswith('time_'):
            stats[key] = round(stats[key], 1)
    res['checks'] = stats
    return res


def meta_block(args):
    return {
        'script': 'scripts/tile_sim.py',
        'uses': 'scripts/fallback_sim.py (slicing, Ozaki-II truncation and CRT, rounding, generators)',
        'format': FMT_NAME, 'slice_bits_b': BITS, 'm': args.m, 'n': args.n,
        'sizes_k': [int(x) for x in args.sizes.split(',')],
        'sampling': 'none: every entry of every 256 x 256 output is simulated (65,536 per GEMM)',
        'mma_shapes': ['%dx%d' % s for s in MMA_SHAPES],
        'coarse_shapes_policy_A_only': ['%dx%d' % s for s in COARSE_SHAPES],
        'splitk_chunk_products': SPLITK_CHUNK,
        'ozaki1_lists': {'plain': PLAIN, 'rule': 'slicesForCR: [s0, s0+1], s0 = slicesFor 11 (53 + clog2 k)'},
        'ozaki2_moduli_counts': OZ2_COUNTS,
        'weights_int64_ops': WEIGHTS,
        'cost_model': {
            'mm_unit': 'A tile product is one TM x TN output tile times one slice or residue product of '
                       'inner dimension k on the matrix multiplier. With 11-bit slices, split-K runs '
                       'chunks of 4 products with one mma.m16n8k16 per chunk (OzakiTC SliceRun.blocks), '
                       'so a 16x8 tile product is ceil(k/4) MMA instructions. dot_products_per_entry = '
                       'tile products x TM TN / (m n), the number of dot products of length k per '
                       'output entry.',
            'C': 'The per-entry costs of fallback_sim (prefix reuse, an exact fallback of s_e^2 minus '
                 'the reused pairs, +1 for the zero-aware indicator product), summed and divided by '
                 'TM TN.',
            'A': 'The level of an entry is the first level at which its rounding test succeeds (the '
                 'exact fallback if none does), and the level of a tile is the largest level of its '
                 'entries; the tile pays the cumulative cost of that level, with S = max s_e in the '
                 'tile for the exact fallback.',
            'A_shuffled': 'A on tiles of uniformly permuted entries (no correlation inside a tile).',
            'B_ideal': 'Level 0 runs on all tiles; level l runs on ceil(#failed/TM TN) tiles, where '
                       '#failed counts the entries whose rounding test failed at every earlier level; '
                       'the exact fallback runs on the entries sorted by s_e, packed TM TN per tile, '
                       'each tile paying its max s_e.',
            'B_gather': 'As B_ideal, but a tile is TM gathered rows x TN gathered columns (an outer '
                        'product) covering the entries whose rounding test failed, with a greedy '
                        'schedule (see the docstring).',
            'adaptive': 'A tile (A, B) or entry (C) with S^2 at most the cost of the first rounding '
                        'test goes straight to the exact fallback (ozaki1CRA).',
            'baselines': 'exact_tile: S^2 per tile; exact_entry: sum s_e^2 / TM TN; exact_global: '
                         '(max s_e)^2 per tile.',
            'off_mm': 'Work off the matrix multiplier: slicing once per matrix to the depth an issued '
                      'product needs; accumulation of useful products only (masked entries skip it); '
                      'rounding tests on whole tiles for A and on the entries still undecided for B '
                      'and C; Ozaki-II conversion of the rows and columns involved per configuration, '
                      'and CRT per modulus for each reconstructed entry (whole tiles for A).',
            'survival': 'The fraction of the per-entry absolute saving that policy X keeps: '
                        '(exact_tile - X) / (exact_tile - C) (like for like: both tiled) and '
                        '(exact_entry - X) / (exact_entry - C) (conservative: early exit pays tile '
                        'costs while the exact-fallback baseline is charged per entry); 1 = all kept, '
                        '<= 0 = none; null when early exit per entry saves less than 0.5 %.',
        },
        'caveats': 'A model of issued instructions and 64-bit integer operations, not GPU time; memory '
                   'traffic, gathers, latency and occupancy are not modelled; the input '
                   'distributions are chosen; entries of one GEMM share rows and columns, so their '
                   'outcomes are correlated (A_shuffled shows the uncorrelated case).',
    }


def main():
    ap = argparse.ArgumentParser(description=__doc__.split('\n')[0])
    ap.add_argument('--out', default='data/tile-sim.json')
    ap.add_argument('--sizes', default='256,1024,4096')
    ap.add_argument('--datasets', default=','.join(DATASETS))
    ap.add_argument('--m', type=int, default=256)
    ap.add_argument('--n', type=int, default=256)
    ap.add_argument('--block', type=int, default=32, help='rows of A per block (memory)')
    ap.add_argument('--validate', type=int, default=2,
                    help='entries per block of rows checked against Fraction arithmetic and the CRT')
    ap.add_argument('--jobs', type=int, default=4)
    ap.add_argument('--summary', metavar='JSON', help='print markdown tables from a results file')
    ap.add_argument('--all', action='store_true', help='with --summary: every scheme configuration')
    args = ap.parse_args()
    if args.summary:
        print_summary(json.load(open(args.summary)), args.all)
        return
    for TM, TN in MMA_SHAPES + COARSE_SHAPES:
        assert args.m % TM == 0 and args.n % TN == 0
    sizes = [int(s) for s in args.sizes.split(',')]
    names = [x for x in args.datasets.split(',') if x]
    jobs = [(name, k) for k in sizes for name in names]
    meta = meta_block(args)
    results = {}
    t_all = time.time()
    with ProcessPoolExecutor(max_workers=args.jobs) as ex:
        futs = {ex.submit(run_one, name, k, args.m, args.n, args.block, args.validate): (name, k)
                for name, k in jobs}
        for fut in as_completed(futs):
            r = fut.result()
            results[futs[fut]] = r
            c = r['checks']
            fails = sum(v for kk, v in c.items() if kk.endswith('_fail'))
            t = r['schemes']['ozaki1[5,6]/normwise']['tiles']['16x8']['dot_products_per_entry']
            print(f"k={r['k']:5d} {r['dataset']:11s} {c['seconds']:7.1f}s viol={c['violations_bound']}/"
                  f"{c['violations_result']} valfail={fails} O-I[5,6] C={t['C']} A={t['A']} "
                  f"Bg={t['B_gather']} exT={t['exact_tile']}", file=sys.stderr, flush=True)
            meta['total_seconds'] = round(time.time() - t_all, 1)
            ordered = [results[j] for j in jobs if j in results]
            write_json(args.out, meta, ordered)


def write_json(path, meta, results):
    """Indented meta, one compact line per result (keeps the file small and diffable)."""
    with open(path, 'w') as fh:
        fh.write('{"meta": ' + json.dumps(meta, indent=1) + ',\n "results": [\n')
        fh.write(',\n'.join(json.dumps(r, separators=(',', ':')) for r in results))
        fh.write('\n]}\n')


# ---------------------------------------------------------------- markdown summary

MAIN = ['ozaki1[5,6]/normwise', 'ozaki1[6,7]/overlap', 'ozaki2[12,13,14]/rational']


def f2(x):
    return '-' if x is None else f'{x:.2f}'


def print_summary(data, all_schemes=False):
    res = data['results']
    keys = list(res[0]['schemes'].keys()) if all_schemes else [k for k in MAIN if k in res[0]['schemes']]
    tot = {}
    for r in res:
        for kk, v in r['checks'].items():
            if isinstance(v, int):
                tot[kk] = tot.get(kk, 0) + v
    print(f"Soundness: {tot['entries']} entries, {tot['rounding_tests_evaluated']} enclosures; enclosure "
          f"violations {tot['violations_bound']}; accepted rounding test != RNE(exact) "
          f"{tot['violations_result']}; "
          f"slice-exact vs independent exact product {tot['validate_independent_fail']}/"
          f"{tot['validate_independent']} mismatches; Fraction {tot['validate_fraction_fail']}/"
          f"{tot['validate_fraction']}; Ozaki-II limbs and CRT {tot['validate_oz2_fail']}/{tot['validate_oz2']}.")
    worst = 0.0
    for r in res:
        for key in r['schemes']:
            for sh in ('16x8', '16x16'):
                p = r['schemes'][key]['tiles'][sh]['dot_products_per_entry']
                worst = max(worst, p['B_ideal'] / p['C'] - 1)
    print(f'B_ideal exceeds C by at most {100 * worst:.1f} % (all schemes, 16x8 and 16x16).')

    for key in keys:
        print(f'\n### {key}: dot products of length k per output entry on the matrix multiplier, '
              '16x8 tiles\n')
        print('| data | k | fallback | exact tile (entry) | C | A | A shuffled | B ideal | B gather | '
              'kept A (tiled / cons.) | kept B gather (tiled / cons.) |')
        print('|---|---|---|---|---|---|---|---|---|---|---|')
        for r in res:
            s = r['schemes'][key]
            t = s['tiles']['16x8']
            p = t['dot_products_per_entry']
            rel = t['relative']
            print(f"| {r['dataset']} | {r['k']} | {100 * s['per_entry']['exact_frac']:.2f}% | "
                  f"{p['exact_tile']:.1f} ({p['exact_entry']:.1f}) | {p['C']:.1f} | {p['A']:.1f} | "
                  f"{p['A_shuffled']:.1f} | {p['B_ideal']:.1f} | {p['B_gather']:.1f} | "
                  f"{f2(rel['A']['survival_like_for_like'])} / {f2(rel['A']['survival_conservative'])} | "
                  f"{f2(rel['B_gather']['survival_like_for_like'])} / "
                  f"{f2(rel['B_gather']['survival_conservative'])} |")

    shapes = ['16x8', '16x16', '64x64', '128x128']
    kmax = max(r['k'] for r in res)
    print(f'\n### Policy A by decision granularity, k = {kmax}: A (exact tile) per entry\n')
    print('| data | scheme | C | ' + ' | '.join(shapes) + ' |')
    print('|---|---|---|' + '---|' * len(shapes))
    for r in res:
        if r['k'] != kmax:
            continue
        for key in keys[1:]:
            s = r['schemes'][key]['tiles']
            cells = [f"{s[sh]['dot_products_per_entry']['A']:.1f} "
                     f"({s[sh]['dot_products_per_entry']['exact_tile']:.1f})" for sh in shapes]
            print(f"| {r['dataset']} | {key} | {s['16x8']['dot_products_per_entry']['C']:.1f} | "
                  + ' | '.join(cells) + ' |')

    print('\n### Ozaki-I adaptive shortcut (zero-aware bound), low-precision inputs, per entry, 16x8\n')
    print('| data | k | list | exact tile (entry) | C adaptive | A adaptive | B gather adaptive | '
          'without shortcut: C / A / B gather |')
    print('|---|---|---|---|---|---|---|---|')
    for r in res:
        if r['dataset'] not in ('fp16', 'int8'):
            continue
        for key in r['schemes']:
            if not (key.startswith('ozaki1') and key.endswith('overlap')):
                continue
            p = r['schemes'][key]['tiles']['16x8']['dot_products_per_entry']
            print(f"| {r['dataset']} | {r['k']} | {key.split('/')[0][6:]} | {p['exact_tile']:.1f} "
                  f"({p['exact_entry']:.1f}) | {p['C_adaptive']:.1f} | {p['A_adaptive']:.1f} | "
                  f"{p['B_gather_adaptive']:.1f} | {p['C']:.1f} / {p['A']:.1f} / {p['B_gather']:.1f} |")

    print('\n### 64-bit integer operations off the matrix multiplier per output entry, 16x8 '
          '(split-K chunk additions apart)\n')
    print('Cell: B gather total = slicing or conversion + accumulate + rounding tests + CRT + (exact '
          'rounding and compaction); [A total; C total]; per MAC on the matrix multiplier under B '
          'gather. Last column: split-K chunk additions per entry under B gather (2 integer '
          'operations each), proportional to the number of products on the matrix multiplier.\n')
    print('| data | k | ' + ' | '.join(keys) + ' | exact fallback alone | split-K adds (' +
          ' / '.join(keys) + ') |')
    print('|---|---|' + '---|' * (len(keys) + 2))
    for r in res:
        ne = r['m'] * r['n']
        cells, adds = [], []
        for key in keys:
            oe = r['schemes'][key]['tiles']['16x8']['off_mm']

            def excl(o):
                return (o['int64_ops_total'] - o['int64_ops']['splitk_chunks']) / ne
            w = oe['B_gather']['int64_ops']
            conv = w['slicing'] + w.get('oz2_conversion', 0)
            other = w['exact_rounding'] + w['compaction']
            cells.append(f"{excl(oe['B_gather']):.0f} = {conv / ne:.0f}+{w['accumulate'] / ne:.0f}+"
                         f"{w['rounding_tests'] / ne:.0f}+{w.get('oz2_reconstruct', 0) / ne:.0f}+"
                         f"{other / ne:.0f} "
                         f"[{excl(oe['A']):.0f}; {excl(oe['C']):.0f}]; "
                         f"{oe['B_gather']['int64_ops_per_mm_mac_excl_splitk']:.4f}/MAC")
            adds.append(f"{oe['B_gather']['counts']['splitk_chunk_adds'] / ne:.0f}")
        ex = r['schemes'][keys[0]]['exact_entry_off_mm']
        exc = ex['counts']
        ex_excl = (exc['slice_elements'] * WEIGHTS['slice_element'] +
                   exc['accumulate_exact'] * WEIGHTS['accumulate_exact'] +
                   exc['exact_roundings'] * WEIGHTS['round_exact']) / ne
        print(f"| {r['dataset']} | {r['k']} | " + ' | '.join(cells) + f" | {ex_excl:.0f} | "
              + ' / '.join(adds) + ' |')


if __name__ == '__main__':
    main()
