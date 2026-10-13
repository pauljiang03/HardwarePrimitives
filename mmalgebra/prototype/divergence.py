"""How far apart can two reduction schedules be? Bounds, worst cases and typical differences.

For a term t over products p_l = a_l b_l (and possibly c), V(t) is the exact value and t(x) the
model's output. The structural bound E(t; x) satisfies |t(x) - V(t)| <= E(t; x); it is built
from the per-block error theorems of the two models and the error of a binary32 addition:

  Tensor Cores   |D - exact| < (K + 1) 2^(eta - F) + ulp(D)              (evalBlock_error_bound)
                 with 2^eta <= max(G, |c|, 2^-126, 2^e_align_min), G = max 2^(e_a + e_b) over the
                 block's nonzero products, ulp(D) <= 2^-23 |D| + 2^-149 and |D| <= |c| + sum |p|
  CDNA 1, SFMA   |d - exact| <= 2^-24 A + 2^-150                         (correctRounding_apriori)
  CDNA 2         |d - exact| <= (flushed inputs) + 2^-21 A + 2^-120        (pairwise_apriori)
  CDNA 3         |d - exact| <= 2^-23 A + (n + 4) 2^(e_max - 24) + 2^-149  (aligned_apriori)
  binary32 add   |fl(x + y) - (x + y)| <= 2^-24 |x + y|  (exact when the sum is subnormal)

with A = |c| + sum |p| for the block. A block's accumulator input is a computed value, so |c| is
bounded by M(child) + E(child); the recursion is

  E(blk(t, I)) = E(t) + err_blk(M(t) + E(t), I),     E(t + u) = E(t) + E(u) + u (M(t) + E(t) + M(u) + E(u)).

Then |t1(x) - t2(x)| <= E(t1; x) + E(t2; x) for terms over the same products, on one architecture
or two. A subterm that both terms share (same architecture) has the same computed value in both,
so it can be treated as a leaf with no error and magnitude M(s) + E(s): the bound only counts the
work after the schedules part. If every block and addition of both terms is exact, the terms agree.

Usage: python3 divergence.py           (tightness study, k = 64; writes results/divergence.txt)
"""
import json
import math
import os
import random
import struct
import sys
from fractions import Fraction as Q
from multiprocessing import Pool

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from normal import *  # noqa

RESULTS = os.path.join(os.path.dirname(os.path.abspath(__file__)), 'results')
sys.setrecursionlimit(20000)  # chains of 1,024 one-product blocks are deep terms
U = Q(1, 2 ** 24)  # unit roundoff of binary32


# ------------------------------------------------------------------ structural bound
def word_exp(fmt, w):
    """Exponent of an operand as the matrix multiplier sees it (subnormals: the minimum normal)."""
    d = fmt.decode(w)
    return d[2]


def block_err(P, A, prods, c_sub=Q(0)):
    """Bound on |block output - exact| for a block with accumulator magnitude bound A_c = A[0]
    and products `prods` (list of (a, b) words); A = (A_c, sum |p|). `c_sub` is |c| when the
    accumulator input is the initial c and is subnormal (CDNA 2 flushes it)."""
    Ac, Ap = A
    tot = Ac + Ap
    name = P.name
    nz = [(a, b) for a, b in prods if P.fmt.value(a) != 0 and P.fmt.value(b) != 0]
    if isinstance(P, TCProfile):
        F = P.F
        G = max((p2(word_exp(P.fmt, a) + word_exp(P.fmt, b)) for a, b in nz), default=Q(0))
        top = max(G, Ac, p2(-126), p2(P.floor) if P.floor is not None else Q(0))
        return (P.K + 1) * top * p2(-F) + p2(-23) * tot + p2(-149)
    if P.acc == 'cr':
        return p2(-24) * tot + p2(-150)
    if P.acc == 'pw':
        flushed = sum((abs(P.fmt.value(a) * P.fmt.value(b)) for a, b in prods
                       if (P.fmt.decode(a)[1] < (1 << P.fmt.mbits) and P.fmt.value(a) != 0) or
                       (P.fmt.decode(b)[1] < (1 << P.fmt.mbits) and P.fmt.value(b) != 0)), Q(0))
        return flushed + c_sub + p2(-21) * tot + p2(-120)
    if P.acc == 'ga':
        G = max((p2(word_exp(P.fmt, a) + word_exp(P.fmt, b)) for a, b in nz), default=Q(0))
        return p2(-23) * tot + (P.K + 4) * G * p2(-24) + p2(-149)
    raise ValueError(name)


def leaves(t):
    tag = t[0]
    if tag == 'zero':
        return []
    if tag == 'c0':
        return ['c']
    if tag == 'blk':
        return leaves(t[1]) + [i for i in t[2] if i is not None]
    return leaves(t[1]) + leaves(t[2])


def bound(P, t, a, b, c0, shared=frozenset(), _memo=None):
    """(E, M): error bound and magnitude of term t on input (a, b, c0). Subterms whose repr is in
    `shared` are treated as exact leaves of magnitude M + E."""
    tag = t[0]
    if repr(t) in shared:
        E, M = bound(P, t, a, b, c0)
        return Q(0), M + E
    if tag == 'zero':
        return Q(0), Q(0)
    if tag == 'c0':
        return Q(0), abs(value32(c0))
    if tag == 'blk':
        Ec, Mc = bound(P, t[1], a, b, c0, shared)
        prods = [(a[i], b[i]) for i in t[2] if i is not None]
        Mp = sum((abs(P.fmt.value(x) * P.fmt.value(y)) for x, y in prods), Q(0))
        c_sub = abs(value32(c0)) if t[1] == ('c0',) and is_sub32(c0) else Q(0)
        return Ec + block_err(P, (Mc + Ec, Mp), prods, c_sub), Mc + Mp
    E1, M1 = bound(P, t[1], a, b, c0, shared)
    E2, M2 = bound(P, t[2], a, b, c0, shared)
    return E1 + E2 + U * (M1 + E1 + M2 + E2), M1 + M2


def subterms(t, out=None):
    out = set() if out is None else out
    if t[0] in ('blk', 'add', 'addftz'):
        out.add(repr(t))
        subterms(t[1], out)
        if t[0] != 'blk':
            subterms(t[2], out)
    return out


def shared_subterms(t1, t2):
    return frozenset(subterms(t1) & subterms(t2))


def eps_const(P):
    """Relative error constant of one block for inputs with normal operands (u = 2^-24 units)."""
    if isinstance(P, TCProfile):
        return (P.K + 1) * p2(-P.F) + p2(-23)
    return {'cr': p2(-24), 'pw': p2(-21), 'ga': p2(-23) + (P.K + 4) * p2(-24)}[P.acc]


def rho(P, t, shared=frozenset()):
    """Constant form: E(t) <= rho(t) * M + (tiny absolute terms), for normal operands."""
    tag = t[0]
    if repr(t) in shared or tag in ('zero', 'c0'):
        return Q(0)
    if tag == 'blk':
        e = eps_const(P)
        return (1 + e) * rho(P, t[1], shared) + e
    return (1 + U) * max(rho(P, t[1], shared), rho(P, t[2], shared)) + U


def rho_pair(P1, t1, P2, t2):
    """rho bound of |t1 - t2| / M, with shared subterms when both use the same model."""
    sh = shared_subterms(t1, t2) if P1 is P2 else frozenset()
    if sh:
        # a shared leaf s contributes (1 + rho(s)) M(s): fold it in by bounding with the
        # unshared rho of each side plus the shared part's own rho on the larger side.
        r1, r2 = rho(P1, t1, sh), rho(P2, t2, sh)
        rs = max((rho(P1, eval_repr(s), frozenset()) for s in sh), default=Q(0))
        return r1 * (1 + rs) + r2 * (1 + rs)
    return rho(P1, t1) + rho(P2, t2)


def eval_repr(s):
    return eval(s)  # terms are tuples of tags, ints and None


# ------------------------------------------------------------------ inputs
def f16(x):
    x = max(min(x, 65504.0), -65504.0)
    return struct.unpack('<H', struct.pack('<e', x))[0]


def f32(x):
    return struct.unpack('<I', struct.pack('<f', x))[0]


def to_f32_word(fmt, w):
    """Exact binary32 word of an fp16/bf16 operand (for the SFMA, CUDA-core path)."""
    return f32(float(fmt.value(w)))


def is_normal(fmt, w):
    d = fmt.decode(w)
    return d is not None and (d[1] == 0 or d[1] >= (1 << fmt.mbits))


def magnitude(P, a, b, c0, idx):
    return sum((abs(P.fmt.value(a[i]) * P.fmt.value(b[i])) for i in idx), Q(0)) + abs(value32(c0))


def ulp32(w):
    e = (w >> 23) & 0xFF
    return p2(max(e - 127, -126) - 23)


def value_or_none(P, t, a, b, c0):
    try:
        return ev(P, t, a, b, c0)
    except ModelError:
        return None


# ------------------------------------------------------------------ adversarial search
def half_word(e, rng, full=True):
    """A normal fp16 word 2^e * (1.xxx); with `full`, a significand close to 2."""
    e = min(max(e, -14), 15)
    m = ((1 << 10) - 1 - rng.getrandbits(3)) if full else rng.getrandbits(10)
    return ((e + 15) << 10) | m


def anchor_dust(k, rng, P, dust_shift, anchor_pos, sign_mode):
    """One large product (or c) and many small products just below the anchor's alignment grid:
    products a_i b_i ~ 2^(-dust_shift) * (2 - small), with both factors normal."""
    B = rng.choice([0x3c00, 0x3c01, 0x3fff, 0x4000, 0x3e00])           # 1, 1+2^-10, ~2, 2, 1.5
    dexp = -dust_shift
    ea = dexp // 2
    a, b = [], []
    for i in range(k):
        wa, wb = half_word(ea, rng), half_word(dexp - ea, rng)
        s = 0
        if sign_mode == 'alt':
            s = i & 1
        elif sign_mode == 'rand':
            s = rng.getrandbits(1)
        a.append(wa)
        b.append(wb | (s << 15))
    c0 = 0
    if anchor_pos == 'c':
        c0 = f32(float(FP16.value(B)))
    elif anchor_pos in ('first', 'last'):
        i = 0 if anchor_pos == 'first' else k - 1
        a[i], b[i] = 0x3c00, B
    elif anchor_pos == 'each':
        for i in range(0, k, P.K):
            a[i], b[i] = 0x3c00, (B if (i // P.K) % 2 == 0 else B | 0x8000)
    return a, b, c0


def mutate(P, a, b, c0, rng):
    a, b = list(a), list(b)
    i = rng.randrange(len(a))
    arr = a if rng.random() < 0.5 else b
    w = arr[i]
    r = rng.random()
    if r < 0.4:
        w = (w & ~0x3ff) | ((w + rng.choice([-3, -2, -1, 1, 2, 3])) & 0x3ff)
    elif r < 0.7:
        e = (w >> 10) & 0x1f
        e = min(max(e + rng.choice([-1, 1]), 1), 30)
        w = (w & ~(0x1f << 10)) | (e << 10)
    elif r < 0.8:
        w ^= 0x8000
    else:
        w = special_word(P.fmt, rng)
        if not is_normal(P.fmt, w):
            w = 0x3c00
    arr[i] = w
    if rng.random() < 0.05 and c0:
        c0 ^= 1 << rng.randrange(0, 23)
    return a, b, c0


def objective(P1, t1, P2, t2, a, b, c0, idx, conv2=None):
    a2, b2 = (a, b) if conv2 is None else conv2(a, b)
    x = value_or_none(P1, t1, a, b, c0)
    y = value_or_none(P2, t2, a2, b2, c0)
    if x is None or y is None:
        return Q(-1)
    M = magnitude(P1, a, b, c0, idx)
    if M == 0:
        return Q(0)
    return abs(value32(x) - value32(y)) / M


def search(P1, t1, P2, t2, k, seed, evals=1500, conv2=None, c_used=True):
    rng = random.Random(seed)
    idx = range(k)
    best = (Q(-1), None)
    # structured seeds
    cands = []
    for shift in range(20, 31):
        for pos in (('c', 'first', 'last', 'each') if c_used else ('first', 'last', 'each')):
            for sm in ('same', 'alt', 'rand'):
                cands.append(anchor_dust(k, rng, P1, shift, pos, sm))
    for _ in range(6):
        a, b = rand_inputs(P1, k, rng, 'mixed')
        a = [w if is_normal(P1.fmt, w) else 0x3c00 for w in a]
        b = [w if is_normal(P1.fmt, w) else 0x3c00 for w in b]
        cands.append((a, b, f32(rng.gauss(0, 4)) if c_used else 0))
    for a, b, c0 in cands:
        f = objective(P1, t1, P2, t2, a, b, c0, idx, conv2)
        if f > best[0]:
            best = (f, (a, b, c0))
    # hill climbing from the best seeds
    spent = len(cands)
    cur = best
    while spent < evals:
        a, b, c0 = mutate(P1, *cur[1], rng)
        if not c_used:
            c0 = 0
        f = objective(P1, t1, P2, t2, a, b, c0, idx, conv2)
        spent += 1
        if f >= cur[0]:
            cur = (f, (a, b, c0))
            if f > best[0]:
                best = cur
    return best


# ------------------------------------------------------------------ schedules
def chain_from(P, idxs, start):
    s = start
    for i in range(0, len(idxs), P.K):
        B = list(idxs[i:i + P.K])
        s = ('blk', s, tuple(B + [None] * (P.K - len(B))))
    return s


def program(P, k, split=1, combine='serial', c_place='epilogue', cuts=None, order=None):
    """One output entry of a GEMM program: split-K into contiguous parts (or at `cuts`), partials
    combined serially, pairwise, or in a given (atomic arrival) order; C in the first block, in the
    epilogue, or in the atomic buffer."""
    if cuts is None:
        step = k // split
        cuts = [i * step for i in range(split)] + [k]
    parts = [list(range(cuts[i], cuts[i + 1])) for i in range(len(cuts) - 1)]
    partials = [chain_from(P, p, ('c0',) if (c_place == 'first' and j == 0) else ('zero',))
                for j, p in enumerate(parts)]
    if combine == 'serial':
        t = partials[0]
        for u in partials[1:]:
            t = ('add', t, u)
    elif combine == 'tree':
        level = partials
        while len(level) > 1:
            nxt = [('add', level[i], level[i + 1]) for i in range(0, len(level) - 1, 2)]
            if len(level) % 2:
                nxt.append(level[-1])
            level = nxt
        t = level[0]
    elif combine == 'atomic':
        t = ('c0',) if c_place == 'buffer' else ('zero',)
        for j in order:
            t = ('add', t, partials[j])
        return t
    if c_place == 'epilogue':
        t = ('add', t, ('c0',))
    return t


def sfma_program(k, c_place='epilogue'):
    """CUDA-core fallback: a sequential binary32 FMA over the products (SFMA semantics)."""
    t = ('c0',) if c_place == 'first' else ('zero',)
    for i in range(k):
        t = ('blk', t, (i,))
    return ('add', t, ('c0',)) if c_place == 'epilogue' else t


def conv_sfma(a, b):
    return [to_f32_word(FP16, w) for w in a], [to_f32_word(FP16, w) for w in b]


# ------------------------------------------------------------------ tightness study (k = 64)
PAIRS64 = [
    ('no split / split-K 2', dict(), dict(split=2)),
    ('no split / split-K 4 pairwise', dict(), dict(split=4, combine='tree')),
    ('C in the first block / C in the epilogue', dict(c_place='first'), dict()),
    ('stream-K cut after 24 / after 16', dict(split=2, cuts=[0, 24, 64]), dict(split=2, cuts=[0, 16, 64])),
]


def tight_task(args):
    pname, label, kw1, kw2, seed = args
    P = {p.name: p for p in ALL + [SFMA]}[pname]
    k = 64
    t1, t2 = program(P, k, **kw1), program(P, k, **kw2)
    sh = shared_subterms(t1, t2)
    f, (a, b, c0) = search(P, t1, P, t2, k, seed, evals=2500)
    E1, M = bound(P, t1, a, b, c0)
    E2, _ = bound(P, t2, a, b, c0)
    S1, _ = bound(P, t1, a, b, c0, sh)
    S2, _ = bound(P, t2, a, b, c0, sh)
    x, y = ev(P, t1, a, b, c0), ev(P, t2, a, b, c0)
    assert abs(value32(x) - value32(y)) <= S1 + S2 <= E1 + E2 + p2(-100), (pname, label)
    return dict(variant=pname, pair=label, worst_u=float(f / U), bound_u=float((E1 + E2) / M / U),
                shared_bound_u=float((S1 + S2) / M / U), rho_u=float(rho_pair(P, t1, P, t2) / U),
                witness=dict(a=[hex(w) for w in a], b=[hex(w) for w in b], c=hex(c0),
                             out1=hex(x), out2=hex(y)))


def check_task(args):
    """|t(x) - V(t)| <= E(t; x) on random inputs (subnormal operands included)."""
    pname, seed = args
    P = {p.name: p for p in ALL + [SFMA]}[pname]
    rng = random.Random(seed)
    k = 64
    progs = [dict(), dict(split=2), dict(split=4, combine='tree'), dict(c_place='first'),
             dict(split=4, combine='atomic', c_place='buffer', order=[3, 1, 0, 2])]
    n = bad = 0
    for kw in progs:
        t = program(P, k, **kw)
        for _ in range(60):
            a, b = rand_inputs(P, k, rng, rng.choice(['mixed', 'narrow', 'wide']))
            c0 = f32(rng.gauss(0, 8)) if rng.random() < 0.8 else rng.getrandbits(32) & 0x807fffff
            x = value_or_none(P, t, a, b, c0)
            if x is None:
                continue
            V = sum((P.fmt.value(a[i]) * P.fmt.value(b[i]) for i in range(k)), Q(0)) + value32(c0)
            E, _ = bound(P, t, a, b, c0)
            n += 1
            bad += abs(value32(x) - V) > E
    return pname, n, bad


def main():
    with Pool(6) as pool:
        checks = pool.map(check_task, [(P.name, 500 + i) for i, P in
                                       enumerate((V100, A100, H100, CDNA1, CDNA2, CDNA3))])
    print('Structural bound |t(x) - V(t)| <= E(t; x) on random inputs (k = 64, five programs,')
    print('normal, subnormal and wide-exponent operands, random c including subnormals):')
    for name, n, bad in checks:
        print(f'  {name:12s} {n:4d} evaluations, {bad} violations')
    print()
    tasks = []
    for P in (V100, A100, H100, CDNA1, CDNA2, CDNA3):
        for j, (label, kw1, kw2) in enumerate(PAIRS64):
            tasks.append((P.name, label, kw1, kw2, 1000 + j))
    with Pool(min(12, len(tasks))) as pool:
        rows = pool.map(tight_task, tasks)
    print('Worst |t1 - t2| / M found by search (k = 64, normal fp16 operands), against the bounds,')
    print('in units of u = 2^-24. bound: E(t1) + E(t2) on the witness; shared: with shared')
    print('subterms as exact leaves; rho: the constant form for normal operands.')
    print(f'{"variant":12s} {"pair":44s} {"worst":>9s} {"shared":>9s} {"bound":>9s} {"rho":>9s} {"worst/shared":>12s}')
    for r in rows:
        print(f'{r["variant"]:12s} {r["pair"]:44s} {r["worst_u"]:9.2f} {r["shared_bound_u"]:9.2f} '
              f'{r["bound_u"]:9.2f} {r["rho_u"]:9.2f} {r["worst_u"] / r["shared_bound_u"]:12.3f}')
    json.dump(rows, open(os.path.join(RESULTS, 'divergence.json'), 'w'), indent=1)


if __name__ == '__main__':
    main()
