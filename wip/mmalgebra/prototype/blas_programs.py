"""How different can BLAS programs be? Modeled GEMM programs for one problem size (k = 1024).

Each program is the reduction term of one output entry of D = AB + C with fp16 inputs and binary32
output: no split-K or split-K by 2, 4 or 8 with serial or pairwise reduction, stream-K, C in the
first block FMA or in the epilogue, atomic split-K in two arrival orders, a CUDA-core fallback
(sequential binary32 FMA), and the same program on different GPUs. For each pair against the
reference (no split-K, C in the epilogue) the script reports whether the two are bitwise equal by
the algebra, the proven bound on |t1 - t2| / M (M = sum |a_l b_l| + |c|) for inputs with normal
operands, the worst case found by an adversarial search, and the typical difference on four
kinds of data. These are modeled programs: the internals of cuBLAS and rocBLAS are not public.

Usage: python3 blas_programs.py [ENTRIES] [EVALS]      (writes results/blas_programs.txt, .json)
"""
import json
import os
import random
import statistics
import sys
from multiprocessing import Pool

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from divergence import *  # noqa
from config_study import nf_c0  # noqa
from terms import FAM2  # noqa

KLEN = 1024
ENTRIES = int(sys.argv[1]) if len(sys.argv) > 1 else 200
EVALS = int(sys.argv[2]) if len(sys.argv) > 2 else 800
ARCHS = [V100, A100, H100, CDNA1, CDNA2, CDNA3]
BYNAME = {P.name: P for P in ARCHS + [SFMA]}
DISTS = ['uniform', 'normal', 'llm', 'cancel']

PROGRAMS = [
    ('cfirst', 'C in the first block FMA', dict(c_place='first')),
    ('s2', 'split-K 2, partials added serially', dict(split=2)),
    ('s4', 'split-K 4, serial', dict(split=4)),
    ('s4t', 'split-K 4, pairwise', dict(split=4, combine='tree')),
    ('s8', 'split-K 8, serial', dict(split=8)),
    ('s8t', 'split-K 8, pairwise', dict(split=8, combine='tree')),
    ('streamk', 'stream-K, cut after 384 products', dict(split=2, cuts=[0, 384, KLEN])),
    ('tiles', 'other BLOCK_K, tile shapes, k = 8 or 16 instructions', dict()),
]
ATOMIC = (dict(split=4, combine='atomic', c_place='buffer', order=[0, 1, 2, 3]),
          dict(split=4, combine='atomic', c_place='buffer', order=[2, 0, 3, 1]))
CROSS = [('A100 fp16', 'H100 fp16'), ('V100 fp16', 'A100 fp16'), ('A100 fp16', 'CDNA3 fp16'),
         ('H100 fp16', 'CDNA3 fp16'), ('A100 fp16', 'CDNA1 fp16'), ('A100 fp16', 'CDNA2 fp16'),
         ('CDNA2 fp16', 'CDNA3 fp16')]


def gen(dist, k, rng):
    g = rng.gauss
    if dist == 'uniform':
        a = [f16(rng.uniform(-1, 1)) for _ in range(k)]
        b = [f16(rng.uniform(-1, 1)) for _ in range(k)]
        c = f32(g(0, (k / 9) ** 0.5))
    elif dist == 'normal':
        a = [f16(g(0, 1)) for _ in range(k)]
        b = [f16(g(0, 1)) for _ in range(k)]
        c = f32(g(0, k ** 0.5))
    elif dist == 'llm':
        # activations with 1% outlier channels 64x larger, weights N(0, 0.02^2)
        a = [f16(g(0, 1) * (64 if rng.random() < 0.01 else 1)) for _ in range(k)]
        b = [f16(g(0, 0.02)) for _ in range(k)]
        c = f32(g(0, 0.02 * (2 * k) ** 0.5))
    else:
        # near-cancelling: every product has a partner of the opposite sign, perturbed by 2^-8
        h = k // 2
        a0 = [g(0, 1) for _ in range(h)]
        b0 = [g(0, 1) for _ in range(h)]
        pairs = [(f16(x), f16(y)) for x, y in zip(a0, b0)]
        pairs += [(f16(x), f16(-y * (1 + g(0, 2 ** -8)))) for x, y in zip(a0, b0)]
        rng.shuffle(pairs)
        a, b = [p[0] for p in pairs], [p[1] for p in pairs]
        c = f32(g(0, 1))
    return a, b, c


def term_of(name, P):
    if name == 'ref':
        return program(P, KLEN)
    if name == 'simt':
        return sfma_program(KLEN)
    if name in ('atomic1', 'atomic2'):
        return program(P, KLEN, **ATOMIC[int(name[-1]) - 1])
    return program(P, KLEN, **dict(PROGRAMS_KW[name]))


PROGRAMS_KW = {n: kw for n, _, kw in PROGRAMS}


def run_term(name, P, a, b, c):
    if name == 'simt':
        sa, sb = conv_sfma(a, b)
        return value_or_none(SFMA, sfma_program(KLEN), sa, sb, c)
    return value_or_none(P, term_of(name, P), a, b, c)


def typical_task(args):
    pname, dist, seed = args
    P = BYNAME[pname]
    rng = random.Random(seed)
    names = ['ref'] + [n for n, _, _ in PROGRAMS] + ['atomic1', 'atomic2', 'simt']
    out = []
    for _ in range(ENTRIES):
        a, b, c = gen(dist, KLEN, rng)
        M = magnitude(P, a, b, c, range(KLEN))
        res = {n: run_term(n, P, a, b, c) for n in names}
        out.append((M, res))
    return pname, dist, out


def stats(pairs):
    """pairs: list of (ref word, other word, M). Share differing, ulps of the reference result."""
    n = len(pairs)
    diff = [(x, y, M) for x, y, M in pairs if x != y]
    ulps = sorted(float(abs(value32(x) - value32(y)) / ulp32(x)) for x, y, M in pairs)
    rel = sorted(float(abs(value32(x) - value32(y)) / M / U) for x, y, M in pairs if M)
    return dict(share=len(diff) / n if n else 0.0, median_ulps=statistics.median(ulps),
                p99_ulps=ulps[min(n - 1, int(0.99 * n))], max_ulps=ulps[-1],
                max_rel_u=rel[-1] if rel else 0.0)


def worst_task(args):
    label, p1, n1, p2, n2, seed = args
    P1, P2 = BYNAME[p1], BYNAME[p2]
    t1 = term_of(n1, P1)
    conv2 = None
    if n2 == 'simt':
        P2b, t2, conv2 = SFMA, sfma_program(KLEN), conv_sfma
    else:
        P2b, t2 = P2, term_of(n2, P2)
    f, (a, b, c) = search(P1, t1, P2b, t2, KLEN, seed, evals=EVALS, conv2=conv2)
    if conv2:
        r = rho(P1, t1) + rho(SFMA, t2)
    else:
        r = rho_pair(P1, t1, P2b, t2)
    a2, b2 = (a, b) if conv2 is None else conv2(a, b)
    E1, M = bound(P1, t1, a, b, c)
    E2, _ = bound(P2b, t2, a2, b2, c)
    x, y = ev(P1, t1, a, b, c), ev(P2b, t2, a2, b2, c)
    assert abs(value32(x) - value32(y)) <= E1 + E2
    return label, dict(worst_u=float(f / U), rho_u=float(r / U), witness_bound_u=float((E1 + E2) / M / U))


def equal_by_algebra(P, n1, n2):
    if n1 == 'simt' or n2 == 'simt':
        return False
    return nf_c0(FAM2[P.name], term_of(n1, P)) == nf_c0(FAM2[P.name], term_of(n2, P))


def main():
    rows = []  # (label, arch1, prog1, arch2, prog2)
    for P in ARCHS:
        for n, desc, _ in PROGRAMS:
            rows.append((f'{P.name}: {desc}', P.name, 'ref', P.name, n))
        rows.append((f'{P.name}: split-K 4, atomic adds, two arrival orders', P.name, 'atomic1', P.name, 'atomic2'))
        rows.append((f'{P.name}: CUDA-core fallback, sequential binary32 FMA', P.name, 'ref', P.name, 'simt'))
    for p1, p2 in CROSS:
        rows.append((f'{p1} against {p2}, same program', p1, 'ref', p2, 'ref'))
    with Pool(12) as pool:
        # the same inputs on every architecture (seeded by the kind of data only)
        typ = pool.map(typical_task, [(P.name, d, 7000 + j) for P in ARCHS for j, d in enumerate(DISTS)])
        wtasks = [(lab, p1, n1, p2, n2, 9000 + i) for i, (lab, p1, n1, p2, n2) in enumerate(rows)]
        worst = dict(pool.map(worst_task, [w for w in wtasks if not (w[2] == 'ref' and w[4] == 'tiles')]))
    T = {(p, d): out for p, d, out in typ}
    report = []
    for lab, p1, n1, p2, n2 in rows:
        eq = (p1 == p2) and equal_by_algebra(BYNAME[p1], n1, n2)
        entry = dict(row=lab, equal=eq)
        if n2 == 'tiles':
            entry.update(worst_u=0.0, rho_u=0.0)
        else:
            entry.update(worst[lab])
        for d in DISTS:
            pairs = []
            for (M1, r1), (M2, r2) in zip(T[(p1, d)], T[(p2, d)]):
                x, y = r1[n1], r2[n2]
                if x is not None and y is not None:
                    pairs.append((x, y, M1))
            entry[d] = stats(pairs)
        report.append(entry)
    json.dump(report, open(os.path.join(RESULTS, 'blas_programs.json'), 'w'), indent=1)
    print(f'k = {KLEN}, fp16 inputs, binary32 output; {ENTRIES} entries per kind of data; worst case '
          f'from {EVALS} evaluations of an adversarial search; u = 2^-24, M = sum |a_l b_l| + |c|.')
    print('typical: share of entries that differ / median ulps / 99th percentile ulps / max ulps')
    hdr = f'{"pair":78s} {"equal":>5s} {"bound/M":>9s} {"worst/M":>9s} ' + ' '.join(f'{d:>26s}' for d in DISTS)
    print(hdr)
    for e in report:
        cells = ' '.join(f'{e[d]["share"]:6.1%} {e[d]["median_ulps"]:5.1f} {e[d]["p99_ulps"]:6.1f} {e[d]["max_ulps"]:6.0f}'
                         for d in DISTS)
        print(f'{e["row"]:78s} {"yes" if e["equal"] else "no":>5s} {e["rho_u"]:8.0f}u {e["worst_u"]:8.1f}u {cells}')


if __name__ == '__main__':
    main()
