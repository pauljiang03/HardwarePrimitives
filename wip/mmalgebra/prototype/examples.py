"""Every concrete input and output cited on the MMAlgebra page, recomputed on the Python port.

Each example is a pair (or list) of reduction terms for one output entry, an input, and the
expected FP32 words; the script evaluates the terms, asserts the words, and prints the decoded
values. The witnesses that are also kernel-checked in Lean are marked with the Lean name.

Usage: python3 examples.py
"""
import os
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from semantics import *  # noqa

if not __debug__:
    raise SystemExit('Run without python -O or PYTHONOPTIMIZE: these checks rely on assert.')


def f16(w):
    return float(FP16.value(w))


def f32(w):
    return float(value32(w))


def blocks(P, idx_blocks, start=('zero',)):
    """A chain of block FMAs: each inner list is one block's product indices (padded with zeros)."""
    s = start
    for B in idx_blocks:
        s = ('blk', s, tuple(list(B) + [None] * (P.K - len(B))))
    return s


def show(title, P, a, b, rows, c0=0, lean=None):
    print(f'\n## {title} ({P.name}){"  [Lean: " + lean + "]" if lean else ""}')
    print('   products: ' + ', '.join(
        f'p{i} = {hex(x)} x {hex(y)} = {f16(x) if P.fmt is FP16 else float(P.fmt.value(x))} x '
        f'{f16(y) if P.fmt is FP16 else float(P.fmt.value(y))}'
        for i, (x, y) in enumerate(zip(a, b)) if x != 0))
    if c0:
        print(f'   c = {hex(c0)} = {f32(c0)}')
    for name, term, want in rows:
        got = evs(P, term, a, b, c0)
        assert got == want, (title, name, hex(got) if isinstance(got, int) else got, hex(want))
        print(f'   {name:44s} {hex(got):12s} {f32(got)!r}')


# ------------------------------------------------------------------ a hand-sized example
# x = 1.5 * 1.5 = 2.25, y = z = 2^-12 * 2^-11 = 2^-23 (fp16 words 0x3e00, 0x0c00, 0x1000).
a = [0x3e00, 0x0c00, 0x0c00]
b = [0x3e00, 0x1000, 0x1000]
TWO25 = 0x40100000            # 2.25
TWO25_UP = 0x40100001         # 2.25 + 2^-22
rows = lambda P: [
    ('one block [x y z]', blocks(P, [[0, 1, 2]]), None),
    ('two blocks [x] [y z]', blocks(P, [[0], [1, 2]]), None),
    ('split-K [x] + [y z]', ('add', blocks(P, [[0]]), blocks(P, [[1, 2]])), None),
]
expected = {
    'V100 fp16': [TWO25_UP, TWO25, TWO25_UP],
    'A100 fp16': [TWO25_UP, TWO25_UP, TWO25_UP],
    'H100 fp16': [TWO25_UP, TWO25_UP, TWO25_UP],
    'CDNA1 fp16': [TWO25_UP, TWO25_UP, TWO25_UP],
    'CDNA2 fp16': [TWO25, TWO25_UP, TWO25_UP],
    'CDNA3 fp16': [TWO25_UP, TWO25_UP, TWO25_UP],
}
for P in (V100, A100, H100, CDNA1, CDNA2, CDNA3):
    show('Block boundaries and split-K', P, a, b,
         [(n, t, w) for (n, t, _), w in zip(rows(P), expected[P.name])])

# C placement on V100: C = 2.25 in the first block versus added in the epilogue.
show('Early versus late addition of C', V100, [0x0c00, 0x0c00], [0x1000, 0x1000], [
    ('C in the block: blk(c, [y z])', blocks(V100, [[0, 1]], ('c0',)), TWO25),
    ('C in the epilogue: c + blk(0, [y z])', ('add', ('c0',), blocks(V100, [[0, 1]])), TWO25_UP),
], c0=TWO25)

# ------------------------------------------------------------------ completeness base witnesses
show('Two products, three patterns', V100, [0x1edc, 0x7add], [0x1cd3, 0x0069], [
    ('[x] alone', blocks(V100, [[0]]), 0x38045d50),
    ('[y] alone', blocks(V100, [[1]]), 0x3eb42940),
    ('[x y]', blocks(V100, [[0, 1]]), 0x3eb42d60),
    ('[x] then [y]', blocks(V100, [[0], [1]]), 0x3eb42d60),
    ('[y] then [x]', blocks(V100, [[1], [0]]), 0x3eb42d62),
], lean='MMAlgebra.TC.v100_complete_pair')
show('Two products, three patterns', A100, [0x1edc, 0x7add], [0x1cd3, 0x0069], [
    ('[x y]', blocks(A100, [[0, 1]]), 0x3eb42d60),
    ('[x] then [y]', blocks(A100, [[0], [1]]), 0x3eb42d60),
    ('[y] then [x]', blocks(A100, [[1], [0]]), 0x3eb42d62),
], lean='MMAlgebra.TC.a100_complete_pair')
show('Two products, three patterns', H100, [0x0052, 0x0ba7], [0x6587, 0x3ff9], [
    ('[x] alone', blocks(H100, [[0]]), 0x3be29f00),
    ('[y] alone', blocks(H100, [[1]]), 0x39f409bc),
    ('[x y]', blocks(H100, [[0, 1]]), 0x3bf1df98),
    ('[x] then [y]', blocks(H100, [[0], [1]]), 0x3bf1df9b),
    ('[y] then [x]', blocks(H100, [[1], [0]]), 0x3bf1df98),
], lean='MMAlgebra.TC.h100_complete_pair')
show('Two products, three patterns', CDNA3, [0x02e6, 0x37ea], [0x0b09, 0x2d78], [
    ('[p0] then [p1]', blocks(CDNA3, [[0], [1]]), 0x3d2d1ec2),
    ('[p1] then [p0]', blocks(CDNA3, [[1], [0]]), 0x3d2d1ec3),
    ('[p0 p1]', blocks(CDNA3, [[0, 1]]), 0x3d2d1ec2),
], lean='MMAlgebra.MC.cdna3_pair')
A3, B3 = [0x081f, 0x43fe, 0x07e0], [0x4ce3, 0x4236, 0x47e3]
show('Three products, summation trees', CDNA1, A3, B3, [
    ('[p0] [p1] [p2]  = ((p0 + p1) + p2)', blocks(CDNA1, [[0], [1], [2]]), 0x41469c44),
    ('[p0] [p2] [p1]  = ((p0 + p2) + p1)', blocks(CDNA1, [[0], [2], [1]]), 0x41469c43),
    ('[p0] [p1 p2]    = (p0 + p1 + p2)', blocks(CDNA1, [[0], [1, 2]]), 0x41469c43),
    ('[p0 p1 p2]      = (p0 + p1 + p2)', blocks(CDNA1, [[0, 1, 2]]), 0x41469c43),
], lean='MMAlgebra.MC.cdna1_trees')
show('Three products, summation trees', CDNA2, A3, B3, [
    ('[p0] [p1] [p2]  = ((p0 + p1) + p2)', blocks(CDNA2, [[0], [1], [2]]), 0x41469c44),
    ('[p0] [p2] [p1]  = ((p0 + p2) + p1)', blocks(CDNA2, [[0], [2], [1]]), 0x41469c43),
], lean='MMAlgebra.MC.cdna2_trees')

# ------------------------------------------------------------------ one instruction, one rounding?
def k16(P, perm):
    """One k = 16 instruction as consecutive blocks of the FMA size, products in slot order `perm`."""
    return blocks(P, [perm[i:i + P.K] for i in range(0, 16, P.K)])


swap = [15] + list(range(1, 15)) + [0]
for P, A, B, w0, w1, lean in [
        (V100, [0x29af, 0xc352], [0x33fb, 0x43e5], 0xc166fc0c, 0xc166fc0d, 'MMAlgebra.TC.v100_wmma_swap'),
        (A100, [0x0467, 0x4496], [0xb7f7, 0x0703], 0x39efb5df, 0x39efb5e0, 'MMAlgebra.TC.a100_wmma_swap'),
        (CDNA1, [0xb853, 0xd7ce, 0xaad7], [0x8cfe, 0xc3cf, 0x47fb], 0x43f38fb8, 0x43f38fb7,
         'MMAlgebra.MC.cdna1_k16_swap'),
        (CDNA2, [0x8cce, 0xd76b, 0x4efe], [0x3be6, 0xbfda, 0x33ce], 0x436fcab2, 0x436fcab1,
         'MMAlgebra.MC.cdna2_k16_swap'),
        (CDNA3, [0x8187, 0xd7f6], [0x8919, 0x0092], 0xba914962, 0xba914961, 'MMAlgebra.MC.cdna3_k16_swap')]:
    a16 = A + [0] * (16 - len(A))
    b16 = B + [0] * (16 - len(B))
    show('One k = 16 instruction, products k = 0 and k = 15 exchanged', P, a16, b16, [
        ('products in order', k16(P, list(range(16))), w0),
        ('k = 0 and k = 15 exchanged', k16(P, swap), w1),
    ], lean=lean)

# ------------------------------------------------------------------ CDNA 1 bf16 at binary32's bottom
# p0 = 2^-75 * 2^-74 = 2^-149, p1 = 2^-75 * 2^-75 = 2^-150 (a tie in binary32), p2 = 0.
show('A product below binary32\'s range', CDNA1BF, [0x1A00, 0x1A00, 0], [0x1A80, 0x1A00, 0x3F80], [
    ('[p0] then [p1]', blocks(CDNA1BF, [[0], [1], [2]]), 0x2),
    ('[p1] then [p0]', blocks(CDNA1BF, [[1], [0], [2]]), 0x1),
    ('[p0 p1]', blocks(CDNA1BF, [[0, 1], [2]]), 0x2),
])

print('\nall examples reproduced')
