"""Random tests of the empty-block laws on the FP8 models.

On each NVIDIA FP8 model: does an empty block return c, or c truncated to a 13-bit mantissa (a
zero result +0; proved in Lean for Ada and Hopper, tc_empty_block_trunc13)? Is an empty block absorbed
by a following nonempty block, and is it the identity on block outputs? On CDNA 3 FP8: does an
empty block return c? Accumulators are random binary32 words with exponents in [-30, 30]; blocks
hold 1 to 4 random products (E4M3 operands of magnitude at most 448, every finite E5M2 operand;
every finite FNUZ operand on CDNA 3).
"""
import random
from fp8models import *

rng = random.Random(7)
N = 3000


def rand_f32(lo=-30, hi=30):
    return (rng.getrandbits(1) << 31) | ((rng.randint(lo, hi) + 127) << 23) | rng.getrandbits(23)


def trunc13(c):
    t = trunc_word(13, c)
    return 0 if t == 0x80000000 else t


def rprods(fa, fb, n):
    return [(rng.choice(WORDS[fa.name]), rng.choice(WORDS[fb.name])) for _ in range(n)]


WORDS = {f.name: f.words() for f in (E4M3, E5M2, E4M3_FNUZ, E5M2_FNUZ)}

for P in (ADA, HOPPER, BLACKWELL, ADA52, HOPPER52, BLACKWELL52):
    passes = trunc = absorb = ident = 0
    for _ in range(N):
        c = rand_f32()
        e = tc_sparse(P, [], c)
        passes += e == c
        trunc += e == trunc13(c)
        ps = rprods(P.fmt, P.fmt, rng.randint(1, 4))
        absorb += tc_sparse(P, ps, e) == tc_sparse(P, ps, c)
        u = tc_sparse(P, ps, c)
        ident += tc_sparse(P, [], u) == u
    print(f'{P.name:18s} empty block = c: {passes}/{N}; = trunc13(c): {trunc}/{N}; '
          f'absorbed by the next block: {absorb}/{N}; identity on block outputs: {ident}/{N}')
for P in (CDNA3_E4M3, CDNA3_E5M2, CDNA3_E4M3E5M2):
    passes = 0
    for _ in range(N):
        c = rand_f32()
        passes += mc_sparse(P, [], [], c) == c
    print(f'{P.name:18s} empty block = c: {passes}/{N}')
