"""CDNA 1 bf16 at the bottom of binary32's range.

CDNA 1 rounds every block once, to nearest, from the exact sum, so whenever every product is
representable in binary32 its chains obey the same laws as CDNA 1 fp16 (a one-product first block
merges into the next block). A bf16 product, unlike an fp16 one, can fall below binary32's range;
then a one-product block rounds it, and the merge law fails. This script checks that the twelve
chain patterns over three products are pairwise separated on CDNA 1 bf16 (the rigid algebra), using
random words, words whose products land near binary32's subnormal range, and every placement of a
tie input (products 2^-149, 2^-150 and 0).

Usage: python3 bf16_extremes.py
"""
import itertools
import os
import random
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from normal import *  # noqa

P = CDNA1BF
rng = random.Random(1)


def tiny_word():
    """A bf16 word of magnitude 2^-126 .. 2^-67, so that products of two land near 2^-149."""
    return (rng.getrandbits(1) << 15) | (rng.randint(1, 60) << 7) | rng.getrandbits(7)


def candidates():
    # every placement of the tie input: p = 2^-149 (0x1A00 * 0x1A80), 2^-150 (0x1A00 * 0x1A00), 0
    tie = [(0x1A00, 0x1A80), (0x1A00, 0x1A00), (0, 0x3F80)]
    for perm in itertools.permutations(tie):
        yield [x for x, _ in perm], [y for _, y in perm]
    for _ in range(20000):
        g = tiny_word if rng.random() < 0.7 else (lambda: special_word(P.fmt, rng))
        yield [g() for _ in range(3)], [g() for _ in range(3)]


reps = {}
for s in schedules(P, 3):
    reps.setdefault(repr(nf_seq(s)), s)
reps = list(reps.values())
unseparated = 0
for s, t in itertools.combinations(reps, 2):
    for a, b in candidates():
        x, y = evs(P, chain_slots(s), a, b, 0), evs(P, chain_slots(t), a, b, 0)
        if isinstance(x, int) and isinstance(y, int) and x != y:
            break
    else:
        unseparated += 1
        print('   not separated:', nf_seq(s), nf_seq(t))
n = len(reps)
print(f'CDNA1 bf16 n=3 chain patterns={n} pairs={n * (n - 1) // 2} unseparated={unseparated}')
