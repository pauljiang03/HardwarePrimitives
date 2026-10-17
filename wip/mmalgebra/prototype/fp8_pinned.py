"""Pinned accumulation on the FP8 models.

1. CDNA 3 E4M3 FNUZ, a pin pair +-2^14 (128 * 128) in every block. With the two pins in different
   parity groups every product is truncated to the grid 2^(14-24) = 2^-10 and a chain is a
   function of the multiset of its products; with both pins in one group the other group is
   aligned to its own maximum and then rounded down, and the result depends on the schedule.
   Per case: 48 products of magnitude at most 2, eight random schedules (random order, 1 to 14
   products per block, random slots); does the multiset give one result?
2. Across vendors: Hopper and Ada with a pin pair +-2^3 (2 * 4; grid 2^(3-13) = 2^-10) and CDNA 3
   with pins +-2^14 straddling the parity groups (grid 2^(14-24) = 2^-10) compute the same
   function, the sum of the products each truncated toward zero to 2^-10, while the running value
   stays below 2^3. Per case: 64 products of operands of magnitude at most 1/4 (values common to
   E4M3 and E4M3 FNUZ), three random schedules per GPU (up to 30 products per block on Hopper,
   14 on Ada and CDNA 3).
"""
import random
from fractions import Fraction as Q
from fp8models import *
from fp8_crossvendor import CV

rng = random.Random(4)
P = CDNA3_E4M3
ws = [w for w in P.fa.words() if P.fa.value(w) != 0 and abs(P.fa.value(w)) <= 2]
PIN, NPIN = (0x78, 0x78), (0xF8, 0x78)          # +-2^14 in E4M3 FNUZ (0x78 = 128)
assert P.fa.value(0x78) == 128 and P.fa.value(0xF8) == -128


def run_cdna3(prods, straddle, rng):
    prods = prods[:]
    rng.shuffle(prods)
    c, i = 0, 0
    while i < len(prods):
        m = rng.randint(1, 14)
        chunk, i = prods[i:i + m], i + m
        slots = [(0, 0)] * 16
        if straddle:
            slots[0], slots[1] = PIN, NPIN
            free = list(range(2, 16))
        else:
            slots[0], slots[2] = PIN, NPIN
            free = [1] + list(range(3, 16))
        for pos, pr in zip(rng.sample(free, len(chunk)), chunk):
            slots[pos] = pr
        c = mc_block(P, slots, c)
    return c


for straddle in (True, False):
    agree = 0
    for t in range(200):
        prods = [(rng.choice(ws), rng.choice(ws)) for _ in range(48)]
        outs = {run_cdna3(prods, straddle, random.Random(rng.random())) for _ in range(8)}
        agree += len(outs) == 1
    where = 'pins in different parity groups' if straddle else 'pins in one parity group'
    print(f'CDNA 3 E4M3, {where}: {agree}/200 multisets give one result under 8 random schedules')


rng = random.Random(8)
vs, vo, vz = CV['e4m3']
small = [v for v in vs if abs(v) <= Q(1, 4)]
HPIN = [(vo[Q(2)], vo[Q(4)]), (vo[Q(-2)], vo[Q(4)])]
CPIN = [(vz[Q(128)], vz[Q(128)]), (vz[Q(-128)], vz[Q(128)])]


def chain_pinned(M, pins, prods, per_block, rng):
    c, i = 0, 0
    prods = prods[:]
    rng.shuffle(prods)
    while i < len(prods):
        m = rng.randint(1, per_block)
        chunk, i = prods[i:i + m], i + m
        slots = [(0, 0)] * M.K
        slots[0], slots[1] = pins
        for pos, pr in zip(rng.sample(range(2, M.K), len(chunk)), chunk):
            slots[pos] = pr
        c = block(M, slots, c)
    return c


same = ref_ok = 0
N = 200
for t in range(N):
    av = [rng.choice(small) for _ in range(64)]
    bv = [rng.choice(small) for _ in range(64)]
    po = [(vo[a], vo[b]) for a, b in zip(av, bv)]
    pz = [(vz[a], vz[b]) for a, b in zip(av, bv)]
    outs = set()
    for s in range(3):
        outs.add(value32(chain_pinned(HOPPER, HPIN, po, 30, random.Random(rng.random()))))
        outs.add(value32(chain_pinned(ADA, HPIN, po, 14, random.Random(rng.random()))))
        outs.add(value32(chain_pinned(CDNA3_E4M3, CPIN, pz, 14, random.Random(rng.random()))))
    ref = sum((trunc_grid(a * b, -10) for a, b in zip(av, bv)), Q(0))
    same += len(outs) == 1
    ref_ok += outs == {ref}
print(f'pinned E4M3 on Ada, Hopper and CDNA 3 (pins straddling the parity groups), random '
      f'schedules: one result in {same}/{N} cases, equal to the sum of trunc_(2^-10)(p_i) in '
      f'{ref_ok}/{N}')
