"""One input, four results: FP8 -> FP32 inner products on Ada, Hopper, Blackwell and CDNA 3.

The same values are given to the NVIDIA models as E4M3 (or E5M2) words and to CDNA 3 as E4M3 FNUZ
(or E5M2 FNUZ) words, so only values representable in both encodings are used (E4M3: magnitudes
2^-9 to 240). The script searches 20,000 short inputs (k = 32, c = 0, three to five nonzero
products) for one on which the four models give four different results, preferring fewer products
and results that also differ from the binary32 value nearest the exact sum, and compares the best
with the input checked in Lean (MMAlgebra.TC.xvendor_nvidia, MMAlgebra.MC.xvendor_cdna3).

Usage: python3 fp8_crossvendor.py [seed]   (default 1)
"""
import random
import sys
from fractions import Fraction as Q
from fp8models import *

PAIRS = {'e4m3': (E4M3, E4M3_FNUZ, ADA, HOPPER, BLACKWELL, CDNA3_E4M3),
         'e5m2': (E5M2, E5M2_FNUZ, ADA52, HOPPER52, BLACKWELL52, CDNA3_E5M2)}
NAMES = ['Ada', 'Hopper', 'Blackwell', 'CDNA3']


def common_values(fo, fz):
    """The nonzero values of both encodings, and each encoding's word of every value."""
    vo = {fo.value(w): w for w in fo.words() if not (fo.value(w) == 0 and w)}
    vz = {fz.value(w): w for w in fz.words()}
    return sorted(v for v in vo if v in vz and v != 0), vo, vz


CV = {f: common_values(PAIRS[f][0], PAIRS[f][1]) for f in PAIRS}


def run_all(fmt, a_vals, b_vals, c=0):
    """Each model's output word for the inner product of the given values (None on an error),
    and RN(exact): the binary32 value nearest the exact sum."""
    fo, fz, ada, hop, bw, cd = PAIRS[fmt]
    _, vo, vz = CV[fmt]
    po = [(vo[a], vo[b]) for a, b in zip(a_vals, b_vals)]
    pz = [(vz[a], vz[b]) for a, b in zip(a_vals, b_vals)]
    out = {}
    for name, P, ps in (('Ada', ada, po), ('Hopper', hop, po), ('Blackwell', bw, po),
                        ('CDNA3', cd, pz)):
        try:
            out[name] = chain(P, c, ps)
        except ModelError:
            out[name] = None
    exact = sum((a * b for a, b in zip(a_vals, b_vals)), Q(0)) + value32(c)
    out['RN(exact)'] = rne32(exact)
    return out, exact


def search(seed, k=32, tries=20000):
    rng = random.Random(seed)
    vs = CV['e4m3'][0]
    best = None
    for it in range(tries):
        nz = rng.choice([3, 4, 5])
        pos = sorted(rng.sample(range(k), nz))
        a, b = [Q(0)] * k, [Q(0)] * k
        for p in pos:
            a[p], b[p] = rng.choice(vs), rng.choice(vs)
        out, exact = run_all('e4m3', a, b)
        vals = {out[n] for n in NAMES}
        if len(vals) == 4:
            score = (nz, -len(vals | {out['RN(exact)']}))
            if best is None or score < best[0]:
                best = (score, it + 1, pos, [a[p] for p in pos], [b[p] for p in pos])
            if score == (3, -5):
                break
    return best


def show(pos, av, bv, k=32):
    a, b = [Q(0)] * k, [Q(0)] * k
    for p, x, y in zip(pos, av, bv):
        a[p], b[p] = x, y
    out, exact = run_all('e4m3', a, b)
    _, vo, vz = CV['e4m3']
    print('  slots (from 0):', pos)
    print('  products:', ', '.join(f'({x})*({y})' for x, y in zip(av, bv)))
    print('  E4M3 words:', ', '.join(f'({vo[x]:#04x}, {vo[y]:#04x})' for x, y in zip(av, bv)))
    print('  E4M3 FNUZ words:', ', '.join(f'({vz[x]:#04x}, {vz[y]:#04x})' for x, y in zip(av, bv)))
    print(f'  exact sum: {exact} = {float(exact)!r}')
    for n in NAMES + ['RN(exact)']:
        print(f'  {n:10s} {out[n]:#010x} = {float(value32(out[n]))!r}')


if __name__ == '__main__':
    seed = int(sys.argv[1]) if len(sys.argv) > 1 else 1
    for fmt in ('e4m3', 'e5m2'):
        vs = CV[fmt][0]
        print(f'{fmt}: {len(vs)} nonzero values common to both encodings, magnitudes '
              f'{min(abs(v) for v in vs)} to {max(vs)}')
    best = search(seed)
    (nz, nres), it, pos, av, bv = best
    print(f'search (seed {seed}, 20000 inputs): the best input has four different results with '
          f'{nz} products and {-nres} distinct values with RN(exact); found at input {it}')
    show(pos, av, bv)
    lean = ([11, 13, 21], [Q(-7, 16), Q(-9, 4), Q(-96)], [Q(13, 256), Q(-36), Q(128)])
    if (pos, av, bv) == lean:
        print('this is the input checked in Lean')
    else:
        print('the input checked in Lean:')
        show(*lean)
