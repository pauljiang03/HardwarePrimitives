"""Search for one input per profile that separates every normal form over two (rigid
families) or three (CDNA 1 fp16, CDNA 2) products, with positive values.
Prints Lean-ready words and writes results/witnesses.json. The searches can take a long time
(up to 200,000 tries per variant); wsearch2.py runs one variant.

Usage: python3 witness_search.py
"""
import json
import random
import os
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
RESULTS = os.path.join(os.path.dirname(os.path.abspath(__file__)), 'results')
from normal import *  # noqa


def pos_word(fmt, rng):
    w = special_word(fmt, rng)
    return w & ~(1 << (fmt.ebits + fmt.mbits))


def patterns(P, n):
    """Representative chain schedules of every normal form over n products."""
    reps = {}
    for s in schedules(P, n):
        reps.setdefault(repr(nf(P, s)), s)
    return list(reps.values())


def search(P, n, rng, tries=200000, positive=True):
    pats = patterns(P, n)
    best = None
    for t in range(tries):
        g = pos_word if positive else special_word
        a = [g(P.fmt, rng) for _ in range(n)]
        b = [g(P.fmt, rng) for _ in range(n)]
        outs = [evs(P, chain_slots(s), a, b, 0) for s in pats]
        if any(not isinstance(o, int) for o in outs):
            continue
        k = len(set(outs))
        if best is None or k > best[0]:
            best = (k, a, b, outs)
            if k == len(pats):
                break
    return pats, best


if __name__ == '__main__':
    rng = random.Random(3)
    res = {}
    for P, n in [(V100, 2), (A100, 2), (H100, 2), (A100BF, 2), (H100BF, 2), (CDNA3, 2), (CDNA3BF, 2),
                 (SFMA, 2), (CDNA1, 3), (CDNA2, 3), (CDNA2BF1K, 3), (CDNA2BF, 3)]:
        pats, best = search(P, n, rng)
        k, a, b, outs = best
        print(f'{P.name:14s} n={n} patterns={len(pats)} separated={k}')
        for s, o in zip(pats, outs):
            print('   ', [[x for x in B] for B in s], hex(o), float(value32(o)))
        print('    a =', [hex(x) for x in a], ' b =', [hex(x) for x in b],
              ' values', [float(P.fmt.value(x)) for x in a], [float(P.fmt.value(x)) for x in b])
        res[P.name] = {'n': n, 'patterns': [[list(B) for B in s] for s in pats], 'a': a, 'b': b,
                       'outs': outs}
    json.dump(res, open(os.path.join(RESULTS, 'witnesses.json'), 'w'), indent=1)
