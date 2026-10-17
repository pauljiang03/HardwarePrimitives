"""Command-line front end of witness_search.py for one variant: search for one input that separates
every chain pattern over n products.

Usage: python3 wsearch2.py VARIANT N pos|any TRIES [SEED]
       (VARIANT: V100, A100, H100, A100BF, H100BF, CDNA1, CDNA1BF, CDNA2, CDNA2BF, CDNA2BF1K,
        CDNA3, CDNA3BF or SFMA)
"""
import os, random, sys
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from witness_search import *
P = {'V100':V100,'A100':A100,'H100':H100,'A100BF':A100BF,'H100BF':H100BF,'CDNA3':CDNA3,'CDNA3BF':CDNA3BF,'SFMA':SFMA,'CDNA1':CDNA1,'CDNA2':CDNA2,'CDNA2BF1K':CDNA2BF1K,'CDNA2BF':CDNA2BF,'CDNA1BF':CDNA1BF}[sys.argv[1]]
n = int(sys.argv[2]); pos = sys.argv[3] == 'pos'; tries = int(sys.argv[4])
rng = random.Random(int(sys.argv[5]) if len(sys.argv) > 5 else 1)
pats, best = search(P, n, rng, tries=tries, positive=pos)
k, a, b, outs = best
print(f'{P.name:14s} n={n} pos={pos} patterns={len(pats)} separated={k}', flush=True)
for s, o in zip(pats, outs):
    print('   ', [[x for x in B] for B in s], hex(o), float(value32(o)))
print('    a =', [hex(x) for x in a], ' b =', [hex(x) for x in b], ' values', [float(P.fmt.value(x)) for x in a], [float(P.fmt.value(x)) for x in b], flush=True)
