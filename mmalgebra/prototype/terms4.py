"""Linear terms over four products: soundness of the normal forms on random inputs, and
completeness reduced to supports of at most three products (every two distinct normal forms have
restrictions to some support of at most three products with distinct normal forms).

Usage: python3 terms4.py
"""
import os, random, sys, time
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from terms import *
from decide_equiv import restrict_term, relabel
rng = random.Random(77)
for P in [V100, H100, CDNA1, CDNA3, SFMA]:
    fam = FAM2[P.name]
    ts = terms(frozenset(range(4)), P.K, False)
    t0 = time.time()
    inputs = []
    for _ in range(80):
        if rng.random() < 0.6:
            a = [special_word(P.fmt, rng) for _ in range(4)]; b = [special_word(P.fmt, rng) for _ in range(4)]
        else:
            a, b = rand_inputs(P, 4, rng, rng.choice(['mixed', 'narrow', 'wide']))
        inputs.append((a, b))
    nfs = {}
    for t in ts: nfs.setdefault(repr(nf2(fam, t)), []).append(t)
    fp = {repr(t): tuple(evs(P, t, a, b, 0) for a, b in inputs) for t in ts}
    unsound = sum(1 for mem in nfs.values() for t in mem[1:] if fp[repr(t)] != fp[repr(mem[0])])
    keys = list(nfs)
    # completeness via restriction: distinct NFs must differ on some <=3 restriction
    undetermined = 0
    for i in range(len(keys)):
        for j in range(i+1, len(keys)):
            t1, t2 = nfs[keys[i]][0], nfs[keys[j]][0]
            ok = False
            for r in (1, 2, 3):
                for S in itertools.combinations(range(4), r):
                    if repr(nf2(fam, restrict_term(t1, set(S)))) != repr(nf2(fam, restrict_term(t2, set(S)))):
                        ok = True; break
                if ok: break
            undetermined += (not ok)
    # also: distinct NFs separated by the shared random inputs?
    sep = sum(1 for i in range(len(keys)) for j in range(i+1, len(keys)) if fp[repr(nfs[keys[i]][0])] != fp[repr(nfs[keys[j]][0])])
    print(f'{P.name:12s} n=4 terms={len(ts)} normal-forms={len(keys)} unsound={unsound} pairs={len(keys)*(len(keys)-1)//2} separated-by-random={sep} not-determined-by-<=3-restrictions={undetermined}', flush=True)
