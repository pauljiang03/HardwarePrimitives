"""Soundness and completeness of the normal forms on small index sets.

For each profile and n: enumerate every chain schedule over n products (from c0 = +0), group by
normal form, then
  * soundness: every member of a class gives the same word on R random inputs;
  * completeness: every two classes are separated by some input (random/special search).
"""
import json
import random
import os
import sys
import time

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
RESULTS = os.path.join(os.path.dirname(os.path.abspath(__file__)), 'results')
from normal import *  # noqa


def run(P, n, R, rng, out):
    scheds = list(schedules(P, n))
    classes = {}
    for s in scheds:
        classes.setdefault(repr(nf(P, s)), []).append(s)
    keys = list(classes)
    # soundness
    bad = 0
    inputs = []
    for _ in range(R):
        if rng.random() < 0.5:
            a = [special_word(P.fmt, rng) for _ in range(n)]
            b = [special_word(P.fmt, rng) for _ in range(n)]
        else:
            a, b = rand_inputs(P, n, rng, rng.choice(['mixed', 'narrow', 'wide']))
        inputs.append((a, b))
    sig = {}
    for key in keys:
        mem = classes[key]
        vals0 = [evs(P, chain_slots(mem[0]), a, b, 0) for a, b in inputs]
        sig[key] = vals0
        for s in mem[1:]:
            vals = [evs(P, chain_slots(s), a, b, 0) for a, b in inputs]
            if vals != vals0:
                bad += 1
                j = next(i for i in range(R) if vals[i] != vals0[i])
                if bad <= 3:
                    print('  UNSOUND', P.name, key, mem[0], s, inputs[j], vals0[j], vals[j])
    # completeness: pairs not separated by the shared inputs get a targeted search
    unsep = 0
    searched = 0
    for i in range(len(keys)):
        for j in range(i + 1, len(keys)):
            vi, vj = sig[keys[i]], sig[keys[j]]
            if any(x != y and isinstance(x, int) and isinstance(y, int) for x, y in zip(vi, vj)):
                continue
            searched += 1
            w = find_witness(P, classes[keys[i]][0], classes[keys[j]][0], n, rng, tries=20000)
            if w is None:
                unsep += 1
                if unsep <= 5:
                    print('  NOT SEPARATED', P.name, keys[i], keys[j])
    line = (f'{P.name:14s} n={n} schedules={len(scheds):5d} classes={len(keys):4d} '
            f'unsound={bad} pairs={len(keys)*(len(keys)-1)//2} searched={searched} unseparated={unsep}')
    print(line, flush=True)
    out.append({'profile': P.name, 'n': n, 'schedules': len(scheds), 'classes': len(keys),
                'unsound': bad, 'unseparated': unsep})


def main():
    rng = random.Random(11)
    out = []
    R = int(sys.argv[1]) if len(sys.argv) > 1 else 300
    profs = [V100, A100, H100, A100BF, H100BF, SFMA, CDNA1, CDNA1BF, CDNA2, CDNA2BF, CDNA2BF1K, CDNA3, CDNA3BF]
    for P in profs:
        for n in ([2, 3] if FAMILY[P.name] != 'tree' else [2, 3]):
            t = time.time()
            run(P, n, R, rng, out)
    json.dump(out, open(os.path.join(RESULTS, 'classes.json'), 'w'), indent=1)


if __name__ == '__main__':
    main()
