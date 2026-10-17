"""Combinatorial check: two chain schedules with different normal forms differ already on
a support of at most three products, i.e. some restriction to <= 3 indices has different normal
forms. Exhaustive for small n. This is the step that reduces completeness to finitely many base
witnesses (zero products are invisible on every model).
"""
import itertools
import os
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from normal import ordered_partitions, slotted, restrict, nf_seq, nf_crm, nf_tree

FAM = {'seq': nf_seq, 'crm': nf_crm, 'tree': nf_tree}


def check(fam, n, K, positional, max_support=3):
    f = FAM[fam]
    scheds = []
    for bl in ordered_partitions(range(n), K):
        for s in slotted(bl, K, positional):
            scheds.append(s)
    # group by normal form; one representative per class suffices (restriction commutes with nf
    # for all members if the normal form is a congruence -- checked below on members as well)
    classes = {}
    for s in scheds:
        classes.setdefault(repr(f(s)), []).append(s)
    subsets = [frozenset(c) for r in range(1, max_support + 1) for c in itertools.combinations(range(n), r)]

    def profile(s):
        return tuple(repr(f(restrict(s, S))) for S in subsets)

    # restriction is well defined on classes
    incoherent = 0
    prof = {}
    for key, mem in classes.items():
        p0 = profile(mem[0])
        for s in mem[1:]:
            if profile(s) != p0:
                incoherent += 1
        prof[key] = p0
    keys = list(classes)
    fails = 0
    for i in range(len(keys)):
        for j in range(i + 1, len(keys)):
            if prof[keys[i]] == prof[keys[j]]:
                fails += 1
                if fails <= 3:
                    print('   undetermined:', keys[i], keys[j])
    print(f'{fam:5s} n={n} K={K} schedules={len(scheds)} classes={len(keys)} '
          f'incoherent={incoherent} pairs-not-determined-by-<=3={fails}', flush=True)


if __name__ == '__main__':
    for n in range(2, 7):
        check('seq', n, 4, False)
        check('crm', n, 4, False)
    for n in range(2, 6):
        check('seq', n, 2, False)
    for n in range(2, 6):
        check('tree', n, 2, True)
    for n in range(2, 5):
        check('tree', n, 4, True)
