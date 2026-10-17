"""ReproCheck prototype: decide whether two GEMM reduction schedules give
bit-identical results for every input on a given architecture, and otherwise construct an input
that separates them.

Algorithm
  1. normal form per architecture family (terms.nf2): 'seq' (Tensor Cores, CDNA 3), 'cr' (CDNA 1
     fp16), 'tree' (CDNA 2), 'sfma'; equal normal forms => equivalent (soundness laws).
  2. different normal forms => search the supports S of size <= 3 for one whose restrictions have
     different normal forms (zero products are invisible, so restriction = setting a_i = 0 outside
     S), then plant the base witness for that small pair of patterns: the witness table maps every
     pair of distinct normal forms over <= 3 products to an input that separates them (found by
     search, see terms.py / witness_search.py). The planted input is re-checked on the model.

Schedules are terms (sched.py): ('zero',) | ('c0',) | ('blk', t, slots) | ('add', t, u).
"""
import itertools
import random
import os
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from terms import *  # noqa


def leaves(t):
    tag = t[0]
    if tag in ('zero', 'c0'):
        return set()
    if tag == 'blk':
        return leaves(t[1]) | {i for i in t[2] if i is not None}
    return leaves(t[1]) | leaves(t[2])


def restrict_term(t, S):
    """Slots outside S emptied; empty blocks removed; additions of zero removed."""
    tag = t[0]
    if tag in ('zero', 'c0'):
        return t
    if tag == 'blk':
        c = restrict_term(t[1], S)
        slots = tuple(i if (i is not None and i in S) else None for i in t[2])
        if all(i is None for i in slots):
            return c
        return ('blk', c, slots)
    u, v = restrict_term(t[1], S), restrict_term(t[2], S)
    if u == ('zero',):
        return v
    if v == ('zero',):
        return u
    return (tag, u, v)


def relabel(t, m):
    tag = t[0]
    if tag in ('zero', 'c0'):
        return t
    if tag == 'blk':
        return ('blk', relabel(t[1], m), tuple(m[i] if i is not None else None for i in t[2]))
    return (tag, relabel(t[1], m), relabel(t[2], m))


class WitnessTable:
    """Separating inputs for pairs of small terms, found by search once per profile."""

    def __init__(self, P, rng, tries=20000):
        self.P, self.rng, self.tries = P, rng, tries
        self.cache = {}

    def find(self, t1, t2, n):
        key = (repr(t1), repr(t2))
        if key in self.cache:
            return self.cache[key]
        P = self.P
        res = None
        for _ in range(self.tries):
            if self.rng.random() < 0.7:
                a = [special_word(P.fmt, self.rng) for _ in range(n)]
                b = [special_word(P.fmt, self.rng) for _ in range(n)]
            else:
                a, b = rand_inputs(P, n, self.rng, self.rng.choice(['mixed', 'narrow', 'wide']))
            x, y = evs(P, t1, a, b, 0), evs(P, t2, a, b, 0)
            if isinstance(x, int) and isinstance(y, int) and x != y:
                res = (a, b)
                break
        self.cache[key] = res
        return res


def decide(P, t1, t2, table, n_total):
    """Return ('equivalent', nf) or ('different', S, (a, b), out1, out2) or ('unknown', ...)."""
    fam = FAM2[P.name]
    n1, n2 = nf2(fam, t1), nf2(fam, t2)
    if repr(n1) == repr(n2):
        return ('equivalent', n1)
    idx = sorted(leaves(t1) | leaves(t2))
    for r in (1, 2, 3):
        for S in itertools.combinations(idx, r):
            S = set(S)
            r1, r2 = restrict_term(t1, S), restrict_term(t2, S)
            if repr(nf2(fam, r1)) == repr(nf2(fam, r2)):
                continue
            # relabel the support to 0..r-1 and look up a base witness
            m = {i: j for j, i in enumerate(sorted(S))}
            w = table.find(relabel(r1, m), relabel(r2, m), r)
            if w is None:
                continue
            a_small, b_small = w
            a = [0] * n_total
            b = [0] * n_total
            for i, j in m.items():
                a[i], b[i] = a_small[j], b_small[j]
            # outside S: a = 0, b = any finite word (keep 0)
            o1, o2 = evs(P, t1, a, b, 0), evs(P, t2, a, b, 0)
            assert o1 != o2, (S, o1, o2)  # restriction + witness must separate the full terms
            return ('different', sorted(S), (a, b), o1, o2)
    return ('unknown', n1, n2)


if __name__ == '__main__':
    # self-test: random pairs of chain/split-K schedules over n products
    rng = random.Random(1)
    for P in [V100, A100, H100, CDNA1, CDNA2, CDNA3, SFMA]:
        fam = FAM2[P.name]
        n = 6
        table = WitnessTable(P, rng)
        stats = {'equivalent': 0, 'different': 0, 'unknown': 0}
        ts = []
        for _ in range(60):
            # random terms over 6 products: random chain or split-K
            perm = list(range(n))
            rng.shuffle(perm)
            K = P.K
            cuts = sorted(rng.sample(range(1, n), rng.randint(0, min(3, n - 1))))
            parts = [perm[i:j] for i, j in zip([0] + cuts, cuts + [n])]
            def chain_of(idxs):
                s = ('zero',)
                for i in range(0, len(idxs), K):
                    B = idxs[i:i + K]
                    slots = list(B) + [None] * (K - len(B))
                    if fam == 'tree':
                        rng.shuffle(slots)
                    s = ('blk', s, tuple(slots))
                return s
            if rng.random() < 0.5:
                t = chain_of([i for p in parts for i in p])
            else:
                t = chain_of(parts[0])
                for p in parts[1:]:
                    t = ('add', t, chain_of(p))
            ts.append(t)
        for t1, t2 in zip(ts[::2], ts[1::2]):
            r = decide(P, t1, t2, table, n)
            stats[r[0]] += 1
        print(f'{P.name:12s} {stats}')
