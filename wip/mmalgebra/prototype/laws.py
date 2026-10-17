"""Random testing of candidate schedule laws on every model.

For each profile and law, count trials and violations (outputs differ as words or errors).
"""
import itertools
import random
import os
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from semantics import *  # noqa

TRIALS = int(sys.argv[1]) if len(sys.argv) > 1 else 300


def rand_c(rng):
    r = rng.random()
    if r < 0.25:
        return 0
    s = rng.getrandbits(1)
    E = rng.randint(100, 150)
    M = rng.getrandbits(23)
    if rng.random() < 0.5:
        M &= ~((1 << 16) - 1)
    return (s << 31) | (E << 23) | M


def neg_word(fmt, w):
    return w ^ (1 << (fmt.ebits + fmt.mbits))


def D4(K):
    if K == 4:
        g = [(0, 1, 2, 3), (1, 0, 2, 3), (0, 1, 3, 2), (1, 0, 3, 2),
             (2, 3, 0, 1), (3, 2, 0, 1), (2, 3, 1, 0), (3, 2, 1, 0)]
        return set(g)
    if K == 2:
        return {(0, 1), (1, 0)}
    return {tuple(range(K))}


def run(P, rng, trials):
    K = P.K
    res = {}

    def rec(name, eq):
        r = res.setdefault(name, [0, 0])
        r[0] += 1
        r[1] += (not eq)

    for _ in range(trials):
        mode = rng.choice(['mixed', 'narrow', 'wide'])
        k = 3 * K + 2
        a, b = rand_inputs(P, k, rng, mode)
        c0 = rand_c(rng)
        # permutation within a block
        I = list(range(K))
        pi = list(range(K))
        rng.shuffle(pi)
        s1 = ('blk', ('c0',), tuple(I))
        s2 = ('blk', ('c0',), tuple(I[j] for j in pi))
        e1, e2 = evs(P, s1, a, b, c0), evs(P, s2, a, b, c0)
        rec('perm (any)', e1 == e2)
        if tuple(pi) in D4(K):
            rec('perm (D4)', e1 == e2)
        else:
            rec('perm (non-D4)', e1 == e2)
        # zero padding anywhere (a block with some empty slots)
        if K >= 2:
            m = rng.randint(1, K - 1)
            slots = list(range(m)) + [None] * (K - m)
            sl2 = slots[:]
            rng.shuffle(sl2)
            rec('zero slots moved', evs(P, ('blk', ('c0',), tuple(slots)), a, b, c0) ==
                evs(P, ('blk', ('c0',), tuple(sl2)), a, b, c0))
        # empty block is the identity (on a block output, and on c0)
        sc = chain(K, [list(range(K))], ('c0',))
        rec('empty block after a block', evs(P, ('blk', sc, (None,) * K), a, b, c0) == evs(P, sc, a, b, c0))
        rec('empty block on c0', evs(P, ('blk', ('c0',), (None,) * K), a, b, c0) == c0)
        # c split: blk(s, I) = s (+) blk(0, I)
        sI = tuple(range(K, 2 * K))
        lhs = evs(P, ('blk', sc, sI), a, b, c0)
        rec('c-split (RNE add)', lhs == evs(P, ('add', sc, ('blk', ('zero',), sI)), a, b, c0))
        rec('c-split (FTZ add)', lhs == evs(P, ('addftz', sc, ('blk', ('zero',), sI)), a, b, c0))
        # singleton first block merges into the next block (from zero)
        if K >= 2:
            J = list(range(1, K))
            m1 = chain(K, [[0], J])
            m2 = chain(K, [[0] + J])
            rec('merge singleton first block', evs(P, m1, a, b, c0) == evs(P, m2, a, b, c0))
            # the same with a product whose significand < 2 (normalized product)
        # one-product block = fma (RNE of exact s + p)
        f1 = ('blk', sc, (K,) + (None,) * (K - 1))
        f2 = ('add', sc, ('blk', ('zero',), (K,) + (None,) * (K - 1)))
        rec('one-product block = add of product', evs(P, f1, a, b, c0) == evs(P, f2, a, b, c0))
        # add of two one-product blocks = two-product block
        if K >= 2:
            g1 = ('add', ('blk', ('zero',), (0,) + (None,) * (K - 1)), ('blk', ('zero',), (1,) + (None,) * (K - 1)))
            g2 = ('blk', ('zero',), (0, 1) + (None,) * (K - 2))
            rec('add of one-product blocks = block', evs(P, g1, a, b, c0) == evs(P, g2, a, b, c0))
        # split-K: chain of 3 blocks vs (chain of 2) + (chain of 1) vs ...
        B = [list(range(0, K)), list(range(K, 2 * K)), list(range(2 * K, 3 * K))]
        full = chain(K, B)
        sp = ('add', chain(K, B[:2]), chain(K, B[2:]))
        rec('split-K (2+1)', evs(P, full, a, b, c0) == evs(P, sp, a, b, c0))
        # block boundary moved by one product
        if K >= 2:
            C1 = chain(K, [list(range(0, K)), list(range(K, 2 * K - 1))])
            C2 = chain(K, [list(range(0, K - 1)), list(range(K - 1, 2 * K - 1))])
            rec('block boundary moved', evs(P, C1, a, b, c0) == evs(P, C2, a, b, c0))
        # negation of every input (a and c0)
        an = [neg_word(P.fmt, w) for w in a]
        x1 = evs(P, full if True else None, a, b, c0)
        cfull = chain(K, B, ('c0',))
        x1 = evs(P, cfull, a, b, c0)
        x2 = evs(P, cfull, an, b, c0 ^ (1 << 31))
        if isinstance(x1, int) and isinstance(x2, int):
            rec('negation symmetric', value32(x1) == -value32(x2))
        # transpose (swap a and b)
        rec('swap a,b', evs(P, cfull, a, b, c0) == evs(P, cfull, b, a, c0))
    return res


def main():
    rng = random.Random(7)
    profs = [V100, A100, H100, A100BF, H100BF, SFMA, CDNA1, CDNA1BF, CDNA2, CDNA2BF, CDNA2BF1K, CDNA3, CDNA3BF]
    allres = {}
    for P in profs:
        allres[P.name] = run(P, rng, TRIALS)
    names = []
    for r in allres.values():
        for n in r:
            if n not in names:
                names.append(n)
    print(f'{"law":38s}' + ''.join(f'{p.name[:11]:>12s}' for p in profs))
    for n in names:
        row = f'{n:38s}'
        for p in profs:
            r = allres[p.name].get(n)
            row += f'{"-":>12s}' if r is None else f'{r[1]:>5d}/{r[0]:<6d}'
        print(row)


if __name__ == '__main__':
    main()
