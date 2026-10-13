"""Schedules with split-K additions: all linear terms over n <= 3 products.

Terms: ('zero',) | ('blk', t, slots) | ('add', t, u). Each product index occurs exactly once; no
empty blocks and no additions of zero. Equivalence classes are computed from fingerprints on
random and special inputs and compared with the hypothesised normal forms:

  'seq'  (Tensor Cores, CDNA 3, CDNA 1 bf16): blk nodes keep their c-child and their product set;
          add nodes are unordered; a one-product block from zero is the product's value when it is
          a child of an add node (but stays a block when it is a c-child: products and c are
          aligned differently).
  'cr'   (CDNA 1 fp16): every node is RNE of the exact sum of its children; one-child nodes vanish.
  'tree' (CDNA 2): binary summation tree; blk(c, I) = c (+) tree(I) (late c); unordered.
  'sfma' (SFMA): blk(c, {x}) = RNE(c + x exactly); blk(0, {x}) = RNE(x) as a value.
"""
import itertools
import random
import os
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from normal import *  # noqa

FAM2 = {'V100 fp16': 'seq', 'A100 fp16': 'seq', 'H100 fp16': 'seq', 'A100 bf16': 'seq',
        'H100 bf16': 'seq', 'CDNA3 fp16': 'seq', 'CDNA3 bf16': 'seq', 'CDNA1 bf16': 'seq',
        'CDNA1 fp16': 'cr', 'CDNA2 fp16': 'tree', 'CDNA2 bf16': 'tree', 'CDNA2 bf16_1k': 'tree',
        'SFMA fp32': 'sfma'}


def subsets_split(S):
    S = sorted(S)
    for r in range(0, len(S) + 1):
        for L in itertools.combinations(S, r):
            yield frozenset(L), frozenset(x for x in S if x not in L)


def terms(S, K, positional, addftz=False):
    """All linear terms over the set S (frozenset)."""
    out = []
    if not S:
        return [('zero',)]
    # blocks: product set L (1..K), c-child over the rest
    for L, R in subsets_split(S):
        if not L or len(L) > K:
            continue
        for c in terms(R, K, positional, addftz):
            if positional:
                arrangements = set(itertools.permutations(list(sorted(L)) + [None] * (K - len(L))))
            else:
                arrangements = [tuple(sorted(L)) + (None,) * (K - len(L))]
            for slots in arrangements:
                out.append(('blk', c, tuple(slots)))
    # additions: both sides nonempty, unordered (take S1 containing min(S))
    m = min(S)
    for S1, S2 in subsets_split(S):
        if m not in S1 or not S2:
            continue
        for t in terms(S1, K, positional, addftz):
            for u in terms(S2, K, positional, addftz):
                out.append(('addftz' if addftz else 'add', t, u))
    return out


def key(x):
    return repr(x)


def nf2(fam, t):
    tag = t[0]
    if tag == 'zero':
        return None
    if fam == 'seq':
        if tag == 'blk':
            return ('blk', nf2(fam, t[1]), frozenset(i for i in t[2] if i is not None))
        a, b = nf2v(fam, t[1]), nf2v(fam, t[2])
        return ('add',) + tuple(sorted([a, b], key=key))
    if fam == 'cr':
        if tag == 'blk':
            ch = [nf2(fam, t[1])] + [('leaf', i) for i in t[2] if i is not None]
        else:
            ch = [nf2(fam, t[1]), nf2(fam, t[2])]
        ch = [c for c in ch if c is not None]
        if len(ch) == 1:
            return ch[0]
        return ('node',) + tuple(sorted(ch, key=key))
    if fam == 'tree':
        if tag == 'blk':
            tr = tree_of_block(t[2])
            tr = canon(tr)
            c = nf2(fam, t[1])
        else:
            c, tr = nf2(fam, t[1]), nf2(fam, t[2])
        if c is None:
            return tr
        if tr is None:
            return c
        return ('node',) + tuple(sorted([c, tr], key=key))
    if fam == 'sfma':
        if tag == 'blk':
            (i,) = [i for i in t[2] if i is not None]
            c = nf2(fam, t[1])
            return ('fma', c, i)
        a, b = nf2(fam, t[1]), nf2(fam, t[2])
        return ('add',) + tuple(sorted([a, b], key=key))
    raise ValueError(fam)


def nf2v(fam, t):
    """Normal form of a term used as a value (child of an add node): a one-product block from zero
    is the product itself on the 'seq' family."""
    if t[0] == 'blk' and t[1] == ('zero',):
        idx = [i for i in t[2] if i is not None]
        if len(idx) == 1:
            return ('leaf', idx[0])
    return nf2(fam, t)


def fingerprint(P, t, inputs):
    return tuple(evs(P, t, a, b, 0) for a, b in inputs)


def run(P, n, R, rng):
    fam = FAM2[P.name]
    positional = fam == 'tree'
    ts = terms(frozenset(range(n)), P.K, positional)
    inputs = []
    for _ in range(R):
        if rng.random() < 0.6:
            a = [special_word(P.fmt, rng) for _ in range(n)]
            b = [special_word(P.fmt, rng) for _ in range(n)]
        else:
            a, b = rand_inputs(P, n, rng, rng.choice(['mixed', 'narrow', 'wide']))
        inputs.append((a, b))
    fps = {}
    nfs = {}
    for t in ts:
        nfs.setdefault(key(nf2(fam, t)), []).append(t)
    fp_of = {}
    for t in ts:
        fp_of[key(t)] = fingerprint(P, t, inputs)
    # soundness: same NF -> same fingerprint
    unsound = 0
    for k_, mem in nfs.items():
        f0 = fp_of[key(mem[0])]
        for t in mem[1:]:
            if fp_of[key(t)] != f0:
                unsound += 1
                if unsound <= 3:
                    j = next(i for i in range(R) if fp_of[key(t)][i] != f0[i])
                    print('   UNSOUND', P.name, mem[0], t, inputs[j], f0[j], fp_of[key(t)][j])
    # completeness: different NF -> different fingerprint (on the shared inputs; else search)
    keys = list(nfs)
    unsep = 0
    for i in range(len(keys)):
        for j in range(i + 1, len(keys)):
            fi = fp_of[key(nfs[keys[i]][0])]
            fj = fp_of[key(nfs[keys[j]][0])]
            if any(x != y and isinstance(x, int) and isinstance(y, int) for x, y in zip(fi, fj)):
                continue
            # targeted search
            t1, t2 = nfs[keys[i]][0], nfs[keys[j]][0]
            found = False
            for _ in range(6000):
                a = [special_word(P.fmt, rng) for _ in range(n)]
                b = [special_word(P.fmt, rng) for _ in range(n)]
                x, y = evs(P, t1, a, b, 0), evs(P, t2, a, b, 0)
                if isinstance(x, int) and isinstance(y, int) and x != y:
                    found = True
                    break
            if not found:
                unsep += 1
                if unsep <= 4:
                    print('   NOT SEPARATED', P.name, keys[i], '|', keys[j])
    print(f'{P.name:14s} n={n} terms={len(ts):6d} normal-forms={len(keys):5d} unsound={unsound} '
          f'unseparated={unsep}', flush=True)


if __name__ == '__main__':
    rng = random.Random(5)
    R = int(sys.argv[1]) if len(sys.argv) > 1 else 300
    profs = [V100, A100, H100, A100BF, H100BF, SFMA, CDNA1, CDNA1BF, CDNA2, CDNA2BF, CDNA3, CDNA3BF]
    for P in profs:
        for n in [2, 3]:
            run(P, n, R, rng)
