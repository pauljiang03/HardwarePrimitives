"""Normal forms of chain schedules per architecture family, restriction to supports, and the
witness search for distinct normal forms.

A chain schedule is a list of blocks; a block is a tuple of K slots (product index or None),
evaluated from c0 = +0 (GEMM with beta = 0).

Families:
  'seq'  : Tensor Cores (V100/A100/H100 fp16/bf16), CDNA 3 fp16/bf16, CDNA 1 bf16
           -> tuple of nonempty frozensets (order of blocks matters, order inside does not).
           CDNA 1 bf16 obeys the 'crm' laws while every product is representable in binary32,
           but a bf16 product can fall below binary32's range; over all inputs it is rigid
           (bf16_extremes.py separates its patterns over three products).
  'crm'  : CDNA 1 fp16 -> 'seq' with a singleton first block merged into the next block
  'tree' : CDNA 2 -> unordered binary summation tree (zero leaves pruned, unary nodes collapsed)
  'sfma' : SFMA (K = 1) -> 'seq' (blocks are singletons)
"""
import itertools
import random
import os
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from semantics import *  # noqa

FAMILY = {'V100 fp16': 'seq', 'A100 fp16': 'seq', 'H100 fp16': 'seq', 'A100 bf16': 'seq',
          'H100 bf16': 'seq', 'CDNA3 fp16': 'seq', 'CDNA3 bf16': 'seq', 'CDNA1 bf16': 'seq',
          'CDNA1 fp16': 'crm', 'CDNA2 fp16': 'tree', 'CDNA2 bf16': 'tree',
          'CDNA2 bf16_1k': 'tree', 'SFMA fp32': 'seq'}


def restrict(blocks, S):
    return [tuple(i if (i is not None and i in S) else None for i in B) for B in blocks]


def nf_seq(blocks):
    out = []
    for B in blocks:
        s = frozenset(i for i in B if i is not None)
        if s:
            out.append(s)
    return tuple(out)


def nf_crm(blocks):
    s = list(nf_seq(blocks))
    if len(s) >= 2 and len(s[0]) == 1:
        s = [s[0] | s[1]] + s[2:]
    return tuple(s)


def tree_of_block(B):
    """pairTree over slots: split at len/2, prune empties."""
    def t(xs):
        if len(xs) == 0:
            return None
        if len(xs) == 1:
            return ('leaf', xs[0]) if xs[0] is not None else None
        h = len(xs) // 2
        u, v = t(xs[:h]), t(xs[h:])
        if u is None:
            return v
        if v is None:
            return u
        return ('node', u, v)
    return t(list(B))


def canon(tr):
    if tr is None:
        return None
    if tr[0] == 'leaf':
        return ('leaf', tr[1])
    a, b = canon(tr[1]), canon(tr[2])
    return ('node',) + tuple(sorted([a, b], key=repr))


def nf_tree(blocks):
    acc = None
    for B in blocks:
        t = tree_of_block(B)
        if t is None:
            continue
        acc = t if acc is None else ('node', acc, t)
    return canon(acc)


NF = {'seq': nf_seq, 'crm': nf_crm, 'tree': nf_tree}


def nf(P, blocks):
    return NF[FAMILY[P.name]](blocks)


# ---------------------------------------------------------------- enumeration of chain schedules
def ordered_partitions(items, K):
    """All sequences of nonempty blocks (as sorted tuples) of size <= K covering items."""
    items = list(items)
    if not items:
        yield []
        return
    n = len(items)
    for r in range(1, min(K, n) + 1):
        for first in itertools.combinations(items, r):
            rest = [x for x in items if x not in first]
            for tail in ordered_partitions(rest, K):
                yield [first] + tail


def slotted(blocks, K, positional):
    """Expand blocks (tuples of indices) into K-slot tuples; with `positional`, every arrangement
    of indices and empty slots up to the D4/pair symmetry is produced."""
    if not positional:
        yield [tuple(list(B) + [None] * (K - len(B))) for B in blocks]
        return
    choices = []
    for B in blocks:
        opts = set()
        for perm in itertools.permutations(list(B) + [None] * (K - len(B))):
            opts.add(perm)
        choices.append(sorted(opts, key=repr))
    for combo in itertools.product(*choices):
        yield list(combo)


def schedules(P, n):
    positional = FAMILY[P.name] == 'tree'
    for bl in ordered_partitions(range(n), P.K):
        for s in slotted(bl, P.K, positional):
            yield s


# ---------------------------------------------------------------- inputs
def special_word(fmt, rng):
    """Words that tend to separate schedules: significands near 2 (products >= 2), wide exponents,
    tiny values (bf16 extremes)."""
    r = rng.random()
    sgn = rng.getrandbits(1) << (fmt.ebits + fmt.mbits)
    emaxf = (1 << fmt.ebits) - 2
    if r < 0.3:
        E = fmt.bias + rng.randint(-3, 3)
        M = (1 << fmt.mbits) - 1 - rng.getrandbits(max(fmt.mbits - 3, 1))  # significand near 2
    elif r < 0.6:
        E = fmt.bias + rng.randint(-12, 12)
        M = rng.getrandbits(fmt.mbits)
    elif r < 0.8:
        E = rng.randint(1, emaxf)
        M = rng.getrandbits(fmt.mbits)
    else:
        E = rng.choice([0, 1, 2, emaxf])
        M = rng.getrandbits(fmt.mbits)
    E = min(max(E, 0), emaxf)
    return sgn | (E << fmt.mbits) | M


def find_witness(P, s1, s2, n, rng, tries=20000):
    for t in range(tries):
        if t % 2 == 0:
            a = [special_word(P.fmt, rng) for _ in range(n)]
            b = [special_word(P.fmt, rng) for _ in range(n)]
        else:
            a, b = rand_inputs(P, n, rng, rng.choice(['mixed', 'narrow', 'wide']))
        e1 = evs(P, chain_slots(s1), a, b, 0)
        e2 = evs(P, chain_slots(s2), a, b, 0)
        if isinstance(e1, int) and isinstance(e2, int) and e1 != e2:
            return a, b, e1, e2
    return None


def chain_slots(blocks):
    s = ('zero',)
    for B in blocks:
        s = ('blk', s, tuple(B))
    return s
