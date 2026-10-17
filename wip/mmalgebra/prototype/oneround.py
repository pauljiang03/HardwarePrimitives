"""Compare the 'MMA instruction = one correctly rounded operation' abstraction with the models
For each architecture and rewrite, report whether the abstraction and the model accept
it (equivalent for all inputs), with a separating input from the decision procedure."""
import os, random, sys
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from decide_equiv import *

def chain_of(P, idxs, start=('zero',)):
    s = start
    for i in range(0, len(idxs), P.K):
        B = list(idxs[i:i+P.K]); s = ('blk', s, tuple(B + [None]*(P.K-len(B))))
    return s

def one_round(P, terms_list, a, b, c0=0):
    """abstraction: each instruction = RNE(c + exact sum of its products)"""
    c = value32(c0)
    for inst in terms_list:
        s = c + sum((P.fmt.value(a[i]) * P.fmt.value(b[i]) for i in inst), Q(0))
        w = rne32(s); c = value32(w)
    return encode32(c) if c != 0 else 0

rng = random.Random(4)
rows = []
for P in [V100, A100, H100, CDNA1, CDNA2, CDNA3]:
    table = WitnessTable(P, rng)
    k = 16
    # R1: permute products across the halves of one k16 instruction (swap 0 and 15)
    base = list(range(16)); sw = base[:]; sw[0], sw[15] = sw[15], sw[0]
    t1, t2 = chain_of(P, base), chain_of(P, sw)
    r = decide(P, t1, t2, table, k)
    rows.append((P.name, 'R1 swap k=0,15 inside one k16 MMA', 'accepts', r[0]))
    if r[0] == 'different':
        a, b = r[2]; print(P.name, 'R1 witness support', r[1], 'a', [hex(a[i]) for i in r[1]], 'b', [hex(b[i]) for i in r[1]], hex(r[3]), hex(r[4]))
    # R2: one k16 instruction vs two k8 instructions (model: blocks of K either way)
    # model term is the same chain of FMA-size blocks; abstraction differs
    rows.append((P.name, 'R2 one k16 MMA -> two k8 MMAs', 'rejects', 'equivalent (same blocks)' if P.K <= 8 else 'n/a (k8 FMA size unknown)'))
    # R3 (CDNA2): blk(c, I) -> c (+) blk(0, I) for one block
    I = tuple(range(P.K))
    t1 = ('blk', ('c0',), I); t2 = ('addftz', ('c0',), ('blk', ('zero',), I))
    # random check
    diff = 0
    for _ in range(300):
        a, b = rand_inputs(P, P.K, rng, 'mixed'); c0 = rng.choice([0x3f800000, 0xc0490fdb, 0x3a000001])
        x, y = evs(P, t1, a, b, c0), evs(P, t2, a, b, c0)
        diff += (isinstance(x, int) and isinstance(y, int) and x != y)
    rows.append((P.name, 'R3 C in accumulator -> C in epilogue (one block)', 'rejects', f'differs on {diff}/300 random' if diff else 'equal on 300 random (law)'))
for r in rows: print('  %-12s %-50s abstraction:%-8s model: %s' % r)
