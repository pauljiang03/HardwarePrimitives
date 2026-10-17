"""The FP8 schedule algebras: every reduction term over 3 products on the FP8 models, its class
of equal outputs, and conjectured normal forms.

Terms, from the zero accumulator, with each product used exactly once:
  ('z',)         the zero accumulator
  ('b', t, S)    a block FMA with accumulator input t and the products S, a set (Tensor Cores) or
                 a pair (O, E) of the products in odd and in even slots (CDNA 3); S may be empty
  ('a', t, u)    a binary32 round-to-nearest-even addition
Up to 3 nonempty blocks, 2 additions and 1 empty block. Normal forms:
  rigid   (Blackwell): rigid labeled trees, each block's products a multiset
  trunc   (Ada, Hopper): rigid, plus an empty block is a truncation node T, kept only over an
          addition (block outputs already have a 13-bit mantissa), absorbed by a following nonempty
          block
  parity  (CDNA 3): rigid, but a block's products form an unordered pair {odd, even} of multisets
Each term is evaluated on N random inputs (structured near the alignment widths 13, 24 and 25; a
quarter unstructured; E4M3 operands of magnitude at most 240 on the Tensor Cores). A normal form is
unsound if two of its terms differ on some input; two normal forms are unseparated if their terms
agree on every input. Unseparated pairs are then searched with targeted inputs until an input
separates them. The rows "rigid" on Hopper and CDNA 3 show that the plain rigid normal forms are
unsound there.

Usage: python3 fp8_enum.py [N]   (default 800; about an hour of CPU time, six processes)
"""
import itertools
import multiprocessing
import random
import sys
from fp8models import *


def subsets(s):
    s = sorted(s)
    for r in range(len(s) + 1):
        for c in itertools.combinations(s, r):
            yield frozenset(c)


def gen(prods, nb, na, ne, parity):
    """Terms over exactly the products `prods`, with at most nb nonempty blocks, na additions and
    ne empty blocks."""
    out = []
    if not prods:
        out.append(('z',))
    if nb >= 1:
        for S in subsets(prods):
            if not S:
                continue
            for t in gen(prods - S, nb - 1, na, ne, parity):
                if parity:
                    for O in subsets(S):
                        out.append(('b', t, (O, S - O)))
                else:
                    out.append(('b', t, S))
    if ne >= 1:
        for t in gen(prods, nb, na, ne - 1, parity):
            out.append(('b', t, (frozenset(), frozenset()) if parity else frozenset()))
    if na >= 1 and len(prods) >= 2:
        for S in subsets(prods):
            if not S or S == prods:
                continue
            for nb1 in range(nb + 1):
                for na1 in range(na):
                    for ne1 in range(ne + 1):
                        for t in gen(S, nb1, na1, ne1, parity):
                            for u in gen(prods - S, nb - nb1, na - 1 - na1, ne - ne1, parity):
                                out.append(('a', t, u))
    return out


def ev(P, t, q):
    if t[0] == 'z':
        return 0
    if t[0] == 'a':
        x, y = ev(P, t[1], q), ev(P, t[2], q)
        if x is None or y is None:
            return None
        return rne32(value32(x) + value32(y))
    c = ev(P, t[1], q)
    if c is None:
        return None
    try:
        if isinstance(P, TCModel):
            return tc_sparse(P, [q[i] for i in sorted(t[2])], c)
        O, E = t[2]
        return mc_sparse(P, [q[i] for i in sorted(O)], [q[i] for i in sorted(E)], c)
    except ModelError:
        return None


def key(x):
    return repr(x)


def nf(t, mode):
    """Normal form; None when the term has no products."""
    if t[0] == 'z':
        return None
    if t[0] == 'a':
        a, b = nf(t[1], mode), nf(t[2], mode)
        if a is None:
            return b
        if b is None:
            return a
        return ('A',) + tuple(sorted([a, b], key=key))
    acc = nf(t[1], mode)
    S = t[2]
    if isinstance(S, tuple) and mode != 'parity':
        S = S[0] | S[1]
    if mode == 'parity':
        O, E = S
        empty = not O and not E
        labels = tuple(sorted([tuple(sorted(O)), tuple(sorted(E))]))
        single = len(O) + len(E) == 1
    else:
        empty = not S
        labels = tuple(sorted(S))
        single = len(S) == 1
    if empty:
        if mode == 'trunc' and acc is not None and acc[0] == 'A':
            return ('T', acc)
        return acc
    if mode == 'trunc' and acc is not None and acc[0] == 'T':
        acc = acc[1]
    if acc is None and single:
        return ('L', (list(O) + list(E))[0] if mode == 'parity' else list(S)[0])
    return ('B', acc, labels)


def product_table(fa, fb, lim):
    """The nonzero products by exponent: {floor(log2 |p|): [(a, b), ...]}."""
    wa = [w for w in fa.words() if fa.value(w) != 0 and abs(fa.value(w)) <= lim]
    wb = [w for w in fb.words() if fb.value(w) != 0 and abs(fb.value(w)) <= lim]
    tab = {}
    for a in wa:
        for b in wb:
            tab.setdefault(floor_log2(abs(fa.value(a) * fb.value(b))), []).append((a, b))
    return tab


def table(P):
    if isinstance(P, TCModel):
        return product_table(P.fmt, P.fmt, 240)
    return product_table(P.fa, P.fb, 10 ** 9)


def rand_inputs(P, n, nprod, rng):
    """Structured inputs: a base exponent in the upper half of the product range and offsets of
    0 to 30 below it, with random signs; every fourth input unstructured."""
    tab = table(P)
    exps = sorted(tab)
    ins = []
    for j in range(n):
        if j % 4 == 3:
            ins.append({i: rng.choice(tab[rng.choice(exps)]) for i in range(nprod)})
            continue
        top = rng.choice(exps[len(exps) // 2:])
        q = {}
        for i in range(nprod):
            off = rng.choice([0, 0, 1, rng.randint(0, 14), rng.randint(10, 16), rng.randint(20, 30)])
            e = max(top - off, exps[0])
            while e not in tab:
                e += 1
            q[i] = rng.choice(tab[e])
        ins.append(q)
    return ins


def separate(P, t1, t2, seed, tries=400000):
    """Search an input on which t1 and t2 differ: alternately unstructured and structured."""
    rng = random.Random(seed)
    tab = table(P)
    exps = sorted(tab)
    for it in range(tries):
        if it % 2 == 0:
            q = {i: rng.choice(tab[rng.choice(exps)]) for i in range(3)}
        else:
            top = rng.choice(exps[len(exps) // 3:])
            q = {}
            for i in range(3):
                e = max(top - rng.choice([0, 0, rng.randint(0, 30)]), exps[0])
                while e not in tab:
                    e += 1
                q[i] = rng.choice(tab[e])
        x, y = ev(P, t1, q), ev(P, t2, q)
        if x != y:
            return it + 1, q, x, y
    return None


def fmt_of(P):
    return (P.fmt, P.fmt) if isinstance(P, TCModel) else (P.fa, P.fb)


def run(args):
    P, mode, nprod, ninputs = args
    rng = random.Random(1)
    prods = frozenset(range(nprod))
    terms = gen(prods, nprod, 2, 1, not isinstance(P, TCModel))
    terms = list({key(t): t for t in terms}.values())
    ins = rand_inputs(P, ninputs, nprod, rng)
    fp, rep = {}, {}
    for t in terms:
        fp[key(t)] = tuple(ev(P, t, q) for q in ins)
        rep.setdefault(key(nf(t, mode)), t)
    by_fp, by_nf = {}, {}
    for t in terms:
        by_fp.setdefault(fp[key(t)], set()).add(key(nf(t, mode)))
        by_nf.setdefault(key(nf(t, mode)), set()).add(fp[key(t)])
    unsound = sum(1 for v in by_nf.values() if len(v) > 1)
    merged = [sorted(v) for v in by_fp.values() if len(v) > 1]
    lines = [f'{P.name:26s} mode={mode:6s} n={nprod} terms={len(terms):5d} '
             f'normal forms={len(by_nf):4d} classes={len(by_fp):4d} unsound normal forms={unsound} '
             f'unseparated pairs={sum(len(v) - 1 for v in merged)}']
    if mode != 'rigid' or isinstance(P, TCModel) and P.out_bits == 23:
        fa, fb = fmt_of(P)
        for v in merged:
            for other in v[1:]:
                lines.append(f'   unseparated: {v[0]}  vs  {other}')
                found = separate(P, rep[v[0]], rep[other], seed=len(lines))
                if found is None:
                    lines.append('      not separated by targeted search')
                    continue
                n, q, x, y = found
                ps = ', '.join(f'{fa.value(a)}*{fb.value(b)}' for a, b in (q[i] for i in range(3)))
                lines.append(f'      separated after {n} targeted inputs: products {ps}; '
                             f'{hex(x) if x is not None else None} vs {hex(y) if y is not None else None}')
    return lines


MODELS = [(BLACKWELL, 'rigid'), (HOPPER, 'trunc'), (ADA, 'trunc'), (HOPPER, 'rigid'),
          (CDNA3_E4M3, 'parity'), (CDNA3_E5M2, 'parity'), (CDNA3_E4M3E5M2, 'parity'),
          (CDNA3_E4M3, 'rigid')]

if __name__ == '__main__':
    ninputs = int(sys.argv[1]) if len(sys.argv) > 1 else 800
    print(f'Terms over 3 products, {ninputs} random inputs per model')
    with multiprocessing.Pool(6) as pool:
        for lines in pool.imap(run, [(P, mode, 3, ninputs) for P, mode in MODELS]):
            print('\n'.join(lines), flush=True)
