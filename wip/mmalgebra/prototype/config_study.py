"""Which GEMM kernel configurations give bit-identical results, per architecture.

A configuration determines, for each output entry, a reduction schedule over the k products:
  * instruction k (k_inst) and k-tile depth BK: the products are consumed in increasing k by
    chained block FMAs of the FMA size K, so neither changes the term (they are kept as
    parameters to show this);
  * split-K factor s with contiguous slices, partials combined serially ((R1+R2)+R3...) or by a
    pairwise tree; stream-K style slices at arbitrary multiples of BK;
  * C added in the first block (early) or by an FP32 addition in the epilogue;
  * k tail: zero-padded block, or (when k is not a multiple of K) a scalar FMA per tail product.

We group configurations by the decision procedure's verdict and print one witness per
non-equivalent pair of interest. Also compares with an abstraction that treats every MMA
instruction as one correctly rounded operation (RNE of c plus the exact sum of its k_inst
products).
"""
import itertools
import json
import random
import os
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
RESULTS = os.path.join(os.path.dirname(os.path.abspath(__file__)), 'results')
from decide_equiv import *  # noqa


def chain_term(P, idxs, start):
    K = P.K
    s = start
    for i in range(0, len(idxs), K):
        B = list(idxs[i:i + K])
        s = ('blk', s, tuple(B + [None] * (K - len(B))))
    return s


def config_term(P, k, cfg):
    split = cfg['split']
    combine = cfg['combine']
    early_c = cfg['early_c']
    bounds = cfg.get('bounds')
    if bounds is None:
        step = k // split
        bounds = [i * step for i in range(split)] + [k]
    parts = [list(range(bounds[i], bounds[i + 1])) for i in range(len(bounds) - 1)]
    partials = []
    for j, p in enumerate(parts):
        start = ('c0',) if (early_c and j == 0) else ('zero',)
        partials.append(chain_term(P, p, start))
    if combine == 'serial':
        t = partials[0]
        for u in partials[1:]:
            t = ('add', t, u)
    else:  # pairwise tree
        level = partials
        while len(level) > 1:
            nxt = [('add', level[i], level[i + 1]) for i in range(0, len(level) - 1, 2)]
            if len(level) % 2:
                nxt.append(level[-1])
            level = nxt
        t = level[0]
    if not early_c:
        t = ('add', t, ('c0',))
    return t


def nf_c0(fam, t):
    """Normal form with the c0 leaf (extends terms.nf2: 'c0' is a value leaf)."""
    return repr(nf2c(fam, t))


def nf2c(fam, t):
    if t[0] == 'c0':
        return ('c0',)
    if t[0] == 'zero':
        return None
    if fam == 'seq':
        if t[0] == 'blk':
            return ('blk', nf2c(fam, t[1]), frozenset(i for i in t[2] if i is not None))
        a, b = nf2cv(fam, t[1]), nf2cv(fam, t[2])
        return ('add',) + tuple(sorted([a, b], key=repr))
    if fam == 'cr':
        if t[0] == 'blk':
            ch = [nf2c(fam, t[1])] + [('leaf', i) for i in t[2] if i is not None]
        else:
            ch = [nf2c(fam, t[1]), nf2c(fam, t[2])]
        ch = [c for c in ch if c is not None]
        if len(ch) == 1:
            return ch[0]
        return ('node',) + tuple(sorted(ch, key=repr))
    if fam == 'tree':
        if t[0] == 'blk':
            tr = canon(tree_of_block(t[2]))
            c = nf2c(fam, t[1])
        else:
            c, tr = nf2c(fam, t[1]), nf2c(fam, t[2])
        if c is None:
            return tr
        if tr is None:
            return c
        return ('node',) + tuple(sorted([c, tr], key=repr))
    if fam == 'sfma':
        if t[0] == 'blk':
            (i,) = [i for i in t[2] if i is not None]
            return ('fma', nf2c(fam, t[1]), i)
        a, b = nf2c(fam, t[1]), nf2c(fam, t[2])
        return ('add',) + tuple(sorted([a, b], key=repr))


def nf2cv(fam, t):
    if t[0] == 'blk' and t[1] == ('zero',):
        idx = [i for i in t[2] if i is not None]
        if len(idx) == 1:
            return ('leaf', idx[0])
    return nf2c(fam, t)


def random_check(P, t1, t2, k, rng, R):
    """Fraction of random dense inputs (and c0) on which the two terms differ."""
    diff = 0
    tot = 0
    for _ in range(R):
        a, b = rand_inputs(P, k, rng, 'mixed')
        c0 = rng.choice([0, 0x3f800000, 0xbf000000, 0x40490fdb])
        x, y = evs(P, t1, a, b, c0), evs(P, t2, a, b, c0)
        if isinstance(x, int) and isinstance(y, int):
            tot += 1
            diff += x != y
    return diff, tot


def main():
    rng = random.Random(2026)
    k = 64
    out = {}
    profs = [V100, A100, H100, CDNA1, CDNA2, CDNA3]
    for P in profs:
        fam = FAM2[P.name]
        K = P.K
        cfgs = {}
        for split in (1, 2, 4):
            for combine in (('serial', 'tree') if split > 2 else ('serial',)):
                for early_c in (True, False):
                    cfgs[f's{split}-{combine}-{"C0" if early_c else "Cepi"}'] = dict(
                        split=split, combine=combine, early_c=early_c)
        # stream-K style: two slices with a boundary that is a multiple of K but not k/2
        cfgs['streamK(24|40)-C0'] = dict(split=2, combine='serial', early_c=True, bounds=[0, 24, 64])
        cfgs['streamK(16|48)-C0'] = dict(split=2, combine='serial', early_c=True, bounds=[0, 16, 64])
        terms_ = {name: config_term(P, k, c) for name, c in cfgs.items()}
        classes = {}
        for name, t in terms_.items():
            classes.setdefault(nf_c0(fam, t), []).append(name)
        print(f'\n{P.name}: {len(cfgs)} configurations, {len(classes)} bitwise classes')
        for v in classes.values():
            if len(v) > 1:
                print('   equivalent:', v)
        # random dense check of a few pairs
        names = list(terms_)
        pairs = [('s1-serial-C0', 's2-serial-C0'), ('s1-serial-C0', 's1-serial-Cepi'),
                 ('s4-serial-C0', 's4-tree-C0'), ('streamK(24|40)-C0', 'streamK(16|48)-C0')]
        rows = []
        for p1, p2 in pairs:
            d, tot = random_check(P, terms_[p1], terms_[p2], k, rng, 60)
            same = nf_c0(fam, terms_[p1]) == nf_c0(fam, terms_[p2])
            rows.append((p1, p2, same, d, tot))
            print(f'   {p1:20s} vs {p2:20s} theory={"equal" if same else "differ"}  '
                  f'random dense inputs differing: {d}/{tot}')
        out[P.name] = {'classes': list(classes.values()), 'pairs': rows}
    json.dump(out, open(os.path.join(RESULTS, 'config_study.json'), 'w'), indent=1)


if __name__ == '__main__':
    main()
