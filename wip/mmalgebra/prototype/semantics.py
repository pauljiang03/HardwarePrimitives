"""Reduction schedules for one output entry, and their semantics on every model.

A schedule is a term
    ('c0',)                      the initial accumulator C[i,j] (an FP32 word)
    ('zero',)                    +0
    ('blk', s, (i1, ..., iK))    one block FMA with c = s; each slot is a product index or None (0)
    ('add', s, t)                binary32 RNE addition (SIMT), subnormals kept
    ('addftz', s, t)             binary32 RNE addition with subnormal results flushed
Inputs: a, b (lists of words of the profile's format), c0 (FP32 word).
"""
import random
import os
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from models import *  # noqa


def ev(P, s, a, b, c0):
    tag = s[0]
    if tag == 'c0':
        return c0
    if tag == 'zero':
        return 0
    if tag == 'blk':
        c = ev(P, s[1], a, b, c0)
        prods = [(a[i], b[i]) if i is not None else (0, 0) for i in s[2]]
        return block(P, prods, c)
    if tag in ('add', 'addftz'):
        x = value32(ev(P, s[1], a, b, c0))
        y = value32(ev(P, s[2], a, b, c0))
        w = fl32(tag == 'addftz', x + y)
        if w is None:
            raise ModelError('addOverflow')
        return w
    raise ValueError(tag)


def evs(P, s, a, b, c0):
    try:
        return ev(P, s, a, b, c0)
    except ModelError as e:
        return 'err:' + str(e)


def chain(K, blocks, start=('zero',)):
    """blocks: list of lists of indices (len <= K); padded with None at the end."""
    s = start
    for B in blocks:
        s = ('blk', s, tuple(list(B) + [None] * (K - len(B))))
    return s


# ---------------------------------------------------------------- random inputs
def rand_word(fmt, rng, mode='mixed', center=None):
    if center is None:
        center = fmt.bias
    s = rng.getrandbits(1)
    emaxf = (1 << fmt.ebits) - 2
    M = rng.getrandbits(fmt.mbits)
    r = rng.random()
    if mode == 'narrow':
        E = min(max(center + rng.randint(-2, 2), 1), emaxf)
    elif mode == 'wide':
        E = rng.randint(0, emaxf)
    else:
        if r < 0.05:
            E = 0
        elif r < 0.8:
            E = min(max(center + rng.randint(-4, 4), 1), emaxf)
        else:
            E = min(max(center + rng.randint(-12, 12), 0), emaxf)
    if rng.random() < 0.3:
        M &= ~((1 << max(fmt.mbits - 2, 0)) - 1)
    return (s << (fmt.ebits + fmt.mbits)) | (E << fmt.mbits) | M


def rand_inputs(P, k, rng, mode='mixed'):
    center = P.fmt.bias + rng.randint(-3, 3)
    a = [rand_word(P.fmt, rng, mode, center) for _ in range(k)]
    b = [rand_word(P.fmt, rng, mode, center) for _ in range(k)]
    return a, b
