#!/usr/bin/env python3
"""Cross-check the NVIDIA Tensor Core models against Microsoft's MMA-Sim.

Usage: python3 scripts/check_mmasim.py --mmasim <MMA-Sim checkout> --python <python with torch>
       [--cases N] [--seed S]     (also from MMASIM_DIR and MMASIM_PYTHON)
"""
if not __debug__:
    raise SystemExit('Run without python -O or PYTHONOPTIMIZE: these checks rely on assert.')
import argparse
import hashlib
import json
import os
import random
import subprocess
import sys
from collections import Counter, defaultdict
from fractions import Fraction as Q
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
FEATURES = ROOT / '.lake/build/bin/tc_features'
TMP = ROOT / 'tmp/mmasim'

# Lean model parameters: (fmt, nfma, F, eAlignMin, outBits)
LEAN = {
    'v100-f16': ('fp16', 4, 23, 'none', 23),
    'a100-f16': ('fp16', 8, 24, '-132', 23), 'a100-bf16': ('bf16', 8, 24, '-132', 23),
    'a100-tf32': ('tf32', 4, 24, '-132', 23),
    'hopper-f16': ('fp16', 16, 25, '-133', 23), 'hopper-bf16': ('bf16', 16, 25, '-133', 23),
    'hopper-tf32-mma': ('tf32', 8, 25, '-133', 23), 'hopper-tf32-wmma': ('tf32', 4, 25, '-133', 23),
    'ada-e4m3': ('e4m3', 16, 13, 'none', 13), 'ada-e5m2': ('e5m2', 16, 13, 'none', 13),
    'hopper-e4m3': ('e4m3', 32, 13, 'none', 13), 'hopper-e5m2': ('e5m2', 32, 13, 'none', 13),
    'blackwell-e4m3': ('e4m3', 32, 25, 'none', 23), 'blackwell-e5m2': ('e5m2', 32, 25, 'none', 23),
}

# (variant, Lean model, MMA-Sim class, arch, shape, kinst)
VARIANTS = [
    ('V100 fp16 mma.m8n8k4', 'v100-f16', 'MMA', 'Volta', 'm8n8k4.f32.f16.f16.f32', 4),
    ('A100 fp16 mma.m16n8k16', 'a100-f16', 'MMA', 'Ampere', 'm16n8k16.f32.f16.f16.f32', 16),
    ('A100 fp16 mma.m16n8k8', 'a100-f16', 'MMA', 'Ampere', 'm16n8k8.f32.f16.f16.f32', 8),
    ('A100 bf16 mma.m16n8k16', 'a100-bf16', 'MMA', 'Ampere', 'm16n8k16.f32.bf16.bf16.f32', 16),
    ('A100 tf32 mma.m16n8k8', 'a100-tf32', 'MMA', 'Ampere', 'm16n8k8.f32.tf32.tf32.f32', 8),
    ('Ada fp16 mma.m16n8k16', 'a100-f16', 'MMA', 'Ada Lovelace', 'm16n8k16.f32.f16.f16.f32', 16),
    ('Ada bf16 mma.m16n8k16', 'a100-bf16', 'MMA', 'Ada Lovelace', 'm16n8k16.f32.bf16.bf16.f32', 16),
    ('Ada tf32 mma.m16n8k8', 'a100-tf32', 'MMA', 'Ada Lovelace', 'm16n8k8.f32.tf32.tf32.f32', 8),
    ('H100 fp16 mma.m16n8k16', 'hopper-f16', 'MMA', 'Hopper', 'm16n8k16.f32.f16.f16.f32', 16),
    ('H100 bf16 mma.m16n8k16', 'hopper-bf16', 'MMA', 'Hopper', 'm16n8k16.f32.bf16.bf16.f32', 16),
    ('H100 tf32 mma.m16n8k8', 'hopper-tf32-mma', 'MMA', 'Hopper', 'm16n8k8.f32.tf32.tf32.f32', 8),
    ('H100 tf32 mma.m16n8k4 (as WMMA HMMA.1684)', 'hopper-tf32-wmma', 'MMA', 'Hopper',
     'm16n8k4.f32.tf32.tf32.f32', 4),
    ('H100 fp16 wgmma.m64n8k16', 'hopper-f16', 'WGMMA', 'Hopper', 'm64n8k16.f32.f16.f16', 16),
    ('H100 bf16 wgmma.m64n8k16', 'hopper-bf16', 'WGMMA', 'Hopper', 'm64n8k16.f32.bf16.bf16', 16),
    ('H100 tf32 wgmma.m64n8k8', 'hopper-tf32-mma', 'WGMMA', 'Hopper', 'm64n8k8.f32.tf32.tf32', 8),
    ('B200 fp16 mma.m16n8k16', 'hopper-f16', 'MMA', 'Blackwell', 'm16n8k16.f32.f16.f16.f32', 16),
    ('B200 bf16 mma.m16n8k16', 'hopper-bf16', 'MMA', 'Blackwell', 'm16n8k16.f32.bf16.bf16.f32', 16),
    ('B200 tf32 mma.m16n8k8', 'hopper-tf32-mma', 'MMA', 'Blackwell', 'm16n8k8.f32.tf32.tf32.f32', 8),
    ('B200 fp16 tcgen05.kind::f16', 'hopper-f16', 'TCGen05MMA', 'Blackwell', 'm64n8k16.f32.f16.f16', 16),
    ('B200 bf16 tcgen05.kind::f16', 'hopper-bf16', 'TCGen05MMA', 'Blackwell', 'm64n8k16.f32.bf16.bf16', 16),
    ('B200 tf32 tcgen05.kind::tf32', 'hopper-tf32-mma', 'TCGen05MMA', 'Blackwell', 'm64n8k8.f32.tf32.tf32', 8),
    ('RTX PRO 6000 fp16 mma.m16n8k16', 'hopper-f16', 'MMA', 'RTX Blackwell', 'm16n8k16.f32.f16.f16.f32', 16),
    ('Ada e4m3 mma.m16n8k32', 'ada-e4m3', 'MMA', 'Ada Lovelace', 'm16n8k32.f32.e4m3.e4m3.f32', 32),
    ('Ada e5m2 mma.m16n8k32', 'ada-e5m2', 'MMA', 'Ada Lovelace', 'm16n8k32.f32.e5m2.e5m2.f32', 32),
    ('Ada e4m3 mma.m16n8k16', 'ada-e4m3', 'MMA', 'Ada Lovelace', 'm16n8k16.f32.e4m3.e4m3.f32', 16),
    ('H100 e4m3 wgmma.m64n8k32', 'hopper-e4m3', 'WGMMA', 'Hopper', 'm64n8k32.f32.e4m3.e4m3', 32),
    ('H100 e5m2 wgmma.m64n8k32', 'hopper-e5m2', 'WGMMA', 'Hopper', 'm64n8k32.f32.e5m2.e5m2', 32),
    ('B200 e4m3 tcgen05.kind::f8f6f4', 'blackwell-e4m3', 'TCGen05MMA', 'Blackwell', 'm64n8k32.f32.e4m3.e4m3', 32),
    ('B200 e5m2 tcgen05.kind::f8f6f4', 'blackwell-e5m2', 'TCGen05MMA', 'Blackwell', 'm64n8k32.f32.e5m2.e5m2', 32),
    ('RTX PRO 6000 e4m3 mma.m16n8k32', 'blackwell-e4m3', 'MMA', 'RTX Blackwell', 'm16n8k32.f32.e4m3.e4m3.f32', 32),
    ('RTX PRO 6000 e5m2 mma.m16n8k32', 'blackwell-e5m2', 'MMA', 'RTX Blackwell', 'm16n8k32.f32.e5m2.e5m2.f32', 32),
]

WIDTH = {'fp16': 16, 'bf16': 16, 'tf32': 32, 'e4m3': 8, 'e5m2': 8}
# (mantissa bits, exponent bits, bias) of the stored operand words (TF32 as a 32-bit word)
LAY = {'fp16': (10, 5, 15), 'bf16': (7, 8, 127), 'tf32': (23, 8, 127), 'e4m3': (3, 4, 7),
       'e5m2': (2, 5, 15)}


def dec(fmt, w):
    """(significand, exponent, mantissa bits) of a word; (0, 0, 0) for zero, None for Inf/NaN."""
    t, eb, bias = LAY[fmt]
    if fmt == 'tf32':
        w, t = w >> 13, 10
    s = (w >> (t + eb)) & 1
    E = (w >> t) & ((1 << eb) - 1)
    M = w & ((1 << t) - 1)
    top = (1 << eb) - 1
    if fmt == 'e4m3':
        if E == top and M == (1 << t) - 1:
            return None
    elif E == top:
        return None
    if E == 0 and M == 0:
        return (0, 0, 0)
    sig, e = (M, 1 - bias) if E == 0 else ((1 << t) + M, E - bias)
    return (-sig if s else sig, e, t)


def mk(fmt, s, E, M):
    t, eb, _ = LAY[fmt]
    if fmt == 'tf32':
        M &= ~0x1fff & ((1 << 23) - 1)
    return (s << (t + eb)) | (E << t) | M


def finite_word(fmt, rng, lo=None, hi=None, sub=0.05, zero=0.05):
    """A random finite operand word: zero, subnormal, or normal with exponent field in [lo, hi]."""
    t, eb, bias = LAY[fmt]
    top = (1 << eb) - 1
    s = rng.getrandbits(1)
    r = rng.random()
    if r < zero:
        return mk(fmt, s, 0, 0)
    if r < zero + sub:
        return mk(fmt, s, 0, rng.randrange(1, 1 << t) | (1 << 13 if fmt == 'tf32' else 0))
    lo = 1 if lo is None else max(1, lo)
    hi = top - 1 if hi is None else min(top - 1, hi)
    while True:
        w = mk(fmt, s, rng.randint(lo, hi), rng.getrandbits(t))
        if dec(fmt, w) is not None:
            return w


def f32_word(s, e, m):
    """FP32 word with unbiased exponent e (normal range clamped) and 23-bit mantissa m."""
    if e < -126:
        # subnormal: value m' 2^-149 with m' = (2^23 + m) >> (-126 - e)
        sh = -126 - e
        if sh > 24:
            return s << 31
        return (s << 31) | (((1 << 23) | m) >> sh)
    if e > 127:
        e = 127
    return (s << 31) | ((e + 127) << 23) | m


def max_prod_exp(fmt, a, b):
    best = None
    for x, y in zip(a, b):
        dx, dy = dec(fmt, x), dec(fmt, y)
        if dx is None or dy is None or dx[0] == 0 or dy[0] == 0:
            continue
        e = dx[1] + dy[1]
        best = e if best is None else max(best, e)
    return best


def gen(fmt, K, rng, family, F):
    t, eb, bias = LAY[fmt]
    top = (1 << eb) - 1
    if family == 'bits':
        a = [rng.getrandbits(WIDTH[fmt]) & (~0x1fff if fmt == 'tf32' else -1) & ((1 << WIDTH[fmt]) - 1)
             for _ in range(K)]
        b = [rng.getrandbits(WIDTH[fmt]) & (~0x1fff if fmt == 'tf32' else -1) & ((1 << WIDTH[fmt]) - 1)
             for _ in range(K)]
        return a, b, rng.getrandbits(32)
    if family == 'wide':
        a = [finite_word(fmt, rng) for _ in range(K)]
        b = [finite_word(fmt, rng) for _ in range(K)]
        c = f32_word(rng.getrandbits(1), rng.randint(-149, 127), rng.getrandbits(23))
        return a, b, c
    if family == 'zeros':
        # exact cancellation and signed zeros: pairs x*y and (-x)*y, c in {+0, -0} or tiny
        a, b = [], []
        while len(a) < K:
            x = finite_word(fmt, rng, bias - 3, bias + 3, sub=0.1, zero=0.3)
            y = finite_word(fmt, rng, bias - 3, bias + 3, sub=0.1, zero=0.3)
            if len(a) + 2 <= K and rng.random() < 0.7:
                a += [x, x ^ (1 << (WIDTH[fmt] - 1))]
                b += [y, y]
            else:
                a.append(x & ~((1 << (WIDTH[fmt] - 1)) - 1) if rng.random() < 0.5 else x)
                b.append(y)
        idx = list(range(K))
        rng.shuffle(idx)
        a = [a[i] for i in idx]
        b = [b[i] for i in idx]
        r = rng.random()
        c = (1 << 31) if r < 0.4 else 0 if r < 0.8 else f32_word(rng.getrandbits(1), -140, rng.getrandbits(23))
        return a, b, c
    if family == 'ovf':
        # c near the top of FP32 and large products of the same sign
        t_, eb_, bias_ = LAY[fmt]
        a = [finite_word(fmt, rng, (1 << eb_) - 4, (1 << eb_) - 2, sub=0, zero=0.2) for _ in range(K)]
        b = [finite_word(fmt, rng, (1 << eb_) - 4, (1 << eb_) - 2, sub=0, zero=0.2) for _ in range(K)]
        sgn = rng.getrandbits(1)
        a = [(x & ((1 << (WIDTH[fmt] - 1)) - 1)) | (sgn << (WIDTH[fmt] - 1)) for x in a]
        b = [x & ((1 << (WIDTH[fmt] - 1)) - 1) for x in b]
        c = f32_word(sgn, 127 - rng.randint(0, 2), rng.getrandbits(23) | (0x7f0000 if rng.random() < 0.5 else 0))
        return a, b, c
    # moderate exponents around 1
    spread = min(4, bias - 1)
    a = [finite_word(fmt, rng, bias - spread, bias + spread) for _ in range(K)]
    b = [finite_word(fmt, rng, bias - spread, bias + spread) for _ in range(K)]
    if family == 'tiny':
        a = [finite_word(fmt, rng, 1, 3, sub=0.4) for _ in range(K)]
        b = [finite_word(fmt, rng, 1, min(top - 1, 3 + rng.randint(0, 6)), sub=0.4) for _ in range(K)]
    if family == 'sparse':
        keep = set(rng.sample(range(K), rng.randint(1, 3)))
        a = [x if i in keep else 0 for i, x in enumerate(a)]
    e = max_prod_exp(fmt, a, b)
    e = 0 if e is None else e
    s, m = rng.getrandbits(1), rng.getrandbits(23)
    if family in ('vals', 'sparse'):
        r = rng.random()
        if r < 0.1:
            c = (rng.getrandbits(1) << 31)
        else:
            c = f32_word(s, e + rng.randint(-30, 30), m)
    elif family == 'cdom':      # c the largest term, by 0 .. F+4 binades
        c = f32_word(s, e + rng.randint(0, F + 4), m)
    elif family == 'cbelow':    # c below the largest product, by 0 .. F+4 binades
        c = f32_word(s, e - rng.randint(0, F + 4), m)
    elif family == 'cancel':    # c cancels the products up to a few units
        acc = 0
        from fractions import Fraction as Q
        for x, y in zip(a, b):
            dx, dy = dec(fmt, x), dec(fmt, y)
            acc += Q(dx[0]) * Q(2) ** (dx[1] - dx[2]) * Q(dy[0]) * Q(2) ** (dy[1] - dy[2])
        if acc == 0:
            c = f32_word(s, e, m)
        else:
            # -acc rounded to FP32, then moved by a few units in the last place
            mag = abs(acc)
            ex = max(floor_log2(mag), -126)
            k = round(mag / Q(2) ** (ex - 23)) + rng.randint(-3, 3)
            k = max(0, min(k, (1 << 24) - 1))
            c = word32(Q(-k if acc > 0 else k) * Q(2) ** (ex - 23))
    elif family == 'tiny':      # tiny products; c zero, +-0 or subnormal
        r = rng.random()
        c = (rng.getrandbits(1) << 31) if r < 0.5 else f32_word(s, -126 - rng.randint(1, 23), m)
    else:
        raise ValueError(family)
    return a, b, c


FAMILIES = ['bits', 'wide', 'vals', 'sparse', 'cdom', 'cbelow', 'cancel', 'tiny', 'zeros', 'ovf']


def floor_log2(x):
    e = x.numerator.bit_length() - x.denominator.bit_length()
    return e - 1 if x < Q(2) ** e else e


def word32(v):
    """The FP32 word of v, rounded to nearest even."""
    if v == 0:
        return 0
    neg, a = v < 0, abs(v)
    e = max(floor_log2(a), -126)
    k = a / Q(2) ** (e - 23)
    f = k.numerator // k.denominator
    r = k - f
    if r > Q(1, 2) or (r == Q(1, 2) and f % 2):
        f += 1
    if f == 1 << 24:
        e, f = e + 1, 1 << 23
    if f < (1 << 23):
        return (neg << 31) | f
    return (neg << 31) | ((e + 127) << 23) | (f - (1 << 23))


def tc_features(lines, name):
    TMP.mkdir(parents=True, exist_ok=True)
    path = TMP / name
    path.write_text('\n'.join(lines) + '\n')
    out = subprocess.run([str(FEATURES), '--file', str(path)], check=True, text=True,
                         capture_output=True).stdout.splitlines()
    assert len(out) == len(lines)
    return [json.loads(line).get('bits') for line in out]


def mmasim(script, cases, name, src, python):
    TMP.mkdir(parents=True, exist_ok=True)
    inp, outp = TMP / f'{name}.jsonl', TMP / f'{name}.out'
    inp.write_text(''.join(json.dumps(c) + '\n' for c in cases))
    env = dict(os.environ, PATH=str(Path(python).parent) + ':' + os.environ.get('PATH', ''))
    subprocess.run([python, '-I', str(ROOT / 'scripts/mmasim' / script), src, str(inp), str(outp)],
                   check=True, env=env)
    out = [int(x) for x in outp.read_text().split()]
    assert len(out) == len(cases)
    return out


def has_special(fmt, a, b, c):
    return any(dec(fmt, x) is None for x in a + b) or (c >> 23) & 0xff == 0xff


def classify(fmt, a, b, c, lean, sim):
    if lean is None:
        return 'special' if has_special(fmt, a, b, c) else 'overflow'
    if lean == sim:
        return 'same'
    if lean & 0x7fffffff == 0 and sim & 0x7fffffff == 0:
        return 'zero-sign'
    return 'mismatch'


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--mmasim', default=os.environ.get('MMASIM_DIR'))
    ap.add_argument('--python', default=os.environ.get('MMASIM_PYTHON'))
    ap.add_argument('--cases', type=int, default=1000)
    ap.add_argument('--seed', type=int, default=20261014)
    args = ap.parse_args()
    if not args.mmasim or not args.python:
        raise SystemExit('Give --mmasim (a checkout of the commit in vendor/mmasim/SOURCES.json) and '
                         '--python (a Python with torch and ninja).')
    pins = json.loads((ROOT / 'vendor/mmasim/SOURCES.json').read_text())
    for name, digest in pins['sha256'].items():
        got = hashlib.sha256((Path(args.mmasim) / name).read_bytes()).hexdigest()
        assert got == digest, f'{name}: not the pinned MMA-Sim commit {pins["commit"]}'
    src = str(Path(args.mmasim) / 'src/mmasim')
    rng = random.Random(args.seed)
    report = dict(mmasim=dict(repository=pins['repository'], commit=pins['commit']),
                  seed=args.seed, cases_per_family_and_length=args.cases, instructions={})
    totals = Counter()
    for vname, model, cls, arch, shape, kinst in VARIANTS:
        fmt, nfma, F, emin, outb = LEAN[model]
        cases, lines, meta = [], [], []
        for K in sorted({kinst, 2 * kinst, max(kinst, 64)}):
            for fam in FAMILIES:
                for _ in range(args.cases):
                    a, b, c = gen(fmt, K, rng, fam, F)
                    cases.append(dict(cls=cls, arch=arch, shape=shape, kinst=kinst, a=a, b=b, c=c))
                    lines.append(f'model-dot {fmt} {nfma} {F} {emin} {outb} {c} ' +
                                 ' '.join(f'{x} {y}' for x, y in zip(a, b)))
                    meta.append((fam, a, b, c))
        tag = ''.join(ch if ch.isalnum() else '_' for ch in vname)
        sim = mmasim('run.py', cases, tag, src, args.python)
        lean = tc_features(lines, f'{tag}.txt')
        counts, with_c = Counter(), 0
        examples = []
        for (fam, a, b, c), s, l in zip(meta, sim, lean):
            k = classify(fmt, a, b, c, l, s)
            counts[k] += 1
            with_c += k == 'same' and c & 0x7fffffff != 0
            if k == 'mismatch' and len(examples) < 3:
                examples.append(dict(family=fam, a=a, b=b, c=c, lean=l, mmasim=s))
        report['instructions'][vname] = dict(
            mmasim=f'{cls}("{arch}", "{shape}")', products_per_instruction=kinst,
            lean=f'model-dot {fmt} {nfma} {F} {emin} {outb}', cases=len(meta),
            outcomes=dict(counts), same_with_nonzero_c=with_c, mismatch_examples=examples)
        totals.update(counts)
        totals['same_with_nonzero_c'] += with_c
        totals['cases'] += len(meta)
        print(f'{vname:44s} {len(meta):6d}  {dict(counts)}', flush=True)
    # FP8 mma.sync against its composite from MMA-Sim's FP16 mma.sync.
    composite = {}
    for arch in ['Hopper', 'Blackwell']:
        for fmt in ['e4m3', 'e5m2']:
            for kinst in [32, 16]:
                cases, lines, meta = [], [], []
                for K in sorted({kinst, 64}):
                    for fam in FAMILIES:
                        for _ in range(max(1, args.cases // 2)):
                            a, b, c = gen(fmt, K, rng, fam, 25)
                            cases.append(dict(arch=arch, fmt=fmt, kinst=kinst, a=a, b=b, c=c))
                            lines.append(f'mma-sync {fmt} {kinst} {c} ' +
                                         ' '.join(f'{x} {y}' for x, y in zip(a, b)))
                            meta.append((fam, a, b, c))
                tag = f'mma_sync_{arch}_{fmt}_{kinst}'
                sim = mmasim('mmasync.py', cases, tag, src, args.python)
                lean = tc_features(lines, f'{tag}.txt')
                counts = Counter(classify(fmt, a, b, c, l, s)
                                 for (fam, a, b, c), s, l in zip(meta, sim, lean))
                composite[f'{arch} {fmt} k={kinst}'] = dict(cases=len(meta), outcomes=dict(counts))
                totals.update({f'mma_sync_{k}': v for k, v in counts.items()})
                print(f'mma.sync composite {arch} {fmt} k={kinst}: {dict(counts)}', flush=True)
    report['mma_sync_composite'] = composite
    report['totals'] = dict(totals)
    (ROOT / 'data/regressions/mmasim-report.json').write_text(json.dumps(report, indent=2) + '\n')
    print(json.dumps(report['totals'], indent=2))
    assert totals['mismatch'] == 0 and totals['zero-sign'] == 0, 'disagreement with MMA-Sim'
    assert totals['mma_sync_mismatch'] == 0 and totals['mma_sync_zero-sign'] == 0


if __name__ == '__main__':
    main()
