#!/usr/bin/env python3
"""Differential test of the Lean CDNA 3 FP8 model against MMA-Sim's CDNA 3 FP8 arithmetic.

Usage: python3 scripts/mmasim_fp8.py [--cases N] [--seed S]   (N cases per profile)

`gtr_fdpa` transcribes MMA-Sim's `gtr_fdpa` (https://github.com/microsoft/MMA-Sim, commit
`aab7f2a`) in exact rational arithmetic and is covered by MMA-Sim's licence:

    Copyright (c) Microsoft Corporation.

    MIT License

    Permission is hereby granted, free of charge, to any person obtaining a copy
    of this software and associated documentation files (the "Software"), to deal
    in the Software without restriction, including without limitation the rights
    to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
    copies of the Software, and to permit persons to whom the Software is
    furnished to do so, subject to the following conditions:

    The above copyright notice and this permission notice shall be included in all
    copies or substantial portions of the Software.

    THE SOFTWARE IS PROVIDED *AS IS*, WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
    IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
    FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
    AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
    LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
    OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
    SOFTWARE.
"""
import argparse
import json
import math
import pathlib
import random
import subprocess
import sys
from fractions import Fraction as Q

import fp8_cases as C

ROOT = pathlib.Path(__file__).resolve().parent.parent
WORK = ROOT / '.lake' / 'mmasim-fp8'
MC_EVAL = ROOT / '.lake' / 'build' / 'bin' / 'mc_eval'
MMASIM = {'repository': 'https://github.com/microsoft/MMA-Sim', 'commit': 'aab7f2a',
          'licence': 'MIT', 'function': 'src/mmasim/mmasim/arithmetic/fdpa.py: gtr_fdpa',
          'selection': 'src/mmasim/mmasim/amd/sim.py: MMA_GTR_FDPA(F=24, F2=31, '
                       'rho="RNE-FP32", L_max=16) for float8_e4m3fnuz and float8_e5m2fnuz'}


def p2(e):
    return Q(2) ** e


def f32_value(w):
    E, M = (w >> 23) & 0xff, w & 0x7fffff
    if E == 255:
        return None
    v = Q(M) * p2(-149) if E == 0 else Q(0x800000 + M) * p2(E - 150)
    return -v if w >> 31 else v


def rne32(x):
    """Round to the nearest even FP32 word (MMA-Sim's RNE-FP32); 'I+' or 'I-' past the largest."""
    if x == 0:
        return 0
    a = abs(x)
    e = max(C.floor_log2(a), -126)
    t = a / p2(e - 23)
    m = math.floor(t)
    r = t - m
    if r > Q(1, 2) or (r == Q(1, 2) and m % 2 == 1):
        m += 1
    if m == 1 << 24:
        m, e = 1 << 23, e + 1
    if e > 127:
        return 'I-' if x < 0 else 'I+'
    word = m if m < 1 << 23 else ((e + 127) << 23) | (m - (1 << 23))
    return word | (1 << 31 if x < 0 else 0)


# ---------------------------------------------------------------- MMA-Sim's gtr_fdpa
def frexp_and_normalize(x, e_subnormal):
    """1 <= |s| < 2; below e_subnormal, e = e_subnormal and |s| < 1; zero: (0, e_subnormal)."""
    if x == 0:
        return Q(0), e_subnormal
    e = C.floor_log2(abs(x))
    s = x / p2(e)
    if e < e_subnormal:
        s, e = s * p2(e - e_subnormal), e_subnormal
    return s, e


def truncated_fused_sum(ss, es, F):
    e_max = max(es)
    return sum((Q(math.trunc(s * p2(e - e_max + F))) * p2(-F) for s, e in zip(ss, es)), Q(0)), e_max


def gtr_fdpa(av, bv, c, esa, esb, F=24, F2=31):
    sa = [frexp_and_normalize(a, esa) for a in av]
    sb = [frexp_and_normalize(b, esb) for b in bv]
    s = [x[0] * y[0] for x, y in zip(sa, sb)]
    e = [-999 if si == 0 else x[1] + y[1] for si, x, y in zip(s, sa, sb)]
    s_even, e_even = truncated_fused_sum(s[0::2], e[0::2], F)
    s_odd, e_odd = truncated_fused_sum(s[1::2], e[1::2], F)
    e_dot = max(e_even, e_odd)
    s_dot = Q(math.floor(s_even * p2(e_even - e_dot + F))) * p2(-F)
    s_dot += Q(math.floor(s_odd * p2(e_odd - e_dot + F))) * p2(-F)
    s_c, e_c = frexp_and_normalize(c, -126)
    e_max = max(e_dot, e_c)
    s_dot = Q(math.floor(s_dot * p2(e_dot - e_max + (F2 + 1)))) * p2(-(F2 + 1))
    s_c = Q(math.floor(s_c * p2(e_c - e_max + F))) * p2(-F)
    if e_c < e_max - F - 1:
        s_c = Q(0)
    s2, e2 = frexp_and_normalize((s_dot + s_c) * p2(e_max), -126)
    s2 = Q(math.floor(s2 * p2(F2))) * p2(-F2)
    return rne32(s2 * p2(e2))


def mmasim_dot(profile, a, b, c):
    """MMA-Sim's dpa: blocks of L_max = 16 products, each output the next block's c."""
    fa, fb = C.PROFILES[profile]
    esa, esb = 1 - fa[2], 1 - fb[2]
    out = c
    for i in range(0, len(a), 16):
        cv = f32_value(out)
        av = [C.fnuz_value(fa, w) for w in a[i:i + 16]]
        bv = [C.fnuz_value(fb, w) for w in b[i:i + 16]]
        av += [Q(0)] * (16 - len(av))
        bv += [Q(0)] * (16 - len(bv))
        out = gtr_fdpa(av, bv, cv, esa, esb)
        if isinstance(out, str):
            return out
    return out


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--cases', type=int, default=30000, help='cases per profile')
    ap.add_argument('--seed', type=int, default=1)
    args = ap.parse_args()
    subprocess.run(['lake', 'build', 'mc_eval'], cwd=ROOT, check=True, capture_output=True)
    rng = random.Random(args.seed)
    cases = []
    for profile in C.PROFILES:
        cases += C.generate(rng, profile, args.cases)
    lean = subprocess.run([str(MC_EVAL)], input=C.mc_eval_input(cases), capture_output=True,
                          text=True, check=True).stdout.split('\n')
    counts, examples, zeros = {}, [], 0
    for i, (profile, regime, a, b, c) in enumerate(cases):
        got = lean[i].strip()
        want = mmasim_dot(profile, a, b, c)
        want = want if isinstance(want, str) else f'F {want:08x}'
        ok = got == want
        if not ok and got.startswith('F ') and want.startswith('F '):
            # The exact transcription has no -0: a zero is compared by value.
            if f32_value(int(got[2:], 16)) == 0 == f32_value(int(want[2:], 16)):
                ok, zeros = True, zeros + 1
        key = f'{profile} regime {regime}'
        n, bad = counts.get(key, (0, 0))
        counts[key] = (n + 1, bad + (not ok))
        if not ok and len(examples) < 5:
            examples.append(dict(profile=profile, regime=regime, a=[f'{w:x}' for w in a],
                                 b=[f'{w:x}' for w in b], c=f'{c:x}', lean=got, mmasim=want))
    total = sum(n for n, _ in counts.values())
    bad = sum(m for _, m in counts.values())
    for key in sorted(counts):
        print(f'{key:28s} {counts[key][1]} / {counts[key][0]} mismatches')
    print(f'total {total} inner products, {bad} mismatches ({zeros} zero results compared by value)')
    WORK.mkdir(parents=True, exist_ok=True)
    (WORK / 'report.json').write_text(json.dumps(dict(
        mmasim=MMASIM, seed=args.seed, cases_per_profile=args.cases, total=total, mismatches=bad,
        zeros_by_value=zeros, counts=counts, examples=examples), indent=1))
    print(f'report: {WORK / "report.json"}')
    sys.exit(1 if bad else 0)


if __name__ == '__main__':
    main()
