"""Portable (hardware-independent, bitwise reproducible) GEMM options vs native, relative error of
one dot product against the exact product of the bf16 inputs:
  native   H100 bf16 chain (not portable)
  pinned   sum_i trunc_g(a_i b_i), g = ceil(log2 ||a|| ||b||) + 1 - 24 (portable: V100/A100/H100/CDNA3)
  pinned+c the same plus the deterministic bias correction g/2 * (#pos - #neg)
  int8     per-vector symmetric INT8 quantization of a and b, exact integer dot product, rescaled
           (portable: exact integer arithmetic)"""
import math, random, sys
import fastmodels as FM
from anchor_sim import gen, word_value
S0 = FM.S0
def run(dist, k, trials, rng):
    errs = {'native': [], 'pinned': [], 'pinned+c': [], 'int8': []}
    for t in range(trials):
        wa, wb = gen(dist, k, FM.BF16, rng)
        a = [word_value(FM.BF16, w) for w in wa]; b = [word_value(FM.BF16, w) for w in wb]
        pt = FM.prods(FM.H100BF, list(zip(wa, wb)))
        S = sum(v for v, _, _ in pt); Sf = FM.units_to_float(S); absS = abs(Sf) or 1e-300
        nat = FM.chain(FM.H100BF, pt, 0)
        beta = math.sqrt(sum(x * x for x in a)) * math.sqrt(sum(y * y for y in b)) * (1 + 1e-9)
        g = math.frexp(beta)[1] + 1 - 24
        G = g + S0
        pin = sum(FM.tz(v, G) for v, _, _ in pt)
        npos = sum(1 for v, _, _ in pt if v > 0); nneg = sum(1 for v, _, _ in pt if v < 0)
        pinc = pin + ((npos - nneg) << (G - 1))
        sa = max(abs(x) for x in a) / 127; sb = max(abs(y) for y in b) / 127
        qa = [round(x / sa) for x in a]; qb = [round(y / sb) for y in b]
        i8 = sum(x * y for x, y in zip(qa, qb)) * sa * sb
        errs['native'].append(abs(FM.units_to_float(nat) - Sf) / absS)
        errs['pinned'].append(abs(FM.units_to_float(pin) - Sf) / absS)
        errs['pinned+c'].append(abs(FM.units_to_float(pinc) - Sf) / absS)
        errs['int8'].append(abs(i8 - Sf) / absS)
    return errs
rng = random.Random(8)
med = lambda xs: sorted(xs)[len(xs) // 2]
for k in (1024, 4096, 16384):
    for dist in ('normal', 'llm', 'uniform+', 'aligned'):
        e = run(dist, k, 20 if k < 16384 else 8, rng)
        print(f'k={k:5d} {dist:9s} log2 median rel err: ' + '  '.join(f'{n} {math.log2(med(v)):6.1f}' for n, v in e.items()), flush=True)
