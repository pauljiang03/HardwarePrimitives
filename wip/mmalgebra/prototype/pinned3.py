"""Portable 3-GEMM variant: A = A1 + A2, B = B1 + B2 with A1 (B1) the vector rounded to a grid
2^(ceil log2 max - bits) (bits = floor((22 - log2 k)/2)); A1.B1 is exact under pinning (all
products on the pinned grid, partial sums within range), A1.B2 and A2.B are pinned with their own
Cauchy-Schwarz grids. Every term is a sum of trunc_g(products): portable. Compare with 1-GEMM
pinned and native (H100 bf16 / fp16)."""
import math, random
import fastmodels as FM
from anchor_sim import gen, word_value
S0 = FM.S0

def split(fmt, ws, bits):
    xs = [word_value(fmt, w) for w in ws]
    m = max(abs(x) for x in xs) or 1.0
    gq = math.frexp(m)[1] - bits                       # grid exponent
    hi = [math.ldexp(round(math.ldexp(x, -gq)), gq) for x in xs]
    lo = [x - h for x, h in zip(xs, hi)]
    enc = FM.f16_word if fmt is FM.FP16 else FM.bf16_word
    whi, wlo = [enc(h) for h in hi], [enc(l) for l in lo]
    # check exactness of the split in the format
    for x, a, b in zip(xs, whi, wlo):
        assert word_value(fmt, a) + word_value(fmt, b) == x, (x, word_value(fmt, a), word_value(fmt, b))
    return whi, wlo

def pinned_val(P, wa, wb):
    fmt = P.fmt
    a = [word_value(fmt, w) for w in wa]; b = [word_value(fmt, w) for w in wb]
    beta = math.sqrt(sum(x * x for x in a)) * math.sqrt(sum(y * y for y in b)) * (1 + 1e-9)
    if beta == 0:
        return 0, 0
    g = math.frexp(beta)[1] + 1 - 24
    G = g + S0
    pt = FM.prods(P, list(zip(wa, wb)))
    return sum(FM.tz(v, G) for v, _, _ in pt), sum(v for v, _, _ in pt)

rng = random.Random(4)
med = lambda xs: sorted(xs)[len(xs) // 2]
for fmt, P in ((FM.BF16, FM.H100BF), (FM.FP16, FM.H100)):
    for k in (1024, 4096, 16384):
        bits = (22 - int(math.log2(k))) // 2
        for dist in ('normal', 'llm'):
            e1, e3, en, exact1 = [], [], [], 0
            for t in range(16 if k < 16384 else 6):
                wa, wb = gen(dist, k, fmt, rng)
                pt = FM.prods(P, list(zip(wa, wb)))
                S = sum(v for v, _, _ in pt); Sf = FM.units_to_float(S); absS = abs(Sf) or 1e-300
                p1, _ = pinned_val(P, wa, wb)
                a1, a2 = split(fmt, wa, bits); b1, b2 = split(fmt, wb, bits)
                r11, s11 = pinned_val(P, a1, b1)
                r12, _ = pinned_val(P, a1, b2)
                r2b, _ = pinned_val(P, a2, wb)
                exact1 += (r11 == s11)
                p3 = r11 + r12 + r2b
                nat = FM.chain(P, pt, 0)
                e1.append(abs(FM.units_to_float(p1) - Sf) / absS)
                e3.append(abs(FM.units_to_float(p3) - Sf) / absS)
                en.append(abs(FM.units_to_float(nat) - Sf) / absS)
            print(f'{P.name:10s} k={k:5d} {dist:7s} bits={bits}: log2 med rel err native {math.log2(med(en)):6.1f}'
                  f'  pinned-1 {math.log2(med(e1)):6.1f}  pinned-3 {math.log2(med(e3)):6.1f}  (A1.B1 exact {exact1}/{len(e1)})', flush=True)
