"""Accuracy of the zero-overhead anchored chain (c0 = 1.5*2^E, E from the Cauchy-Schwarz bound,
2^(E-1) >= 2*beta) with the deterministic floor-bias correction (1 - 2^(23-F))/2 ulp per block,
against native, on H100 / A100 / V100 fp16. Block-granular invariance is proven (AnchoredTC.lean)."""
import math, random
import fastmodels as FM
from anchor_sim import gen, word_value
S0 = FM.S0
rng = random.Random(12)
med = lambda xs: sorted(xs)[len(xs) // 2]
for P in (FM.H100, FM.A100, FM.V100):
    for k in (1024, 4096):
        for dist in ('normal', 'llm', 'uniform+'):
            en, ea, ec = [], [], []
            for t in range(16):
                wa, wb = gen(dist, k, FM.FP16, rng)
                pt = FM.prods(P, list(zip(wa, wb)))
                S = sum(v for v, _, _ in pt); Sf = FM.units_to_float(S); absS = abs(Sf) or 1e-300
                a = [word_value(FM.FP16, w) for w in wa]; b = [word_value(FM.FP16, w) for w in wb]
                beta = math.sqrt(sum(x * x for x in a)) * math.sqrt(sum(y * y for y in b)) * (1 + 1e-9)
                E = math.frexp(beta)[1] + 2
                A = 3 << (E - 1 + S0)
                d = FM.chain(P, pt, A) - A
                nb = k // P.K
                corr = nb * (1 - 2.0 ** (23 - P.F)) / 2 * 2.0 ** (E - 23)
                en.append(abs(FM.units_to_float(FM.chain(P, pt, 0)) - Sf) / absS)
                ea.append(abs(FM.units_to_float(d) - Sf) / absS)
                ec.append(abs(FM.units_to_float(d) + corr - Sf) / absS)
            print(f'{P.name:10s} k={k:5d} {dist:9s} log2 med rel err native {math.log2(med(en)):6.1f}  anchored {math.log2(med(ea)):6.1f}  anchored+corr {math.log2(med(ec)):6.1f}', flush=True)
