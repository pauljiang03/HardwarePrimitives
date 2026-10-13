"""Model-predicted pitfall: an fp16 subnormal operand has exponent -14 and significand < 1, so a
product with a subnormal factor can have a small value but a large exponent sum; it then sets the
alignment exponent of the whole block and coarsens the grid of every other product.
Search for blocks maximizing |D - S| / (gamma_n * sum|p|), n = K + 1, u = 2^-24, c = 0."""
from fractions import Fraction as Q
import random
import fastmodels as FM
S0 = FM.S0
def val(N): return Q(N, 1 << S0)
rng = random.Random(1)
for P in (FM.V100, FM.A100, FM.H100):
    K = P.K; n = K + 1; u = Q(1, 1 << 24); gamma = n * u / (1 - n * u)
    best = (0, None)
    bestn = 0
    for t in range(4000):
        eb = rng.randint(5, 15)
        sub = (0x0001, (eb + 15) << 10)                     # 2^-24 * 2^eb: value 2^(eb-24), exponent eb-14
        Eo = eb - 14 - rng.randint(1, 9)                     # others' exponent below the subnormal's
        others = []
        for _ in range(K - 1):
            x = FM.f16_word(rng.uniform(1, 2) * 2.0 ** (Eo // 2))
            y = FM.f16_word(rng.uniform(1, 2) * 2.0 ** (Eo - Eo // 2))
            others.append((x, y))
        for words, tag in (([sub] + others, 'sub'), ([(0, 0)] + others, 'nosub')):
            pt = FM.prods(P, words)
            S = sum(val(v) for v, _, _ in pt)
            D = val(FM.block_terms(P, pt, 0))
            A = sum(abs(val(v)) for v, _, _ in pt)
            r = abs(D - S) / (gamma * A)
            if tag == 'sub' and r > best[0]:
                best = (r, (eb, Eo))
            if tag == 'nosub':
                bestn = max(bestn, r)
    print(f'{P.name:10s} worst err/(gamma_{n} sum|p|): with a subnormal factor {float(best[0]):7.2f} (eb, Eo) = {best[1]};'
          f' same blocks without it {float(bestn):.2f}')
