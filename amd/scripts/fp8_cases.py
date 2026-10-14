"""Random and targeted CDNA 3 binary8 inner products for the differential tests.

Shared by `mmasim_fp8.py` and `matlab_fp8.py`. Each case is one inner product with `k = 16` or
`k = 32` (one block, or two chained blocks) for one of the `mc_eval` profiles `cdna3E4M3`,
`cdna3E5M2` and `cdna3E4M3E5M2`, in one of six regimes, cycled case by case:

0. random bits: uniformly random words (NaN excluded), a random binary32 `c`;
1. odd slots large, even slots small: operands of magnitude `2^2`–`2^7` in the odd slots (first,
   third, ...) and `2^-9`–`2^-3` in the even slots, so the two groups have different exponents;
2. `c` near the binary8 cutoff, where `e_max − e_c` is about 22 to 28;
3. cancellation across the groups: pairs `x·y` and `−x·y` in adjacent slots, three of them
   replaced by small products;
4. sparse: two or three nonzero products in random slots;
5. `c` larger than every product (the shifted-sum path).
"""
import random
from fractions import Fraction as Q

# (exponent bits, mantissa bits, bias) of the FNUZ formats
E4M3FNUZ = (4, 3, 8)
E5M2FNUZ = (5, 2, 16)
PROFILES = {'cdna3E4M3': (E4M3FNUZ, E4M3FNUZ), 'cdna3E5M2': (E5M2FNUZ, E5M2FNUZ),
            'cdna3E4M3E5M2': (E4M3FNUZ, E5M2FNUZ)}


def fnuz_value(fmt, w):
    """The value of an FNUZ word; None for its NaN, 0x80."""
    eb, mb, bias = fmt
    s, E, M = (w >> (eb + mb)) & 1, (w >> mb) & ((1 << eb) - 1), w & ((1 << mb) - 1)
    if s and E == 0 and M == 0:
        return None
    v = Q(M) * Q(2) ** (1 - bias - mb) if E == 0 else Q((1 << mb) + M) * Q(2) ** (E - bias - mb)
    return -v if s else v


def floor_log2(x):
    e = x.numerator.bit_length() - x.denominator.bit_length()
    return e - 1 if x < Q(2) ** e else e


WORDS = {fmt: [w for w in range(256) if fnuz_value(fmt, w) is not None]
         for fmt in (E4M3FNUZ, E5M2FNUZ)}
BANDS = {}


def rand_word(rng, fmt, band=None):
    """A random word; with a band (lo, hi), one whose magnitude is zero or in [2^lo, 2^(hi+1))."""
    if band is None:
        return rng.choice(WORDS[fmt])
    if (fmt, band) not in BANDS:
        lo, hi = band
        BANDS[(fmt, band)] = [w for w in WORDS[fmt] if fnuz_value(fmt, w) == 0 or
                              lo <= floor_log2(abs(fnuz_value(fmt, w))) <= hi]
    return rng.choice(BANDS[(fmt, band)])


def rand_c(rng, emin, emax):
    """A random binary32 word with exponent in [emin, emax] (clamped to the normal range), zero
    one time in ten."""
    if rng.random() < 0.1:
        return 0
    m = rng.getrandbits(23)
    e = max(min(rng.randint(emin, emax), 127), -126)
    return (rng.getrandbits(1) << 31) | ((e + 127) << 23) | m


def generate(rng, profile, n):
    """n cases (profile, regime, a words, b words, c word), regimes cycled."""
    fa, fb = PROFILES[profile]
    out = []
    for i in range(n):
        kind = i % 6
        k = rng.choice([16, 32])
        if kind == 0:
            a = [rand_word(rng, fa) for _ in range(k)]
            b = [rand_word(rng, fb) for _ in range(k)]
            c = rand_c(rng, -40, 40)
        elif kind == 1:
            a = [rand_word(rng, fa, (2, 7) if j % 2 == 0 else (-9, -3)) for j in range(k)]
            b = [rand_word(rng, fb, (2, 7) if j % 2 == 0 else (-9, -3)) for j in range(k)]
            c = rand_c(rng, -20, 10)
        elif kind == 2:
            a = [rand_word(rng, fa, (3, 7)) for _ in range(k)]
            b = [rand_word(rng, fb, (3, 7)) for _ in range(k)]
            c = rand_c(rng, -16, -8)
        elif kind == 3:
            a, b = [], []
            for j in range(k // 2):
                x, y = rand_word(rng, fa, (0, 6)), rand_word(rng, fb, (0, 6))
                a += [x, x ^ 0x80 if fnuz_value(fa, x) != 0 else x]
                b += [y, y]
            for j in rng.sample(range(k), 3):
                a[j] = rand_word(rng, fa, (-8, -4))
            c = rand_c(rng, -30, 5)
        elif kind == 4:
            a, b = [0] * k, [0] * k
            for j in rng.sample(range(k), rng.choice([2, 3])):
                a[j] = rand_word(rng, fa)
                b[j] = rand_word(rng, fb)
            c = rand_c(rng, -30, 30)
        else:
            a = [rand_word(rng, fa, (-6, 0)) for _ in range(k)]
            b = [rand_word(rng, fb, (-6, 0)) for _ in range(k)]
            c = rand_c(rng, 0, 12)
        out.append((profile, kind, a, b, c))
    return out


def mc_eval_input(cases):
    """The lines `mc_eval` reads: profile, a words, b words, c word."""
    return ''.join(f"{p} {','.join(f'{w:x}' for w in a)} {','.join(f'{w:x}' for w in b)} {c:x}\n"
                   for p, _, a, b, c in cases)
