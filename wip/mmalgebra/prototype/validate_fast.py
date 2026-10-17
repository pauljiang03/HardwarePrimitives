"""Check fastmodels.py against models.py (the Lean-validated port) on random blocks."""
import random, struct
import models as M
import fastmodels as FM

PAIRS = [(M.V100, FM.V100), (M.A100, FM.A100), (M.H100, FM.H100), (M.A100BF, FM.A100BF),
         (M.H100BF, FM.H100BF), (M.CDNA1, FM.CDNA1), (M.CDNA2, FM.CDNA2), (M.CDNA3, FM.CDNA3),
         (M.CDNA3BF, FM.CDNA3BF)]


def rand_word(fmt, rng):
    while True:
        if fmt.ebits == 5:
            w = rng.getrandbits(16)
        else:
            w = rng.getrandbits(16)
        E = (w >> fmt.mbits) & ((1 << fmt.ebits) - 1)
        if E != (1 << fmt.ebits) - 1:
            # bias towards moderate exponents half the time
            return w


def rand_word_moderate(fmt, rng, lo, hi):
    s = rng.getrandbits(1)
    E = rng.randint(fmt.bias + lo, fmt.bias + hi)
    M_ = rng.getrandbits(fmt.mbits)
    return (s << (fmt.ebits + fmt.mbits)) | (E << fmt.mbits) | M_


def rand_c(rng):
    k = rng.random()
    if k < 0.2:
        return 0
    s = rng.getrandbits(1)
    E = rng.randint(100, 160) if k < 0.9 else rng.randint(0, 254)
    return (s << 31) | (E << 23) | rng.getrandbits(23)


def main():
    rng = random.Random(7)
    bad = 0
    n = 0
    for Pm, Pf in PAIRS:
        for trial in range(400):
            fmt = Pm.fmt if hasattr(Pm, 'fmt') else None
            K = Pm.K
            if trial % 2:
                words = [(rand_word_moderate(Pf.fmt, rng, -6, 6), rand_word_moderate(Pf.fmt, rng, -6, 6))
                         for _ in range(K)]
            else:
                words = [(rand_word(Pf.fmt, rng), rand_word(Pf.fmt, rng)) for _ in range(K)]
            c = rand_c(rng)
            try:
                ref = M.block(Pm, words, c)
            except M.ModelError:
                ref = None
            try:
                got = FM.block_terms(Pf, FM.prods(Pf, words), FM.f32word_to_units(c))
                got = FM.units_to_f32word(got)
            except FM.ModelError:
                got = None
            n += 1
            if ref is None or got is None:
                if (ref is None) != (got is None):
                    bad += 1
                    print('error mismatch', Pm.name, words, hex(c), ref, got)
                continue
            if ref != got and not (ref & 0x7FFFFFFF == 0 and got & 0x7FFFFFFF == 0):
                bad += 1
                if bad < 10:
                    print('mismatch', Pm.name, [(hex(a), hex(b)) for a, b in words], hex(c), hex(ref), hex(got))
    print('blocks', n, 'mismatches', bad)


if __name__ == '__main__':
    main()
