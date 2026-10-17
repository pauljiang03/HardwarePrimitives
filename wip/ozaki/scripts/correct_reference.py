#!/usr/bin/env python3
"""Compute correctly rounded matrix products with exact rational arithmetic.

An oracle for the correctly rounded schemes (`OzakiTC/Correct.lean`, `OzakiMC/Correct.lean`),
independent of Lean: every entry of `C = AB` is computed exactly with `fractions.Fraction` and
rounded once to nearest, ties to even, by integer arithmetic written here.

* binary32: the Z3 models' two test cases (from `data/z3-reference.json`) and two hard vectors,
  one with heavy cancellation and one whose product lies exactly halfway between two binary32
  values;
* binary64: two seeded random `4 x 8` by `8 x 4` products of binary64 values, one with exponents
  in `[-4, 0)` and one in `[-20, 20)`, for ADP.

Usage:

    python3 scripts/correct_reference.py > data/correct-reference.json
    python3 scripts/correct_reference.py --lean    # the same data as Lean definitions
"""
import json
import random
import struct
import sys
from fractions import Fraction


def round_nearest_even(q, p, emin, emax):
    """Bits of `q` rounded to nearest, ties to even, in a binary format with `p` significand bits
    (hidden bit included), exponent range `[emin, emax]`; None on overflow."""
    if q == 0:
        return 0, 0
    sign = 1 if q < 0 else 0
    a = abs(q)
    e = a.numerator.bit_length() - a.denominator.bit_length()
    if Fraction(2) ** e > a:
        e -= 1
    e = max(e, emin)                         # subnormals share the grid of emin
    scaled = a / Fraction(2) ** (e - (p - 1))
    m = scaled.numerator // scaled.denominator
    r = scaled - m
    if r > Fraction(1, 2) or (r == Fraction(1, 2) and m % 2 == 1):
        m += 1
    if m == 2 ** p:                          # rounding carried into the next binade
        m //= 2
        e += 1
    if e > emax:
        return None
    return sign, (e, m)


def encode(sign, em, p, emin, ebits):
    if em == 0:
        return sign << (p - 1 + ebits)
    e, m = em
    if m < 2 ** (p - 1):                     # subnormal
        field = 0
    else:
        field = e - emin + 1
        m -= 2 ** (p - 1)
    return (sign << (p - 1 + ebits)) | (field << (p - 1)) | m


def rne32(q):
    r = round_nearest_even(q, 24, -126, 127)
    return None if r is None else '0x%08X' % encode(r[0], r[1], 24, -126, 8)


def rne64(q):
    r = round_nearest_even(q, 53, -1022, 1023)
    return None if r is None else '0x%016X' % encode(r[0], r[1], 53, -1022, 11)


def value32(h):
    return Fraction(struct.unpack('>f', struct.pack('>I', int(h, 16)))[0])


def value64(h):
    return Fraction(struct.unpack('>d', struct.pack('>Q', int(h, 16)))[0])


def product(A, B, value, rne):
    return [[rne(sum(value(A[i][t]) * value(B[t][j]) for t in range(len(B))))
             for j in range(len(B[0]))] for i in range(len(A))]


def random64(rng, rows, cols, lo, span):
    out = []
    for _ in range(rows):
        row = []
        for _ in range(cols):
            m = (1 << 52) | rng.getrandbits(52)
            e = lo + rng.randrange(span)
            v = Fraction(m) * Fraction(2) ** (e - 52) * (1 if rng.random() < 0.5 else -1)
            row.append('0x%016X' % struct.unpack('>Q', struct.pack('>d', float(v)))[0])
        out.append(row)
    return out


def main():
    z3 = json.load(open('data/z3-reference.json'))
    out = {'binary32': [], 'binary64': []}
    for case in z3:
        out['binary32'].append({'case': case['case'], 'A': case['A'], 'B': case['B'],
                                'C': product(case['A'], case['B'], value32, rne32)})
    # x . y = 2^-40 with max|x| = 1; and 1 + 2^-24, halfway between 1 and 1 + 2^-23.
    hard = [('cancel', ['0x3F800000', '0xBF800000', '0x2B800000', '0x00000000'],
             ['0x3F800000', '0x3F800000', '0x3F800000', '0x00000000']),
            ('halfway', ['0x3F800000', '0x33800000', '0x00000000', '0x00000000'],
             ['0x3F800000', '0x3F800000', '0x00000000', '0x00000000'])]
    for name, x, y in hard:
        out['binary32'].append({'case': name, 'A': [x], 'B': [[v] for v in y],
                                'C': product([x], [[v] for v in y], value32, rne32)})
    rng = random.Random(2026)
    for name, lo, span in [('narrow64', -4, 4), ('wide64', -20, 40)]:
        A = random64(rng, 4, 8, lo, span)
        B = random64(rng, 8, 4, lo, span)
        out['binary64'].append({'case': name, 'A': A, 'B': B,
                                'C': product(A, B, value64, rne64)})
    if '--lean' in sys.argv:
        for fmt in ('binary32', 'binary64'):
            for c in out[fmt]:
                for key in ('A', 'B', 'C'):
                    rows = ',\n    '.join('[' + ', '.join(r) + ']' for r in c[key])
                    print(f'def {key}_{c["case"]} : List (List {"F32" if fmt == "binary32" else "F64"}) :=\n  [{rows}]\n')
    else:
        json.dump(out, sys.stdout, indent=1)
        print()


if __name__ == '__main__':
    main()
