"""Exact ordered-encoding rounding oracle for the native EFT scalar tests."""
if not __debug__:
    raise SystemExit('Run without python -O or PYTHONOPTIMIZE: these checks rely on assert.')
from fractions import Fraction as Q
from functools import lru_cache

FORMATS = {16: (10, 5, 15), 32: (23, 8, 127), 64: (52, 11, 1023)}

def power(e):
    return Q(1 << e) if e >= 0 else Q(1, 1 << -e)


@lru_cache(maxsize=300000)
def positive_value(fmt, word):
    p, e, bias = fmt
    exponent, mantissa = divmod(word, 1 << p)
    return Q(mantissa if exponent == 0 else (1 << p) + mantissa) * power((1 if exponent == 0 else exponent) - bias - p)


def decode(width, word):
    p, e, _ = FORMATS[width]
    negative = bool(word >> (width - 1))
    mag = word & ((1 << (width - 1)) - 1)
    exp, frac = divmod(mag, 1 << p)
    if exp == (1 << e) - 1:
        if frac == 0:
            return ('inf', negative, None, False, 0)
        return ('nan', negative, None, not bool(frac & (1 << (p - 1))), frac % (1 << (p - 1)))
    value = positive_value(FORMATS[width], mag)
    return ('finite', negative, -value if negative else value, False, 0)


def select_magnitude(fmt, magnitude, mode, negative):
    p, e, bias = fmt
    infinity = ((1 << e) - 1) << p
    low, high = 0, infinity
    while low < high:
        middle = (low + high) // 2
        if positive_value(fmt, middle) < magnitude:
            low = middle + 1
        else:
            high = middle
    upper = low
    if upper < infinity and positive_value(fmt, upper) == magnitude:
        return upper
    lower = max(0, upper - 1)
    if mode == 'trunc' or mode == 'rdn' and not negative or mode == 'rup' and negative:
        return lower
    if mode != 'rne':
        return upper
    # The next unbounded normal value defines the nearest overflow midpoint.
    upper_value = power(((1 << e) - 2) - bias + 1) if upper == infinity else positive_value(fmt, upper)
    dl = magnitude - positive_value(fmt, lower)
    du = upper_value - magnitude
    return lower if dl < du or dl == du and lower % 2 == 0 else upper


def precision_value(fmt, magnitude, mode, negative):
    p, _, _ = fmt
    if not magnitude:
        return Q(0)
    exponent = magnitude.numerator.bit_length() - magnitude.denominator.bit_length()
    if magnitude < power(exponent):
        exponent -= 1
    # The local format holds the input binade and its neighbours with no subnormal or overflow loss.
    local = (p, 2, 1 - exponent)
    return positive_value(local, select_magnitude(local, magnitude, mode, negative))


def rounded(width, value, zero_sign, mode, tiny):
    if not value:
        return (int(zero_sign) << (width - 1)), 0
    fmt = FORMATS[width]
    p, e, bias = fmt
    negative = value < 0
    magnitude = abs(value)
    selected = select_magnitude(fmt, magnitude, mode, negative)
    infinity = ((1 << e) - 1) << p
    precise = precision_value(fmt, magnitude, mode, negative)
    overflow = precise > positive_value(fmt, infinity - 1)
    inexact = selected == infinity or positive_value(fmt, selected) != magnitude
    underflow = (magnitude if tiny == 'before' else precise) < power(1 - bias) and inexact
    return (int(negative) << (width - 1)) | selected, int(inexact) | (int(underflow) << 1) | (int(overflow) << 2)
