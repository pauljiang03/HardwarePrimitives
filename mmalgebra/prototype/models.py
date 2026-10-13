"""Python port of the block FMA models.

Bit-exact ports of
  * TensorCore.evalBlock (NVIDIA V100/A100/H100, fp16/bf16 inputs, FP32 c and d), and
  * MatrixCore.blockBits (AMD SFMA, CDNA 1, CDNA 2, CDNA 3 global alignment),
written from the Lean definitions (TensorCore/TC/Block.lean, amd/MatrixCore/MC/Stages.lean,
Eval.lean). Exact arithmetic with Fractions. Cross-checked against the Lean models by
ValidateTC.lean and ValidateMC.lean (generated and compared by validate_port.py).

A block returns an FP32 word (int) or raises ModelError.
"""
from fractions import Fraction as Q
import math

if not __debug__:
    raise SystemExit('Run without python -O or PYTHONOPTIMIZE: these checks rely on assert.')


class ModelError(Exception):
    pass


# ---------------------------------------------------------------- formats
class Fmt:
    def __init__(self, name, ebits, mbits):
        self.name, self.ebits, self.mbits = name, ebits, mbits
        self.bias = (1 << (ebits - 1)) - 1
        self.width = 1 + ebits + mbits
        self.emin = 1 - self.bias

    def decode(self, w):
        """(negative, significand incl. hidden bit, exponent (emin for subnormal/zero), mbits)
        or None for Inf/NaN."""
        s = (w >> (self.ebits + self.mbits)) & 1
        E = (w >> self.mbits) & ((1 << self.ebits) - 1)
        M = w & ((1 << self.mbits) - 1)
        if E == (1 << self.ebits) - 1:
            return None
        if E == 0:
            return (bool(s), M, self.emin, self.mbits)
        return (bool(s), M | (1 << self.mbits), E - self.bias, self.mbits)

    def value(self, w):
        d = self.decode(w)
        neg, m, e, t = d
        v = Q(m) * Q(2) ** (e - t)
        return -v if neg else v


FP16 = Fmt('fp16', 5, 10)
BF16 = Fmt('bf16', 8, 7)
FP32 = Fmt('fp32', 8, 23)


def p2(e):
    return Q(2) ** e


def floor_log2(x):
    """floor(log2 x) for a positive Fraction."""
    n, d = x.numerator, x.denominator
    e = n.bit_length() - d.bit_length()
    if Q(n, d) < p2(e):
        e -= 1
    return e


def trunc_grid(x, g):
    """Magnitude truncation onto multiples of 2^g."""
    u = x / p2(g)
    k = math.floor(u) if x >= 0 else -math.floor(-u)
    return Q(k) * p2(g)


def rd_grid(x, g):
    return Q(math.floor(x / p2(g))) * p2(g)


def rne_int(t):
    f = math.floor(t)
    r = t - f
    if r > Q(1, 2):
        return f + 1
    if r < Q(1, 2):
        return f
    return f if f % 2 == 0 else f + 1


MAXF32 = Q(16777215) * p2(104)


def encode32(x):
    """FP32 word of an exactly representable value (x already on the binary32 grid)."""
    if x == 0:
        return 0
    s = 1 if x < 0 else 0
    a = abs(x)
    e = max(floor_log2(a), -126)
    m = a / p2(e - 23)
    assert m.denominator == 1, x
    m = int(m)
    if m < (1 << 23):
        assert e == -126
        return (s << 31) | m
    return (s << 31) | ((e + 127) << 23) | (m - (1 << 23))


def decode32(w):
    return FP32.decode(w)


def value32(w):
    return FP32.value(w)


def enc(neg, e, m):
    """encode32 of both Lean models: sign bit kept even when m = 0."""
    s = (1 << 31) if neg else 0
    if m < (1 << 23):
        return s | m
    return s | ((e + 127) << 23) | (m - (1 << 23))


def rz32(x):
    """TensorCore round32 .truncate: RZ with gradual underflow; None above maxFinite."""
    if abs(x) > MAXF32:
        return None
    if x == 0:
        return 0
    a = abs(x)
    e = max(floor_log2(a), -126)
    m = math.floor(a / p2(e - 23))
    return enc(x < 0, e, m)


def rne32(x):
    """MatrixCore rne32: RNE to binary32, None on overflow (|x| >= 2^128 - 2^103)."""
    if x == 0:
        return 0
    a = abs(x)
    e = max(floor_log2(a), -126)
    m = rne_int(a / p2(e - 23))
    if m == (1 << 24):
        m, e = 1 << 23, e + 1
    if e > 127:
        return None
    return enc(x < 0, e, m)


def is_sub32(w):
    return ((w >> 23) & 0xFF) == 0 and (w & 0x7FFFFF) != 0


def fl32(ftz, x):
    w = rne32(x)
    if w is None:
        return None
    if ftz and is_sub32(w):
        return w & 0x80000000
    return w


# ---------------------------------------------------------------- NVIDIA Tensor Cores
class TCProfile:
    def __init__(self, name, fmt, K, F, floor):
        self.name, self.fmt, self.K, self.F, self.floor = name, fmt, K, F, floor


V100 = TCProfile('V100 fp16', FP16, 4, 23, None)
A100 = TCProfile('A100 fp16', FP16, 8, 24, -132)
H100 = TCProfile('H100 fp16', FP16, 16, 25, -133)
A100BF = TCProfile('A100 bf16', BF16, 8, 24, -132)
H100BF = TCProfile('H100 bf16', BF16, 16, 25, -133)


def tc_block(P, prods, c):
    """TensorCore.evalBlock: prods = list of (a_word, b_word) of length K, c an FP32 word."""
    if len(prods) != P.K:
        raise ModelError('wrongProductCount')
    dc = decode32(c)
    if dc is None:
        raise ModelError('nonfiniteInput')
    terms = []  # (value, exp, nonzero)
    neg, m, e, t = dc
    terms.append(((-1 if neg else 1) * Q(m) * p2(e - t), e, m != 0))
    for a, b in prods:
        da, db = P.fmt.decode(a), P.fmt.decode(b)
        if da is None or db is None:
            raise ModelError('nonfiniteInput')
        sg = -1 if da[0] != db[0] else 1
        mm = da[1] * db[1]
        ee = da[2] + db[2]
        tt = da[3] + db[3]
        terms.append((sg * Q(mm) * p2(ee - tt), ee, mm != 0))
    exps = [ex for (_, ex, nz) in terms if nz]
    if exps:
        alpha = max(exps)
        if P.floor is not None:
            alpha = max(alpha, P.floor)
    else:
        alpha = 0
    g = alpha - P.F
    acc = sum((trunc_grid(v, g) for (v, _, _) in terms), Q(0))
    w = rz32(acc)
    if w is None:
        raise ModelError('accumulatorOutOfRange')
    return w


# ---------------------------------------------------------------- AMD matrix cores
class MCProfile:
    def __init__(self, name, fmt, nfma, acc, subnormals=True, product_overflow=False):
        self.name, self.fmt, self.K, self.acc = name, fmt, nfma, acc
        self.subnormals, self.product_overflow = subnormals, product_overflow


SFMA = MCProfile('SFMA fp32', FP32, 1, 'cr')
CDNA1 = MCProfile('CDNA1 fp16', FP16, 4, 'cr')
CDNA1BF = MCProfile('CDNA1 bf16', BF16, 2, 'cr')
CDNA2 = MCProfile('CDNA2 fp16', FP16, 4, 'pw', subnormals=False)
CDNA2BF = MCProfile('CDNA2 bf16', BF16, 2, 'pw', subnormals=False)
CDNA2BF1K = MCProfile('CDNA2 bf16_1k', BF16, 4, 'pw', subnormals=False)
CDNA3 = MCProfile('CDNA3 fp16', FP16, 8, 'ga', product_overflow=True)
CDNA3BF = MCProfile('CDNA3 bf16', BF16, 8, 'ga', product_overflow=True)


def unpack(fmt, w):
    d = fmt.decode(w)
    if d is None:
        raise ModelError('nonfiniteInput')
    return d  # (neg, m, e, t)


def uval(u):
    neg, m, e, t = u
    v = Q(m) * p2(e - t)
    return -v if neg else v


def flush(u):
    neg, m, e, t = u
    return (neg, 0, e, t) if m < (1 << t) else u


def umul(a, b):
    return (a[0] != b[0], a[1] * b[1], a[2] + b[2], a[3] + b[3])


def fl_value(ftz, x):
    w = fl32(ftz, x)
    return None if w is None else value32(w)


def pair_tree(ftz, xs):
    if len(xs) == 0:
        return Q(0)
    if len(xs) == 1:
        return xs[0]
    h = len(xs) // 2
    u = pair_tree(ftz, xs[:h])
    v = pair_tree(ftz, xs[h:])
    if u is None or v is None:
        return None
    return fl_value(ftz, u + v)


def norm_exp(a):
    return max(floor_log2(a), -126)


def mc_block(P, prods, c):
    if len(prods) != P.K:
        raise ModelError('wrongLength')
    A = [unpack(P.fmt, a) for a, _ in prods]
    B = [unpack(P.fmt, b) for _, b in prods]
    C = decode32(c)
    if C is None:
        raise ModelError('nonfiniteInput')
    ps = [umul(a, b) for a, b in zip(A, B)]
    if P.product_overflow and any(abs(uval(p)) >= p2(128) for p in ps):
        raise ModelError('productOverflow')
    if P.acc == 'cr':
        S = sum((uval(p) for p in ps), Q(0)) + uval(C)
    elif P.acc == 'pw':
        ftz = not P.subnormals
        if ftz:
            A2 = [flush(a) for a in A]
            B2 = [flush(b) for b in B]
            C2 = flush(C)
            ps = [umul(a, b) for a, b in zip(A2, B2)]
        else:
            C2 = C
        vs = []
        for p in ps:
            v = fl_value(ftz, uval(p))
            if v is None:
                raise ModelError('intermediateOverflow')
            vs.append(v)
        t = pair_tree(ftz, vs)
        if t is None:
            raise ModelError('intermediateOverflow')
        S = uval(C2) + t
    elif P.acc == 'ga':
        nz = [p for p in ps if p[1] != 0]
        if nz:
            emax = max(p[2] for p in nz)
            psum = sum((trunc_grid(uval(p), emax - 24) for p in ps), Q(0))
        else:
            emax, psum = None, Q(0)
        ec = -126 if C[1] == 0 else C[2]
        cv = uval(C)
        if emax is not None and ec <= emax:
            S = psum + rd_grid(cv, emax - 24)
        else:
            x = rd_grid(psum, ec - 32) + cv
            S = Q(0) if x == 0 else rd_grid(x, norm_exp(abs(x)) - 31)
    else:
        raise ValueError(P.acc)
    w = fl32(not P.subnormals, S)
    if w is None:
        raise ModelError('outputOverflow')
    return w


def block(P, prods, c):
    if isinstance(P, TCProfile):
        return tc_block(P, prods, c)
    return mc_block(P, prods, c)


ALL = [V100, A100, H100, A100BF, H100BF, CDNA1, CDNA1BF, CDNA2, CDNA2BF, CDNA2BF1K, CDNA3, CDNA3BF]
