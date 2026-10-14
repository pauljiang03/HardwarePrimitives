"""Python port of the FP8 -> FP32 block FMA models.

Bit-exact ports, written from the Lean definitions, with exact arithmetic (Fractions):

  * NVIDIA: TensorCore.evalBlock (TensorCore/TC/Block.lean) with the FP8 models of
    TensorCore/TC/GPUs.lean:
      Ada, L40S    (adaE4M3F32, adaE5M2F32):             K = 16, a 13-bit mantissa after
                   alignment, the block output truncated to a 13-bit mantissa
      H100, H200   (hopperE4M3F32, hopperE5M2F32):       K = 32, the same
      B200         (blackwellE4M3F32, blackwellE5M2F32): K = 32, the 23-bit mantissa plus 2
                   padding bits after alignment, binary32 block output
    with no minimum alignment exponent. E4M3 is decoded as TensorCore.e4m3Encoding (no
    infinities, finite values up to 448, NaN only S.1111.111); E5M2 has IEEE specials.
  * AMD CDNA 3: MatrixCore.blockBits (amd/MatrixCore/MC/Stages.lean, Eval.lean) for
    cdna3FP8 fa fb with E4M3 FNUZ and E5M2 FNUZ operands: N_FMA = 16, the products of odd and of
    even slots aligned separately (odd/even grouping), each product truncated to the 23-bit
    mantissa plus 1 padding bit below its group's maximum exponent, each group sum rounded
    down to the common grid, c added late with the binary8 cutoff (c is dropped once
    e_max - e_c > 25), final round-to-nearest-even.

Slots are numbered from 1 as in the Lean model: "odd slots" are the 1st, 3rd, ... (Python indices
0, 2, ...). A block returns an FP32 word (int) or raises ModelError. fp8_validate.py checks the
port against the recorded GPU outputs and against the Lean CDNA 3 model.
"""
from fractions import Fraction as Q
import math

if not __debug__:
    raise SystemExit('Run without python -O or PYTHONOPTIMIZE: these checks rely on assert.')


class ModelError(Exception):
    pass


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
    """x truncated toward zero to a multiple of 2^g."""
    u = x / p2(g)
    k = math.floor(u) if x >= 0 else -math.floor(-u)
    return Q(k) * p2(g)


def rd_grid(x, g):
    """x rounded down to a multiple of 2^g."""
    return Q(math.floor(x / p2(g))) * p2(g)


def rne_int(t):
    f = math.floor(t)
    r = t - f
    if r > Q(1, 2):
        return f + 1
    if r < Q(1, 2):
        return f
    return f if f % 2 == 0 else f + 1


# ------------------------------------------------------------------ formats
class Fmt:
    """kind: 'ieee' (all-ones exponent = Inf/NaN), 'ocp' (E4M3: only S.1111.111 is NaN, no Inf),
    'fnuz' (0x80 is NaN, no Inf, no -0)."""

    def __init__(self, name, ebits, mbits, bias, kind):
        self.name, self.ebits, self.mbits, self.bias, self.kind = name, ebits, mbits, bias, kind
        self.width = 1 + ebits + mbits
        self.emin = 1 - bias

    def decode(self, w):
        """(negative, significand, exponent, mbits), or None for Inf/NaN. Subnormals and zero
        carry the exponent emin."""
        s = (w >> (self.ebits + self.mbits)) & 1
        E = (w >> self.mbits) & ((1 << self.ebits) - 1)
        M = w & ((1 << self.mbits) - 1)
        top = (1 << self.ebits) - 1
        if self.kind == 'ieee' and E == top:
            return None
        if self.kind == 'ocp' and E == top and M == (1 << self.mbits) - 1:
            return None
        if self.kind == 'fnuz' and s == 1 and E == 0 and M == 0:
            return None
        if E == 0:
            return (bool(s), M, self.emin, self.mbits)
        return (bool(s), M | (1 << self.mbits), E - self.bias, self.mbits)

    def value(self, w):
        d = self.decode(w)
        if d is None:
            return None
        neg, m, e, t = d
        v = Q(m) * p2(e - t)
        return -v if neg else v

    def words(self):
        return [w for w in range(1 << self.width) if self.decode(w) is not None]


E4M3 = Fmt('e4m3', 4, 3, 7, 'ocp')
E5M2 = Fmt('e5m2', 5, 2, 15, 'ieee')
E4M3_FNUZ = Fmt('e4m3fnuz', 4, 3, 8, 'fnuz')
E5M2_FNUZ = Fmt('e5m2fnuz', 5, 2, 16, 'fnuz')
FP32 = Fmt('fp32', 8, 23, 127, 'ieee')


def value32(w):
    return FP32.value(w)


def enc32(neg, e, m):
    s = (1 << 31) if neg else 0
    if m < (1 << 23):
        return s | m
    return s | ((e + 127) << 23) | (m - (1 << 23))


MAXF32 = Q(16777215) * p2(104)


def rz32(x):
    """Binary32 truncation (round toward zero); None beyond the largest finite value."""
    if abs(x) > MAXF32:
        return None
    if x == 0:
        return 0
    a = abs(x)
    e = max(floor_log2(a), -126)
    m = math.floor(a / p2(e - 23))
    return enc32(x < 0, e, m)


def rne32(x):
    """Binary32 round-to-nearest-even; None on overflow."""
    if x == 0:
        return 0
    a = abs(x)
    e = max(floor_log2(a), -126)
    m = rne_int(a / p2(e - 23))
    if m == (1 << 24):
        m, e = 1 << 23, e + 1
    if e > 127:
        return None
    return enc32(x < 0, e, m)


def trunc_word(m, w):
    """The binary32 word with its mantissa truncated to its leading m bits (truncateFraction32)."""
    return (w >> (23 - m)) << (23 - m)


def encode(fmt, v):
    """The word of an exactly representable finite value (positive zero for 0)."""
    if v == 0:
        return 0
    for w in fmt.words():
        if fmt.value(w) == v:
            return w
    raise ValueError(f'{v} not representable in {fmt.name}')


# ------------------------------------------------------------------ NVIDIA FP8 Tensor Cores
class TCModel:
    def __init__(self, name, fmt, K, F, out_bits):
        self.name, self.fmt, self.K, self.F, self.out_bits = name, fmt, K, F, out_bits


ADA = TCModel('Ada e4m3', E4M3, 16, 13, 13)
HOPPER = TCModel('Hopper e4m3', E4M3, 32, 13, 13)
BLACKWELL = TCModel('Blackwell e4m3', E4M3, 32, 25, 23)
ADA52 = TCModel('Ada e5m2', E5M2, 16, 13, 13)
HOPPER52 = TCModel('Hopper e5m2', E5M2, 32, 13, 13)
BLACKWELL52 = TCModel('Blackwell e5m2', E5M2, 32, 25, 23)


def tc_decode(fmt, w):
    """TensorCore Decoded: (signed significand, exponent, mbits); zero is (0, 0, 0)."""
    d = fmt.decode(w)
    if d is None:
        raise ModelError('nonfiniteInput')
    neg, m, e, t = d
    if m == 0:
        return (0, 0, 0)
    return (-m if neg else m, e, t)


def tc_terms(P, prods, c):
    if FP32.decode(c) is None:
        raise ModelError('nonfiniteInput')
    terms = [tc_decode(FP32, c)]
    for a, b in prods:
        sa, ea, ta = tc_decode(P.fmt, a)
        sb, eb, tb = tc_decode(P.fmt, b)
        terms.append((sa * sb, ea + eb, ta + tb))
    return terms


def tc_accumulate(P, terms):
    exps = [e for (s, e, t) in terms if s != 0]
    eta = max(exps) if exps else 0
    g = eta - P.F
    acc = sum((trunc_grid(Q(s) * p2(e - t), g) for (s, e, t) in terms), Q(0))
    w = rz32(acc)
    if w is None:
        raise ModelError('accumulatorOutOfRange')
    return trunc_word(P.out_bits, w)


def tc_block(P, prods, c):
    """TensorCore.evalBlock on K operand pairs and a binary32 word c."""
    if len(prods) != P.K:
        raise ModelError('wrongProductCount')
    return tc_accumulate(P, tc_terms(P, prods, c))


def tc_sparse(P, prods, c):
    """The same block given by its nonzero products only (the others are zero pairs)."""
    return tc_accumulate(P, tc_terms(P, prods, c))


# ------------------------------------------------------------------ AMD CDNA 3 FP8
class MCModel:
    def __init__(self, name, fa, fb):
        self.name, self.fa, self.fb = name, fa, fb
        self.K = 16
        self.neab = 1
        self.cutoff = 25


CDNA3_E4M3 = MCModel('CDNA3 e4m3fnuz', E4M3_FNUZ, E4M3_FNUZ)
CDNA3_E5M2 = MCModel('CDNA3 e5m2fnuz', E5M2_FNUZ, E5M2_FNUZ)
CDNA3_E4M3E5M2 = MCModel('CDNA3 e4m3fnuz x e5m2fnuz', E4M3_FNUZ, E5M2_FNUZ)
CDNA3_E5M2E4M3 = MCModel('CDNA3 e5m2fnuz x e4m3fnuz', E5M2_FNUZ, E4M3_FNUZ)


def uval(u):
    neg, m, e, t = u
    v = Q(m) * p2(e - t)
    return -v if neg else v


def umul(a, b):
    return (a[0] != b[0], a[1] * b[1], a[2] + b[2], a[3] + b[3])


def aligned_sum(neab, ps):
    """One group: aligned to its own maximum exponent, each product truncated to 23 + neab bits."""
    nz = [p for p in ps if p[1] != 0]
    if not nz:
        return (None, Q(0))
    e = max(p[2] for p in nz)
    return (e, sum((trunc_grid(uval(p), e - (23 + neab)) for p in ps), Q(0)))


def join_exp(a, b):
    if a is None:
        return b
    if b is None:
        return a
    return max(a, b)


def norm_exp(a):
    return max(floor_log2(a), -126)


def mc_block(P, prods, c):
    """MatrixCore.blockBits for cdna3FP8 on 16 operand pairs and a binary32 word c."""
    if len(prods) != P.K:
        raise ModelError('wrongLength')
    A, B = [], []
    for a, b in prods:
        da, db = P.fa.decode(a), P.fb.decode(b)
        if da is None or db is None:
            raise ModelError('nonfiniteInput')
        A.append(da)
        B.append(db)
    C = FP32.decode(c)
    if C is None:
        raise ModelError('nonfiniteInput')
    ps = [umul(a, b) for a, b in zip(A, B)]
    if any(abs(uval(p)) >= p2(128) for p in ps):
        raise ModelError('productOverflow')
    k = 23 + P.neab
    oe, osum = aligned_sum(P.neab, ps[0::2])
    ee, esum = aligned_sum(P.neab, ps[1::2])
    e = join_exp(oe, ee)
    if e is None:
        emax, psum = None, Q(0)
    else:
        emax, psum = e, rd_grid(osum, e - k) + rd_grid(esum, e - k)
    ec = -126 if C[1] == 0 else C[2]
    cv = uval(C)
    if emax is not None and ec <= emax:
        S = psum + (Q(0) if emax - ec > P.cutoff else rd_grid(cv, emax - 24))
    else:
        x = rd_grid(psum, ec - 32) + cv
        S = Q(0) if x == 0 else rd_grid(x, norm_exp(abs(x)) - 31)
    w = rne32(S)
    if w is None:
        raise ModelError('outputOverflow')
    return w


def mc_sparse(P, odd, even, c):
    """The same block given by the products of its odd and of its even slots (zeros elsewhere)."""
    assert len(odd) <= P.K // 2 and len(even) <= P.K // 2
    slots = []
    for i in range(P.K // 2):
        slots.append(odd[i] if i < len(odd) else (0, 0))
        slots.append(even[i] if i < len(even) else (0, 0))
    return mc_block(P, slots, c)


def block(P, prods, c):
    if isinstance(P, TCModel):
        return tc_block(P, prods, c)
    return mc_block(P, prods, c)


def chain(P, c, prods):
    """Consecutive block FMAs over a product list padded with zero pairs to a multiple of K, each
    block's output the next block's c (TensorCore Model.dot; MatrixCore dotOutcome)."""
    K = P.K
    prods = list(prods) + [(0, 0)] * ((-len(prods)) % K)
    for i in range(0, len(prods), K):
        c = block(P, prods[i:i + K], c)
    return c
