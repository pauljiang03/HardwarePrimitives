"""Fast integer versions of the block FMA models in models.py.

Every value is an integer N meaning N * 2^-S0.  Validated bit for bit against models.py
(itself validated against the Lean models) by validate_fast.py.
"""
import struct, math, random

S0 = 640  # common scale; bf16 products reach 2^-266, FP32 subnormals 2^-149


class ModelError(Exception):
    pass


# ---------------------------------------------------------------- formats
class Fmt:
    def __init__(self, name, ebits, mbits):
        self.name, self.ebits, self.mbits = name, ebits, mbits
        self.bias = (1 << (ebits - 1)) - 1
        self.emin = 1 - self.bias

    def decode(self, w):
        """(neg, significand, exponent, mbits); exponent emin for subnormal and zero."""
        s = (w >> (self.ebits + self.mbits)) & 1
        E = (w >> self.mbits) & ((1 << self.ebits) - 1)
        M = w & ((1 << self.mbits) - 1)
        if E == (1 << self.ebits) - 1:
            raise ModelError('nonfinite')
        if E == 0:
            return (bool(s), M, self.emin, self.mbits)
        return (bool(s), M | (1 << self.mbits), E - self.bias, self.mbits)


FP16 = Fmt('fp16', 5, 10)
BF16 = Fmt('bf16', 8, 7)
FP32 = Fmt('fp32', 8, 23)


def to_units(neg, m, e, t):
    sh = e - t + S0
    assert sh >= 0
    v = m << sh
    return -v if neg else v


def tz(N, G):
    """truncate N toward zero to a multiple of 2^G (G >= 0)."""
    if N >= 0:
        return (N >> G) << G
    return -(((-N) >> G) << G)


def fl(N, G):
    return (N >> G) << G


MAXF32_UNITS = ((1 << 24) - 1) << (104 + S0)


def rz32(N):
    """TensorCore round32 .truncate on units: RZ, gradual underflow; returns units."""
    if N == 0:
        return 0
    a = abs(N)
    if a > MAXF32_UNITS:
        raise ModelError('accumulatorOutOfRange')
    e = max(a.bit_length() - 1 - S0, -126)
    G = e - 23 + S0
    r = (a >> G) << G
    return -r if N < 0 else r


def rne32(N):
    """RNE to binary32 on units; returns units or raises on overflow."""
    if N == 0:
        return 0
    a = abs(N)
    e = max(a.bit_length() - 1 - S0, -126)
    G = e - 23 + S0
    q, r = divmod(a, 1 << G)
    half = 1 << (G - 1)
    if r > half or (r == half and (q & 1)):
        q += 1
    v = q << G
    if v >= (1 << (128 + S0)):
        raise ModelError('overflow')
    return -v if N < 0 else v


def f32_decode_units(N):
    """(neg, sig, exp, 23) of a binary32 value given in units (exp = -126 for zero/subnormal)."""
    if N == 0:
        return (False, 0, -126, 23)
    a = abs(N)
    e = max(a.bit_length() - 1 - S0, -126)
    sig = a >> (e - 23 + S0)
    assert (sig << (e - 23 + S0)) == a, 'not a binary32 value'
    return (N < 0, sig, e, 23)


def units_to_f32word(N):
    neg, m, e, _ = f32_decode_units(N)
    s = (1 << 31) if neg else 0
    if m < (1 << 23):
        return s | m
    return s | ((e + 127) << 23) | (m - (1 << 23))


def f32word_to_units(w):
    neg, m, e, t = FP32.decode(w)
    return to_units(neg, m, e, t)


def float_to_units(x):
    """exact units of a Python float that is a binary32 value."""
    w = struct.unpack('<I', struct.pack('<f', x))[0]
    return f32word_to_units(w)


def units_to_float(N):
    return math.ldexp(N, -S0) if abs(N) < (1 << 1000) else float(N) * 2.0 ** -S0


# ---------------------------------------------------------------- operand words
def f16_word(x):
    return struct.unpack('<H', struct.pack('<e', x))[0]


def bf16_word(x):
    """round-to-nearest-even of a float to bf16 (finite inputs)."""
    w = struct.unpack('<I', struct.pack('<f', x))[0]
    lsb = (w >> 16) & 1
    w = (w + 0x7FFF + lsb) >> 16
    return w & 0xFFFF


# ---------------------------------------------------------------- products
def prod_term(fmt, a, b):
    """denormalized product: (units value, exponent sum, nonzero)."""
    na, ma, ea, ta = fmt.decode(a)
    nb, mb, eb, tb = fmt.decode(b)
    m = ma * mb
    v = to_units(na != nb, m, ea + eb, ta + tb)
    return v, ea + eb, m != 0


# ---------------------------------------------------------------- NVIDIA Tensor Cores
class TC:
    kind = 'tc'

    def __init__(self, name, fmt, K, F, floor):
        self.name, self.fmt, self.K, self.F, self.floor = name, fmt, K, F, floor


V100 = TC('V100 fp16', FP16, 4, 23, None)
A100 = TC('A100 fp16', FP16, 8, 24, -132)
H100 = TC('H100 fp16', FP16, 16, 25, -133)
A100BF = TC('A100 bf16', BF16, 8, 24, -132)
H100BF = TC('H100 bf16', BF16, 16, 25, -133)


def tc_block_terms(P, pterms, cN):
    """pterms: list of (units, exp, nonzero) products; cN: units of an FP32 c. Returns units of D."""
    neg, m, e, t = f32_decode_units(cN)
    exps = [e] if m != 0 else []
    exps += [ex for (_, ex, nz) in pterms if nz]
    if exps:
        alpha = max(exps)
        if P.floor is not None:
            alpha = max(alpha, P.floor)
    else:
        alpha = 0
    G = alpha - P.F + S0
    acc = tz(cN, G) + sum(tz(v, G) for (v, _, _) in pterms)
    return rz32(acc)


# ---------------------------------------------------------------- AMD Matrix Cores
class MC:
    kind = 'mc'

    def __init__(self, name, fmt, K, acc, subnormals=True):
        self.name, self.fmt, self.K, self.acc, self.subnormals = name, fmt, K, acc, subnormals


CDNA1 = MC('CDNA1 fp16', FP16, 4, 'cr')
CDNA2 = MC('CDNA2 fp16', FP16, 4, 'pw', subnormals=False)
CDNA3 = MC('CDNA3 fp16', FP16, 8, 'ga')
CDNA3BF = MC('CDNA3 bf16', BF16, 8, 'ga')


def fl32(ftz, N):
    w = rne32(N)
    if ftz and w != 0 and abs(w) < (1 << (S0 - 126)):
        return 0
    return w


def mc_pair_tree(ftz, xs):
    if len(xs) == 1:
        return xs[0]
    h = len(xs) // 2
    return fl32(ftz, mc_pair_tree(ftz, xs[:h]) + mc_pair_tree(ftz, xs[h:]))


def mc_block_terms(P, pterms, cN):
    """pterms as for tc (products already formed; flushing of subnormal inputs is the caller's job
    for CDNA2, see mc_prods)."""
    if P.acc == 'cr':
        S = cN + sum(v for (v, _, _) in pterms)
    elif P.acc == 'pw':
        ftz = not P.subnormals
        vs = [fl32(ftz, v) for (v, _, _) in pterms]
        S = cN + mc_pair_tree(ftz, vs)
    elif P.acc == 'ga':
        nz = [(v, ex) for (v, ex, n) in pterms if n]
        if nz:
            emax = max(ex for (_, ex) in nz)
            G = emax - 24 + S0
            psum = sum(tz(v, G) for (v, _, _) in pterms)
        else:
            emax, psum = None, 0
        neg, m, ec, t = f32_decode_units(cN)
        if m == 0:
            ec = -126
        if emax is not None and ec <= emax:
            S = psum + fl(cN, emax - 24 + S0)
        else:
            x = fl(psum, ec - 32 + S0) + cN
            if x == 0:
                S = 0
            else:
                ex = max(abs(x).bit_length() - 1 - S0, -126)
                S = fl(x, ex - 31 + S0)
    else:
        raise ValueError(P.acc)
    return fl32(not P.subnormals, S)


def mc_prods(P, words):
    out = []
    for a, b in words:
        if P.acc == 'pw':
            na, ma, ea, ta = P.fmt.decode(a)
            nb, mb, eb, tb = P.fmt.decode(b)
            if ma < (1 << ta):
                ma = 0
            if mb < (1 << tb):
                mb = 0
            m = ma * mb
            out.append((to_units(na != nb, m, ea + eb, ta + tb), ea + eb, m != 0))
        else:
            out.append(prod_term(P.fmt, a, b))
    return out


def prods(P, words):
    if P.kind == 'tc':
        return [prod_term(P.fmt, a, b) for a, b in words]
    return mc_prods(P, words)


def block_terms(P, pterms, cN):
    if P.kind == 'tc':
        return tc_block_terms(P, pterms, cN)
    if P.acc == 'pw' and cN != 0 and abs(cN) < (1 << (S0 - 126)):
        cN = 0  # CDNA2 flushes a subnormal c
    return mc_block_terms(P, pterms, cN)


def chain(P, pterms, cN):
    """sequential chain of block FMAs over pterms (length a multiple of K), starting from c."""
    assert len(pterms) % P.K == 0
    for i in range(0, len(pterms), P.K):
        cN = block_terms(P, pterms[i:i + P.K], cN)
    return cN


def add32(x, y):
    """binary32 RN addition (SIMT) on units."""
    return rne32(x + y)
