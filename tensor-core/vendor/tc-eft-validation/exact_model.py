"""Exact dyadic reference for the finite FP32 paths in Accurate Models v4.

No GPU execution is performed. TF32 encodings here are compact 19-bit tf19
(sign, 8 exponent bits, 10 fraction bits); shift an FP32 TF32 container right 13.
The raw decoder follows MATLAB Tensor Core v0.5, bbcf00a273868172494eaacaa8d6128ab0fb8704.
"""
from fractions import Fraction as Q
import struct

FORMATS = {'fp16': (5, 10), 'bf16': (8, 7), 'tf32': (8, 10),
           'fp32': (8, 23), 'fp64': (11, 52)}
PROFILES = {
    'v100-fp16': ('fp16', 4, 0, None),
    'a100-fp16': ('fp16', 8, 1, -132),
    'a100-bf16': ('bf16', 8, 1, -132),
    'a100-tf32': ('tf32', 4, 1, -132),
    'h100-fp16': ('fp16', 16, 2, -133),
    'h100-bf16': ('bf16', 16, 2, -133),
    'h100-tf32': ('tf32', 8, 2, -133),
    'h100-tf32-k4': ('tf32', 4, 2, -133),
}

def pow2(e):
    return Q(1 << e) if e >= 0 else Q(1, 1 << -e)

def exponent(x):
    x = abs(Q(x))
    if not x:
        raise ValueError('zero has no value exponent')
    e = x.numerator.bit_length() - x.denominator.bit_length()
    return e - (x < pow2(e))

def decode(bits, fmt):
    eb, fb = FORMATS[fmt]
    assert 0 <= bits < 1 << (1 + eb + fb)
    frac = bits & ((1 << fb) - 1)
    exp = (bits >> fb) & ((1 << eb) - 1)
    if exp == (1 << eb) - 1:
        raise ValueError('finite inputs required')
    sign = -1 if bits >> (eb + fb) else 1
    bias = (1 << (eb - 1)) - 1
    scale = max(exp, 1) - bias
    sig = frac + ((1 << fb) if exp else 0)
    return sign * Q(sig, 1 << fb), scale

def value(bits, fmt):
    sig, scale = decode(bits, fmt)
    return sig * pow2(scale)

def trunc(x, q):
    x = Q(x)
    return (1 if x >= 0 else -1) * (abs(x) // q) * q

def encode(x, fmt='fp32', mode='rne'):
    """Round an exact rational directly to an encoding; includes ties/underflow."""
    x = Q(x)
    if not x:
        return 0
    sign = int(x < 0)
    x = abs(x)
    eb, fb = FORMATS[fmt]
    bias = (1 << (eb - 1)) - 1
    emin, emax = 1 - bias, bias
    e = max(exponent(x), emin)
    q = pow2(e - fb)
    z, rem = divmod(x, q)
    if mode == 'rne':
        z += int(2 * rem > q or (2 * rem == q and z % 2))
    elif mode != 'rtz':
        raise ValueError(mode)
    if z == 1 << (fb + 1):
        z >>= 1
        e += 1
    if e > emax:
        raise OverflowError('output outside the finite theorem domain')
    if z < 1 << fb:
        body = z
    else:
        body = ((e + bias) << fb) | (z - (1 << fb))
    return (sign << (eb + fb)) | body

MAX32 = value(0x7f7fffff, 'fp32')

def model(a, b, c, profile):
    fmt, k, p, floor = PROFILES[profile]
    assert len(a) == len(b) == k
    raw, terms, scales = [], [], []
    for ai, bi in zip(a, b):
        sa, ea = decode(ai, fmt)
        sb, eb = decode(bi, fmt)
        sig, rho = sa * sb, ea + eb
        raw.append((sig, rho))
        terms.append(sig * pow2(rho))
        if sig:
            scales.append(rho)
    sc, ec = decode(c, 'fp32')
    terms.append(sc * pow2(ec))
    if sc:
        scales.append(ec)
    eta = max(scales) if scales else 0
    if floor is not None:
        eta = max(eta, floor)
    qa = pow2(eta - 23 - p)
    aligned = [trunc(t, qa) for t in terms]
    acc = sum(aligned, Q(0))
    assert abs(acc) <= MAX32, 'finite truncation domain required'
    bits = encode(acc, mode='rtz')
    d = value(bits, 'fp32')
    qd = pow2(max(exponent(d), -126) - 23) if d else pow2(-149)
    qe = max(qa, qd)
    h = [trunc(t, qe) for t in terms]
    eps = [t - hi for t, hi in zip(terms, h)]
    H = sum(h, Q(0))
    eo = d - H
    residuals = [t - u for t, u in zip(terms, aligned)]
    rout = acc - d
    recovered = d - eo + sum(eps, Q(0))
    assert abs(recovered) <= MAX32, 'finite exact-result domain required for the rounding contract'
    scalar_cr = scalar_recovery(d, H, eo, eps)
    return dict(raw=raw, terms=terms, eta=eta, qa=qa, aligned=aligned,
                acc=acc, bits=bits, d=d, qd=qd, qe=qe, H=H, eps=eps,
                eo=eo, residuals=residuals, rout=rout, recovered=recovered,
                cr=encode(recovered), scalar_cr=scalar_cr)

def grid_predicate(components, fmt='fp32'):
    """Sufficient common-grid predicate in revised Theorem IV.9."""
    nonzero = [Q(x) for x in components if x]
    if not nonzero:
        return True
    if any(x.denominator & (x.denominator - 1) for x in nonzero):
        raise ValueError('components must be exact binary dyadics')
    eb, fb = FORMATS[fmt]
    bias = (1 << (eb-1)) - 1
    ell = min((abs(x.numerator) & -abs(x.numerator)).bit_length()-1
              - (x.denominator.bit_length()-1) for x in nonzero)
    q = pow2(ell)
    L = sum(abs(x / q) for x in nonzero)
    return q >= pow2(1-bias-fb) and L < 1 << (fb+1) and L*q <= value(((1<<eb)-2)<<fb | ((1<<fb)-1), fmt)

def ideal_oracle(a, b, c, fmt):
    """Independent path: input encodings -> rational products -> exact sum.

    Does not use eta, aligned values, residuals, model output, or recovery.
    """
    return sum((oracle_value(x, fmt)*oracle_value(y, fmt) for x,y in zip(a,b)), oracle_value(c,'fp32'))

def oracle_value(bits, fmt):
    """Independent value decoder via standard IEEE unpacking (all values exact in binary64)."""
    if fmt == 'fp16':
        return Q.from_float(struct.unpack('>e', bits.to_bytes(2,'big'))[0])
    if fmt == 'fp64':
        return Q.from_float(struct.unpack('>d', bits.to_bytes(8,'big'))[0])
    shift = {'fp32':0, 'bf16':16, 'tf32':13}[fmt]
    return Q.from_float(struct.unpack('>f', (bits << shift).to_bytes(4,'big'))[0])

def scalar_recovery(d, H, eo, eps):
    """Simulate the conditional FP32 branch with exact nearest-even scalar operations.

    Returns None when the sufficient predicate fails; caller uses exact fallback.
    This is software simulation, not a CUDA run.
    """
    if not grid_predicate(eps):
        return None
    try:
        if any(value(encode(x),'fp32') != x for x in [d,H,eo]):
            return None
    except OverflowError:
        return None
    total = eps[0]
    for x in eps[1:]:
        total = value(encode(total+x),'fp32')
    corrected = value(encode(d-eo),'fp32')
    return encode(corrected+total)
