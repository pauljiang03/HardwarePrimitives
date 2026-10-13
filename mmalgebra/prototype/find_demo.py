"""Find a small fp16 example: native H100 sequential vs split-K differ; pinned chains (V100 anchored
or pinned, A100 pinned at g+24, H100 pinned at g+25) all return the same value sum trunc_g."""
import random
import fastmodels as FM
S0 = FM.S0
rng = random.Random(11)
def w16(x): return FM.f16_word(x)
g = -15
pinH = [(0x5000, 0x5000), (0xD000, 0x5000)]          # +-2^10, alpha = 10 = g + 25
pinA = [(0x4C00, 0x5000), (0xCC00, 0x5000)]          # +-2^9,  alpha = 9  = g + 24
pinV = [(0x4C00, 0x4C00), (0xCC00, 0x4C00)]          # +-2^8,  alpha = 8  = g + 23
for trial in range(2000):
    real = [(w16(rng.uniform(-2, 2)), w16(rng.uniform(-2, 2))) for _ in range(28)]
    # native H100: 2 blocks of 14 real + 2 zero products (to keep same real products) vs split
    z = (0, 0)
    b1 = real[:14] + [z, z]; b2 = real[14:] + [z, z]
    P = FM.H100
    seq = FM.chain(P, FM.prods(P, b1 + b2), 0)
    d1 = FM.chain(P, FM.prods(P, b2), 0); d2 = FM.chain(P, FM.prods(P, b1), 0)
    split = FM.add32(d1, d2)
    rev = FM.chain(P, FM.prods(P, b2 + b1), 0)
    if len({seq, split, rev}) < 2:
        continue
    # pinned H100
    pH1 = real[:14] + pinH; pH2 = real[14:] + pinH
    hs = FM.chain(P, FM.prods(P, pH1 + pH2), 0)
    hr = FM.chain(P, FM.prods(P, pH2 + pH1), 0)
    hsp = FM.add32(FM.chain(P, FM.prods(P, pH1), 0), FM.chain(P, FM.prods(P, pH2), 0))
    # pinned A100: blocks of 6 real + 2 pins (28 real -> 5 blocks: pad with zeros)
    PA = FM.A100
    realA = real + [z, z]
    blocksA = [realA[i:i+6] + pinA for i in range(0, 30, 6)]
    a_seq = FM.chain(PA, FM.prods(PA, sum(blocksA, [])), 0)
    a_rev = FM.chain(PA, FM.prods(PA, sum(blocksA[::-1], [])), 0)
    # pinned V100: blocks of 2 real + 2 pins
    PV = FM.V100
    blocksV = [real[i:i+2] + pinV for i in range(0, 28, 2)]
    v_seq = FM.chain(PV, FM.prods(PV, sum(blocksV, [])), 0)
    ref = sum(FM.tz(v, g + S0) for (v, _, _) in FM.prods(P, real))
    vals = {hs, hr, hsp, a_seq, a_rev, v_seq}
    print('trial', trial, 'native H100 seq/split/rev:', [hex(FM.units_to_f32word(x)) for x in (seq, split, rev)])
    print('  pinned H100 seq/rev/split, A100 seq/rev, V100:', [hex(FM.units_to_f32word(x)) for x in (hs, hr, hsp, a_seq, a_rev, v_seq)],
          'ref', hex(FM.units_to_f32word(ref)), 'all equal', len(vals) == 1 and ref in vals)
    print('  real =', [(hex(a), hex(b)) for a, b in real])
    break
