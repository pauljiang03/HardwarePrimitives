"""Accuracy of pinned accumulation (grid g = E0-23, product-granular sum of trunc_g(p_i)) with and
without a deterministic bias correction (+g/2 per nonzero product, signed by the product), against
native H100 / A100 chains.  Pinned uses the tighter exponent E0 = ceil(log2 beta) + 1 (pinned only,
no V100 anchor), so that |partials| <= beta < 2^E0 <= 2^(g+24) with margin for truncation drift."""
import math, random, sys
import fastmodels as FM
from anchor_sim import gen, word_value, bf16_round_units
S0 = FM.S0

def run(dist, k, trials, rng, fmt, P):
    out = dict(nat=[], pin=[], pinc=[], natw=0, pinw=0, pincw=0)
    for t in range(trials):
        wa, wb = gen(dist, k, fmt, rng)
        words = list(zip(wa, wb))
        na = math.sqrt(sum(word_value(fmt, w) ** 2 for w in wa))
        nb = math.sqrt(sum(word_value(fmt, w) ** 2 for w in wb))
        beta = na * nb * (1 + 1e-9)
        E0 = math.frexp(beta)[1] + 1            # beta < 2^(E0-1)
        g = E0 - 24                              # |partials| < 2^(E0-1) = 2^(g+23): one bit of headroom
        pt = FM.prods(P, words)
        S = sum(v for (v, _, _) in pt)
        G = g + S0
        pin = sum(FM.tz(v, G) for (v, _, _) in pt)          # what the pinned chain returns (checked in pinned_sim)
        corr = sum(((1 if v > 0 else -1) << (G - 1)) for (v, _, _) in pt if v % (1 << G))
        # deterministic correction needs only signs and "has bits below g", which the GPU cannot see;
        # the implementable version adds g/2 * (#positive - #negative products) -- use that:
        npos = sum(1 for (v, _, _) in pt if v > 0); nneg = sum(1 for (v, _, _) in pt if v < 0)
        corr_impl = (npos - nneg) << (G - 1)
        nat = FM.chain(P, pt, 0)
        Sf = FM.units_to_float(S); absS = abs(Sf) if S else 1e-300
        for key, val in (('nat', nat), ('pin', pin), ('pinc', pin + corr_impl)):
            out[key].append(abs(FM.units_to_float(val) - Sf) / absS)
        r16 = bf16_round_units(S)
        out['natw'] += bf16_round_units(nat) != r16
        out['pinw'] += bf16_round_units(pin) != r16
        out['pincw'] += bf16_round_units(pin + corr_impl) != r16
    return out

if __name__ == '__main__':
    rng = random.Random(5)
    trials = int(sys.argv[1]) if len(sys.argv) > 1 else 30
    med = lambda xs: sorted(xs)[len(xs) // 2]
    for k in (256, 1024, 4096, 16384):
        for P in (FM.H100, FM.A100):
            for dist in ('normal', 'llm', 'uniform+', 'aligned', 'lognormal'):
                r = run(dist, k, trials if k < 16384 else trials // 3, rng, FM.FP16, P)
                print(f"{P.name:10s} k={k:5d} {dist:9s} log2 med relerr: native {math.log2(med(r['nat'])):6.1f}"
                      f" pinned {math.log2(med(r['pin'])):6.1f} pinned+corr {math.log2(med(r['pinc'])):6.1f}"
                      f" | bf16 wrong native {r['natw']} pinned {r['pinw']} pinned+corr {r['pincw']} /{len(r['nat'])}", flush=True)
