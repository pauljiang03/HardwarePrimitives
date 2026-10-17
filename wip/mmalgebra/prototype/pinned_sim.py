"""Anchored vs pinned accumulation, invariance across schedules and across architectures.

anchored: c0 = 1.5 * 2^E, every block holds K real products (block-granular function).
pinned:   every block holds K-2 real products and a dummy pair (+2^alpha, -2^alpha), so the
          alignment exponent is alpha in every block; c0 = 0.  Product-granular function
          sum_i trunc_g(p_i) with g = alpha - F (Tensor Cores) or alpha - 24 (CDNA 3).
Cross-architecture: V100 anchored at E0, A100 pinned at E0+1, H100 pinned at E0+2,
CDNA3 pinned at E0+1 all compute sum_i trunc_{E0-23}(p_i).
"""
import math, random, sys
import fastmodels as FM
from anchor_sim import gen, word_value, schedules, bf16_round_units

S0 = FM.S0


def pow2_word(fmt, e):
    """fp16/bf16 word of 2^e (normal range)."""
    return (e + fmt.bias) << fmt.mbits


def dummy_pair(fmt, alpha):
    """two (a, b) word pairs with products +2^alpha and -2^alpha."""
    lo = max(fmt.emin, alpha - (fmt.bias))   # keep both factors normal
    ea = min(fmt.bias, max(fmt.emin, alpha // 2))
    eb = alpha - ea
    assert fmt.emin <= eb <= fmt.bias, (alpha, ea, eb)
    a = pow2_word(fmt, ea)
    b = pow2_word(fmt, eb)
    sign = 1 << (fmt.ebits + fmt.mbits)
    return [(a, b), (a | sign, b)]


def norms_exponent(fmt, wa, wb):
    na = math.sqrt(sum(word_value(fmt, w) ** 2 for w in wa))
    nb = math.sqrt(sum(word_value(fmt, w) ** 2 for w in wb))
    beta = na * nb * (1 + 1e-9)
    emax = max(fmt.decode(w)[2] for w in wa) + max(fmt.decode(w)[2] for w in wb)
    return beta, emax


def run_pinned(P, words, alpha, sched_groups, G):
    """words: real (a,b) pairs; G real products per block; sched_groups: block ranges."""
    nblk = len(words) // G
    dp = dummy_pair(P.fmt, alpha)
    blocks = [FM.prods(P, words[i * G:(i + 1) * G] + dp) for i in range(nblk)]
    partials = []
    for (l, r) in sched_groups:
        c = 0
        for b in range(l, r):
            c = FM.block_terms(P, blocks[b], c)
        partials.append(c)
    acc = partials[0]
    for t in partials[1:]:
        acc = FM.add32(acc, t)
    return acc


def run_anchored(P, words, E, sched_groups):
    K = P.K
    pt = FM.prods(P, words)
    A = 3 << (E - 1 + S0)
    partials = [FM.chain(P, pt[l * K:r * K], A) for (l, r) in sched_groups]
    ts = [FM.add32(d, -A) for d in partials]
    acc = ts[0]
    for t in ts[1:]:
        acc = FM.add32(acc, t)
    return acc


def trunc_sum(P, words, g):
    """reference: sum_i trunc_{2^g}(p_i), exact."""
    G = g + S0
    return sum(FM.tz(v, G) for (v, _, _) in FM.prods(P, words))


def main():
    rng = random.Random(int(sys.argv[1]) if len(sys.argv) > 1 else 3)
    k = int(sys.argv[2]) if len(sys.argv) > 2 else 1680   # divisible by 4, 6, 14 and 8*... (lcm 84)
    trials = int(sys.argv[3]) if len(sys.argv) > 3 else 10
    dists = sys.argv[4].split(',') if len(sys.argv) > 4 else ['normal', 'llm', 'uniform+', 'lognormal']
    for fmtname in ('fp16', 'bf16'):
        fmt = FM.FP16 if fmtname == 'fp16' else FM.BF16
        if fmt is FM.FP16:
            V, A, H, C3 = FM.V100, FM.A100, FM.H100, FM.CDNA3
        else:
            V, A, H, C3 = None, FM.A100BF, FM.H100BF, FM.CDNA3BF
        for dist in dists:
            stats = dict(inv_V=0, inv_A=0, inv_H=0, inv_C3=0, cross=0, eq_ref=0, n=0)
            errs = {'native': [], 'pinned': [], 'anchV': []}
            bf16w = {'native': 0, 'pinned': 0}
            for t in range(trials):
                wa, wb = gen(dist, k, fmt, rng)
                words = list(zip(wa, wb))
                beta, emax = norms_exponent(fmt, wa, wb)
                E0 = max(math.frexp(beta)[1] + 2, emax + 2)   # 2^(E0-3) <= beta: |partials| < 2^(E0-1)
                S = sum(v for (v, _, _) in FM.prods(H, words))
                ref = trunc_sum(H, words, E0 - 23)
                results = {}
                # V100 anchored (fp16 only)
                if V is not None:
                    nb = k // V.K
                    outs = set(run_anchored(V, words, E0, s) for _, s in schedules(nb, rng, 4))
                    stats['inv_V'] += (len(outs) == 1)
                    results['V100'] = outs.pop()
                for P, shift, Gp in ((A, 1, A.K - 2), (H, 2, H.K - 2), (C3, 1, C3.K - 2)):
                    nb = k // Gp
                    outs = set(run_pinned(P, words, E0 + shift, s, Gp) for _, s in schedules(nb, rng, 4))
                    key = {A: 'inv_A', H: 'inv_H', C3: 'inv_C3'}[P]
                    stats[key] += (len(outs) == 1)
                    results[P.name] = outs.pop()
                vals = set(results.values())
                stats['cross'] += (len(vals) == 1)
                stats['eq_ref'] += all(v == ref for v in vals)
                stats['n'] += 1
                # accuracy: native H100 sequential vs pinned
                nat = FM.chain(H, FM.prods(H, words), 0)
                Sf = FM.units_to_float(S)
                absS = abs(Sf) if S else 1e-300
                errs['native'].append(abs(FM.units_to_float(nat) - Sf) / absS)
                errs['pinned'].append(abs(FM.units_to_float(results[H.name]) - Sf) / absS)
                r16 = bf16_round_units(S)
                bf16w['native'] += bf16_round_units(nat) != r16
                bf16w['pinned'] += bf16_round_units(results[H.name]) != r16
            med = lambda xs: sorted(xs)[len(xs) // 2]
            print(f"{fmtname} {dist:9s} k={k}: invariant V100 {stats['inv_V']}/{stats['n']} A100 {stats['inv_A']}"
                  f" H100 {stats['inv_H']} CDNA3 {stats['inv_C3']} | identical across archs {stats['cross']}"
                  f" | = sum trunc_(E0-23) {stats['eq_ref']}"
                  f" | log2 med relerr native(H100) {math.log2(med(errs['native'])):.1f}"
                  f" pinned {math.log2(med(errs['pinned'])):.1f}"
                  f" | bf16 wrong native {bf16w['native']} pinned {bf16w['pinned']}", flush=True)


if __name__ == '__main__':
    main()
