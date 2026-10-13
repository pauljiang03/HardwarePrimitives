"""Anchored accumulation: start every chain at A = 1.5 * 2^E instead of 0.

For each vector pair and each model, run many GEMM-style reduction schedules over the K
dimension (sequential, split-K into s parts, random stream-K partitions, random combine order)
* natively (each split from c = 0, partials combined with binary32 RN additions), and
* anchored (each split from c = A, partials combined as sum of (D_s - A) with binary32 RN adds).
Report the number of distinct results over schedules, and the error against the exact sum.
"""
import math, os, random, sys, json
import fastmodels as FM

S0 = FM.S0


def bf16_round_units(N):
    """RNE to bf16 (8-bit significand) of a value in units, normal range."""
    if N == 0:
        return 0
    a = abs(N)
    e = a.bit_length() - 1 - S0
    G = e - 7 + S0
    q, r = divmod(a, 1 << G)
    half = 1 << (G - 1)
    if r > half or (r == half and (q & 1)):
        q += 1
    v = q << G
    return -v if N < 0 else v


def gen(dist, k, fmt, rng):
    if dist == 'normal':
        a = [rng.gauss(0, 1) for _ in range(k)]
        b = [rng.gauss(0, 1) for _ in range(k)]
    elif dist == 'uniform+':
        a = [rng.random() for _ in range(k)]
        b = [rng.random() for _ in range(k)]
    elif dist == 'llm':
        # activations with ~1% outlier channels, weights ~ N(0, 0.02)
        a = [rng.gauss(0, 1) * (40.0 if rng.random() < 0.01 else 1.0) for _ in range(k)]
        b = [rng.gauss(0, 0.02) for _ in range(k)]
    elif dist == 'lognormal':
        a = [math.copysign(math.exp(rng.gauss(0, 2)), rng.random() - 0.5) for _ in range(k)]
        b = [math.copysign(math.exp(rng.gauss(0, 2)), rng.random() - 0.5) for _ in range(k)]
    elif dist == 'aligned':
        # strongly correlated rows: |S| close to the Cauchy-Schwarz bound
        a = [rng.gauss(0, 1) for _ in range(k)]
        b = [x + 0.3 * rng.gauss(0, 1) for x in a]
    else:
        raise ValueError(dist)
    if fmt is FM.FP16:
        wa = [FM.f16_word(max(-60000.0, min(60000.0, x))) for x in a]
        wb = [FM.f16_word(max(-60000.0, min(60000.0, x))) for x in b]
    else:
        wa = [FM.bf16_word(x) for x in a]
        wb = [FM.bf16_word(x) for x in b]
    return wa, wb


def word_value(fmt, w):
    neg, m, e, t = fmt.decode(w)
    v = math.ldexp(m, e - t)
    return -v if neg else v


def cs_exponent(fmt, wa, wb):
    """E with 2^(E-2) > ||a|| ||b|| (a sound Cauchy-Schwarz bound computed in float64 with margin)
    and E > every product exponent sum + 1."""
    na = math.sqrt(sum(word_value(fmt, w) ** 2 for w in wa))
    nb = math.sqrt(sum(word_value(fmt, w) ** 2 for w in wb))
    beta = na * nb * (1 + 1e-9)
    E1 = math.frexp(beta)[1] + 2 if beta > 0 else -100   # 2^(E1-3) <= beta < 2^(E1-2)
    emax_a = max(fmt.decode(w)[2] for w in wa)
    emax_b = max(fmt.decode(w)[2] for w in wb)
    return max(E1, emax_a + emax_b + 2), beta


def schedules(nb, rng, n_random=6):
    """lists of (block ranges in combine order)."""
    out = [('seq', [(0, nb)])]
    for s in (2, 3, 4, 8):
        if s <= nb:
            cuts = [round(i * nb / s) for i in range(s + 1)]
            out.append((f'splitK{s}', [(cuts[i], cuts[i + 1]) for i in range(s)]))
    for r in range(n_random):
        s = rng.randint(2, min(12, nb))
        cuts = sorted(rng.sample(range(1, nb), s - 1))
        cuts = [0] + cuts + [nb]
        parts = [(cuts[i], cuts[i + 1]) for i in range(s)]
        rng.shuffle(parts)
        out.append((f'streamK{r}', parts))
    return out


def run_schedule(P, pt, sched, c0, anchored):
    K = P.K
    partials = [FM.chain(P, pt[l * K:r * K], c0) for (l, r) in sched]
    if anchored:
        ts = [FM.add32(d, -c0) for d in partials]
    else:
        ts = partials
    acc = ts[0]
    for t in ts[1:]:
        acc = FM.add32(acc, t)
    return acc


def experiment(P, dist, k, trials, rng):
    res = dict(model=P.name, dist=dist, k=k, trials=trials, native_distinct=[], anch_distinct=[],
               native_relerr=[], anch_relerr=[], anchc_relerr=[], native_bf16_wrong=0,
               anch_bf16_wrong=0, anchc_bf16_wrong=0, native_err_beta=[], anch_err_beta=[],
               anchc_err_beta=[], S_over_beta=[])
    nbk = k // P.K
    for t in range(trials):
        wa, wb = gen(dist, k, P.fmt, rng)
        pt = FM.prods(P, list(zip(wa, wb)))
        S = sum(v for (v, _, _) in pt)
        E, beta = cs_exponent(P.fmt, wa, wb)
        A = 3 << (E - 1 + S0)          # 1.5 * 2^E in units
        sch = schedules(nbk, rng)
        nat = [run_schedule(P, pt, s, 0, False) for _, s in sch]
        anc = [run_schedule(P, pt, s, A, True) for _, s in sch]
        res['native_distinct'].append(len(set(nat)))
        res['anch_distinct'].append(len(set(anc)))
        Sf = FM.units_to_float(S)
        absS = abs(Sf) if S != 0 else 1e-300
        # bias correction for the floor of each block increment (Tensor Cores only)
        ulp = 2.0 ** (E - 23)
        corr = nbk * ulp / 2 if P.kind == 'tc' else 0.0
        nat0 = FM.units_to_float(nat[0])
        anc0 = FM.units_to_float(anc[0])
        ancc = anc0 + corr
        res['native_relerr'].append(abs(nat0 - Sf) / absS)
        res['anch_relerr'].append(abs(anc0 - Sf) / absS)
        res['anchc_relerr'].append(abs(ancc - Sf) / absS)
        res['native_err_beta'].append(abs(nat0 - Sf) / beta)
        res['anch_err_beta'].append(abs(anc0 - Sf) / beta)
        res['anchc_err_beta'].append(abs(ancc - Sf) / beta)
        res['S_over_beta'].append(absS / beta)
        ref16 = bf16_round_units(S)
        if bf16_round_units(nat[0]) != ref16:
            res['native_bf16_wrong'] += 1
        if bf16_round_units(anc[0]) != ref16:
            res['anch_bf16_wrong'] += 1
        ancc_units = round(ancc * 2.0 ** 0 * (1 << 0) * 0) if False else None
        # corrected value rounded to bf16 via float64 (exact enough for the bf16 decision)
        if P.kind == 'tc':
            cu = anc[0] + (nbk << (E - 24 + S0))
        else:
            cu = anc[0]
        if bf16_round_units(cu) != ref16:
            res['anchc_bf16_wrong'] += 1
    return res


def med(xs):
    xs = sorted(xs)
    return xs[len(xs) // 2]


def summarize(r):
    lg = lambda x: math.log2(x) if x > 0 else -999
    return (f"{r['model']:11s} {r['dist']:9s} k={r['k']:5d}  distinct(native) max {max(r['native_distinct']):2d}"
            f" mean {sum(r['native_distinct'])/len(r['native_distinct']):5.2f}"
            f" | distinct(anch) max {max(r['anch_distinct'])}"
            f" | log2 relerr med: nat {lg(med(r['native_relerr'])):6.1f} anc {lg(med(r['anch_relerr'])):6.1f}"
            f" ancC {lg(med(r['anchc_relerr'])):6.1f}"
            f" | bf16 wrong: nat {r['native_bf16_wrong']} anc {r['anch_bf16_wrong']} ancC {r['anchc_bf16_wrong']}"
            f" /{r['trials']} | med |S|/beta 2^{lg(med(r['S_over_beta'])):.1f}")


if __name__ == '__main__':
    rng = random.Random(int(sys.argv[1]) if len(sys.argv) > 1 else 1)
    models = [FM.V100, FM.A100, FM.H100, FM.A100BF, FM.H100BF, FM.CDNA1, FM.CDNA2, FM.CDNA3, FM.CDNA3BF]
    ks = [int(x) for x in (sys.argv[2].split(',') if len(sys.argv) > 2 else ['1024'])]
    trials = int(sys.argv[3]) if len(sys.argv) > 3 else 20
    dists = sys.argv[4].split(',') if len(sys.argv) > 4 else ['normal', 'uniform+', 'llm', 'lognormal', 'aligned']
    allres = []
    for k in ks:
        for P in models:
            for d in dists:
                r = experiment(P, d, k, trials, rng)
                allres.append(r)
                print(summarize(r), flush=True)
    out = os.path.join(os.path.dirname(os.path.abspath(__file__)), 'results',
                       f'anchor_sim_{"_".join(map(str, ks))}.json')
    with open(out, 'w') as f:
        json.dump(allres, f)
