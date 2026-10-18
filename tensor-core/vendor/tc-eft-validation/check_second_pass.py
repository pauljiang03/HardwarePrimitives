"""Additional independent, full-range and boundary checks for the second review.

Run after check_revision.py. No device measurements or solver proofs.
"""
import itertools
import json
import random
from pathlib import Path
from check_revision import check, vector, neighbor_round, integer_block_oracle
from exact_model import *


def main():
    rng = random.Random(20260906)
    counts, rejected = {}, {}
    scalar_branches = 0
    # Sample every finite exponent field, with explicit opposite-product pairs
    # in half the trials to exercise extreme ranges without excluding cancellation.
    for profile, (fmt, k, p, floor) in PROFILES.items():
        eb, fb = FORMATS[fmt]
        signbit = 1 << (eb + fb)
        def operand():
            return (rng.randrange(2) * signbit |
                    rng.randrange((1 << eb) - 1) << fb | rng.randrange(1 << fb))
        passed = skipped = 0
        while passed < 200:
            a, b = [operand() for _ in range(k)], [operand() for _ in range(k)]
            if rng.randrange(2):
                for i in range(0, k, 2):
                    a[i + 1], b[i + 1] = a[i] ^ signbit, b[i]
            c = rng.randrange(2) << 31 | rng.randrange(255) << 23 | rng.randrange(1 << 23)
            independent = integer_block_oracle(a, b, c, profile)
            ideal = ideal_oracle(a, b, c, fmt)
            if independent['bits'] is None or abs(ideal) > MAX32:
                skipped += 1
                continue
            r = check(a, b, c, profile)
            scalar_branches += r['scalar_cr'] is not None
            # Both sign-first orderings attain the extreme prefix magnitudes.
            w = 23 + p + 3 + k.bit_length()  # ceil(log2(k+1)) for these K
            for order in [sorted(r['aligned']), sorted(r['aligned'], reverse=True)]:
                prefix = Q(0)
                for u in order:
                    prefix += u / r['qa']
                    assert abs(prefix) < 1 << (w - 1)
            # Check the claimed identity for extraction grids other than max(qA,qD).
            for tau in [0, 1, 3, 9]:
                qe = r['qa'] * (1 << tau)
                h = [trunc(t, qe) for t in r['terms']]
                eps = [t - hi for t, hi in zip(r['terms'], h)]
                phi = [trunc(e, r['qa']) for e in eps]
                assert all(u == hi + v for u, hi, v in zip(r['aligned'], h, phi))
                eo = sum(phi) - r['rout']
                assert r['d'] - eo + sum(eps) == ideal
            passed += 1
        counts[profile], rejected[profile] = passed, skipped

    # Endpoints outside the small synthetic enumeration, including the upper K bound.
    endpoints = 0
    for p in range(5):
        for k in [1, 3 * (1 << p) - 1, 3 * (1 << p), 3 * (1 << p) + 1,
                  (1 << (24 + p)) - 1]:
            J = min(1 << 23, k // (1 << p) - 2)
            js = {1, (1 << 23) - 1, 1 << 23, max(1, J), min(1 << 23, max(1, J + 1))}
            for j in js:
                acc = 1 + (k - j * (1 << p)) * pow2(-24 - p)
                d = oracle_value(neighbor_round(acc, 'rtz'), 'fp32')
                assert (d > 1) == (j <= J)
                if d > 1:
                    assert d - 1 == pow2(-23) * ((k - j * (1 << p)) // (1 << (p + 1)))
                endpoints += 1

    # Exact scalar support at both precision limits, including cancellation and FTZ-sensitive sums.
    scalar_cases = 0
    for fmt, P, emin in [('fp32', 24, -149), ('fp64', 53, -1074)]:
        qmin = pow2(emin)
        cases = [([qmin, -qmin, 2 * qmin], True),
                 ([pow2(P - 1) - 1, -pow2(P - 1)], True),
                 ([pow2(P - 1), -pow2(P - 1), Q(1)], False),
                 ([qmin / 2, -qmin / 2], False),
                 ([value(((1 << FORMATS[fmt][0]) - 2) << (P - 1) | ((1 << (P - 1)) - 1), fmt)] * 2, False)]
        for terms, expected in cases:
            assert grid_predicate(terms, fmt) is expected
            if expected:
                for order in itertools.permutations(terms):
                    total = Q(0)
                    for x in order:
                        rounded = oracle_value(encode(total + x, fmt), fmt)
                        assert rounded == total + x
                        total = rounded
            scalar_cases += 1
    try:
        grid_predicate([Q(1, 3)])
    except ValueError:
        pass
    else:
        raise AssertionError('non-dyadic input was accepted')

    # Double rounding is a real counterexample even when both inputs fit FP64.
    midpoint = 1 + pow2(-24)
    exact = midpoint + pow2(-54)
    intermediate = oracle_value(encode(exact, 'fp64'), 'fp64')
    assert intermediate == midpoint
    assert neighbor_round(intermediate) == 0x3f800000
    assert neighbor_round(exact) == 0x3f800001

    # Signed zero, minimum subnormals, and the finite exact-result domain.
    special = 0
    for profile in ['a100-bf16', 'a100-tf32', 'h100-bf16', 'h100-tf32']:
        r = check(*vector(profile, [-pow2(-75)], [pow2(-75)]), profile)
        assert r['bits'] == 0x80000000 and r['cr'] == 0x80000000
        special += 1
    for sign in [-1, 1]:
        r = check(*vector('v100-fp16', [], [], sign * MAX32), 'v100-fp16')
        assert r['cr'] == (0x7f7fffff if sign > 0 else 0xff7fffff)
        special += 1
    try:
        model(*vector('v100-fp16', [1], [1], MAX32), 'v100-fp16')
    except AssertionError as exc:
        assert 'finite exact-result' in str(exc)
    else:
        raise AssertionError('out-of-domain exact sum was accepted')

    # A two-block schedule: correctly rounding each block still loses a global residual.
    d0, exact_total, ledger = 0, Q(0), Q(0)
    for av, bv in [([1, pow2(-12)], [1, pow2(-12)]),
                   ([-1, pow2(-12)], [1, pow2(-12)])]:
        a, b, c = vector('v100-fp16', av, bv, oracle_value(d0, 'fp32'))
        r = check(a, b, c, 'v100-fp16')
        exact_total += ideal_oracle(a, b, 0, 'fp16')
        ledger += r['recovered'] - r['d']
        d0 = r['bits']
    assert oracle_value(d0, 'fp32') + ledger == exact_total == pow2(-23)
    assert oracle_value(d0, 'fp32') == 0
    # The first block's exact 1+2^-24 rounds to 1 even under RNE.
    assert neighbor_round(1 + pow2(-24)) == 0x3f800000
    sequential_rne = neighbor_round(Q(1) - 1 + pow2(-24))
    assert oracle_value(sequential_rne, 'fp32') == pow2(-24) != exact_total

    report = dict(result='PASS', seed=20260906, full_range_finite_blocks=counts,
                  out_of_domain_draws=rejected, scalar_branches_checked=scalar_branches,
                  extraction_grids_per_block=4, family_endpoint_cases=endpoints,
                  scalar_support_cases=scalar_cases, double_rounding_counterexamples=1,
                  signed_zero_and_extreme_cases=special, serial_composition_examples=1,
                  non_dyadic_rejection=True, exact_sum_overflow_rejection=True,
                  independent_alignment_oracle=True, independent_neighbor_decoder=True,
                  gpu_measurements=0)
    Path(__file__).with_name('second_pass_results.json').write_text(json.dumps(report, indent=2) + '\n')
    print(json.dumps(report, indent=2))


if __name__ == '__main__':
    main()
