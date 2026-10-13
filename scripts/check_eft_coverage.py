#!/usr/bin/env python3
"""Check scalar-precondition cohorts using the executable Lean specification."""
if not __debug__:
    raise SystemExit('Run without python -O or PYTHONOPTIMIZE: these checks rely on assert.')
from collections import Counter
from fractions import Fraction as Q
from pathlib import Path
import hashlib
import json
import random
import subprocess
import time

from check_device import fp32_word_to_fp16, read_hex_rows, read_bin
from check_features import decode, val32, round32_search, MAX32, reference

ROOT = Path(__file__).resolve().parents[1]
CONFIGS = [('V100', 4, 0), ('A100', 8, 1), ('H100', 16, 2)]
SEED = 20260906


def nearest(x):
    """Independent nearest-even: binary-search adjacent encodings, compare distances."""
    floor = round32_search(abs(x))
    if floor is None:
        return None
    if val32(floor) == abs(x) or floor == 0x7f7fffff:
        result = floor
    else:
        lo, hi = abs(x) - val32(floor), val32(floor + 1) - abs(x)
        result = floor if lo < hi or (lo == hi and floor % 2 == 0) else floor + 1
    return result | (0x80000000 if x < 0 else 0)


def cases():
    rng = random.Random(SEED)
    for cohort in ['finite_bits', 'near_one']:
        for device, k, extra in CONFIGS:
            for index in range(1000):
                def sample(half):
                    if cohort == 'finite_bits':
                        mag = rng.randrange(0x7c00 if half else 0x7f800000)
                    else:
                        mag = rng.randrange(0x3800, 0x4000) if half else rng.randrange(0x3f000000, 0x40000000)
                    return mag | (rng.randrange(2) << (15 if half else 31))
                yield dict(cohort=cohort, device=device, k=k, extra=extra, index=index,
                           words=[sample(True) for _ in range(2*k)] + [sample(False)])
    pins = json.loads((ROOT / 'vendor/SOURCES.json').read_text())
    for device, k, extra in CONFIGS:
        prefix = f'model_validation/{device}/fp16'
        folder = ROOT / 'vendor/matlab-tensor-core-v0.5' / prefix
        for name in [f'a_{device}_fp16.txt', f'b_{device}_fp16.txt',
                     f'c_{device}_fp32.txt', f'd_{device}_fp32.txt']:
            assert hashlib.sha256((folder / name).read_bytes()).hexdigest() == pins['sha256'][f'{prefix}/{name}']
        aa, bb = (read_hex_rows(folder / f'{v}_{device}_fp16.txt') for v in ['a', 'b'])
        cc, dd = (read_bin(folder / f'{v}_{device}_fp32.txt') for v in ['c', 'd'])
        assert len(aa) == len(bb) == len(cc) == len(dd) == 5000
        for index, (a, b, c, d) in enumerate(zip(aa, bb, cc, dd)):
            assert len(a) == len(b) == k
            words = [fp32_word_to_fp16(x) for pair in zip(a, b) for x in pair] + [c]
            yield dict(cohort='published', device=device, k=k, extra=extra,
                       index=index, words=words, measured=d)
    # Additional application-like signed blocks, cancellation and padded partial tails.
    rng = random.Random(SEED + 1)
    for device, k, extra in CONFIGS:
        for index in range(160):
            n = index % k + 1
            words = []
            for _ in range(n):
                for _ in range(2):
                    words.append((rng.randrange(7, 23) << 10) | rng.randrange(1024) | (rng.randrange(2) << 15))
            if index % 4 == 0 and n >= 2:
                words[2:4] = [words[0] ^ 0x8000, words[1]]
            words += [0] * (2 * (k - n))
            words.append(rng.choice([0, 0x80000000, 0x3f800000, 0xbf800000, 1]))
            yield dict(cohort='bounded_signed_tails', device=device, k=k, extra=extra,
                       index=index, words=words)
    rng = random.Random(SEED + 2)
    for device, k, extra in CONFIGS:
        for index in range(160):
            n = index % k + 1
            words = [rng.randrange(0x2c00) | (rng.randrange(2) << 15) for _ in range(2*n)]
            if index % 4 == 0 and n >= 2:
                words[2:4] = [words[0] ^ 0x8000, words[1]]
            words += [0] * (2 * (k-n))
            c = rng.randrange(0x3e800000, 0x3f800001) if index % 4 else rng.choice([0, 1])
            words.append(c | (rng.randrange(2) << 31))
            assert all(abs(decode(w, 10, 5, 15)[0]) < Q(1, 16) for w in words[:-1])
            assert abs(val32(words[-1])) <= 1
            yield dict(cohort='application_small', device=device, k=k, extra=extra,
                       index=index, words=words)
    # Exact counterexample, coefficient overflow, nonfinite inputs and finite overflow.
    adversarial = [
        ('subnormal_accumulator', [0x3c00, 0x3c00, 1, 0x3c00, 0, 0, 0, 0, 1]),
        ('support_overflow', [0x5bff, 0x37ff]*3 + [1, 1, 0x4e800000]),
        ('nan_operand', [0x7e00, 0x3c00] + [0]*7),
        ('inf_accumulator', [0]*8 + [0x7f800000]),
        ('finite_overflow', [0x7bff, 0x7bff]*4 + [0x7f7fffff]),
        ('negative_zero', [0x8000, 0x3c00]*4 + [0x80000000]),
    ]
    for index, (name, words) in enumerate(adversarial):
        yield dict(cohort='adversarial', device='V100', k=4, extra=0, index=index,
                   name=name, words=words)


def low_support(parts):
    """Independent oracle: exponent of the lowest bit actually set in the NONZERO low parts."""
    exponents = []
    for q in parts:
        if q:
            assert q.denominator & (q.denominator - 1) == 0
            n = abs(q.numerator)
            exponents.append((n & -n).bit_length() - 1 - (q.denominator.bit_length() - 1))
    if not exponents:
        return None, 0
    support = min(exponents)
    coefficients = [q / Q(2)**support for q in parts]
    assert all(q.denominator == 1 for q in coefficients)
    return support, sum(abs(q.numerator) for q in coefficients)


def main():
    generated = list(cases())
    temp = ROOT / 'tmp/eft'
    temp.mkdir(parents=True, exist_ok=True)
    rows = '\n'.join(f"{c['k']} {c['extra']} " + ' '.join(f'{w:x}' for w in c['words']) for c in generated) + '\n'
    input_file = temp / 'coverage.txt'
    input_file.write_text(rows)
    start = time.perf_counter()
    proc = subprocess.run(['lake', 'env', 'lean', '--run', 'examples/EFTCoverage.lean', str(input_file)],
                          cwd=ROOT, check=True, text=True, capture_output=True)
    lean_seconds = time.perf_counter() - start
    outputs = [json.loads(line) for line in proc.stdout.splitlines()]
    assert len(outputs) == len(generated)
    totals, records = {}, []
    for case, out in zip(generated, outputs):
        key = f"{case['cohort']}/{case['device']}"
        tally = totals.setdefault(key, dict(cases=0, model_rejections=0, scalar_accepted=0,
                                          corrected_changed=0, unchecked_mismatches=0,
                                          tighter_support_bound_passes=0, failures=Counter()))
        tally['cases'] += 1
        oracle = reference(case['words'], case['k'], case['extra'], None)
        record = {**case, **out}
        record['words'] = [f'{w:04x}' if i < 2*case['k'] else f'{w:08x}' for i, w in enumerate(case['words'])]
        if 'error' in out:
            assert oracle is None, (case, out, oracle)
            tally['model_rejections'] += 1
            record['oracle'] = None
        else:
            assert oracle is not None and out['bits'] == oracle['bits'], (case, out, oracle)
            if 'measured' in case:
                assert case['measured'] == out['bits'], (case, out)
            # Ideal comes only from original encoded operands in the independent oracle.
            expected = nearest(oracle['ideal'])
            assert out['accepted'] == (not out['failed']), (case, out)
            assert out['corrected'] == out['tceft'], (case, out)
            assert out['accepted'] == (out['corrected'] is not None), (case, out)
            if out['accepted']:
                assert out['corrected'] == expected, (case, out, expected)
            changed = out['accepted'] and out['corrected'] != out['bits']
            tally['scalar_accepted'] += out['accepted']
            tally['corrected_changed'] += changed
            tally['unchecked_mismatches'] += out['unchecked'] != expected
            tally['failures'].update(out['failed'])
            parts = [Q(q) for q in out['low_parts']]
            support, mag = low_support(parts)
            tighter_pass = mag < 2**24 and (support is None or -149 <= support <= 104)
            tally['tighter_support_bound_passes'] += tighter_pass
            # The Lean predicate uses the lowest bit actually set, as this independent oracle does.
            bit_checks = {'lowest_bit_min', 'lowest_bit_max', 'low_bits_on_grid', 'low_bits_sum_below_2pow24'}
            if not (bit_checks & set(out['failed'])) != tighter_pass:
                raise SystemExit(f'Lean low-bit checks disagree with the oracle: {case} {out}')
            record.update(oracle=expected, correction_changed=changed,
                          actual_low_support=support, actual_low_coefficient_sum=str(mag))
            if case.get('name') == 'subnormal_accumulator':
                assert (out['unchecked'], expected, out['corrected']) == (0x3f800000, 0x3f800001, None)
        records.append(record)
    # A changed sufficient predicate must be separately named; baseline is a strict gate.
    for (device, _, _), accepted, changed in zip(CONFIGS, [86, 24, 1], [1885, 1919, 2093]):
        assert totals[f'finite_bits/{device}']['scalar_accepted'] == accepted
        assert totals[f'finite_bits/{device}']['failures'] == {'low_bits_sum_below_2pow24': 1000 - accepted}
        assert totals[f'near_one/{device}']['scalar_accepted'] == 1000
        assert totals[f'published/{device}']['scalar_accepted'] == 5000
        assert totals[f'published/{device}']['corrected_changed'] == changed
        for cohort in ['finite_bits', 'near_one', 'published']:
            assert totals[f'{cohort}/{device}']['model_rejections'] == 0
    destination = ROOT / 'data/regressions'
    case_text = json.dumps(records, separators=(',', ':')) + '\n'
    report = dict(seed=SEED, floor=None, cases=len(records), baseline_gate='passed',
                  input_sha256=hashlib.sha256(rows.encode()).hexdigest(),
                  case_record_sha256=hashlib.sha256(case_text.encode()).hexdigest(),
                  comparison='Actual Lean predicate and safe API; binary-search original-input rational oracle',
                  limits=['All extraction and guard work here is exact arithmetic.',
                          'The Lean predicate and this oracle both use the lowest bit actually set in the low parts.',
                          'Published rows are prior measurements; no GPU was run.'],
                  cohorts=totals)
    timing = dict(lean_reference_runner_seconds=round(lean_seconds, 3),
                  total_seconds=round(time.perf_counter() - start, 3))
    (ROOT / 'tmp/timings').mkdir(parents=True, exist_ok=True)
    (ROOT / 'tmp/timings/eft-coverage.json').write_text(json.dumps(timing, indent=2) + '\n')
    (destination / 'eft-coverage-cases.json').write_text(case_text)
    (destination / 'eft-coverage.json').write_text(json.dumps(report, indent=2) + '\n')
    print(json.dumps(report, indent=2))


if __name__ == '__main__':
    main()
