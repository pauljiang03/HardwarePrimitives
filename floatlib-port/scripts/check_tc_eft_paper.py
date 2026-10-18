#!/usr/bin/env python3
"""Reproduce the pinned TC-EFT paper suites and compare their exact cases with Lean."""
if not __debug__:
    raise SystemExit('Run without python -O or PYTHONOPTIMIZE: these checks rely on assert.')
from collections import Counter
from contextlib import redirect_stdout
from copy import deepcopy
from fractions import Fraction as Q
from functools import lru_cache
from pathlib import Path
import hashlib
import io
import json
import shutil
import subprocess
import sys
import time

PORT = Path(__file__).resolve().parents[1]
ROOT = PORT.parent
VENDOR = ROOT / 'vendor/tc-eft-validation'
WORK = PORT / 'test-results/eft-paper'
DEST = PORT / 'test-results'


def sha(data):
    return hashlib.sha256(data).hexdigest()


def reproduce():
    pins = json.loads((VENDOR / 'SOURCES.json').read_text())
    scratch = WORK / 'original'
    scratch.mkdir(parents=True, exist_ok=True)
    for name, expected in pins['files'].items():
        data = (VENDOR / name).read_bytes()
        assert sha(data) == expected, ('changed pinned generator', name)
        (scratch / name).write_bytes(data)
    sys.path.insert(0, str(scratch))
    import exact_model as ref
    import check_revision as rev

    checked, draws = [], []
    original_check = rev.check

    def capture_check(a, b, c, profile):
        result = original_check(a, b, c, profile)
        checked.append((list(a), list(b), c, profile, result))
        return result

    rev.check = capture_check
    log = io.StringIO()
    with redirect_stdout(log):
        rev.main()
    first = json.loads((scratch / 'results.json').read_text())
    assert first['result'] == 'PASS'
    assert (len(first['named_regressions']), first['random_blocks'],
            first['synthetic_perturbations'], first['rounding_cases']) == (59, 800, 49005, 100)
    assert len(checked) == 859

    import check_second_pass as second
    second.check = capture_check
    original_oracle = second.integer_block_oracle

    def capture_draw(a, b, c, profile):
        result = original_oracle(a, b, c, profile)
        draws.append((list(a), list(b), c, profile, result))
        return result

    second.integer_block_oracle = capture_draw
    with redirect_stdout(log):
        second.main()
    extra = json.loads((scratch / 'second_pass_results.json').read_text())
    assert extra['result'] == 'PASS' and sum(extra['full_range_finite_blocks'].values()) == 1600
    assert all(n == 200 for n in extra['full_range_finite_blocks'].values())
    assert len(draws) == 1600 + sum(extra['out_of_domain_draws'].values())
    assert len(checked) == 859 + 1600 + 8  # six special cases and two composition blocks
    (WORK / 'original.log').write_text(log.getvalue())
    return pins, ref, rev, checked, draws, first, extra


def key(a, b, c, profile):
    return tuple(a), tuple(b), c, profile


def rotate_c_first(values):
    return values[-1:] + values[:-1]


def compare_block(case, out):
    expected = case['expected']
    assert Q(out['ideal']) == Q(expected['ideal']), (case['id'], 'independent ideal', out)
    model, correction = out['model'], out['correction']
    if expected['bits'] is None:
        assert model == {'error': 'TensorCore.ModelError.accumulatorOutOfRange'}, (case['id'], model)
    else:
        assert 'error' not in model, (case['id'], model)
        assert model['bits'] == expected['bits'], (case['id'], 'alignment/output bits', model)
        assert Q(model['accumulator']) == Q(expected['accumulator']), (case['id'], 'accumulator')
        assert model['alignExp'] == expected['alignExp'], (case['id'], 'exponent maximum')
        assert model['algorithm_bits'] == expected['corrected'], (case['id'], 'trace Algorithm 1')
        assert model['scalar_predicate'] == (model['scalar_bits'] is not None)
        if model['scalar_predicate']:
            assert model['scalar_bits'] == expected['corrected'], (case['id'], 'scalar correction')
        source = case.get('_stage')
        if source is not None:
            assert Q(model['alignGridStep']) == source['qa'], (case['id'], 'alignment quantum')
            for field, source_field in [('terms', 'terms'), ('aligned', 'aligned'),
                                        ('alignment_residuals', 'residuals'), ('low_parts', 'eps')]:
                assert list(map(Q, model[field])) == rotate_c_first(source[source_field]), (case['id'], field)
            assert Q(model['output_residual']) == source['rout'], (case['id'], 'output residual')
            assert Q(model['overlap']) == source['eo'], (case['id'], 'overlap')
    assert 'error' not in correction, (case['id'], correction)
    assert correction['bits'] == expected['corrected'], (case['id'], 'encoded correction', correction)
    if expected['alignExp'] is None:
        assert correction['branch'] == 'allZero', (case['id'], 'zero shortcut')
    elif expected['corrected'] is None:
        assert correction['branch'] == 'outOfRange', (case['id'], 'finite ideal rejection')
    else:
        assert correction['branch'] in {'scalar', 'exactReference'}



def main():
    start = time.perf_counter()
    WORK.mkdir(parents=True, exist_ok=True)
    DEST.mkdir(parents=True, exist_ok=True)
    pins, ref, rev, checked, draws, source_report, source_extra = reproduce()

    @lru_cache(maxsize=None)
    def rounded(x, mode='rne'):
        return rev.neighbor_round(x, mode) if abs(x) <= ref.MAX32 else None

    records = []

    def add(identifier, cohort, a, b, c, profile, stage=None, oracle=None):
        fmt, k, p, floor = ref.PROFILES[profile]
        oracle = oracle if oracle is not None else rev.integer_block_oracle(a, b, c, profile)
        ideal = ref.ideal_oracle(a, b, c, fmt)
        supplied = oracle['bits'] if oracle['bits'] is not None else 0
        row = ' '.join(map(str, ['block', fmt, k, p, 'none' if floor is None else floor,
                                *[w for pair in zip(a, b) for w in pair], c, supplied]))
        records.append(dict(id=identifier, cohort=cohort, profile=profile,
                            a=[hex(x) for x in a], b=[hex(x) for x in b], c=hex(c), D=hex(supplied),
                            expected=dict(alignExp=oracle['eta'], accumulator=str(oracle['acc']),
                                          bits=oracle['bits'], ideal=str(ideal), corrected=rounded(ideal)),
                            _row=row, _stage=stage))

    for i, (a, b, c, profile, stage) in enumerate(checked[:859]):
        if i < 59:
            named = source_report['named_regressions'][i]
            assert (a, b, c, profile) == ([int(x, 16) for x in named['a']],
                                         [int(x, 16) for x in named['b']], int(named['c'], 16), named['profile'])
            identifier, cohort = profile + '/' + named['name'], 'named'
        else:
            identifier, cohort = f'{profile}/seed-20260905/{i - 59}', 'deterministic'
        add(identifier, cohort, a, b, c, profile, stage)

    stages = {key(a, b, c, p): r for a, b, c, p, r in checked[859:2459]}
    full_counts = Counter({profile: 0 for profile in ref.PROFILES})
    excluded_counts = Counter({profile: 0 for profile in ref.PROFILES})
    for i, (a, b, c, profile, oracle) in enumerate(draws):
        ideal = ref.ideal_oracle(a, b, c, ref.PROFILES[profile][0])
        accepted = oracle['bits'] is not None and abs(ideal) <= ref.MAX32
        cohort = 'full_range' if accepted else 'excluded_draw'
        (full_counts if accepted else excluded_counts)[profile] += 1
        stage = stages[key(a, b, c, profile)] if accepted else None
        add(f'{profile}/seed-20260906/{i}', cohort, a, b, c, profile, stage, oracle)
    assert dict(full_counts) == source_extra['full_range_finite_blocks']
    assert dict(excluded_counts) == source_extra['out_of_domain_draws']
    for i, (a, b, c, profile, stage) in enumerate(checked[2459:]):
        add(f'{profile}/boundary-composition/{i}', 'boundary_composition', a, b, c, profile, stage)
    assert len({r['id'] for r in records}) == len(records)

    # The source's synthetic grid family, with encoded FP16 operands in Lean.
    families = []
    for p in range(5):
        for k in range(1, 100):
            for j in range(1, 100):
                acc = 1 + (k - j * (1 << p)) * ref.pow2(-24 - p)
                families.append((f'family {p} {k} {j}', acc, rounded(acc, 'rtz')))
    assert len(families) == source_report['synthetic_perturbations']
    rounding = []
    for low in [0, 1, 2, 0x007ffffe, 0x007fffff, 0x00800000,
                0x3f7fffff, 0x3f800000, 0x3f800001, 0x7f7ffffd]:
        x, y = ref.oracle_value(low, 'fp32'), ref.oracle_value(low + 1, 'fp32')
        for t in [Q(0), Q(1, 4), Q(1, 2), Q(3, 4), Q(1)]:
            for sign in [-1, 1]:
                q = sign * (x + t * (y - x))
                rounding.append((f'round {q.numerator} {q.denominator}',
                                 dict(rne=rounded(q), trunc=rounded(q, 'rtz'))))
    assert len(rounding) == source_report['rounding_cases']

    rows = [r['_row'] for r in records] + [r[0] for r in families] + [r[0] for r in rounding]
    input_text = '\n'.join(rows) + '\n'
    input_path, output_path = WORK / 'inputs.txt', WORK / 'outputs.jsonl'
    input_path.write_text(input_text)
    binary = PORT / '.lake/build/bin/tc_floatlib'
    lean_start = time.perf_counter()
    with output_path.open('w') as output:
        subprocess.run([str(binary), str(input_path)], cwd=ROOT, stdout=output, check=True)
    lean_seconds = time.perf_counter() - lean_start
    outputs = [json.loads(line) for line in output_path.read_text().splitlines()]
    assert len(outputs) == len(rows)
    branches, predicate_differences = Counter(), Counter()
    for case, out in zip(records, outputs):
        compare_block(case, out)
        branches[out['correction']['branch']] += 1
        if case['_stage'] is not None:
            # The manuscript chooses the finest nonzero residual grid.
            paper_accepted = case['_stage']['scalar_cr'] is not None
            if paper_accepted != out['model']['scalar_predicate']:
                predicate_differences[case['cohort']] += 1
    offset = len(records)
    for (row, acc, bits), out in zip(families, outputs[offset:]):
        assert out['bits'] == bits and Q(out['accumulator']) == acc, (row, out, acc, bits)
    offset += len(families)
    for (row, expected), out in zip(rounding, outputs[offset:]):
        assert out == expected, (row, out, expected)

    controls = []
    for field in ['model', 'correction']:
        wrong = deepcopy(outputs[0])
        wrong[field]['bits'] ^= 1
        try:
            compare_block(records[0], wrong)
        except AssertionError:
            controls.append('wrong_' + field + '_bits_rejected')
        else:
            raise AssertionError(('negative control passed', field))
    for row in ['round 1 0', 'family 5 4 1', 'family 0 4 0',
                'block fp16 0 0 none 4294967296 0', 'block fp16 1 0 none 65536 0 0 0']:
        bad = WORK / 'invalid.txt'
        bad.write_text(row + '\n')
        proc = subprocess.run([str(binary), str(bad)], capture_output=True, text=True)
        assert proc.returncode != 0, ('invalid parser input accepted', row)
    controls.append('invalid_shapes_widths_and_denominators_rejected')


    cases = dict(blocks=[{k: v for k, v in r.items() if not k.startswith('_')} for r in records],
                 synthetic_family=dict(p=[0, 4], K=[1, 99], j=[1, 99], inclusive=True,
                                       a_fp16='0x0c00', b_fp16=['0x0c00', '0x0800', '0x0400', '0x0200', '0x0100'],
                                       c_fp32='0x3f800000 - j'),
                 rounding=[dict(row=row, expected=expected) for row, expected in rounding])
    case_text = json.dumps(cases, indent=2) + '\n'
    (DEST / 'eft-paper-cases.json').write_text(case_text)
    for src, dst in [('results.json', 'eft-paper-original.json'),
                     ('second_pass_results.json', 'eft-paper-second-pass.json')]:
        shutil.copyfile(WORK / 'original' / src, DEST / dst)
    report = dict(status='passed', source_sha256=pins['files'], paper_sha256=pins['paper_sha256'],
                  named_cases=59, deterministic_blocks=800, deterministic_seed=20260905,
                  profile_combinations=len(ref.PROFILES), synthetic_perturbations=len(families),
                  rounding_cases=len(rounding), full_range_blocks=sum(full_counts.values()),
                  full_range_seed=20260906, excluded_draws=dict(excluded_counts),
                  boundary_composition_blocks=8, lean_comparisons=len(outputs),
                  executable_dependency_checks=0,
                  source_additional_checks=dict(family_endpoints=source_extra['family_endpoint_cases'],
                                                scalar_support=source_extra['scalar_support_cases'],
                                                scope='Reproduced in the original Python generator; not additional Lean comparisons.'),
                  correction_branches=dict(branches), scalar_predicate_differences=dict(predicate_differences),
                  mismatches=0, negative_controls=controls,
                  input_sha256=sha(input_text.encode()), cases_sha256=sha(case_text.encode()),
                  output_sha256=sha(output_path.read_bytes()),
                  timing=dict(lean_seconds=round(lean_seconds, 3), total_seconds=round(time.perf_counter()-start, 3)),
                  historical_v100_experiments=dict(reported=100, surviving_vectors=0, reproduced=False),
                  limits=['Software model checks; zero new GPU measurements.',
                          'Original generators are pinned and reproduced, not Lean proofs.',
                          'Finite reference ranges exclude overflow; excluded draws are retained and checked.',
                          'Original scalar support uses the finest residual grid; the Lean baseline remains conservative.',
                          'The synthetic family comparison evaluates encoded blocks, not GPU instructions.'])
    (DEST / 'eft-paper-report.json').write_text(json.dumps(report, indent=2) + '\n')
    print(json.dumps(report, indent=2))


if __name__ == '__main__':
    main()
