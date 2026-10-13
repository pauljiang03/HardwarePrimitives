#!/usr/bin/env python3
"""Compare 16-position Lean instruction outputs with an independent exact-arithmetic oracle."""
if not __debug__:
    raise SystemExit('Run without python -O or PYTHONOPTIMIZE: these checks rely on assert.')
from pathlib import Path
import hashlib
import json
import subprocess
from check_features import reference

ROOT = Path(__file__).resolve().parents[1]
PROFILES = {'V100': (4, 0, None), 'A100': (8, 1, -132), 'H100': (16, 2, -133)}


def vectors():
    for profile, (k, _, _) in PROFILES.items():
        def row(name, pairs, c=0):
            assert len(pairs) == 16
            return dict(id=f'{profile}/{name}', profile=profile,
                        a=[f'{a:04x}' for a, _ in pairs],
                        b=[f'{b:04x}' for _, b in pairs], c=f'{c:08x}')
        yield row('all_groups_populated', [(0x3c00, 0x3c00)] * 16)
        for position in range(16):
            pairs = [(0, 0)] * 16
            pairs[position] = (0x3c00, 0x3c00)
            yield row(f'position_{position:02}', pairs)
        for group in range(16 // k):
            pairs = [(0, 0)] * 16
            pairs[group*k:(group+1)*k] = [(0x3c00, 0x3c00)] * k
            yield row(f'group_{group}', pairs)
        # All ordered pairs of block FMAs; the two orderings have the same exact ideal.
        for first in range(16 // k):
            for later in range(first + 1, 16 // k):
                for reverse in [False, True]:
                    pairs = [(0, 0)] * 16
                    a, b = (later*k, first*k) if reverse else (first*k, later*k)
                    pairs[a], pairs[b] = (0xbc00, 0x3c00), (1, 0x3c00)
                    yield row(f'order_{first}_{later}_{int(reverse)}', pairs, 0x3f800000)
        yield row('signed_zero', [(0x8000, 0x3c00)]*16, 0x80000000)
        yield row('mixed_signed_zero', [(0x8000, 0x3c00), (0, 0xbc00)]*8, 0x80000000)
        yield row('subnormal_accumulator', [(0, 0)]*16, 1)
        yield row('negative_subnormal_accumulator', [(0, 0)]*16, 0x80000001)
        yield row('subnormal_products', [(1, 1)]*16)
        yield row('subnormal_negative_products', [(0x8001, 1)]*16)
        yield row('normal_boundary', [(0x03ff, 0x3c00), (0x0400, 0xbc00)]*8)
        yield row('cancellation', [(0x3c00, 0x3c00), (0xbc00, 0x3c00)]*8, 1)
        pairs = [(0, 0)]*16
        pairs[0], pairs[1] = (0x3c00, 0x3c00), (1, 0x3c00)
        yield row('subnormal_mixed_products', pairs, 1)


def main():
    inputs = list(vectors())
    assert len({v['id'] for v in inputs}) == len(inputs)
    lines = []
    for v in inputs:
        words = [int(w, 16) for pair in zip(v['a'], v['b']) for w in pair] + [int(v['c'], 16)]
        lines.append(v['profile'] + ' ' + ' '.join(map(str, words)))
    tmp = ROOT / 'tmp/instruction-groups'
    tmp.mkdir(parents=True, exist_ok=True)
    path = tmp / 'inputs.txt'
    path.write_text('\n'.join(lines) + '\n')
    proc = subprocess.run(['lake', 'env', 'lean', '--run', 'examples/InstructionGroups.lean', str(path)],
                          cwd=ROOT, check=True, text=True, capture_output=True)
    outputs = [json.loads(x) for x in proc.stdout.splitlines()]
    assert len(outputs) == len(inputs)
    expected = []
    for v, bits in zip(inputs, outputs):
        assert bits is not None
        k, extra, floor = PROFILES[v['profile']]
        c = int(v['c'], 16)
        for start in range(0, 16, k):
            words = [int(w, 16) for pair in zip(v['a'][start:start+k], v['b'][start:start+k]) for w in pair] + [c]
            result = reference(words, k, extra, floor)
            assert result is not None
            c = result['bits']
        assert bits == c, (v, bits, c)
        expected.append(dict(id=v['id'], bits=f'{bits:08x}', status='model_result'))
    lookup = {x['id']: x['bits'] for x in expected}
    assert lookup['A100/order_0_1_0'] == '33800000'
    assert lookup['A100/order_0_1_1'] == '00000000'
    for first in range(4):
        for later in range(first+1, 4):
            assert lookup[f'V100/order_{first}_{later}_0'] == '33800000'
            assert lookup[f'V100/order_{first}_{later}_1'] == '00000000'
    report = dict(status='passed', cases=len(inputs), mismatches=0,
                  profiles={profile: sum(v['profile'] == profile for v in inputs)
                            for profile in PROFILES},
                  scope='16-position FP16/FP32 instruction variants, ordered accumulation of block FMAs, zeros, subnormals, and cancellation',
                  oracle='Lean instruction outputs compared with independent exact rational arithmetic per ordered block FMA',
                  source_sha256={name: hashlib.sha256((ROOT/name).read_bytes()).hexdigest()
                                 for name in ['scripts/check_instruction_groups.py',
                                              'scripts/check_features.py',
                                              'examples/InstructionGroups.lean']})
    (ROOT / 'data/regressions/instruction-groups-report.json').write_text(
        json.dumps(report, indent=2) + '\n')
    print(json.dumps(report, indent=2))


if __name__ == '__main__':
    main()
