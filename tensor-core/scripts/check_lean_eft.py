#!/usr/bin/env python3
"""Compare native EFT accumulation to the bounded reference and IEEE oracle."""
if not __debug__:
    raise SystemExit('Run without python -O or PYTHONOPTIMIZE: these checks rely on assert.')
from collections import Counter
import hashlib
import json
from pathlib import Path
import random
import subprocess
import time

from scalar_oracle import decode, power, rounded

ROOT = Path(__file__).resolve().parents[1]
SEED = 20260909
MAX = decode(32, 0x7f7fffff)[2]


def expected(acc, terms):
    for term in terms:
        left, right = decode(32, acc), decode(32, term)
        if left[0] != 'finite' or right[0] != 'finite':
            return None
        exact = left[2] + right[2]
        if abs(exact) > MAX:
            return None
        acc = rounded(32, exact, False, 'rne', 'after')[0]
    return acc


def cases():
    magnitudes = [0, 1, 2, 0x007fffff, 0x00800000, 0x00800001,
                  0x337fffff, 0x33800000, 0x33800001, 0x3effffff, 0x3f000000,
                  0x3f7fffff, 0x3f800000, 0x3f800001, 0x3fffffff, 0x40000000,
                  0x4b800000, 0x7f7ffffe, 0x7f7fffff, 0x7f800000, 0x7f800001, 0x7fc00007]
    edges = [b | sign for sign in (0, 0x80000000) for b in magnitudes]
    for acc in edges:
        yield 'empty', {'acc': acc, 'terms': []}
        for b in edges:
            yield 'edge_pair', {'acc': acc, 'terms': [b]}
    for terms in [[0x3f800000, 0x33800000, 0x33800000],
                  [0x4b800000, 0x3f800000, 0xcb800000],
                  [0x4b800000, 0xcb800000, 0x3f800000],
                  [0x7f7fffff, 0x7f7fffff, 0xff7fffff],
                  [0x80000000] * 17, [1] * 17,
                  [0x007fffff, 1, 0x80800000],
                  [0x3f800000, 0xbf000000, 0x3e800000]]:
        yield 'ordering_and_rounding', {'acc': 0, 'terms': terms}
    rng = random.Random(SEED)
    for _ in range(4000):
        yield 'random_pair', {'acc': rng.getrandbits(32), 'terms': [rng.getrandbits(32)]}
    for _ in range(1000):
        yield 'random_fold', {'acc': 0, 'terms': [rng.getrandbits(32) for _ in range(rng.randrange(1, 18))]}
    for _ in range(1000):
        grid = rng.randrange(-149, 105)
        coefficients = [rng.randrange(-(1 << 18), 1 << 18) for _ in range(rng.randrange(1, 18))]
        assert sum(map(abs, coefficients)) < 1 << 24
        terms = []
        for z in coefficients:
            bits, flags = rounded(32, z * power(grid), False, 'rne', 'after')
            assert flags == 0
            terms.append(bits)
        answer = expected(0, terms)
        assert answer is not None and decode(32, answer)[2] == sum(coefficients) * power(grid)
        yield 'eft_exact_grid', {'acc': 0, 'terms': terms}


def main():
    started = time.monotonic()
    subprocess.run(['lake', 'build', 'tc_lean_eft_check'], cwd=ROOT, check=True,
                   stdout=subprocess.DEVNULL)
    inputs = list(cases())
    data = ''.join(json.dumps(r, separators=(',', ':')) + '\n' for _, r in inputs)
    binary = ROOT / '.lake/build/bin/tc_lean_eft_check'
    proc = subprocess.run([str(binary)], input=data, text=True, capture_output=True, check=True)
    outputs = [json.loads(line) for line in proc.stdout.splitlines()]
    if len(outputs) != len(inputs):
        raise RuntimeError(f'Expected {len(inputs)} results, got {len(outputs)}')
    failures = []
    rejected = 0
    for index, ((_, request), got) in enumerate(zip(inputs, outputs)):
        want = expected(request['acc'], request['terms'])
        rejected += want is None
        if got != {'reference': want, 'native': want}:
            failures.append({'index': index, 'request': request, 'expected': want, 'actual': got})
    invalid = [{'acc': 1 << 32, 'terms': []}, {'acc': 0, 'terms': [-1]},
               {'acc': 0, 'terms': [1 << 32]}]
    for request in invalid:
        result = subprocess.run([str(binary)], input=json.dumps(request) + '\n',
                                text=True, capture_output=True)
        if result.returncode != 2 or result.stdout:
            raise RuntimeError(f'Invalid request was not rejected: {request}')
    sources = [Path(__file__).resolve(), ROOT / 'scripts/scalar_oracle.py',
               ROOT / 'Main/LeanEFTCheck.lean', ROOT / 'Main/BoundedEFT.lean',
               ROOT / 'lean-toolchain', ROOT / 'lakefile.toml',
               ROOT / 'TensorCore/Kernels/EFT/Native.lean',
               ROOT / 'TensorCore/Kernels/EFT/Defs.lean',
               ROOT / 'tests/TensorCoreTests/EFT/NativeEFT.lean',
               *sorted((ROOT / 'TensorCore/Scalar').glob('*.lean')),
               *sorted((ROOT / 'TensorCore/Kernels/EFT').glob('*.lean'))]
    report = {'status': 'failed' if failures else 'passed', 'seed': SEED,
              'scope': 'FP32 left-to-right native EFT accumulation; finite exact-range and positive exact-zero policy',
              'samples_are_not_proofs': True, 'cases': len(inputs),
              'groups': dict(Counter(g for g, _ in inputs)), 'rejected_sequences': rejected,
              'invalid_request_controls': len(invalid), 'failures': len(failures),
              'first_failures': failures[:20],
              'preservation_theorems': ['TensorCore.EFMachine.add32WithLean_eq',
                                       'TensorCore.EFMachine.naiveSum32WithLeanFrom_eq',
                                       'TensorCore.EFMachine.tcEftWithLean_eq'],
              'correctness_theorem': 'TensorCore.EFMachine.tcEftWithLean_correct',
              'request_sha256': hashlib.sha256(data.encode()).hexdigest(),
              'source_sha256': {str(p.relative_to(ROOT)): hashlib.sha256(p.read_bytes()).hexdigest()
                                for p in sources}}
    timing = {'elapsed_seconds': round(time.monotonic() - started, 3)}
    (ROOT / 'tmp/timings').mkdir(parents=True, exist_ok=True)
    (ROOT / 'tmp/timings/lean-eft.json').write_text(json.dumps(timing, indent=2) + '\n')
    (ROOT / 'data/regressions/lean-eft-report.json').write_text(json.dumps(report, indent=2) + '\n')
    print(json.dumps(report, indent=2))
    return bool(failures)


if __name__ == '__main__':
    if not __debug__:
        raise SystemExit('Run without Python -O; the oracle uses assertions.')
    raise SystemExit(main())
