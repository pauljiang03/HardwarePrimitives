#!/usr/bin/env python3
"""Independent integer checks of the complete bounded EFT and final rounding."""
if not __debug__:
    raise SystemExit('Run without python -O or PYTHONOPTIMIZE: these checks rely on assert.')
from collections import Counter
from fractions import Fraction
from pathlib import Path
import hashlib
import json
import random
import re
import subprocess
import time

ROOT = Path(__file__).resolve().parents[1]
WORK = ROOT / 'tmp/bounded-eft'
PROFILES = {
    'v100-fp16': (10, 5, 15, 4, 23, None),
    'a100-fp16': (10, 5, 15, 8, 24, -132),
    'h100-fp16': (10, 5, 15, 16, 25, -133),
    'a100-bf16': (7, 8, 127, 8, 24, -132),
    'h100-bf16': (7, 8, 127, 16, 25, -133),
    'a100-tf32': (10, 8, 127, 4, 24, -132),
    'h100-tf32-k4': (10, 8, 127, 4, 25, -133),
    'h100-tf32': (10, 8, 127, 8, 25, -133),
}
SCALE = 1 << 272
MAX = ((1 << 24) - 1) << 376


def decode(n, frac, exp, bias):
    e = n >> frac & ((1 << exp) - 1)
    m = n & ((1 << frac) - 1)
    if e == (1 << exp) - 1:
        return None
    sign = -1 if n >> (frac + exp) else 1
    if e == 0:
        return (0, 0, 0) if m == 0 else (sign * m, 1 - bias, frac)
    return sign * ((1 << frac) + m), e - bias, frac


def coefficient32(n):
    m, e, f = decode(n, 23, 8, 127)
    return m << (e - f + 272)


def round32(n):
    sign = 1 << 31 if n < 0 else 0
    n = abs(n)
    if n > MAX:
        return None
    lo, hi = 0, 0x7f7fffff
    while lo < hi:
        mid = (lo + hi + 1) // 2
        if coefficient32(mid) <= n:
            lo = mid
        else:
            hi = mid - 1
    if lo == 0x7f7fffff or coefficient32(lo) == n:
        return sign | lo
    dl, du = n - coefficient32(lo), coefficient32(lo + 1) - n
    return sign | (lo + 1 if du < dl or (du == dl and lo & 1) else lo)


def expected(case):
    f, e, bias, _, align, floor = PROFILES[case['profile']]
    terms, raws = [], []
    mc, ec, fc = decode(int(case['c'], 0), 23, 8, 127)
    terms.append(mc << (ec - fc + 272))
    if mc:
        raws.append(ec)
    for aa, bb in zip(case['a'], case['b']):
        ma, ea, fa = decode(int(aa, 0), f, e, bias)
        mb, eb, fb = decode(int(bb, 0), f, e, bias)
        terms.append((ma * mb) << (ea + eb - fa - fb + 272))
        if ma * mb:
            raws.append(ea + eb)
    d = int(case['D'], 0)
    de = d >> 23 & 255
    qd = (de + 122) if de else 123
    eta = max(raws) if raws else 0
    if floor is not None:
        eta = max(eta, floor)
    grid = max(eta - align + 272, qd)
    hi = [(1 if t >= 0 else -1) * ((abs(t) >> grid) << grid) for t in terms]
    lo = [t - h for t, h in zip(terms, hi)]
    ideal = sum(terms)
    return dict(terms=terms, grid=grid, coarse=hi, low=lo, recovered=ideal,
                overlap=coefficient32(d) - sum(hi), bits=round32(ideal))


def row(case):
    words = [str(int(n, 0)) for ab in zip(case['a'], case['b']) for n in ab]
    return ' '.join(['block', case['profile'], *words,
                     str(int(case['c'], 0)), str(int(case['D'], 0))])


def check_dependencies():
    proc = subprocess.run(['lake', 'env', 'lean', 'scripts/lean/BoundedEFTAudit.lean'],
                          cwd=ROOT, text=True, capture_output=True)
    output = proc.stdout + proc.stderr
    (WORK / 'audit.log').write_text(output)
    assert proc.returncode == 0, output
    assert output.count('bounded_execution_audit:') == 12, output
    assert 'bounded_proof_audit:' in output, output
    prefix = (ROOT / 'scripts/lean/BoundedEFTAudit.lean').read_text().rsplit('\nbounded_eft_audit', 1)[0]
    controls = {
        'rational': 'TensorCore.EFMachine.Word.value',
        'model': 'fun x : TensorCore.BlockInput TensorCore.v100F16F32 => TensorCore.evalBlock x',
        'linear_scan': 'fun x : TensorCore.EFMachine.Magnitude => x.ctz',
    }
    for name, expr in controls.items():
        path = WORK / (name + '-dependency.lean')
        path.write_text(prefix + '\ndef hidden := ' + expr +
                        '\ndef contaminated := hidden\nrun_cmd BoundedEFTAudit.check ``contaminated\n')
        p = subprocess.run(['lake', 'env', 'lean', str(path)], cwd=ROOT,
                           text=True, capture_output=True)
        log = p.stdout + p.stderr
        (WORK / (name + '-dependency.log')).write_text(log)
        assert p.returncode != 0 and 'Forbidden bounded execution dependencies:' in log, log
    return dict(executable_roots=12, negative_controls=list(controls),
                proof_audit=next(line for line in output.splitlines() if line.startswith('bounded_proof_audit:')))


def main():
    start = time.perf_counter()
    WORK.mkdir(parents=True, exist_ok=True)
    build = subprocess.run(['lake', 'build', 'TensorCore.Kernels.EFT.Success',
                            'TensorCoreTests.EFT.BoundedEFT',
                            'TensorCoreTests.EFT.NativeEFT', 'tc_bounded_eft',
                            'tc_lean_eft_check'], cwd=ROOT,
                           capture_output=True, text=True)
    (WORK / 'build.log').write_text(build.stdout + build.stderr)
    assert build.returncode == 0, build.stdout + build.stderr
    assert not re.search(r'^warning:', build.stdout + build.stderr, re.M), build.stdout + build.stderr
    audit = check_dependencies()
    corpus = json.loads((ROOT / 'data/regressions/eft-paper-cases.json').read_text())['blocks']
    cases = list(corpus)
    rng = random.Random(20260907)

    def finite(frac, exp):
        while True:
            n = rng.getrandbits(1 + exp + frac)
            if (n >> frac & ((1 << exp) - 1)) != (1 << exp) - 1:
                return hex(n)

    for profile, (f, e, _, k, _, _) in PROFILES.items():
        for i in range(128):
            cases.append(dict(id=f'{profile}/arbitrary-D/{i}', profile=profile,
                              a=[finite(f, e) for _ in range(k)],
                              b=[finite(f, e) for _ in range(k)],
                              c=finite(23, 8), D=finite(23, 8)))
    rounds = {0, 1, -1, MAX, -MAX, MAX + 1, -MAX - 1, (1 << 575) - 1, -(1 << 575)}
    for _ in range(512):
        b = rng.randrange(0x7f7fffff)
        midpoint = (coefficient32(b) + coefficient32(b + 1)) // 2
        for delta in (-1, 0, 1):
            rounds.add(midpoint + delta)
            rounds.add(-midpoint - delta)
    for e in (0, 1, 122, 123, 124, 145, 146, 147, 271, 272, 273, 398, 399, 400, 574, 575):
        for delta in (-1, 0, 1):
            rounds.add((1 << e) + delta)
            rounds.add(-((1 << e) + delta))
    rounds = sorted(rounds)
    batch = WORK / 'inputs.txt'
    batch.write_text('\n'.join([*(row(c) for c in cases), *(f'round {n}' for n in rounds)]) + '\n')
    proc = subprocess.run([str(ROOT / '.lake/build/bin/tc_bounded_eft'), str(batch)],
                          cwd=ROOT, text=True, capture_output=True)
    (WORK / 'execution.log').write_text(proc.stderr)
    assert proc.returncode == 0, proc.stdout[-4000:] + proc.stderr
    outputs = [json.loads(line) for line in proc.stdout.splitlines()]
    assert len(outputs) == len(cases) + len(rounds)
    requests = [dict(profile=c['profile'], a=[int(n, 0) for n in c['a']],
                     b=[int(n, 0) for n in c['b']], c=int(c['c'], 0), D=int(c['D'], 0))
                for c in cases]
    controls = [dict(profile='v100-fp16', a=[], b=[], c=0, D=0),
                dict(profile='v100-fp16', a=[0x7c00]*4, b=[0]*4, c=0, D=0),
                dict(profile='v100-fp16', a=[0]*4, b=[0]*4, c=0, D=0x7f800000)]
    comparison = subprocess.run([str(ROOT / '.lake/build/bin/tc_lean_eft_check')],
                                input=''.join(json.dumps(r) + '\n' for r in requests + controls),
                                text=True, capture_output=True, check=True)
    compared = [json.loads(line) for line in comparison.stdout.splitlines()]
    assert len(compared) == len(requests) + len(controls)
    for request, actual in zip(requests + controls, compared):
        assert actual['native'] == actual['reference'], (request, actual)
    for out, actual in zip(outputs, compared[:len(cases)]):
        assert actual['native'] == {k: out[k] for k in ('bits', 'branch')}, (out, actual)
    assert all('error' in actual['native'] for actual in compared[len(cases):])
    branches = Counter()
    for case, out in zip(cases, outputs):
        ex = expected(case)
        assert 'error' not in out, (case['id'], out)
        assert out['bits'] == ex['bits'], (case['id'], 'bits', out, ex)
        for key in ('recovered', 'overlap'):
            assert int(out[key]) == ex[key], (case['id'], key, out[key], ex[key])
        for key in ('coarse', 'low'):
            assert list(map(int, out[key])) == ex[key], (case['id'], key)
        if any(ex['terms']):
            assert out['grid'] == ex['grid'], (case['id'], 'grid', out, ex)
        if 'expected' in case:
            assert ex['recovered'] == Fraction(case['expected']['ideal']) * SCALE
            assert ex['bits'] == case['expected']['corrected']
        branches[out['branch']] += 1
    for n, out in zip(rounds, outputs[len(cases):]):
        assert out['bits'] == round32(n), (n, out, round32(n))
    sources = [*sorted((ROOT / 'TensorCore/Kernels/EFT').glob('*.lean')),
               *sorted((ROOT / 'TensorCore/Kernels/EFT').glob('*.lean')),
               ROOT / 'TensorCore/Kernels/EFT/Defs.lean', ROOT / 'Main/BoundedEFT.lean',
               ROOT / 'Main/LeanEFTCheck.lean',
               ROOT / 'TensorCore/Kernels/EFT/Native.lean',
               ROOT / 'tests/TensorCoreTests/EFT/NativeEFT.lean',
               ROOT / 'TensorCore/Scalar/LeanFiniteAddition.lean',
               ROOT / 'TensorCore/Scalar/LeanBridge.lean', ROOT / 'TensorCore/Scalar/LeanRounding.lean',
               ROOT / 'tests/TensorCoreTests/EFT/BoundedEFT.lean', ROOT / 'scripts/lean/BoundedEFTAudit.lean',
               ROOT / 'examples/BoundedEFT.lean', ROOT / 'data/regressions/eft-paper-cases.json',
               Path(__file__)]
    report = dict(status='passed', audit=audit,
                  backend='compiled Lean BitVec extraction and guards; native Float32 scalar addition',
                  preservation_theorem='TensorCore.EFMachine.tcEftWithLean_eq',
                  full_result_comparisons=len(requests) + len(controls),
                  error_preservation_controls=len(controls),
                  paper_blocks=len(corpus), arbitrary_D_blocks=len(cases) - len(corpus),
                  rounding_cases=len(rounds), branches=dict(branches), mismatches=0,
                  coefficient_width=576, common_grid_exponent=-272, seed=20260907,
                  source_sha256={str(p.relative_to(ROOT)): hashlib.sha256(p.read_bytes()).hexdigest()
                                 for p in sources})
    timing = dict(elapsed_seconds=round(time.perf_counter() - start, 3))
    (ROOT / 'tmp/timings').mkdir(parents=True, exist_ok=True)
    (ROOT / 'tmp/timings/bounded-eft.json').write_text(json.dumps(timing, indent=2) + '\n')
    (ROOT / 'data/regressions/bounded-eft-report.json').write_text(json.dumps(report, indent=2) + '\n')
    print(json.dumps(report, indent=2))


if __name__ == '__main__':
    main()
