#!/usr/bin/env python3
"""Independent exact IEEE decoder, common-integer-grid alignment, neighbor oracle."""
if not __debug__:
    raise SystemExit('Run without python -O or PYTHONOPTIMIZE: these checks rely on assert.')
from fractions import Fraction as Q
from pathlib import Path
import json
import random
import subprocess

ROOT = Path(__file__).resolve().parents[1]
SEED = 20260905


def power(e):
    return Q(1 << e) if e >= 0 else Q(1, 1 << -e)


def ieee(bits, frac, expbits, bias):
    sign = -1 if bits >> (frac + expbits) else 1
    e = (bits >> frac) & ((1 << expbits) - 1)
    m = bits & ((1 << frac) - 1)
    if e == (1 << expbits) - 1:
        raise ValueError('nonfinite')
    return sign * (Q(m) if e == 0 else Q((1 << frac) + m)) * power(
        (1 - bias if e == 0 else e - bias) - frac)


def f32(bits):
    return ieee(bits, 23, 8, 127)


MAX32 = f32(0x7f7fffff)


def neighbors(x):
    """Search the ordered positive encoding space, without computing an exponent."""
    lo, hi = 0, 0x7f7fffff
    while lo < hi:
        mid = (lo + hi + 1) // 2
        if f32(mid) <= x:
            lo = mid
        else:
            hi = mid - 1
    return lo, min(lo + 1, 0x7f7fffff)


def round_oracle(x, nearest):
    # Public converter domain: do not infer an overflow policy from finite outputs.
    if abs(x) > MAX32:
        return None
    lo, hi = neighbors(abs(x))
    chosen = lo
    if nearest:
        dl, dh = abs(x) - f32(lo), f32(hi) - abs(x)
        if dh < dl or (dh == dl and lo % 2):
            chosen = hi
    return chosen | (0x80000000 if x < 0 else 0)


def scale(bits, frac, expbits, bias):
    e = bits >> frac & ((1 << expbits) - 1)
    return max(1, e) - bias


def block_oracle(words):
    pairs, cbits = list(zip(words[0:8:2], words[1:8:2])), words[8]
    try:
        values = [f32(cbits)]
        raw_scales = []
        active = [] if values[0] == 0 else [scale(cbits, 23, 8, 127)]
        for a, b in pairs:
            av, bv = ieee(a, 10, 5, 15), ieee(b, 10, 5, 15)
            # Lean represents a decoded zero with scale zero; nonzero operands retain their format scale.
            rho = (scale(a, 10, 5, 15) if av else 0) + (scale(b, 10, 5, 15) if bv else 0)
            raw_scales.append(rho)
            values.append(av * bv)
            if av * bv:
                active.append(rho)
    except ValueError:
        return {'error': 'TensorCore.ModelError.nonfiniteInput'}
    eta = max(active) if active else None
    qe = (eta if eta is not None else 0) - 23
    grid_units = 1 << (qe + 149)
    # All finite V100 terms are integer multiples of the FP32 minimum quantum.
    units = [v * (1 << 149) for v in values]
    assert all(u.denominator == 1 for u in units)
    coeff = [(1 if u >= 0 else -1) * (abs(u.numerator) // grid_units) for u in units]
    aligned = [Q(z * grid_units, 1 << 149) for z in coeff]
    acc = sum(aligned, Q(0))
    bits = round_oracle(acc, False)
    if bits is None:
        return {'error': 'TensorCore.ModelError.accumulatorOutOfRange'}
    ideal = sum(values, Q(0))
    residuals = [v - u for v, u in zip(values, aligned)]
    out_loss = acc - f32(bits)
    text = lambda q: f'{q.numerator}/{q.denominator}'
    return dict(bits=bits, alignExp=eta, alignGridExponent=qe, exponents=raw_scales,
                coefficients=coeff, ideal=text(ideal), accumulator=text(acc),
                alignmentResiduals=list(map(text, residuals)), outputResidual=text(out_loss),
                residual=text(ideal - f32(bits)), correctedBits=round_oracle(ideal, True))


def run_file(flag, path, rows):
    path.write_text('\n'.join(rows) + '\n')
    proc = subprocess.run([str(ROOT / '.lake/build/bin/tc_trace'), flag, str(path)],
                          check=True, text=True, capture_output=True)
    result = [json.loads(line) for line in proc.stdout.splitlines()]
    assert len(result) == len(rows)
    return result


def main():
    tmp = ROOT / 'tmp/validation'
    tmp.mkdir(parents=True, exist_ok=True)
    rng = random.Random(SEED)
    named = json.loads((ROOT / 'data/regressions/inputs.json').read_text())
    blocks = [[int(x, 16) for x in case['words']] for case in named]
    def finite(frac, exps):
        return (rng.randrange(2) << (frac + exps)) | rng.randrange(((1 << exps) - 1) << frac)
    for _ in range(512):
        blocks.append([finite(10, 5) for _ in range(8)] + [finite(23, 8)])
    for _ in range(128):
        a, b = finite(10, 5), finite(10, 5)
        blocks.append([a, b, a ^ 0x8000, b, finite(10, 5), finite(10, 5), 0, 0, finite(23, 8)])
    for _ in range(64):
        blocks.append([rng.randrange(1024) | (rng.randrange(2) << 15) for _ in range(8)]
                      + [rng.randrange(1 << 23)])
    for bad in [0x7c00, 0xfc00, 0x7e00]:
        blocks.append([bad, 0] + [0] * 7)
    actual = run_file('--file', tmp / 'blocks.txt', [' '.join(f'{x:x}' for x in b) for b in blocks])
    for i, (b, got) in enumerate(zip(blocks, actual)):
        want = block_oracle(b)
        assert got == want, (i, [hex(x) for x in b], got, want)
    anchors = {0, 1, 2, 0x7ffffe, 0x7fffff, 0x800000, 0x800001, 0x3f7fffff,
               0x3f800000, 0x3f800001, 0x3fffffff, 0x7f7ffffe}
    anchors.update((e << 23) - 1 for e in range(1, 255))
    anchors.update(rng.randrange(0x7f7fffff) for _ in range(100))
    rounds = [Q(0), MAX32, -MAX32, MAX32 + 1, -MAX32 - 1, Q(1) - 3 * power(-25),
              MAX32 + power(102), MAX32 + power(103), MAX32 + power(103) + 1, power(128) - 1, power(128),
              -(MAX32 + power(103)), -power(128), power(130)]
    for a in sorted(anchors):
        lo, hi = f32(a), f32(a + 1)
        for t in [Q(0), Q(1, 4), Q(1, 2), Q(3, 4)]:
            x = lo + t * (hi - lo)
            rounds.extend([x, -x])
    actual_r = run_file('--round-file', tmp / 'rounds.txt',
                        [f'{x.numerator} {x.denominator}' for x in rounds])
    for i, (x, got) in enumerate(zip(rounds, actual_r)):
        want = {'trunc': round_oracle(x, False), 'rne': round_oracle(x, True)}
        assert got == want, (i, str(x), got, want)
    report = dict(seed=SEED, blocks=len(blocks), rounding_cases=len(rounds),
                  rejected_blocks=sum('error' in x for x in actual),
                  mismatches=0, device_measurements=0,
                  method='Independent IEEE decoder, integer-grid alignment, encoding binary-search rounding')
    (ROOT / 'data/regressions/validation-report.json').write_text(json.dumps(report, indent=2) + '\n')
    expected = [dict(name=n['name'], trace=block_oracle(b)) for n, b in zip(named, blocks)]
    golden = ROOT / 'data/regressions/expected-traces.json'
    if golden.exists():
        assert json.loads(golden.read_text()) == expected, 'oracle traces drifted from the golden file'
    else:
        golden.write_text(json.dumps(expected, indent=2) + '\n')
    print(json.dumps(report, indent=2))


if __name__ == '__main__':
    main()
