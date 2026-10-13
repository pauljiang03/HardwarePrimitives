#!/usr/bin/env python3
"""Compare the Lean V100 FP16->FP32 block evaluator with GPU-measured vectors."""
if not __debug__:
    raise SystemExit('Run without python -O or PYTHONOPTIMIZE: these checks rely on assert.')
from fractions import Fraction as Q
from pathlib import Path
import json
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[1]
VECTORS = ROOT / 'vendor/matlab-tensor-core-v0.5/model_validation/V100/fp16'


def value(bits, frac, expbits, bias):
    sign = -1 if bits >> (frac + expbits) else 1
    e = (bits >> frac) & ((1 << expbits) - 1)
    m = bits & ((1 << frac) - 1)
    if e == (1 << expbits) - 1:
        raise ValueError('nonfinite')
    mant = Q(m) if e == 0 else Q((1 << frac) + m)
    return sign * mant * Q(2) ** ((1 - bias if e == 0 else e - bias) - frac)


def fp32_word_to_fp16(bits):
    """Exact conversion; fails if the FP32 word is not an FP16 value."""
    sign, e, m = bits >> 31, (bits >> 23) & 0xff, bits & 0x7fffff
    if e == 0xff:
        raise ValueError('nonfinite multiplicand')
    if e == 0:
        if m:
            raise ValueError('FP32 subnormal is not an FP16 value')
        half = sign << 15
    elif e - 127 >= -14:
        assert e - 127 <= 15 and m & 0x1fff == 0, hex(bits)
        half = (sign << 15) | ((e - 127 + 15) << 10) | (m >> 13)
    else:
        shift = 23 - (e - 127 + 24)
        full = (1 << 23) | m
        assert shift >= 0 and full & ((1 << shift) - 1) == 0, hex(bits)
        half = (sign << 15) | (full >> shift)
    assert value(half, 10, 5, 15) == value(bits, 23, 8, 127), hex(bits)
    return half


def read_hex_rows(path):
    return [[int(w, 16) for w in line.split()] for line in path.read_text().splitlines() if line.strip()]


def read_bin(path):
    return [int(line.strip(), 2) for line in path.read_text().splitlines() if line.strip()]


def main():
    a_rows = read_hex_rows(VECTORS / 'a_V100_fp16.txt')
    b_rows = read_hex_rows(VECTORS / 'b_V100_fp16.txt')
    c_words = read_bin(VECTORS / 'c_V100_fp32.txt')
    d_words = read_bin(VECTORS / 'd_V100_fp32.txt')
    n = len(d_words)
    assert len(a_rows) == len(b_rows) == len(c_words) == n and n > 0
    assert all(len(r) == 4 for r in a_rows + b_rows), 'V100 rows must hold K=4 products'
    coverage = dict(zero_operands=0, subnormal_operands=0, zero_c=0, subnormal_c=0)
    rows = []
    for a, b, c in zip(a_rows, b_rows, c_words):
        words = []
        for x, y in zip(a, b):
            for h in (fp32_word_to_fp16(x), fp32_word_to_fp16(y)):
                if h & 0x7fff == 0:
                    coverage['zero_operands'] += 1
                elif (h >> 10) & 0x1f == 0:
                    coverage['subnormal_operands'] += 1
                words.append(h)
        if c & 0x7fffffff == 0:
            coverage['zero_c'] += 1
        elif (c >> 23) & 0xff == 0:
            coverage['subnormal_c'] += 1
        rows.append(' '.join(f'{w:x}' for w in words + [c]))
    tmp = ROOT / 'tmp/validation'
    tmp.mkdir(parents=True, exist_ok=True)
    blocks = tmp / 'device-blocks.txt'
    blocks.write_text('\n'.join(rows) + '\n')
    proc = subprocess.run([str(ROOT / '.lake/build/bin/tc_trace'), '--file', str(blocks)],
                          check=True, text=True, capture_output=True)
    traces = [json.loads(line) for line in proc.stdout.splitlines()]
    assert len(traces) == n

    def q(text):
        num, den = text.split('/')
        return Q(int(num), int(den))

    mismatches, errors = [], 0
    exercised = dict(alignment_loss=0, output_loss=0, both_losses=0, mixed_signs=0,
                     denormalized_product=0, eta_from_c_only=0, corrected_differs_from_device=0)
    for i, (t, d, row) in enumerate(zip(traces, d_words, rows)):
        if 'error' in t:
            errors += 1
            mismatches.append((i, row, d, t))
            continue
        if t['bits'] != d:
            mismatches.append((i, row, d, t))
        align = any(q(r) != 0 for r in t['alignmentResiduals'])
        out = q(t['outputResidual']) != 0
        exercised['alignment_loss'] += align
        exercised['output_loss'] += out
        exercised['both_losses'] += align and out
        exercised['mixed_signs'] += len({c > 0 for c in t['coefficients'] if c}) > 1
        words = [int(w, 16) for w in row.split()]
        sig = lambda h: (h & 1023) if (h >> 10) & 31 == 0 else 1024 + (h & 1023)
        exercised['denormalized_product'] += any(
            sig(words[k]) * sig(words[k + 1]) >= 2 ** 21 for k in range(0, 8, 2))
        c_scale = ((words[8] >> 23) & 255) - 127
        exercised['eta_from_c_only'] += (t['alignExp'] is not None and t['alignExp'] == c_scale
                                         and all(s < c_scale for s in t['exponents']))
        exercised['corrected_differs_from_device'] += (
            t['correctedBits'] is not None and t['correctedBits'] != d)
    report = dict(source='MATLAB Tensor Core v0.5 model_validation/V100/fp16', profile='V100 FP16->FP32',
                  vectors=n, model_errors=errors, bit_mismatches=len(mismatches) - errors,
                  coverage=coverage, exercised=exercised,
                  method='Exact FP32-word to FP16 conversion, one evaluator call per row, bitwise output comparison')
    (ROOT / 'data/regressions/device-report.json').write_text(json.dumps(report, indent=2) + '\n')
    print(json.dumps(report, indent=2))
    for i, row, d, t in mismatches[:10]:
        print(f'row {i}: inputs {row}: device {d:08x} model {t}', file=sys.stderr)
    if mismatches:
        raise SystemExit(1)


if __name__ == '__main__':
    main()
