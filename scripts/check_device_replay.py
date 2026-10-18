#!/usr/bin/env python3
"""Replay recorded Ada, L40S, H100, H200 and B200 outputs through the Lean models and descriptors."""
if not __debug__:
    raise SystemExit('Run without python -O or PYTHONOPTIMIZE: these checks rely on assert.')
from fractions import Fraction as Q
from pathlib import Path
import hashlib
import json
import subprocess
import sys

from check_device import fp32_word_to_fp16, read_bin, read_hex_rows, value

ROOT = Path(__file__).resolve().parents[1]
VENDOR = ROOT / 'vendor/matlab-tensor-core-79143bd'
VENDOR_V01 = ROOT / 'vendor/matlab-tensor-core-v0.1'
BASE = VENDOR / 'model_validation'
FEATURES = ROOT / '.lake/build/bin/tc_features'
GPUS = ['Ada', 'L40S', 'H100', 'H200', 'B200']
FORMATS = ['fp16', 'bf16', 'tf32', 'E4M3', 'E5M2']
ARCH = {'Ada': 'ada', 'L40S': 'ada', 'H100': 'hopper', 'H200': 'hopper', 'B200': 'blackwell'}
# Descriptors of the FP16, BF16 and TF32 rows: Ada has A100's features, H200 and B200 H100's.
DESCRIPTOR = {('ada', 'fp16'): 'a100-f16', ('ada', 'bf16'): 'a100-bf16', ('ada', 'tf32'): 'a100-tf32',
              ('hopper', 'fp16'): 'hopper-f16', ('hopper', 'bf16'): 'hopper-bf16',
              ('hopper', 'tf32'): 'hopper-tf32-wmma', ('blackwell', 'fp16'): 'hopper-f16',
              ('blackwell', 'bf16'): 'hopper-bf16', ('blackwell', 'tf32'): 'hopper-tf32-wmma'}
NFMA = {('ada', 'fp16'): 8, ('ada', 'bf16'): 8, ('ada', 'tf32'): 4, ('hopper', 'fp16'): 16,
        ('hopper', 'bf16'): 16, ('hopper', 'tf32'): 4, ('blackwell', 'fp16'): 16,
        ('blackwell', 'bf16'): 16, ('blackwell', 'tf32'): 4, ('ada', 'E4M3'): 16, ('ada', 'E5M2'): 16,
        ('hopper', 'E4M3'): 32, ('hopper', 'E5M2'): 32, ('blackwell', 'E4M3'): 32,
        ('blackwell', 'E5M2'): 32}
FP8 = {'E4M3': (3, 4, 7), 'E5M2': (2, 5, 15)}
NAME = {'fp16': 'f16', 'bf16': 'bf16', 'tf32': 'tf32', 'E4M3': 'e4m3', 'E5M2': 'e5m2'}
# (mantissa bits, exponent bits, bias) of the operand words passed to Lean.
LAYOUT = {'fp16': (10, 5, 15), 'bf16': (7, 8, 127), 'tf32': (23, 8, 127), 'E4M3': (3, 4, 7),
          'E5M2': (2, 5, 15)}
# Minimum alignment exponents of the FP16, BF16 and TF32 models; FP8 has none (Table 3).
EALIGNMIN = {'ada': -132, 'hopper': -133, 'blackwell': -133}


def scale(bits, fmt):
    frac, exps, bias = LAYOUT[fmt]
    return max((bits >> frac) & ((1 << exps) - 1), 1) - bias


def align_exp(words, c, fmt):
    """Largest exponent of a nonzero term: c, and each product in denormalized form."""
    exps = [scale(c, 'tf32')] if c & 0x7fffffff else []
    frac, exps_bits, _ = LAYOUT[fmt]
    nonzero = lambda w: w & ((1 << (frac + exps_bits)) - 1) != 0
    for x, y in zip(words[::2], words[1::2]):
        if nonzero(x) and nonzero(y):
            exps.append(scale(x, fmt) + scale(y, fmt))
    return max(exps) if exps else None


def fp8_value(bits, fmt):
    """Independent decoder (E4M3: no infinities, NaNs only S.1111.111); None for NaN or infinity."""
    frac, exps, bias = FP8[fmt]
    sign = -1 if bits >> 7 else 1
    e, m = (bits >> frac) & ((1 << exps) - 1), bits & ((1 << frac) - 1)
    if fmt == 'E5M2' and e == 31:
        return None
    if fmt == 'E4M3' and e == 15 and m == 7:
        return None
    sig = Q(m) if e == 0 else Q((1 << frac) + m)
    return sign * sig * Q(2) ** ((1 if e == 0 else e) - bias - frac)


TABLES = {fmt: {} for fmt in FP8}
for _fmt in FP8:
    for _bits in range(256):
        _v = fp8_value(_bits, _fmt)
        if _v is not None and not (_v == 0 and _bits >> 7):
            assert _v not in TABLES[_fmt], (_fmt, _bits)
            TABLES[_fmt][_v] = _bits


def fp32_word_to_fp8(word, fmt):
    """The FP8 word of an FP32 word holding an FP8 value; fails if the value is not one."""
    v = value(word, 23, 8, 127)
    if v == 0:
        return 0x80 if word >> 31 else 0
    bits = TABLES[fmt][v]
    assert fp8_value(bits, fmt) == v, hex(word)
    return bits


def operand(word, fmt):
    """Lean input word and its kind: zero, subnormal, top (E4M3's top binade) or normal."""
    if fmt == 'fp16':
        h = fp32_word_to_fp16(word)
        kind = 'zero' if h & 0x7fff == 0 else 'subnormal' if (h >> 10) & 0x1f == 0 else 'normal'
        return h, kind
    if fmt == 'bf16':
        assert word & 0xffff == 0, f'not a BF16 value: {word:08x}'
        h = word >> 16
        kind = 'zero' if h & 0x7fff == 0 else 'subnormal' if (h >> 7) & 0xff == 0 else 'normal'
        return h, kind
    if fmt == 'tf32':
        assert word & 0x1fff == 0, f'not a TF32 value: {word:08x}'
        kind = ('zero' if word & 0x7fffffff == 0 else
                'subnormal' if (word >> 23) & 0xff == 0 else 'normal')
        return word, kind
    b = fp32_word_to_fp8(word, fmt)
    frac, exps, _ = FP8[fmt]
    e = (b >> frac) & ((1 << exps) - 1)
    kind = ('zero' if b & 0x7f == 0 else 'subnormal' if e == 0 else
            'top' if fmt == 'E4M3' and e == 15 else 'normal')
    return b, kind


def run(lines, filename):
    path = ROOT / 'tmp/validation' / filename
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text('\n'.join(lines) + '\n')
    proc = subprocess.run([str(FEATURES), '--file', str(path)], check=True, text=True,
                          capture_output=True)
    out = [json.loads(line) for line in proc.stdout.splitlines()]
    assert len(out) == len(lines)
    return out


def check_decoders():
    """All 256 words of each FP8 format, Lean's decoder against the independent one."""
    lines, expected = [], []
    for fmt, name in [('E4M3', 'e4m3'), ('E5M2', 'e5m2')]:
        for bits in range(256):
            lines.append(f'decode {name} {bits}')
            v = fp8_value(bits, fmt)
            expected.append(None if v is None else f'{v.numerator}/{v.denominator}')
    got = [r['value'] for r in run(lines, 'fp8-decode.txt')]
    bad = [(line, g, e) for line, g, e in zip(lines, got, expected) if g != e]
    assert not bad, bad[:5]
    return dict(words=len(lines), mismatches=0,
                nonfinite={'E4M3': sum(fp8_value(b, 'E4M3') is None for b in range(256)),
                           'E5M2': sum(fp8_value(b, 'E5M2') is None for b in range(256))},
                largest={'E4M3': str(max(TABLES['E4M3'])), 'E5M2': str(max(TABLES['E5M2']))})


def main():
    pins = json.loads((VENDOR / 'SOURCES.json').read_text())
    for name, expected in pins['sha256'].items():
        assert hashlib.sha256((VENDOR / name).read_bytes()).hexdigest() == expected, name
    decoders = check_decoders()
    report, failures, totals, distinct = {}, [], dict(vectors=0, mismatches=0), {}
    for fmt in FORMATS:
        for gpu in GPUS:
            arch = ARCH[gpu]
            folder = BASE / gpu / fmt
            a_rows = read_hex_rows(folder / f'a_{gpu}_{fmt}.txt')
            b_rows = read_hex_rows(folder / f'b_{gpu}_{fmt}.txt')
            c_words = read_bin(folder / f'c_{gpu}_fp32.txt')
            d_words = read_bin(folder / f'd_{gpu}_fp32.txt')
            n = len(d_words)
            k = len(a_rows[0])
            assert len(a_rows) == len(b_rows) == len(c_words) == n and n > 0
            assert all(len(r) == k for r in a_rows + b_rows), f'{gpu} {fmt} rows must hold K={k}'
            fp8 = fmt in FP8
            c_file = list(c_words)
            if fp8 and arch == 'hopper':
                convention = ('c = 0: the Hopper block FMA from a zero accumulator, as the toolbox '
                              'reads these rows (wgmma with D = 0); the c file is not used')
                c_words = [0] * n
            elif fp8 and arch == 'blackwell':
                convention = ('recorded with the toolbox\'s mma.sync harness: c added after the '
                              'products in FP32 with round-to-nearest-even (mmaSyncFP8Dot; '
                              'also Model.dotThenAdd)')
            else:
                convention = 'c accumulated in the block FMA'
            model = f'{arch}-{NAME[fmt]}' + ('-wmma' if fmt == 'tf32' and arch != 'ada' else '')
            model_cmd = 'dot-then-add' if fp8 and arch == 'blackwell' else 'dot'
            if fp8:
                descriptor = model + ('-then-add' if arch == 'blackwell' else '')
                descriptor_cmd = 'chain'
            else:
                descriptor, descriptor_cmd = DESCRIPTOR[(arch, fmt)], 'block'
            kinds = dict(zero=0, subnormal=0, top=0, normal=0)
            model_lines, descriptor_lines, mma_lines, binding = [], [], [], 0
            for a, b, c in zip(a_rows, b_rows, c_words):
                words = []
                for x in [w for pair in zip(a, b) for w in pair]:
                    word, kind = operand(x, fmt)
                    kinds[kind] += 1
                    words.append(word)
                eta = align_exp(words, c, fmt)
                binding += not fp8 and eta is not None and eta < EALIGNMIN[arch]
                row = ' '.join(map(str, words + [c]))
                model_lines.append(f'{model_cmd} {model} {row}')
                descriptor_lines.append(f'{descriptor_cmd} {descriptor} {row}')
                mma_lines.append(f'mma-sync {NAME[fmt]} 32 {c} ' + ' '.join(map(str, words)))
            key = f'{gpu}-{fmt}'
            distinct.setdefault(fmt, set()).update(
                (tuple(a), tuple(b), c, d, convention)
                for a, b, c, d in zip(a_rows, b_rows, c_words, d_words))
            models = run(model_lines, f'replay-{key}-model.txt')
            descriptors = run(descriptor_lines, f'replay-{key}-descriptor.txt')
            errors = sum('error' in r for r in models)
            mismatches = [(i, r.get('bits'), d) for i, (r, d) in enumerate(zip(models, d_words))
                          if r.get('bits') != d]
            descriptor_mismatches = sum(r.get('bits') != d for r, d in zip(descriptors, d_words))
            disagreements = sum(r.get('bits') != s.get('bits') for r, s in zip(models, descriptors))
            report[key] = dict(
                model=f'{model_cmd} {model}', descriptor=f'{descriptor_cmd} {descriptor}',
                products_per_row=k, nfma=NFMA[(arch, fmt)],
                block_fmas_per_row=-(-k // NFMA[(arch, fmt)]), accumulator_input=convention,
                vectors=n, model_errors=errors, bit_mismatches=len(mismatches) - errors,
                descriptor_bit_mismatches=descriptor_mismatches,
                descriptor_model_disagreements=disagreements,
                operands=kinds, rows_where_eAlignMin_binds=binding,
                c=dict(zero=sum(c & 0x7fffffff == 0 for c in c_words),
                       subnormal=sum(c & 0x7fffffff != 0 and (c >> 23) & 0xff == 0 for c in c_words)))
            if fp8 and arch != 'blackwell':
                # Negative control: the same model with an FP32 block output.
                control = run([line.replace(f' {model} ', f' {model}-fp32-output ', 1)
                               for line in model_lines], f'replay-{key}-control.txt')
                report[key]['fp32_output_control_mismatches'] = sum(
                    r.get('bits') != d for r, d in zip(control, d_words))
                assert report[key]['fp32_output_control_mismatches'] > 0, key
            if fp8 and arch == 'blackwell':
                # Control: the B200 block FMA holding c (tcgen05.mma) disagrees with these rows.
                mma = run(mma_lines, f'replay-{key}-mma-sync.txt')
                mma_mismatches = sum(r.get('bits') != d for r, d in zip(mma, d_words))
                report[key]['mma_sync_model'] = f'mma-sync {NAME[fmt]} 32 (mmaSyncFP8Dot)'
                report[key]['mma_sync_model_bit_mismatches'] = mma_mismatches
                totals['mismatches'] += mma_mismatches
                inside = run([line.replace('dot-then-add ', 'dot ', 1) for line in model_lines],
                             f'replay-{key}-c-inside-control.txt')
                report[key]['c_inside_control_mismatches'] = sum(
                    r.get('bits') != d for r, d in zip(inside, d_words))
                assert report[key]['c_inside_control_mismatches'] > 0, key
            totals['vectors'] += n
            totals['mismatches'] += len(mismatches) + descriptor_mismatches + disagreements
            failures += [(key, *m) for m in mismatches]
    # Release v0.1: H100 and H200 FP8 outputs for the same inputs, through the mma.sync model.
    pins01 = json.loads((VENDOR_V01 / 'SOURCES.json').read_text())
    for name, expected in pins01['sha256'].items():
        assert hashlib.sha256((VENDOR_V01 / name).read_bytes()).hexdigest() == expected, name
    for gpu in ['H100', 'H200']:
        for fmt in ['E4M3', 'E5M2']:
            folder = BASE / gpu / fmt
            a_rows = read_hex_rows(folder / f'a_{gpu}_{fmt}.txt')
            b_rows = read_hex_rows(folder / f'b_{gpu}_{fmt}.txt')
            c_words = read_bin(folder / f'c_{gpu}_fp32.txt')
            d_words = read_bin(VENDOR_V01 / f'model_validation/{gpu}/{fmt}/d_{gpu}_fp32.txt')
            assert len(d_words) == len(a_rows) == len(c_words)
            mma_lines, control_lines = [], []
            for a, b, c in zip(a_rows, b_rows, c_words):
                words = [operand(x, fmt)[0] for pair in zip(a, b) for x in pair]
                mma_lines.append(f'mma-sync {NAME[fmt]} 32 {c} ' + ' '.join(map(str, words)))
                control_lines.append(f'dot hopper-{NAME[fmt]} ' + ' '.join(map(str, words + [0])))
            key = f'v0.1-{gpu}-{fmt}'
            mma = run(mma_lines, f'replay-{key}-mma-sync.txt')
            control = run(control_lines, f'replay-{key}-control.txt')
            mismatches = sum(r.get('bits') != d for r, d in zip(mma, d_words))
            report[key] = dict(
                model=f'mma-sync {NAME[fmt]} 32 (mmaSyncFP8Dot)', vectors=len(d_words),
                accumulator_input='c from the c file, added after the products (mma.sync)',
                bit_mismatches=mismatches,
                hopper_13bit_zero_c_control_mismatches=sum(
                    r.get('bits') != d for r, d in zip(control, d_words)))
            assert report[key]['hopper_13bit_zero_c_control_mismatches'] > 0, key
            totals['vectors'] += len(d_words)
            totals['mismatches'] += mismatches
    # Recorded files that the v0.5 replay already covers, by hash.
    v05 = json.loads((ROOT / 'vendor/SOURCES.json').read_text())['sha256']
    v05_hashes = {(n.split('/')[1], n.split('/')[2], n.split('/')[-1][0]): h for n, h in v05.items()
                  if n.startswith('model_validation/') and n.count('/') == 3}
    same = []
    for key in [k for k in report if '-' in k and not k.startswith('v0.1-')]:
        gpu, fmt = key.split('-')
        names = {r: f'model_validation/{gpu}/{fmt}/{r}_{gpu}_' + (fmt if r in 'ab' else 'fp32') + '.txt'
                 for r in 'abcd'}
        if all(v05_hashes.get((gpu, fmt, r)) == pins['sha256'][n] for r, n in names.items()):
            same.append(key)
    report['fp8_decoders'] = decoders
    report['totals'] = dict(totals, fp16_bf16_tf32=sum(v['vectors'] for k, v in report.items()
                                                       if k.split('-')[-1] in ('fp16', 'bf16', 'tf32')),
                            fp8=sum(v['vectors'] for k, v in report.items()
                                    if k.split('-')[-1] in ('E4M3', 'E5M2')
                                    and not k.startswith('v0.1-')),
                            fp8_release_v0_1=sum(v['vectors'] for k, v in report.items()
                                                 if k.startswith('v0.1-')),
                            distinct_rows={fmt: len(rows) for fmt, rows in distinct.items()},
                            identical_to_v0_5=same)
    report['notes'] = ['The L40S files are byte-identical to the Ada files.',
                       'H100 and H200 share their FP8 inputs and, with c = 0, their FP8 outputs.',
                       'distinct_rows counts the rows that differ in inputs, c, output or c convention.',
                       'The TF32 inputs are the V100 FP16 inputs of v0.5: FP16 values.',
                       'No recorded E4M3 operand lies in the top binade (256 to 448); the decoder '
                       'comparison covers it.',
                       'Release v0.1 holds H100 and H200 FP8 outputs for the same inputs; from v0.3 '
                       'on the toolbox holds the outputs replayed above with c = 0.',
                       'No recorded output has c inside the FP8 block FMA of wgmma or tcgen05.mma; '
                       'scripts/check_mmasim.py cross-checks those against MMA-Sim.']
    report['method'] = ('One model and one descriptor evaluation per row, bitwise comparison with the '
                        'recorded output and with each other; no new GPU measurements')
    (ROOT / 'data/regressions/device-replay-report.json').write_text(json.dumps(report, indent=2) + '\n')
    print(json.dumps(report, indent=2))
    for key, i, got, want in failures[:10]:
        print(f'{key} row {i}: model {got} device {want:08x}', file=sys.stderr)
    if totals['mismatches']:
        raise SystemExit(1)


if __name__ == '__main__':
    main()
