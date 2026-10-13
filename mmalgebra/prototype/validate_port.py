"""Cross-check models.py against the Lean models, bit for bit, on random blocks.

  python3 validate_port.py gen N      -> writes validation/ValidateTC.lean, ValidateMC.lean and
                                         expected.json (N random blocks per variant)
  (run the two Lean files from mmalgebra/, saving stdout to validation/tc.out and mc.out)
  python3 validate_port.py check      -> compares, and fails on any mismatch

`python3 scripts/check.py --port` runs all three steps.
"""
import json
import random
import os
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from models import *  # noqa

HERE = os.path.join(os.path.dirname(os.path.abspath(__file__)), 'validation') + os.sep

TC_LEAN = {'V100 fp16': 'v100F16F32', 'A100 fp16': 'ampereF16F32', 'H100 fp16': 'hopperF16F32',
           'A100 bf16': 'a100BF16F32', 'H100 bf16': 'hopperBF16F32'}
MC_LEAN = {'CDNA1 fp16': 'cdna1F16', 'CDNA1 bf16': 'cdna1BF16', 'CDNA2 fp16': 'cdna2F16',
           'CDNA2 bf16': 'cdna2BF16', 'CDNA2 bf16_1k': 'cdna2BF16_1k', 'CDNA3 fp16': 'cdna3F16',
           'CDNA3 bf16': 'cdna3BF16'}


def rand_word(fmt, rng, center):
    """Random finite word; exponent field near `center` most of the time."""
    r = rng.random()
    if r < 0.08:
        return 0
    s = rng.getrandbits(1)
    emaxf = (1 << fmt.ebits) - 2
    if r < 0.15:
        E = 0  # subnormal
    elif r < 0.85:
        E = min(max(center + rng.randint(-3, 3), 1), emaxf)
    else:
        E = rng.randint(1, emaxf)
    M = rng.getrandbits(fmt.mbits)
    if rng.random() < 0.3:
        M &= ~((1 << max(fmt.mbits - 3, 0)) - 1)  # few significant bits
    return (s << (fmt.ebits + fmt.mbits)) | (E << fmt.mbits) | M


def rand_c(rng, scale_e):
    r = rng.random()
    if r < 0.2:
        return 0
    s = rng.getrandbits(1)
    E = min(max(scale_e + 127 + rng.randint(-30, 30), 0), 254)
    M = rng.getrandbits(23)
    if rng.random() < 0.4:
        M &= ~((1 << 18) - 1)
    return (s << 31) | (E << 23) | M


def gen(n):
    os.makedirs(HERE, exist_ok=True)
    rng = random.Random(20261012)
    cases = []
    for P in ALL:
        for _ in range(n):
            center = P.fmt.bias + rng.randint(-6, 6)
            prods = [(rand_word(P.fmt, rng, center), rand_word(P.fmt, rng, center)) for _ in range(P.K)]
            ce = 2 * (center - P.fmt.bias) + rng.randint(-3, 3)
            c = rand_c(rng, ce)
            try:
                exp = block(P, prods, c)
            except ModelError as e:
                exp = 'err'
            cases.append((P.name, prods, c, exp))
    json.dump(cases, open(HERE + 'expected.json', 'w'))
    for lib, table, fname, mk in [
        ('TensorCore', TC_LEAN, 'ValidateTC.lean',
         lambda prof, prods, c: f'(evalBlock (p := {prof}) ⟨[{", ".join(f"({a}, {b})" for a, b in prods)}], {c}⟩).toOption.map (fun t => t.output.bits.toNat)'),
        ('MatrixCore', MC_LEAN, 'ValidateMC.lean',
         lambda prof, prods, c: f'(blockBits (P := {prof}) ⟨[{", ".join(str(a) for a, _ in prods)}], [{", ".join(str(b) for _, b in prods)}], {c}⟩).toOption.map BitVec.toNat'),
    ]:
        lines = [f'import {lib}', f'open {lib}', '']
        rows = [mk(table[name], prods, c) for (name, prods, c, _) in cases if name in table]
        # print in chunks to keep elaboration light
        for i in range(0, len(rows), 50):
            chunk = rows[i:i + 50]
            lines.append('#eval ([' + ',\n  '.join(chunk) + '] : List (Option Nat))')
        open(HERE + fname, 'w').write('\n'.join(lines) + '\n')


def parse(path):
    txt = open(path).read()
    out = []
    import re
    for m in re.finditer(r'\[([^\[\]]*)\]', txt):
        body = m.group(1)
        for tok in body.split(','):
            tok = tok.strip()
            if not tok:
                continue
            if tok == 'none':
                out.append('err')
            else:
                out.append(int(tok.replace('some', '').strip()))
    return out


def check():
    cases = json.load(open(HERE + 'expected.json'))
    tc = parse(HERE + 'tc.out')
    mc = parse(HERE + 'mc.out')
    ti = mi = 0
    bad = 0
    per = {}
    for (name, prods, c, exp) in cases:
        if name in TC_LEAN:
            got = tc[ti]; ti += 1
        else:
            got = mc[mi]; mi += 1
        ok = got == exp
        per.setdefault(name, [0, 0])
        per[name][0] += ok
        per[name][1] += 1
        if not ok:
            bad += 1
            if bad < 10:
                print('MISMATCH', name, prods, hex(c), exp, got)
    for k, v in per.items():
        print(f'{k:16s} {v[0]}/{v[1]}')
    if bad or ti != len(tc) or mi != len(mc):
        raise SystemExit(f'FAIL: {bad} mismatches; outputs read {ti}/{len(tc)} and {mi}/{len(mc)}')
    print(f'ok   {len(cases)} blocks agree bit for bit with the Lean models')


if __name__ == '__main__':
    if sys.argv[1] == 'gen':
        gen(int(sys.argv[2]))
    else:
        check()
