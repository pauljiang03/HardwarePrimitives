#!/usr/bin/env python3
"""Record the outputs of the Z3 ADP model on small test matrices.

The Z3 model of NVIDIA's ADP (`ozaki-NVIDIA/adp.py` of a local clone)
emulates binary64 GEMM on an INT8 matrix multiplier with ESC-driven slicing, and falls back to
native binary64 GEMM for Inf/NaN inputs or when emulation would be uneconomic. This script imports
`adp.py` and the data generators of `tests.py` from an unmodified clone, runs `adp.adp` with the
default configuration (block 2, zeros as -inf, remapped slices, speed ratio 100) on a few small
cases, and prints every input and output as a binary64 bit pattern, with the path, the matrix
ESC, the width `W` and the slice count.

The result is `data/z3-adp-reference.json`, which `tests/OzakiTCTests/ADPMatrices.lean` checks
against `Ozaki.TC.adp` by kernel evaluation. The cases cover both paths: U(0,1) and U(-1,1)
inputs and a Test 2 matrix with a small exponent range are emulated; a Test 2 matrix with a wide
exponent range falls back to native binary64; a matrix with an Inf takes the non-finite path.

Usage (needs `pip install z3-solver`):

    python3 scripts/z3_adp_reference.py /path/to/ozaki > data/z3-adp-reference.json
"""
if not __debug__:
    raise SystemExit('Run without python -O: the Z3 model relies on its own checks.')
import importlib
import json
import math
import struct
import sys

sys.dont_write_bytecode = True        # leave the clone untouched


def load(repo):
    sys.path.insert(0, f'{repo}/ozaki-NVIDIA')
    try:
        for name in ('adp', 'lemmas', 'tests'):
            sys.modules.pop(name, None)
        return importlib.import_module('adp'), importlib.import_module('tests')
    finally:
        sys.path.pop(0)


def bits(x):
    """binary64 bit pattern of a Python float."""
    return '0x%016X' % struct.unpack('>Q', struct.pack('>d', x))[0]


def main():
    repo = sys.argv[1]
    adp, tests = load(repo)
    nonfinite = tests.rnd(4, 31)
    nonfinite[1][2] = math.inf
    cases = [
        ('uniform', tests.rnd(4, 0, 0.0, 1.0), tests.rnd(4, 50, 0.0, 1.0)),
        ('signed', tests.rnd(4, 11), tests.rnd(4, 12)),
        ('test2_b2', *tests.gen_test2(4, 2)[:2]),
        ('test2_b64', *tests.gen_test2(8, 64)[:2]),
        ('nonfinite', nonfinite, tests.rnd(4, 32)),
    ]
    out = []
    for name, A, B in cases:
        C, info = adp.adp(A, B)
        entry = {'case': name, 'path': info['path'],
                 'A': [[bits(x) for x in r] for r in A],
                 'B': [[bits(x) for x in r] for r in B]}
        if info['path'] != 'native-nonfinite':
            entry['C'] = [[bits(x) for x in r] for r in C]
        for key in ('esc', 'W', 'slices'):
            if key in info and info[key] is not None:
                entry[key] = info[key]
        out.append(entry)
    print(json.dumps(out, indent=1))


if __name__ == '__main__':
    main()
