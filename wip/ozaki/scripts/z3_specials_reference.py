#!/usr/bin/env python3
"""Record the outputs of the Z3 ADP model on inputs with IEEE special values.

The Z3 model of NVIDIA's ADP (`ozaki-NVIDIA/adp.py` of a local clone) falls back to native binary64
GEMM (`acc = acc + A[i][t] * B[t][j]` from `acc = 0.0`) when an input is Inf or NaN, and returns
`±Inf` when an emulated product overflows. This script imports `adp.py` and the data generators of
`tests.py` from an unmodified clone, runs `adp.adp` with the default configuration on three cases,
and prints every input and output as a binary64 bit pattern, with the path:

* `nonfinite`: the non-finite case of `z3-adp-reference.json` (an Inf in `A`), whose outputs that
  file does not record;
* `nan`: a NaN in `A`;
* `overflow`: finite inputs whose products overflow on the emulated path (`[T.10]`), and a row
  whose products cancel exactly.

The result is `data/z3-specials-reference.json`, which `tests/OzakiTCTests/Specials.lean` checks
against `Ozaki.TC.adpIEEE` by kernel evaluation, NaN compared by class.

Usage (needs `pip install z3-solver`):

    python3 scripts/z3_specials_reference.py /path/to/ozaki > data/z3-specials-reference.json
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
    nan = tests.rnd(4, 41)
    nan[0][1] = math.nan
    cases = [
        ('nonfinite', nonfinite, tests.rnd(4, 32)),
        ('nan', nan, tests.rnd(4, 42)),
        ('overflow', [[1e300, 1e300], [1.0, 2.0]], [[1e10, 1.0], [1e10, -1.0]]),
    ]
    out = []
    for name, A, B in cases:
        C, info = adp.adp(A, B)
        out.append({'case': name, 'path': info['path'],
                    'A': [[bits(x) for x in r] for r in A],
                    'B': [[bits(x) for x in r] for r in B],
                    'C': [[bits(x) for x in r] for r in C]})
    print(json.dumps(out, indent=1))


if __name__ == '__main__':
    main()
