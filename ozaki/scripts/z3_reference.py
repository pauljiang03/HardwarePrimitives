#!/usr/bin/env python3
"""Record the outputs of the Z3 Ozaki models on their own test matrices.

The Z3 models (`ozaki1/ozaki1.py` and `ozaki2/ozaki2.py` of a local clone)
emulate a binary32 4x4 GEMM on a matrix multiplier with fp16 inputs. This script imports both
modules from an unmodified clone, regenerates their two test cases exactly as their `main()` does
(`random.Random(2026)`, exponent spreads 1 and 6), runs `ozaki1_gemm` (four slices) and
`ozaki2_gemm` (four moduli), and prints every input and output as a binary32 bit pattern.

The result is `data/z3-reference.json`, which `tests/OzakiTCTests/Z3Matrices.lean` and
`tests/OzakiMCTests/Z3Matrices.lean` check against the Lean pipelines by kernel evaluation.
The Z3 proofs (`lemma_*`) are not run.

Usage (needs `pip install z3-solver`):

    python3 scripts/z3_reference.py /path/to/ozaki > data/z3-reference.json
"""
if not __debug__:
    raise SystemExit('Run without python -O: the Z3 models rely on their own checks.')
import importlib
import json
import random
import struct
import sys


def load(repo, name):
    sys.path.insert(0, f'{repo}/{name}')
    try:
        sys.modules.pop(name, None)
        return importlib.import_module(name)
    finally:
        sys.path.pop(0)


def bits(module, x):
    """binary32 bit pattern of a Z3 binary32 constant, checked to round-trip exactly."""
    q = module.to_frac(x)
    f = float(q)
    assert f == q and struct.unpack('>f', struct.pack('>f', f))[0] == f
    return '0x%08X' % struct.unpack('>I', struct.pack('>f', f))[0]


def main():
    repo = sys.argv[1]
    o1 = load(repo, 'ozaki1')
    o2 = load(repo, 'ozaki2')
    out = []
    rng = random.Random(2026)                       # as both models' main()
    for case, spread in [('narrow', 1), ('wide', 6)]:
        A = o1.random_matrix(rng, spread)
        B = o1.random_matrix(rng, spread)
        C1, gemms = o1.ozaki1_gemm(A, B, 4)
        A2 = [[o2.FPVal(float(o1.to_frac(x)), o2.FP32) for x in r] for r in A]
        B2 = [[o2.FPVal(float(o1.to_frac(x)), o2.FP32) for x in r] for r in B]
        C2, P, _ = o2.ozaki2_gemm(A2, B2)
        out.append({'case': case,
                    'A': [[bits(o1, x) for x in r] for r in A],
                    'B': [[bits(o1, x) for x in r] for r in B],
                    'ozaki1': [[bits(o1, x) for x in r] for r in C1], 'gemms1': gemms,
                    'ozaki2': [[bits(o2, x) for x in r] for r in C2], 'P': P})
    print(json.dumps(out, indent=1))


if __name__ == '__main__':
    main()
