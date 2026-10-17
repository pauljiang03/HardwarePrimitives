#!/usr/bin/env python3
"""Record the Z3 ADP model's zero-policy cases and two constructed ones.

The Z3 model of NVIDIA's ADP (`ozaki-NVIDIA/adp.py` of a local clone) chooses how the coarsened ESC
treats zeros (`zero_policy`): `neg_inf` (the paper's, safe), `skip` and `field0` (unsafe). Its
`[T.12]` test shows that the unsafe policies are caught by the assertion `[X.4]` on
`tests.zeros_case()` and `tests.field0_case()`. This script imports the model from an unmodified
clone and records, as binary64 bit patterns:

* `zeros_case` and `field0_case`: the inputs, the `neg_inf` run (path, ESC, `W`, slices, `C`), and
  the label that stops each unsafe policy;
* `skip_breaks` and `field0_breaks`: a row and column, constructed here, on which the unsafe
  policy's estimate is far too low (`skip`: a large entry beside a zero; `field0`: a zero paired
  with a huge entry), with the same records.

`tests/OzakiTCTests/ADPZeroPolicy.lean` runs the Lean routine with each policy on these inputs.
The model's assertions stop the unsafe policies; the Lean routine shows what they would compute.

Usage (needs `pip install z3-solver`):

    python3 scripts/z3_adp_zero_policies.py /path/to/ozaki > data/z3-adp-zero-policies.json
"""
if not __debug__:
    raise SystemExit('Run without python -O: the Z3 model relies on its own checks.')
import importlib
import json
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


def matrix(M):
    return [[bits(x) for x in r] for r in M]


def record(adp, A, B):
    entry = {'A': matrix(A), 'B': matrix(B)}
    C, info = adp.adp(A, B, adp.Config(zero_policy='neg_inf'))
    entry['neg_inf'] = {'path': info['path'], 'C': matrix(C)}
    for key in ('esc', 'W', 'slices'):
        if key in info and info[key] is not None:
            entry['neg_inf'][key] = info[key]
    for policy in ('skip', 'field0'):
        try:
            adp.adp(A, B, adp.Config(zero_policy=policy))
            entry[policy] = None
        except adp.CheckFailure as ex:
            entry[policy] = ex.label
    return entry


def main():
    repo = sys.argv[1]
    adp, tests = load(repo)
    out = {}
    out['zeros_case'] = record(adp, *tests.zeros_case())
    out['field0_case'] = record(adp, *tests.field0_case())
    # skip: the zero of y beside 1.75 hides the small exponent 0 of x's second entry
    out['skip_breaks'] = record(adp, [[1024.0, 2.0 - 2.0 ** -52, 0.0, 0.0]],
                                [[0.0], [1.75], [0.0], [0.0]])
    # field0: y's zero, read as exponent -1022, pairs with x's 2^1000
    out['field0_breaks'] = record(adp, [[1.5 * 2.0 ** 1000, 1.25 * 2.0 ** -20, 0.0, 0.0]],
                                  [[0.0], [1.75 * 2.0 ** -1000], [0.0], [0.0]])
    print(json.dumps(out, indent=1))


if __name__ == '__main__':
    main()
