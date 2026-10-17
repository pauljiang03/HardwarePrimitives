#!/usr/bin/env python3
"""Record the Z3 ADP model's test-level cases ([T.1]-[T.12]).

The Z3 model of NVIDIA's ADP (`ozaki-NVIDIA/adp.py` of a local clone) has fourteen test-level
checks in `tests.py`. This script imports `adp.py` and the data generators of `tests.py` from an
unmodified clone and reruns the inputs of the checks that concern particular matrices, recording
every input and output as a binary64 bit pattern:

* T.1: the decode edge values, with the model's `(m, e)`;
* T.2: the paper's remap example;
* T.4: the `signed` case with the three slice encodings (path, slice count, C);
* T.7: two wide-exponent cases (spans 3 and 10);
* T.8: Test 2 with n = 8 and b = 0 and b = 64, through ADP and through a fixed 55-bit emulation
  without guardrails, with whether that emulation passes the Grade-A check P.2;
* T.10: the emergent-overflow case (all entries 1e200);
* T.11: the subnormal case;
* T.12: the label that catches the unsafe zero policies, and the identity case.

The result is `data/z3-adp-labels.json`, which `tests/OzakiTCTests/ADPLabels.lean` checks against
the Lean routine by kernel evaluation. The recorded cases of `scripts/z3_adp_reference.py` are not
repeated.

Usage (needs `pip install z3-solver`):

    python3 scripts/z3_adp_labels.py /path/to/ozaki > data/z3-adp-labels.json
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


def run(adp, A, B, cfg=None):
    C, info = adp.adp(A, B) if cfg is None else adp.adp(A, B, cfg)
    entry = {'path': info['path'], 'A': matrix(A), 'B': matrix(B)}
    if info['path'] != 'native-nonfinite':
        entry['C'] = matrix(C)
    for key in ('esc', 'W', 'slices'):
        if key in info and info[key] is not None:
            entry[key] = info[key]
    return entry


def main():
    repo = sys.argv[1]
    adp, tests = load(repo)
    out = {}

    vals = [1.0, -1.5, 0.1, 2.0 ** -1074, 2.0 ** -1022, 3e-310, -(2 - 2.0 ** -52) * 2.0 ** 1023]
    out['t1_decode'] = [{'x': bits(v), 'm': adp.decode(v)[0], 'e': adp.decode(v)[1]} for v in vals]
    out['t1_zeros'] = [{'x': bits(v), 'm': adp.decode(v)[0], 'e': adp.decode(v)[1]}
                       for v in (0.0, -0.0)]

    N = 123 * 256 + 200
    out['t2_remap'] = {'N': N, 'floor_u8': adp.encode(N, 2, 'floor_u8'),
                       'remap': adp.encode(N, 2, 'remap')}

    A, B = tests.rnd(4, 11), tests.rnd(4, 12)
    out['t4_encodings'] = {'A': matrix(A), 'B': matrix(B), 'runs': []}
    for enc in ('remap', 'floor_u8', 'naive_s8'):
        C, info = adp.adp(A, B, adp.Config(encoding=enc))
        out['t4_encodings']['runs'].append({'encoding': enc, 'path': info['path'],
                                            'slices': info['slices'], 'C': matrix(C)})

    out['t7_wide'] = []
    for span in (3, 10):
        e = run(adp, tests.rnd_wide(4, 21, span), tests.rnd_wide(4, 22, span))
        e['span'] = span
        out['t7_wide'].append(e)

    out['t8_test2'] = []
    for b in (0, 64):
        A, B, _ = tests.gen_test2(8, b)
        e = run(adp, A, B)
        e['b'] = b
        Coff, ioff = adp.adp(A, B, adp.Config(guardrails=False, fixed_W=55))
        try:
            adp.verify(A, B, Coff, ioff, check_p1=False)
            ok = True
        except adp.CheckFailure as ex:
            assert ex.label == 'P.2'
            ok = False
        e['fixed55'] = {'slices': ioff['slices'], 'C': matrix(Coff), 'gradeA': ok}
        out['t8_test2'].append(e)

    big = [[1e200] * 4 for _ in range(4)]
    out['t10_overflow'] = run(adp, big, big)

    A = [[2.0 ** -1060, 3.0 * 2.0 ** -1070, 1.0 * 2.0 ** -1050, 2.0 ** -1074]] * 4
    B = [[2.0 ** 1000, 1.5 * 2.0 ** 990, 2.0 ** 995, 1.0]] * 4
    out['t11_subnormal'] = run(adp, A, B)

    caught = {}
    for policy, case in (('skip', tests.zeros_case), ('field0', tests.field0_case)):
        A, B = case()
        try:
            adp.adp(A, B, adp.Config(zero_policy=policy))
            caught[policy] = None
        except adp.CheckFailure as ex:
            caught[policy] = ex.label
    I = [[1.0 if i == j else 0.0 for j in range(4)] for i in range(4)]
    out['t12_zeros'] = {'caught': caught, 'identity': run(adp, I, I)}

    print(json.dumps(out, indent=1))


if __name__ == '__main__':
    main()
