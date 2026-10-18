"""Run MMA-Sim, unmodified, on batches of inner products through its `dpa` entry points.

Usage: run.py <MMA-Sim src dir> <in.jsonl> <out.txt>   (in a Python with torch)
"""
import json
import sys
from collections import defaultdict

sys.path.insert(0, sys.argv[1])
import types  # noqa: E402
import torch  # noqa: E402
import mmasim.arithmetic  # noqa: E402

# Stub for the FP64 FMA module, whose C++ kernel needs -fopenmp (rejected by Apple clang).
_fma = types.ModuleType('mmasim.arithmetic.fma')


class _NoFMA:
    def __init__(self, *args, **kwargs):
        raise RuntimeError('FP64 FMA is not used by this cross-check')


_fma.MMA_FMA = _NoFMA
sys.modules['mmasim.arithmetic.fma'] = _fma
mmasim.arithmetic.fma = _fma
from mmasim.nv_ptx import sim as nv  # noqa: E402

SIGNED = {torch.float16: torch.int16, torch.bfloat16: torch.int16, torch.float32: torch.int32,
          torch.float8_e4m3fn: torch.uint8, torch.float8_e5m2: torch.uint8}


def to_tensor(rows, dtype):
    store = SIGNED[dtype]
    bits = torch.iinfo(store).bits
    if store == torch.uint8:
        t = torch.tensor(rows, dtype=torch.uint8)
    else:
        half = 1 << (bits - 1)
        t = torch.tensor([[w - (1 << bits) if w >= half else w for w in r] for r in rows],
                         dtype=store)
    return t.view(dtype)


def main():
    src, inp, outp = sys.argv[1:4]
    cases = [json.loads(line) for line in open(inp) if line.strip()]
    groups = defaultdict(list)
    for i, c in enumerate(cases):
        groups[(c['cls'], c['arch'], c['shape'], len(c['a']), c.get('kinst', len(c['a'])))].append(i)
    out = [None] * len(cases)
    for (cls, arch, shape, k, kinst), idx in groups.items():
        op = getattr(nv, cls)(arch, shape)
        a = to_tensor([cases[i]['a'] for i in idx], op.a_type)
        b = to_tensor([cases[i]['b'] for i in idx], op.b_type)
        c = to_tensor([[cases[i]['c']] for i in idx], op.c_type).reshape(-1)
        d = c
        for j in range(0, k, kinst):
            d = op.dpa(a[:, j:j + kinst], b[:, j:j + kinst], d)
        width = 32 if d.dtype == torch.float32 else 16
        raw = d.view(torch.int32 if width == 32 else torch.int16).tolist()
        for i, w in zip(idx, raw):
            out[i] = w & ((1 << width) - 1)
    with open(outp, 'w') as f:
        f.write(''.join(f'{w}\n' for w in out))


if __name__ == '__main__':
    main()
