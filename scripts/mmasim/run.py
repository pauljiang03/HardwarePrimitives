"""Run Microsoft's MMA-Sim (https://github.com/microsoft/MMA-Sim, MIT licence, Copyright (c)
Microsoft Corporation; the commit is pinned in vendor/mmasim/SOURCES.json) on batches of inner
products, unmodified, through its own `dpa` entry points. Called by scripts/check_mmasim.py.

Usage (in a Python with torch; MMA-Sim is imported from the checkout, not installed):
    run.py <MMA-Sim src dir> <in.jsonl> <out.txt>
Each input line: {"cls": "MMA"|"WGMMA"|"TCGen05MMA", "arch": ..., "shape": ...,
                  "kinst": k, "a": [words], "b": [words], "c": word}
The K products are fed to consecutive instructions of `kinst` products each (dpa on each slice),
each output the next instruction's accumulator, as a K loop of MMA instructions does.
Output: one FP32 (or FP16) output word per line, in decimal, in input order.
Cases with the same (cls, arch, shape, len(a)) are evaluated in one batched call."""
import json
import sys
from collections import defaultdict

sys.path.insert(0, sys.argv[1])
import types  # noqa: E402
import torch  # noqa: E402
import mmasim.arithmetic  # noqa: E402

# MMA-Sim's FP64 FMA module JIT-compiles a C++ kernel with -fopenmp, which Apple clang rejects.
# Only FP64 instructions use it; it is replaced by a stub that fails if called. Everything this
# cross-check runs is in mmasim/arithmetic/fdpa.py, imported unmodified.
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
