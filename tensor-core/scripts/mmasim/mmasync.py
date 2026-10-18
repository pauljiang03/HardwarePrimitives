"""Evaluate the FP8 mma.sync path of H100, H200 and B200 composed from MMA-Sim's FP16 mma.sync.

Usage: mmasync.py <MMA-Sim src dir> <in.jsonl> <out.txt>
"""
import json
import sys
import types
from collections import defaultdict

sys.path.insert(0, sys.argv[1])
import torch  # noqa: E402
import mmasim.arithmetic  # noqa: E402

_fma = types.ModuleType('mmasim.arithmetic.fma')


class _NoFMA:
    def __init__(self, *args, **kwargs):
        raise RuntimeError('FP64 FMA is not used')


_fma.MMA_FMA = _NoFMA
sys.modules['mmasim.arithmetic.fma'] = _fma
mmasim.arithmetic.fma = _fma
from mmasim.nv_ptx import sim as nv  # noqa: E402

DT = {'e4m3': torch.float8_e4m3fn, 'e5m2': torch.float8_e5m2}


def main():
    src, inp, outp = sys.argv[1:4]
    cases = [json.loads(line) for line in open(inp) if line.strip()]
    groups = defaultdict(list)
    for i, c in enumerate(cases):
        groups[(c['arch'], c['fmt'], c['kinst'], len(c['a']))].append(i)
    out = [None] * len(cases)
    for (arch, fmt, kinst, K), idx in groups.items():
        op = nv.MMA(arch, 'm16n8k16.f32.f16.f16.f32')
        a8 = torch.tensor([cases[i]['a'] for i in idx], dtype=torch.uint8).view(DT[fmt])
        b8 = torch.tensor([cases[i]['b'] for i in idx], dtype=torch.uint8).view(DT[fmt])
        a16, b16 = a8.to(torch.float16), b8.to(torch.float16)
        c = torch.tensor([[cases[i]['c'] - (1 << 32) if cases[i]['c'] >= 1 << 31 else cases[i]['c']]
                          for i in idx], dtype=torch.int32).view(torch.float32).reshape(-1)
        pos = torch.arange(kinst)
        ga = pos[(pos % 4) < 2]
        gb = pos[(pos % 4) >= 2]
        d = c
        for j in range(0, K, kinst):
            sa, sb = a16[:, j:j + kinst], b16[:, j:j + kinst]
            zero = torch.zeros_like(d)
            d1 = op.dpa(sa[:, ga], sb[:, ga], zero)
            d2 = op.dpa(sa[:, gb], sb[:, gb], d1)
            d = d2 + d          # FP32 addition, round to nearest even
        raw = d.view(torch.int32).tolist()
        for i, w in zip(idx, raw):
            out[i] = w & 0xffffffff
    with open(outp, 'w') as f:
        f.write(''.join(f'{w}\n' for w in out))


if __name__ == '__main__':
    main()
