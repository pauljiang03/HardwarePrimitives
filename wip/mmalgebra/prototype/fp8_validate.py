"""Validation of the FP8 port (fp8models.py).

1. The recorded FP8 outputs of Ada, L40S, H100, H200 and B200 (the Accurate Models toolbox's
   validation vectors at commit 79143bd, vendored in ../../../tensor-core/vendor/matlab-tensor-core-79143bd),
   replayed through the port as the repository replays them through the Lean models
   (scripts/check_device_replay.py): c accumulated in the block FMA on Ada and L40S, c = 0 on H100
   and H200 (wgmma), and c added after the block FMA with round-to-nearest-even on B200.
2. The sparse evaluators of the enumeration against the full blocks, on random blocks.
3. CDNA 3 binary8 against the Lean model (`mc_eval`, built in ../../../matrix-core), on the random and
   targeted cases of ../../../matrix-core/scripts/fp8_cases.py, including mixed E4M3 x E5M2 operands.
"""
import pathlib
import random
import subprocess
import sys
from fractions import Fraction as Q
from fp8models import *

ROOT = pathlib.Path(__file__).resolve().parents[3]
VENDOR = ROOT / 'tensor-core' / 'vendor' / 'matlab-tensor-core-79143bd' / 'model_validation'
MC_EVAL = ROOT / 'matrix-core' / '.lake' / 'build' / 'bin' / 'mc_eval'
sys.path.insert(0, str(ROOT / 'matrix-core' / 'scripts'))
import fp8_cases  # noqa: E402

MODELS = {('Ada', 'E4M3'): ADA, ('L40S', 'E4M3'): ADA, ('H100', 'E4M3'): HOPPER,
          ('H200', 'E4M3'): HOPPER, ('B200', 'E4M3'): BLACKWELL,
          ('Ada', 'E5M2'): ADA52, ('L40S', 'E5M2'): ADA52, ('H100', 'E5M2'): HOPPER52,
          ('H200', 'E5M2'): HOPPER52, ('B200', 'E5M2'): BLACKWELL52}


def words_of(fmt):
    table = {}
    for w in fmt.words():
        table.setdefault(fmt.value(w), w)
    return table


def replay():
    total = bad = 0
    for (gpu, fmt), P in MODELS.items():
        folder = VENDOR / gpu / fmt
        word = words_of(P.fmt)
        rows = lambda f: [[int(x, 16) for x in line.split()]
                          for line in (folder / f).read_text().splitlines() if line.strip()]
        bins = lambda f: [int(line, 2) for line in (folder / f).read_text().splitlines()
                          if line.strip()]
        a_rows, b_rows = rows(f'a_{gpu}_{fmt}.txt'), rows(f'b_{gpu}_{fmt}.txt')
        c_words, d_words = bins(f'c_{gpu}_fp32.txt'), bins(f'd_{gpu}_fp32.txt')
        n = 0
        for a, b, c, d in zip(a_rows, b_rows, c_words, d_words):
            ps = [(word[value32(x)], word[value32(y)]) for x, y in zip(a, b)]
            if gpu in ('H100', 'H200'):
                got = chain(P, 0, ps)
            elif gpu == 'B200':
                got = rne32(value32(chain(P, 0, ps)) + value32(c))
            else:
                got = chain(P, c, ps)
            n += 1
            bad += got != d
        total += n
        print(f'  {gpu:5s} {fmt}: {n} recorded outputs')
    print(f'recorded GPU outputs: {total}, mismatches {bad}')


def sparse(n=300, seed=1):
    rng = random.Random(seed)
    bad = 0
    for P in (ADA, HOPPER, BLACKWELL, ADA52, HOPPER52, BLACKWELL52):
        ws = P.fmt.words()
        for _ in range(n):
            m = rng.randint(0, 4)
            prods = [(rng.choice(ws), rng.choice(ws)) for _ in range(m)]
            c = rne32(Q(rng.randint(-2 ** 12, 2 ** 12), 2 ** rng.randint(0, 20)))
            full = prods + [(0, 0)] * (P.K - m)
            rng.shuffle(full)
            bad += tc_sparse(P, prods, c) != tc_block(P, full, c)
    for P in (CDNA3_E4M3, CDNA3_E5M2, CDNA3_E4M3E5M2, CDNA3_E5M2E4M3):
        wa, wb = P.fa.words(), P.fb.words()
        for _ in range(n):
            o = [(rng.choice(wa), rng.choice(wb)) for _ in range(rng.randint(0, 3))]
            e = [(rng.choice(wa), rng.choice(wb)) for _ in range(rng.randint(0, 3))]
            c = rne32(Q(rng.randint(-2 ** 12, 2 ** 12), 2 ** rng.randint(0, 20)))
            slots = [(0, 0)] * 16
            for i, x in zip(rng.sample(range(0, 16, 2), len(o)), o):
                slots[i] = x
            for i, x in zip(rng.sample(range(1, 16, 2), len(e)), e):
                slots[i] = x
            bad += mc_sparse(P, o, e, c) != mc_block(P, slots, c)
    print(f'sparse evaluators against full blocks: {10 * n} random blocks, mismatches {bad}')


def lean(n=2000, seed=6):
    models = {'cdna3E4M3': CDNA3_E4M3, 'cdna3E5M2': CDNA3_E5M2, 'cdna3E4M3E5M2': CDNA3_E4M3E5M2}
    rng = random.Random(seed)
    cases = []
    for name in models:
        cases += fp8_cases.generate(rng, name, n)
    out = subprocess.run([str(MC_EVAL)], input=fp8_cases.mc_eval_input(cases),
                         capture_output=True, text=True, check=True).stdout.split('\n')
    bad = 0
    for i, (name, _, a, b, c) in enumerate(cases):
        try:
            mine = 'F %08x' % chain(models[name], c, list(zip(a, b)))
        except ModelError:
            mine = None
        got = out[i].strip()
        bad += not (got == mine or (mine is None and not got.startswith('F ')))
    print(f'CDNA 3 binary8 against the Lean model (mc_eval): {len(cases)} inner products, '
          f'mismatches {bad}')


if __name__ == '__main__':
    replay()
    sparse()
    lean()
