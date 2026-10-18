#!/usr/bin/env python3
"""Targeted differential test of the CDNA 3 FP8 model against the MATLAB model.

Usage: python3 scripts/matlab_fp8.py [--cases N] [--seed S]   (N cases per format)
"""
import argparse
import json
import pathlib
import random
import subprocess
import sys

import fp8_cases as C
import matlab_diff as M

ROOT = pathlib.Path(__file__).resolve().parent.parent
WORK = ROOT / '.lake' / 'matlab-fp8'
FORMATS = {'cdna3E4M3': M.E4M3, 'cdna3E5M2': M.E5M2}


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--cases', type=int, default=10000, help='cases per format')
    ap.add_argument('--seed', type=int, default=2026)
    args = ap.parse_args()
    WORK.mkdir(parents=True, exist_ok=True)
    hashes = M.fetch_model()
    subprocess.run(['lake', 'build', 'mc_eval'], cwd=ROOT, check=True, capture_output=True)
    rng = random.Random(args.seed)
    cases = []
    for profile in FORMATS:
        cases += C.generate(rng, profile, args.cases)
    lean_out = subprocess.run([str(ROOT / '.lake' / 'build' / 'bin' / 'mc_eval')],
                              input=C.mc_eval_input(cases), capture_output=True, text=True,
                              check=True).stdout.split('\n')
    mat_in = WORK / 'cases.txt'
    mat_in.write_text(''.join(
        f'{p} {len(a)} ' + ' '.join(M.to_hex64(M.decode(FORMATS[p], w)) for w in a) + ' ' +
        ' '.join(M.to_hex64(M.decode(FORMATS[p], w)) for w in b) + ' ' +
        M.to_hex64(M.decode(M.FP32, c)) + '\n' for p, _, a, b, c in cases))
    report = {'commit': M.COMMIT, 'sha256': hashes, 'seed': args.seed,
              'cases_per_format': args.cases, 'runs': {}}
    for variant in ['shipped', 'rdfix']:
        out_file = WORK / f'{variant}.out.txt'
        subprocess.run(['octave', '--no-gui', '--quiet', '--eval',
                        f"cd('{ROOT / 'scripts' / 'matlab'}'); driver('{M.MODEL}', "
                        f"'{mat_in}', '{out_file}', '{variant}')"],
                       check=True, capture_output=True)
        mat_out = out_file.read_text().split('\n')
        counts, examples = {}, []
        for i, (profile, regime, a, b, c) in enumerate(cases):
            lv, mv = M.classify_lean(lean_out[i]), M.classify_matlab(mat_out[i])
            key = f'{profile} regime {regime}'
            counts.setdefault(key, [0, 0])
            counts[key][0] += 1
            if lv != mv:
                counts[key][1] += 1
                if len(examples) < 5:
                    examples.append({'profile': profile, 'regime': regime,
                                     'a': [f'{w:x}' for w in a], 'b': [f'{w:x}' for w in b],
                                     'c': f'{c:x}', 'lean': str(lv), 'matlab': str(mv)})
        total = sum(n for n, _ in counts.values())
        bad = sum(m for _, m in counts.values())
        print(f'{variant}: {bad} / {total} mismatches')
        for key in sorted(counts):
            print(f'   {key:24s} {counts[key][1]} / {counts[key][0]}')
        report['runs'][variant] = {'total': total, 'mismatches': bad, 'counts': counts,
                                   'examples': examples}
    (WORK / 'report.json').write_text(json.dumps(report, indent=1))
    print(f'report: {WORK / "report.json"}')
    sys.exit(1 if report['runs']['rdfix']['mismatches'] else 0)


if __name__ == '__main__':
    main()
