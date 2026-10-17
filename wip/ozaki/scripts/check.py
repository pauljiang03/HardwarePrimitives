#!/usr/bin/env python3
"""Validate the Ozaki formalization.

1. Build the three libraries, the two test libraries (kernel-checked regressions against the Z3
   models' outputs) and the axiom audits (`lake build`, one test module at a time), optionally from
   a clean build directory.
2. Check every worked example under `examples/`.
3. Elaborate every ```lean code block in the README, the results summary and the test walkthrough,
   each as a standalone file.

Usage: python3 scripts/check.py [--clean]
"""
if not __debug__:
    raise SystemExit('Run without python -O or PYTHONOPTIMIZE: these checks rely on assert.')
import pathlib
import re
import shutil
import subprocess
import sys
import tempfile

ROOT = pathlib.Path(__file__).resolve().parent.parent
DOCS = [ROOT / 'README.md', ROOT / 'THEOREMS.md', ROOT / 'tests' / 'README.md']
BLOCK = re.compile(r'```lean\n(.*?)```', re.S)


def run(cmd, what):
    proc = subprocess.run(cmd, cwd=ROOT, capture_output=True, text=True)
    out = proc.stdout + proc.stderr
    errors = [line for line in out.splitlines()
              if ': error' in line or line.startswith('error') or 'declaration uses' in line]
    if proc.returncode != 0 or errors:
        print(f'FAIL {what}')
        print(out)
        sys.exit(1)
    return out


def main():
    if '--clean' in sys.argv:
        shutil.rmtree(ROOT / '.lake' / 'build', ignore_errors=True)
    # The test modules evaluate large terms in the kernel; built in parallel they can exhaust
    # memory, so the libraries are built first and then each test module on its own.
    out = run(['lake', 'build', 'Ozaki', 'OzakiTC', 'OzakiMC'], 'lake build (libraries)')
    for lib in ['OzakiTCTests', 'OzakiMCTests']:
        for test in sorted((ROOT / 'tests' / lib).glob('*.lean')):
            out += run(['lake', 'build', f'{lib}.{test.stem}'], f'lake build {lib}.{test.stem}')
    out += run(['lake', 'build'], 'lake build')
    for line in dict.fromkeys(line for line in out.splitlines() if 'axiom_audit' in line):
        print(line.split(': ', 2)[-1])
    warnings = [line for line in out.splitlines() if 'warning' in line]
    print(f'ok   lake build ({len(warnings)} warnings)')

    for ex in sorted((ROOT / 'examples').glob('*.lean')):
        run(['lake', 'env', 'lean', str(ex)], ex.name)
        print(f'ok   {ex.relative_to(ROOT)}')

    (ROOT / '.lake').mkdir(exist_ok=True)
    with tempfile.TemporaryDirectory(dir=ROOT / '.lake') as tmp:
        count = 0
        for doc in DOCS:
            for i, block in enumerate(BLOCK.findall(doc.read_text())):
                path = pathlib.Path(tmp) / f'{doc.stem}_{i}.lean'
                path.write_text(block)
                run(['lake', 'env', 'lean', str(path)], f'{doc.relative_to(ROOT)} block {i + 1}')
                count += 1
        print(f'ok   {count} documentation code blocks')

    links = 0
    for doc in [*DOCS, ROOT / 'examples' / 'README.md']:
        for target in re.findall(r'\]\(([^\s)#]+)', doc.read_text()):
            if target.startswith(('http:', 'https:', 'mailto:')):
                continue
            if not (doc.parent / target).exists():
                print(f'FAIL {doc.relative_to(ROOT)}: missing local link {target}')
                sys.exit(1)
            links += 1
    print(f'ok   {links} local links')


if __name__ == '__main__':
    main()
