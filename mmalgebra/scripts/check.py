#!/usr/bin/env python3
"""Validate MMAlgebra, the reduction algebra of block FMAs.

1. Build the two libraries, then each test module on its own (kernel-checked worked examples and
   the axiom audits, which allow only Lean's standard axioms), optionally from a clean build
   directory. The models themselves (`TensorCore` in `..`, `MatrixCore` in `../amd`) are built by
   their own projects and reused.
2. Elaborate every ```lean code block in the README as a standalone file.
3. Check the local links of the README files.
4. With --prototype, rerun the Python prototype's checks and compare their output with the
   recorded files in prototype/results/ (with --slow, also the enumerations that take minutes).
5. With --port, regenerate the random blocks of prototype/validate_port.py, evaluate them with the
   Lean models, and compare them bit for bit with the Python port.

Usage: python3 scripts/check.py [--clean] [--prototype [--slow]] [--port]
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
PROTO = ROOT / 'prototype'
DOCS = [ROOT / 'README.md', PROTO / 'README.md']
BLOCK = re.compile(r'```lean\n(.*?)```', re.S)
LIBS = ['MMAlgebra', 'MMAlgebraTC', 'MMAlgebraMC']
TESTS = ['MMAlgebraTCTests', 'MMAlgebraMCTests']
# (script, arguments, recorded output); the slow ones run only with --slow.
FAST = [('examples.py', [], 'examples.txt'),
        ('bf16_extremes.py', [], 'bf16_extremes.txt'),
        ('restriction_lemma.py', [], 'restriction_lemma.txt'),
        ('decide_equiv.py', [], 'decide_equiv.txt'),
        ('oneround.py', [], 'oneround.txt'),
        ('config_study.py', [], 'config_study.txt'),
        ('laws.py', ['300'], 'laws.txt')]
SLOW = [('terms4.py', [], 'terms4.txt'),
        ('classes.py', ['300'], 'classes.txt'),
        ('terms.py', ['300'], 'terms.txt'),
        ('divergence.py', [], 'divergence.txt'),
        ('blas_programs.py', ['200', '800'], 'blas_programs.txt')]


def run(cmd, what, cwd=ROOT):
    proc = subprocess.run(cmd, cwd=cwd, capture_output=True, text=True)
    out = proc.stdout + proc.stderr
    errors = [line for line in out.splitlines()
              if ': error' in line or line.startswith('error') or 'declaration uses' in line]
    if proc.returncode != 0 or errors:
        print(f'FAIL {what}')
        print(out)
        sys.exit(1)
    return out


def lean():
    if '--clean' in sys.argv:
        shutil.rmtree(ROOT / '.lake' / 'build', ignore_errors=True)
    out = ''.join(run(['lake', 'build', lib], f'lake build {lib}') for lib in LIBS)
    for lib in TESTS:
        for test in sorted((ROOT / 'tests' / lib).glob('*.lean')):
            out += run(['lake', 'build', f'{lib}.{test.stem}'], f'lake build {lib}.{test.stem}')
    out += run(['lake', 'build'], 'lake build')
    for line in dict.fromkeys(line for line in out.splitlines() if 'axiom_audit' in line):
        print(line.split(': ', 2)[-1])
    warnings = [line for line in out.splitlines() if 'warning' in line]
    if warnings:
        print('\n'.join(warnings))
    print(f'ok   lake build ({len(warnings)} warnings)')

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


def links():
    count = 0
    for doc in DOCS:
        for target in re.findall(r'\]\(([^\s)#]+)', doc.read_text()):
            if target.startswith(('http:', 'https:', 'mailto:')):
                continue
            if not (doc.parent / target).exists():
                print(f'FAIL {doc.relative_to(ROOT)}: missing local link {target}')
                sys.exit(1)
            count += 1
    print(f'ok   {count} local links')


def prototype():
    for script, args, recorded in FAST + (SLOW if '--slow' in sys.argv else []):
        out = run([sys.executable, script, *args], script, cwd=PROTO)
        want = (PROTO / 'results' / recorded).read_text()
        if out != want:
            print(f'FAIL prototype/{script}: output differs from prototype/results/{recorded}')
            sys.exit(1)
        print(f'ok   prototype/{script} reproduces results/{recorded}')


def port():
    run([sys.executable, 'validate_port.py', 'gen', '150'], 'validate_port.py gen', cwd=PROTO)
    for name, out in [('ValidateTC.lean', 'tc.out'), ('ValidateMC.lean', 'mc.out')]:
        text = run(['lake', 'env', 'lean', str(PROTO / 'validation' / name)], name)
        (PROTO / 'validation' / out).write_text(text)
    print(run([sys.executable, 'validate_port.py', 'check'], 'validate_port.py check',
              cwd=PROTO).strip().splitlines()[-1])


def main():
    lean()
    links()
    if '--prototype' in sys.argv:
        prototype()
    if '--port' in sys.argv:
        port()


if __name__ == '__main__':
    main()
