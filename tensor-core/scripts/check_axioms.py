#!/usr/bin/env python3
"""Rebuild and audit all theorem dependencies against the standard Lean axiom allowlist."""
if not __debug__:
    raise SystemExit('Run without python -O or PYTHONOPTIMIZE: these checks rely on assert.')
from pathlib import Path
import re
import subprocess
import sys

root = Path(__file__).resolve().parents[1]
build = subprocess.run(['lake', 'build', 'TensorCoreTests'], cwd=root,
                       text=True, capture_output=True)
if build.returncode:
    print(build.stdout + build.stderr, file=sys.stderr, end='')
    raise SystemExit(build.returncode)
allowed = {'propext', 'Classical.choice', 'Quot.sound'}
proc = subprocess.run(['lake', 'env', 'lean', 'scripts/lean/Audit.lean'], cwd=root,
                      check=True, text=True, capture_output=True)
lines = [line for line in proc.stdout.splitlines() if line]
summary = [line for line in lines if 'tc_audit:' in line]
assert len(summary) == 1, proc.stdout + proc.stderr
expected = int(re.search(r'(\d+) theorem roots', summary[0]).group(1))
written = int(re.search(r'\((\d+) written in source', summary[0]).group(1))
theorems = [line for line in lines if 'tc_audit:' not in line]
assert len(theorems) == expected, (len(theorems), expected)
for line in theorems:
    match = re.search(r"'([^']+)' depends on axioms: \[(.*)\]$", line)
    assert match, line
    names = set(match.group(2).split(', ')) if match.group(2) else set()
    assert names <= allowed, (line, names - allowed)
sources = [*(root / 'TensorCore').rglob('*.lean'), *(root / 'tests').rglob('*.lean'), *(root / 'examples').glob('*.lean'),
           *(root / 'Main').rglob('*.lean'), *root.glob('*.lean')]
for source in sources:
    text = source.read_text()
    assert not re.search(r'\b(sorry|admit|axiom|native_decide|ofReduceBool|skipKernelTC)\b', text), source
(root / 'docs/axioms.txt').write_text('\n'.join(theorems) + '\n')
print(f'{expected} theorem roots audited ({written} written in source); only standard Lean axioms; no placeholders or compiled reflection.')
