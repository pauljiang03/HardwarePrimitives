#!/usr/bin/env python3
"""Build and audit a fresh source copy, with no preexisting .lake directory."""
if not __debug__:
    raise SystemExit('Run without python -O or PYTHONOPTIMIZE: these checks rely on assert.')
from pathlib import Path
import hashlib
import json
import os
import re
import shutil
import subprocess
import sys
import tempfile


def source_manifest(directory):
    """Inputs to validation, excluding caches and reports that the gates regenerate."""
    result = {}
    for path in sorted(directory.rglob('*')):
        rel = path.relative_to(directory)
        if any(part in {'.git', '.lake', 'tmp', '__pycache__', '.DS_Store', 'proposals', 'reference-compat', 'test-results',
                                 'node_modules', 'dist', '.astro'} for part in rel.parts):
            continue
        if rel.parts[:2] == ('data', 'regressions') or str(rel) == 'docs/axioms.txt':
            continue
        if path.is_file():
            result[str(rel)] = hashlib.sha256(path.read_bytes()).hexdigest()
    return result


def repository_manifest(directory):
    return source_manifest(directory)


root = Path(__file__).resolve().parents[1]
before = source_manifest(root)
repository_before = repository_manifest(root)
target = Path(tempfile.mkdtemp(prefix='tensor-core-clean-')) / 'tensor-core'
shutil.copytree(root, target, dirs_exist_ok=True,
                ignore=shutil.ignore_patterns('.git', '.lake', 'tmp', '__pycache__', '.DS_Store', 'proposals', 'reference-compat', 'test-results',
                                             'node_modules', 'dist', '.astro'))
assert not (target / '.lake').exists()
if (repository_before != repository_manifest(root) or
        repository_before != repository_manifest(target)):
    raise SystemExit(f'Source changed while copying; no validation claimed. Snapshot retained: {target}')
commands = [['lake', 'build'], [sys.executable, 'scripts/check_axioms.py'],
            [sys.executable, 'scripts/check_features.py'],
            [sys.executable, 'scripts/check_device_formats.py'],
            [sys.executable, 'scripts/check_device_replay.py'],
            [sys.executable, 'scripts/validate.py'],
            [sys.executable, 'scripts/check_device.py'],
            [sys.executable, 'scripts/check_eft.py'],
            [sys.executable, 'scripts/check_independent_spec.py'],
            [sys.executable, 'scripts/check_axioms_regression.py'],
            [sys.executable, 'scripts/check_lean_eft.py']]
commands += [['lake', 'env', 'lean', str(p.relative_to(target))]
             for p in sorted((target / 'examples').glob('*.lean'))]
commands += [[sys.executable, 'scripts/check_docs.py'],
             [sys.executable, 'scripts/check_layout.py']]
logs = []
for index, command in enumerate(commands, 1):
    print(f'[{index}/{len(commands)}] {" ".join(command)}', file=sys.stderr, flush=True)
    env = {k: v for k, v in os.environ.items() if k != 'PYTHONOPTIMIZE'}
    proc = subprocess.run(command, cwd=target, text=True, capture_output=True, env=env)
    logs.append(proc.stdout + proc.stderr)
    if proc.returncode:
        print(logs[-1])
        raise SystemExit(proc.returncode)
targets = re.findall(r'\[(\d+)/(\d+)\]', logs[0])
report = {'preexisting_build_cache': False,
          'commands': [['python3' if part == sys.executable else part for part in c] for c in commands],
          'targets_built': int(targets[-1][1]) if targets else None,
          'audit': logs[1].strip().splitlines()[-1] if logs[1].strip() else None,
          'feature_checks': json.loads(logs[2]), 'format_evidence': json.loads(logs[3]),
          'device_replay': json.loads(logs[4])['totals'],
          'success': True, 'all_standalone_examples': True,
          'axiom_audit_regression_passed': True,
          'lean_warnings': len(re.findall(r'^warning:', logs[0], re.M)),
          'linker_warnings': len(re.findall(r'^(?:ld|ld64\.lld|ld\.lld): warning:', logs[0], re.M))}
(root / 'tmp').mkdir(exist_ok=True)
(root / 'tmp/clean-build.log').write_text('\n'.join(logs))
report['documentation_checks'] = json.loads(logs[-2])
report['layout_checks'] = json.loads(logs[-1])
report['lean_eft_checks'] = json.loads((target / 'data/regressions/lean-eft-report.json').read_text())
report.update(source_sha256=before, repository_source_sha256=repository_before,
              snapshot_stable=repository_before == repository_manifest(target),
              workspace_matches_snapshot=repository_before == repository_manifest(root))
if not report['snapshot_stable'] or not report['workspace_matches_snapshot']:
    report['publication_skipped'] = True
    (root / 'tmp/clean-build-unpublished.json').write_text(json.dumps(report, indent=2) + '\n')
    raise SystemExit(f'Source changed during validation; reports not published. Validated copy retained: {target}')
generated = ['docs/axioms.txt']
generated += ['data/regressions/' + name for name in [
    'feature-report.json', 'device-formats-report.json', 'device-replay-report.json', 'device-report.json',
    'validation-report.json',
    'eft-checks.json', 'eft-coverage.json', 'eft-coverage-cases.json', 'eft-paper-report.json',
    'eft-paper-cases.json', 'eft-paper-original.json', 'eft-paper-second-pass.json',
    'independent-spec-report.json', 'bounded-eft-report.json', 'lean-eft-report.json',
    'instruction-groups-report.json']]
for name in generated:
    shutil.copyfile(target / name, root / name)
(root / 'data/regressions/clean-build.json').write_text(json.dumps(report, indent=2) + '\n')
shutil.rmtree(target.parent, ignore_errors=True)
print(json.dumps(report, indent=2))
