#!/usr/bin/env python3
"""Check the standalone audit against cold, stale, and repaired library sources."""
if not __debug__:
    raise SystemExit('Run without python -O or PYTHONOPTIMIZE: these checks rely on assert.')
from pathlib import Path
import json
import shutil
import subprocess
import sys
import tempfile

ROOT = Path(__file__).resolve().parents[1]


def require(condition, message):
    if not condition:
        raise RuntimeError(message)


def main():
    with tempfile.TemporaryDirectory(prefix='tc-axiom-regression-') as folder:
        project = Path(folder)
        for name in ['scripts/lean', 'TensorCore', 'docs', 'Main', 'tests/TensorCoreTests']:
            (project / name).mkdir(parents=True, exist_ok=True)
        for name in ['lean-toolchain', 'scripts/lean/Audit.lean', 'scripts/check_axioms.py']:
            shutil.copyfile(ROOT / name, project / name)
        (project / 'lakefile.toml').write_text(
            'name = "auditRegression"\n'
            'defaultTargets = ["TensorCore", "TensorCoreTests"]\n\n'
            '[[lean_lib]]\nname = "TensorCore"\nglobs = ["TensorCore", "TensorCore.*"]\n'
            '[[lean_lib]]\nname = "TensorCoreTests"\nsrcDir = "tests"\nglobs = ["TensorCoreTests", "TensorCoreTests.*"]\n')
        (project / 'TensorCore.lean').write_text('import TensorCore.Probe\n')
        (project / 'tests/TensorCoreTests.lean').write_text('import TensorCore\n')
        for name in ['Main/Trace.lean', 'Main/Features.lean', 'Main/EFT.lean', 'Main/BoundedEFT.lean']:
            (project / name).write_text('import TensorCore\n')
        source = project / 'TensorCore/Probe.lean'
        valid = 'namespace TensorCore\ntheorem auditBaseline : (1 : Nat) = 1 := rfl\n'
        source.write_text(valid + 'end TensorCore\n')

        def audit():
            return subprocess.run([sys.executable, 'scripts/check_axioms.py'],
                                  cwd=project, text=True, capture_output=True, timeout=90)

        cold = audit()
        require(cold.returncode == 0, cold.stdout + cold.stderr)
        report = project / 'docs/axioms.txt'
        baseline = report.read_text()
        require('TensorCore.auditBaseline' in baseline, 'Cold audit omitted the imported theorem')

        # Only a rebuild catches this invalid proof: the cached module still holds the valid baseline.
        source.write_text(valid + 'theorem auditInvalid : False := by decide\nend TensorCore\n')
        stale = audit()
        require(stale.returncode != 0, 'Audit accepted broken source behind a valid build cache')
        require('Probe.lean' in stale.stdout + stale.stderr,
                'Audit failed without reporting the broken imported source')
        require('theorem roots audited' not in stale.stdout, 'Failed audit reported success')
        require(report.read_text() == baseline, 'Failed build replaced the previous audit report')

        source.write_text(valid + 'theorem auditFresh : (2 : Nat) = 2 := rfl\nend TensorCore\n')
        repaired = audit()
        require(repaired.returncode == 0, repaired.stdout + repaired.stderr)
        require('TensorCore.auditFresh' in report.read_text(), 'Audit did not rebuild repaired source')

    print(json.dumps(dict(status='passed', cold_build=True, stale_source_rejected=True,
                         failed_build_preserves_report=True, repaired_source_rebuilt=True), indent=2))


if __name__ == '__main__':
    main()
