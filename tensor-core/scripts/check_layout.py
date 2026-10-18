#!/usr/bin/env python3
"""Enforce production/test ownership and the numerical/model/kernel import layers."""
if not __debug__:
    raise SystemExit('Run without python -O or PYTHONOPTIMIZE: these checks rely on assert.')
from pathlib import Path
import json
import re

ROOT = Path(__file__).resolve().parents[1]


def main():
    production = {'.'.join(p.relative_to(ROOT).with_suffix('').parts): p
                  for p in (ROOT / 'TensorCore').rglob('*.lean')}
    production['TensorCore'] = ROOT / 'TensorCore.lean'
    tests = {'.'.join(p.relative_to(ROOT / 'tests').with_suffix('').parts): p
             for p in (ROOT / 'tests').rglob('*.lean')}
    modules = {**production, **tests}
    imports = {name: [dep for line in re.findall(r'^import ([^\n]+)', p.read_text(), re.M)
                      for dep in line.split() if dep.startswith('TensorCore')]
               for name, p in modules.items()}
    for name, deps in imports.items():
        assert all(dep in modules for dep in deps), (name, 'missing import', deps)
        if name in production:
            assert not any(dep.startswith('TensorCoreTests') for dep in deps), (name, 'imports tests')
        if name.startswith('TensorCore.Numerics.'):
            assert all(dep.startswith('TensorCore.Numerics.') for dep in deps), (name, deps)
        if name.startswith('TensorCore.TC.'):
            assert all(dep.startswith(('TensorCore.TC.', 'TensorCore.Numerics.')) for dep in deps), (name, deps)
        if name.startswith('TensorCore.EFT.'):
            assert all(dep.startswith(('TensorCore.EFT.', 'TensorCore.TC.', 'TensorCore.Numerics.'))
                       for dep in deps), (name, deps)
        assert not any(any(part in {'Gemm', 'Meta', 'Program', 'Regression'} for part in name.split('.'))
                       for name in production), 'Application or regression modules remain in the library'

    def closure(name, seen=None):
        seen = set() if seen is None else seen
        if name in seen:
            return seen
        seen.add(name)
        for dep in imports[name]:
            closure(dep, seen)
        return seen

    public = closure('TensorCore')
    assert set(production) <= public, ('production modules omitted', sorted(set(production) - public))
    assert not set(tests) & public, 'Public root imports test modules'
    assert set(modules) <= closure('TensorCoreTests'), 'Test root omits modules from the full audit'
    assert not any(name.startswith('TensorCore.Kernels') for name in closure('TensorCore.EFT'))
    active = [*(ROOT / 'Main').glob('*.lean'), *(ROOT / 'examples').glob('*.lean'),
              *(ROOT / 'scripts/lean').glob('*.lean')]
    for p in active:
        for line in re.findall(r'^import ([^\n]+)', p.read_text(), re.M):
            for dep in line.split():
                if dep.startswith('TensorCore'):
                    assert dep in modules, (p, 'missing import', dep)
    config = (ROOT / 'lakefile.toml').read_text()
    targets = json.loads(re.search(r'^defaultTargets\s*=\s*(\[[^\]]*\])', config, re.M).group(1))
    assert {'TensorCore', 'TensorCoreTests'} <= set(targets)
    # The wip/ projects are standalone Lake projects that this package never builds.
    assert 'wip' not in config
    print(json.dumps({'status': 'passed', 'library_modules': len(production), 'test_modules': len(tests),
                      'public_root_excludes_tests': True, 'reference_eft_excludes_kernels': True,
                      'numerical_model_kernel_boundaries_checked': True,
                      'full_import_covers_every_module': True}, indent=2))


if __name__ == '__main__':
    main()
