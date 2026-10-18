#!/usr/bin/env python3
"""Check maintained documentation links and elaborate each standalone Lean example."""
if not __debug__:
    raise SystemExit('Run without python -O or PYTHONOPTIMIZE: these checks rely on assert.')
from pathlib import Path
import json
import re
import subprocess
import tempfile

ROOT = Path(__file__).resolve().parents[1]
LINK = re.compile(r'\]\(([^\s)]+)(?:\s+"[^"]*")?\)')
LEAN = re.compile(r'^```lean\s*\n(.*?)^```\s*$', re.M | re.S)


def main():
    build = subprocess.run(['lake', 'build', 'TensorCoreTests'], cwd=ROOT,
                           text=True, capture_output=True)
    if build.returncode:
        raise SystemExit(build.stdout + build.stderr)
    documents = [ROOT / 'README.md', ROOT / 'tests/README.md', ROOT / 'examples/README.md',
                 *(ROOT / 'floatlib-port').glob('*.md')]
    links = 0
    for document in documents:
        for target in LINK.findall(document.read_text()):
            if target.startswith(('https:', 'http:', 'mailto:', '#')):
                continue
            target = target.split('#', 1)[0]
            if not target:
                continue
            if not (document.parent / target).exists():
                raise SystemExit(f'{document.relative_to(ROOT)}: missing local link {target}')
            links += 1
    checked = [ROOT / 'README.md', ROOT / 'tests/README.md']
    snippets = []
    with tempfile.TemporaryDirectory(prefix='tc-doc-examples-') as directory:
        for document in checked:
            for index, match in enumerate(LEAN.finditer(document.read_text()), 1):
                source = match.group(1)
                path = Path(directory) / 'Example.lean'
                path.write_text(source)
                proc = subprocess.run(['lake', 'env', 'lean', str(path)], cwd=ROOT,
                                      text=True, capture_output=True)
                if proc.returncode:
                    line = document.read_text()[:match.start()].count('\n') + 1
                    raise SystemExit(f'{document.relative_to(ROOT)}:{line}, Lean block {index}\n' +
                                     proc.stdout + proc.stderr)
                snippets.append({'document': str(document.relative_to(ROOT)), 'block': index})
    print(json.dumps({'status': 'passed', 'local_links_checked': links,
                      'lean_blocks_checked': len(snippets), 'examples': snippets}, indent=2))


if __name__ == '__main__':
    main()
