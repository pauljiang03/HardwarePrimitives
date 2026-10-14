#!/usr/bin/env python3
"""Pin the FloatLib equivalence proofs to a reviewed revision of the parent library.

Usage (from floatlib-port/): python3 scripts/pin_reference.py REVISION
Rewrites reference-manifest.json from the parent dependency files at REVISION, updates the
pinned revision and manifest checksum used by prepare_reference.py and the reports, and
clears renamed-identifiers.json and the RENAMED_MODULES table of prepare_reference.py (renames
before the new pin are part of it).
Use this only after a deliberate change to the parent's behavior has been reviewed.
"""
if not __debug__:
    raise SystemExit('Run without python -O or PYTHONOPTIMIZE: these checks rely on assert.')
import hashlib, json, re, subprocess, sys
import prepare_reference as pr


def main():
    if len(sys.argv) != 2:
        raise SystemExit(__doc__)
    rev = subprocess.check_output(['git', 'rev-parse', sys.argv[1]], cwd=pr.REPO, text=True).strip()
    pending = [m for p in (pr.PORT / 'TCFloat/Equivalence').glob('*.lean') for m in pr.imports(p.read_text())]
    files = {}
    while pending:
        module = pending.pop()
        name = module.replace('.', '/') + '.lean'
        if name in files:
            continue
        data = subprocess.check_output(['git', 'show', f'{rev}:{name}'], cwd=pr.REPO)
        lines = data.splitlines(True)
        body = b''.join(l for l in lines if not l.startswith(b'import ')).decode()
        tokens = json.dumps(pr.lean_tokens(body), ensure_ascii=False, separators=(',', ':')).encode()
        files[name] = dict(source_sha256=hashlib.sha256(data).hexdigest(),
                           body_tokens_sha256=hashlib.sha256(tokens).hexdigest(),
                           imports=[l.decode() for l in lines if l.startswith(b'import ')])
        pending.extend(pr.imports(data.decode()))
    manifest = json.dumps(dict(format=1, revision=rev, files=dict(sorted(files.items()))), indent=2) + '\n'
    pr.REFERENCE.write_text(manifest)
    digest = hashlib.sha256(manifest.encode()).hexdigest()
    for script, pattern, value in [
            ('prepare_reference.py', r'^PIN = "[0-9a-f]+"', f'PIN = "{rev}"'),
            ('prepare_reference.py', r'^REFERENCE_SHA256 = "[0-9a-f]+"', f'REFERENCE_SHA256 = "{digest}"'),
            ('check_equivalence.py', r"^REV = '[0-9a-f]+'", f"REV = '{rev}'"),
            ('check_all.py', r"'reference_commit':'[0-9a-f]+'", f"'reference_commit':'{rev}'")]:
        path = pr.PORT / 'scripts' / script
        text = path.read_text()
        new, n = re.subn(pattern, value, text, flags=re.M)
        if n != 1:
            raise SystemExit(f'{script}: expected one match for {pattern}')
        path.write_text(new)
    (pr.PORT / 'renamed-identifiers.json').write_text('{}\n')
    # Module renames before the new pin are part of it too.
    path = pr.PORT / 'scripts' / 'prepare_reference.py'
    text = path.read_text()
    new, n = re.subn(r'^RENAMED_MODULES = \{.*?^\}\n|^RENAMED_MODULES = \{\}\n', 'RENAMED_MODULES = {}\n',
                     text, count=1, flags=re.M | re.S)
    if n != 1:
        raise SystemExit('prepare_reference.py: expected one RENAMED_MODULES table')
    path.write_text(new)
    print(f'Pinned {len(files)} parent dependencies at {rev}; manifest sha256 {digest}')


if __name__ == '__main__':
    main()
