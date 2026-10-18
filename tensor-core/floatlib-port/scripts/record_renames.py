#!/usr/bin/env python3
"""Regenerate renamed-identifiers.json after a parent rename (run from floatlib-port/)."""
if not __debug__:
    raise SystemExit('Run without python -O or PYTHONOPTIMIZE: these checks rely on assert.')
import hashlib, json, subprocess
import prepare_reference as pr


def body_tokens(lines):
    return pr.lean_tokens(b''.join(l for l in lines if not l.startswith(b'import ')).decode())


def main():
    reference = json.loads(pr.REFERENCE.read_bytes())
    pending = [m for p in (pr.PORT / 'TCFloat/Equivalence').glob('*.lean') for m in pr.imports(p.read_text())]
    seen, out = set(), {}
    while pending:
        module = pending.pop()
        name = module.replace('.', '/') + '.lean'
        if name in seen:
            continue
        seen.add(name)
        origin = pr.legacy_module(module).replace('.', '/') + '.lean'
        if origin not in reference['files']:
            raise SystemExit(f'Unpinned original dependency: {name} (expected {origin})')
        data = (pr.REPO / name).read_bytes()
        pinned = subprocess.check_output(['git', 'show', f'{pr.PIN}:{origin}'], cwd=pr.REPO)
        a = body_tokens(pinned.splitlines(True))
        b = body_tokens([pr.legacy_import(l) for l in data.splitlines(True)])
        if len(a) != len(b):
            raise SystemExit(f'{name}: token count differs from the pin; not a pure rename')
        diffs = [[i, y, x] for i, (x, y) in enumerate(zip(a, b)) if x != y]
        if any(x.startswith('"') or y.startswith('"') for _, y, x in diffs):
            raise SystemExit(f'{name}: a string literal changed; not a pure rename')
        digest = hashlib.sha256(json.dumps(a, ensure_ascii=False, separators=(',', ':')).encode()).hexdigest()
        if digest != reference['files'][origin]['body_tokens_sha256']:
            raise SystemExit(f'{name}: pinned file does not match the reference manifest')
        if diffs:
            out[name] = diffs
        pending.extend(pr.imports(data.decode()))
    (pr.PORT / 'renamed-identifiers.json').write_text(json.dumps(dict(sorted(out.items())), indent=1) + '\n')
    pairs = {(y, x) for v in out.values() for _, y, x in v}
    print(f'{len(seen)} dependencies; {len(out)} with renames; {len(pairs)} distinct current/pinned pairs')


if __name__ == '__main__':
    main()
