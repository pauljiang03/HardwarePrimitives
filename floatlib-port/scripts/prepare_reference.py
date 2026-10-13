#!/usr/bin/env python3
"""Verify pinned Lean code and copy current sources into the compatibility project."""
if not __debug__:
    raise SystemExit('Run without python -O or PYTHONOPTIMIZE: these checks rely on assert.')
from pathlib import Path
import hashlib, json, re

PORT = Path(__file__).resolve().parents[1]
REPO = PORT.parent
PIN = "8829cccf4bad4629c5bf2eee2b8ff76b859c8158"
REFERENCE = PORT / "reference-manifest.json"
REFERENCE_SHA256 = "6ea0e28894e77de24c1ec1cad627134dc39cc7ef55de878df35f132b1635a25d"
OUT = PORT / "reference-compat"

def lean_tokens(source):
    """Preserve code tokens and string literals; ignore whitespace and nested comments."""
    tokens = []
    i = 0
    while i < len(source):
        if source[i].isspace():
            i += 1
        elif source.startswith('--', i):
            end = source.find('\n', i)
            i = len(source) if end < 0 else end
        elif source.startswith('/-', i):
            depth = 1
            i += 2
            while depth and i < len(source):
                if source.startswith('/-', i):
                    depth += 1
                    i += 2
                elif source.startswith('-/', i):
                    depth -= 1
                    i += 2
                else:
                    i += 1
            if depth:
                raise ValueError('Unclosed Lean comment')
        elif source[i] == '"':
            start = i
            i += 1
            while i < len(source):
                if source[i] == '\\':
                    i += 2
                elif source[i] == '"':
                    i += 1
                    break
                else:
                    i += 1
            tokens.append(source[start:i])
        elif source[i].isalnum() or source[i] == '_':
            start = i
            i += 1
            while i < len(source) and (source[i].isalnum() or source[i] in "_'"):
                i += 1
            tokens.append(source[start:i])
        else:
            tokens.append(source[i])
            i += 1
    return tokens

def imports(data):
    return [module for line in re.findall(r'^import ([^\n]+)', data, re.M)
            for module in line.split() if module.startswith('TensorCore.')]

# Identifiers renamed after the pinned revision, as [token index, current, pinned] per file.
# Restoring exactly these positions must reproduce the pinned token hash, so a passing check
# shows each parent source differs from the pin only by these renames.
RENAMED_POSITIONS = json.loads((PORT / 'renamed-identifiers.json').read_text())


def pinned_spelling(tokens, name):
    tokens = list(tokens)
    for index, current, pinned in RENAMED_POSITIONS.get(name, []):
        if index < len(tokens) and tokens[index] == current:
            tokens[index] = pinned
    return tokens


# Parent modules renamed after the pinned revision: current name -> pinned name.
RENAMED_MODULES = {
    'TensorCore.Numerics.Binary.ResidualBound': 'TensorCore.Numerics.Binary.ResidualBudget',
    'TensorCore.Numerics.DenormalizedProduct': 'TensorCore.Numerics.UnnormalizedProduct',
    'TensorCore.TC.CanonicalEAlignMin': 'TensorCore.TC.CanonicalFloor',
    'TensorCore.TC.ExtraAlignmentBits': 'TensorCore.TC.Padding',
    'TensorCore.TC.Models': 'TensorCore.TC.Profiles',
    'TensorCore.TC.Specification.Variants': 'TensorCore.TC.Specification.Profiles',
}


def legacy_module(module):
    """Resolve a parent module to its pinned reference-manifest key."""
    return RENAMED_MODULES.get(module, module)


def legacy_import(line):
    if not line.startswith(b'import '):
        return line
    words = line.decode().strip().split()
    return ('import ' + ' '.join(legacy_module(word) for word in words[1:]) + '\n').encode()


def body_hash(lines, name=''):
    body = b''.join(line for line in lines if not line.startswith(b'import ')).decode()
    tokens = json.dumps(pinned_spelling(lean_tokens(body), name), ensure_ascii=False, separators=(',', ':')).encode()
    return hashlib.sha256(tokens).hexdigest()


def main():
    reference_data = REFERENCE.read_bytes()
    if hashlib.sha256(reference_data).hexdigest() != REFERENCE_SHA256:
        raise RuntimeError('Pinned reference manifest checksum mismatch')
    reference = json.loads(reference_data)
    if reference['format'] != 1 or reference['revision'] != PIN:
        raise RuntimeError('Unexpected pinned reference manifest version or revision')
    pending = [module for p in (PORT/'TCFloat/Equivalence').glob('*.lean')
               for module in imports(p.read_text())]
    verified = {}
    pruned_imports = {}
    origins = {}
    sources = {}
    while pending:
        module = pending.pop()
        name = module.replace('.', '/') + '.lean'
        if name in verified:
            continue
        origin = legacy_module(module).replace('.', '/') + '.lean'
        origins[name] = origin
        if origin not in reference['files']:
            raise RuntimeError(f'Unpinned original dependency: {name}')
        pinned = reference['files'][origin]
        data = (REPO / name).read_bytes()
        digest = hashlib.sha256(data).hexdigest()
        if digest != pinned['source_sha256']:
            current_lines = [legacy_import(line) for line in data.splitlines(keepends=True)]
            if body_hash(current_lines, name) != pinned['body_tokens_sha256']:
                raise RuntimeError(f"Original arithmetic/proof source differs from pinned revision: {name}")
            old = pinned['imports']
            new = [line.decode() for line in current_lines if line.startswith(b'import ')]
            remaining = iter(old)
            if not all(any(line == candidate for candidate in remaining) for line in new):
                raise RuntimeError(f"Original imports are not a subset of pinned imports: {name}")
            pruned_imports[name] = [line.strip() for line in old if line not in new]
        verified[name] = digest
        sources[name] = data
        pending.extend(imports(data.decode()))

    for name, data in sources.items():
        if name == "TensorCore/Numerics/Notation.lean":
            data = data.replace(b'notation "', b'namespace TensorCore\nnotation "', 1) + b"\nend TensorCore\n"
            for symbol, suffix in [("ℕ", "Nat"), ("ℤ", "Int"), ("ℚ", "Rat")]:
                data = data.replace(f'notation "{symbol}"'.encode(),
                    f'scoped notation (name := compat{suffix}) "{symbol}"'.encode())
        target = OUT / name
        target.parent.mkdir(parents=True, exist_ok=True)
        if not target.exists() or target.read_bytes() != data:
            target.write_bytes(data)
    for stale in (OUT/'TensorCore').rglob('*.lean'):
        if str(stale.relative_to(OUT)) not in verified:
            stale.unlink()
    (OUT/'manifest.json').write_text(json.dumps({'revision':PIN,
        'reference_manifest_sha256':REFERENCE_SHA256,
        'comparison':'exact non-import code tokens and string literals; comments and whitespace ignored',
        'notation_shim':'three declarations renamed and scoped; same expansions',
        'removed_unused_imports':dict(sorted(pruned_imports.items())),
        'source_origin':dict(sorted(origins.items())),
        'source_sha256':dict(sorted(verified.items()))},indent=2)+'\n')
    print(f"Verified {len(verified)} parent dependencies against the reference manifest; compatibility sources prepared with scoped Nat/Int/Rat notation")

if __name__ == "__main__":
    main()
