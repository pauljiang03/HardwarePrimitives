#!/usr/bin/env python3
"""Verify the `MatrixCore` sources against the pinned manifest and copy them to `reference-compat/`.

Usage: python3 scripts/prepare_reference.py [--pin]
"""
import hashlib
import json
import sys
from pathlib import Path

PORT = Path(__file__).resolve().parents[1]
REPO = PORT.parent
MANIFEST = PORT / "reference-manifest.json"
OUT = PORT / "reference-compat"


def lean_tokens(source):
    """Code tokens and string literals; whitespace and (nested) comments are ignored."""
    tokens, i = [], 0
    while i < len(source):
        if source[i].isspace():
            i += 1
        elif source.startswith("--", i):
            end = source.find("\n", i)
            i = len(source) if end < 0 else end
        elif source.startswith("/-", i):
            depth, i = 1, i + 2
            while depth and i < len(source):
                if source.startswith("/-", i):
                    depth, i = depth + 1, i + 2
                elif source.startswith("-/", i):
                    depth, i = depth - 1, i + 2
                else:
                    i += 1
            if depth:
                raise ValueError("unclosed Lean comment")
        elif source[i] == '"':
            start, i = i, i + 1
            while i < len(source):
                if source[i] == "\\":
                    i += 2
                elif source[i] == '"':
                    i += 1
                    break
                else:
                    i += 1
            tokens.append(source[start:i])
        elif source[i].isalnum() or source[i] == "_":
            start, i = i, i + 1
            while i < len(source) and (source[i].isalnum() or source[i] in "_'"):
                i += 1
            tokens.append(source[start:i])
        else:
            tokens.append(source[i])
            i += 1
    return tokens


def sources():
    files = [REPO / "MatrixCore.lean"] + sorted((REPO / "MatrixCore").rglob("*.lean"))
    return {str(f.relative_to(REPO)): f.read_text() for f in files}


def token_hash(text):
    return hashlib.sha256(json.dumps(lean_tokens(text), ensure_ascii=False).encode()).hexdigest()


def scoped_notation(text):
    lines = []
    for line in text.splitlines():
        for symbol, name in (("ℕ", "Nat"), ("ℤ", "Int"), ("ℚ", "Rat")):
            if line.startswith(f'notation "{symbol}"'):
                line = f'scoped notation (name := compat{name}) "{symbol}" => {name}'
        lines.append(line)
    out, inserted = [], False
    for line in lines:
        if line.startswith("scoped notation") and not inserted:
            out.append("namespace MatrixCore")
            inserted = True
        out.append(line)
    out.append("end MatrixCore")
    return "\n".join(out) + "\n"


def main():
    src = sources()
    hashes = {name: token_hash(text) for name, text in src.items()}
    if "--pin" in sys.argv:
        MANIFEST.write_text(json.dumps(hashes, indent=1, sort_keys=True) + "\n")
        print(f"Pinned {len(hashes)} Matrix-Core sources in {MANIFEST.name}")
    pinned = json.loads(MANIFEST.read_text())
    changed = sorted(n for n in set(pinned) | set(hashes) if pinned.get(n) != hashes.get(n))
    if changed:
        sys.exit("Matrix-Core sources differ from the pinned manifest (re-pin with --pin): " +
                 ", ".join(changed))
    for name, text in src.items():
        target = OUT / name
        target.parent.mkdir(parents=True, exist_ok=True)
        if name == "MatrixCore/Numerics/Notation.lean":
            text = scoped_notation(text)
        if not target.exists() or target.read_text() != text:
            target.write_text(text)
    print(f"Verified {len(src)} Matrix-Core sources against the manifest; "
          "compatibility copy prepared with scoped ℕ/ℤ/ℚ notation")


if __name__ == "__main__":
    main()
