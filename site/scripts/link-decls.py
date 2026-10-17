#!/usr/bin/env python3
"""Resolve Lean declaration links in the site's Markdown.

- `{{Name}}` becomes [`Name`](GitHub link to the declaration's line).
- Existing [`Name`](GitHub ...lean#Lnn) links are refreshed to the current file and line.
Run from anywhere; fails if a name cannot be resolved uniquely.
"""
import re, subprocess, sys
from pathlib import Path

SITE = Path(__file__).resolve().parents[1]
REPO = SITE.parent
BLOB = 'https://github.com/pauljiang03/HardwarePrimitives/blob/main/'
DECL = re.compile(r"^\s*(?:@\[[^\]]*\]\s*)?(?:(?:private|protected|noncomputable|partial)\s+)*"
                  r"(?:theorem|lemma|def|abbrev|structure|inductive|class|instance)\s+([^\s(:{\[]+)")


def declarations():
    files = subprocess.check_output(['git', 'ls-files', '*.lean'], cwd=REPO, text=True).split()
    found = {}
    for f in files:
        if 'floatlib-port/reference-compat/' in f or f.startswith('site/'):
            continue
        stack = []
        for no, line in enumerate((REPO / f).read_text().splitlines(), 1):
            m = re.match(r'^namespace\s+(\S+)', line)
            if m:
                stack.append(m.group(1)); continue
            m = re.match(r'^end\s+(\S+)', line)
            if m and stack and stack[-1] == m.group(1):
                stack.pop(); continue
            m = DECL.match(line)
            if m:
                full = '.'.join(stack + [m.group(1)])
                found.setdefault(full, []).append((f, no))
    return found


def resolve(name, decls):
    hits = [(full, loc) for full, locs in decls.items()
            if full == name or full.endswith('.' + name) for loc in locs]
    if len(hits) > 1:
        # The FloatLib ports mirror some names; the main libraries are the canonical source.
        hits = [h for h in hits if 'floatlib-port/' not in h[1][0]] or hits
    if len(hits) > 1:
        # A name shared by the NVIDIA and AMD libraries means the NVIDIA one; write
        # `MatrixCore.Name` for the AMD one.
        hits = [h for h in hits if not h[1][0].startswith('amd/')] or hits
    if len(hits) > 1:
        # An unqualified name means the least-nested declaration (e.g. not ExtractionGrid.*).
        depth = min(h[0].count('.') for h in hits)
        hits = [h for h in hits if h[0].count('.') == depth]
    if len(hits) != 1:
        raise SystemExit(f'cannot resolve {name!r}: {hits}')
    f, no = hits[0][1]
    return f'{BLOB}{f}#L{no}'


def main():
    decls = declarations()
    link = re.compile(r'\[`([A-Za-z_][\w.\']*)`\]\(' + re.escape(BLOB) + r'[^)#]+\.lean#L\d+\)')
    for page in (SITE / 'src/content/docs').rglob('*.md*'):
        text = page.read_text()
        new = re.sub(r'\{\{([A-Za-z_][\w.\']*)\}\}',
                     lambda m: f'[`{m.group(1)}`]({resolve(m.group(1), decls)})', text)
        new = link.sub(lambda m: f'[`{m.group(1)}`]({resolve(m.group(1), decls)})', new)
        if new != text:
            page.write_text(new)
            print('updated', page.relative_to(SITE))


if __name__ == '__main__':
    main()
