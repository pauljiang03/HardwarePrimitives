#!/usr/bin/env python3
"""Validate Matrix-Core.

1. Build the library, the paper's test vectors and the trust audit (`lake build`), optionally
   from a clean build directory.
2. Check every worked example under `examples/`.
3. Elaborate every ```lean code block in the README, the results summary, the guide, the paper
   notes and the test walkthrough, each as a standalone file.

Usage: python3 scripts/check.py [--clean]
"""
import pathlib
import re
import shutil
import subprocess
import sys
import tempfile

ROOT = pathlib.Path(__file__).resolve().parent.parent
DOCS = [ROOT / "README.md", ROOT / "tests" / "README.md", *sorted((ROOT / "docs").rglob("*.md"))]
BLOCK = re.compile(r"```lean\n(.*?)```", re.S)


def run(cmd, what):
    proc = subprocess.run(cmd, cwd=ROOT, capture_output=True, text=True)
    out = proc.stdout + proc.stderr
    errors = [line for line in out.splitlines() if ": error" in line or line.startswith("error")]
    if proc.returncode != 0 or errors:
        print(f"FAIL {what}")
        print(out)
        sys.exit(1)
    return out


def main():
    if "--clean" in sys.argv:
        shutil.rmtree(ROOT / ".lake" / "build", ignore_errors=True)
    out = run(["lake", "build"], "lake build")
    for line in out.splitlines():
        if "_audit" in line or "negative_control" in line:
            print(line.split(": ", 2)[-1])
    warnings = [line for line in out.splitlines() if "warning" in line]
    print(f"ok   lake build ({len(warnings)} warnings)")

    for ex in sorted((ROOT / "examples").glob("*.lean")):
        run(["lake", "env", "lean", str(ex)], ex.name)
        print(f"ok   {ex.relative_to(ROOT)}")

    with tempfile.TemporaryDirectory(dir=ROOT / ".lake") as tmp:
        count = 0
        for doc in DOCS:
            for i, block in enumerate(BLOCK.findall(doc.read_text())):
                path = pathlib.Path(tmp) / f"{doc.stem}_{i}.lean"
                path.write_text(block)
                run(["lake", "env", "lean", str(path)], f"{doc.relative_to(ROOT)} block {i + 1}")
                count += 1
        print(f"ok   {count} documentation code blocks")


if __name__ == "__main__":
    main()
