#!/usr/bin/env python3
"""Run every check of the FloatLib implementation.

1. Verify the Matrix-Core sources against the pinned manifest and prepare `reference-compat/`.
2. `lake build`: the implementation, the equivalence proofs, the audit and the examples. The
   build fails on any error; warnings outside the generated reference copy are reported.
3. Compare `mc_floatlib` with Matrix-Core's `mc_eval` on random inner products.

Usage: python3 scripts/check.py [--cases N] [--seed S]
"""
import argparse
import subprocess
import sys
from pathlib import Path

PORT = Path(__file__).resolve().parents[1]


def step(name, cmd):
    print(f"--- {name}", flush=True)
    result = subprocess.run(cmd, cwd=PORT, capture_output=True, text=True)
    out = result.stdout + result.stderr
    if result.returncode != 0:
        print(out)
        sys.exit(f"FAILED: {name}")
    return out


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--cases", type=int, default=2000, help="comparison cases per model and regime")
    ap.add_argument("--seed", type=int, default=1)
    args = ap.parse_args()
    print(step("reference sources", ["python3", "scripts/prepare_reference.py"]).strip())
    out = step("lake build", ["lake", "build"])
    for line in out.splitlines():
        if line.startswith("info:") and "Audit.lean" in line:
            print(line.split(": ", 2)[-1])
    warnings = [l for l in out.splitlines()
                if l.startswith("warning:") and "reference-compat/" not in l]
    print(f"ok   lake build ({len(warnings)} warnings outside reference-compat)")
    for w in warnings:
        print("     " + w)
    out = step("comparison with mc_eval",
               ["python3", "scripts/compare.py", "--cases", str(args.cases), "--seed", str(args.seed)])
    print(out.strip().splitlines()[-1])
    print("ok   all checks")


if __name__ == "__main__":
    main()
