#!/usr/bin/env python3
"""Compare `mc_floatlib` with `mc_eval` bit for bit on random inner products.

Usage: python3 scripts/compare.py [--cases N] [--seed S]
"""
import argparse
import random
import subprocess
import sys
from pathlib import Path

PORT = Path(__file__).resolve().parents[1]
REPO = PORT.parent

# (exponent bits, mantissa bits, fnuz)
FORMATS = {"f16": (5, 10, False), "bf16": (8, 7, False), "f32": (8, 23, False),
           "e4m3": (4, 3, True), "e5m2": (5, 2, True)}
PROFILES = {  # name: (a format, b format, N_FMA, k values)
    "sfma": ("f32", "f32", 1, [1, 3]),
    "cdna1F16": ("f16", "f16", 4, [4, 16]), "cdna1BF16": ("bf16", "bf16", 2, [2, 8]),
    "cdna2F16": ("f16", "f16", 4, [4, 16]), "cdna2BF16": ("bf16", "bf16", 2, [2, 16]),
    "cdna2BF16_1k": ("bf16", "bf16", 4, [4, 16]),
    "cdna3F16": ("f16", "f16", 8, [8, 16]), "cdna3BF16": ("bf16", "bf16", 8, [8, 16]),
    "cdna3XF32": ("f32", "f32", 4, [4, 8]),
    "cdna3E4M3": ("e4m3", "e4m3", 16, [16, 32]), "cdna3E5M2": ("e5m2", "e5m2", 16, [16, 32]),
    "cdna3E4M3E5M2": ("e4m3", "e5m2", 16, [16, 32]),
}


def word(fmt, sign, exp_field, frac):
    eb, mb, _ = FORMATS[fmt]
    return (sign << (eb + mb)) | (exp_field << mb) | frac


def finite(rng, fmt, lo=None, hi=None):
    eb, mb, fnuz = FORMATS[fmt]
    top = (1 << eb) - 1 if fnuz else (1 << eb) - 2
    lo = 1 if lo is None else max(0, lo)
    hi = top if hi is None else min(top, hi)
    e = rng.randint(lo, hi)
    w = word(fmt, rng.randint(0, 1), e, rng.randrange(1 << mb))
    if fnuz and w == 1 << (eb + mb):
        w = 0
    return w


def any_word(rng, fmt):
    eb, mb, _ = FORMATS[fmt]
    return rng.randrange(1 << (1 + eb + mb))


def extreme(rng, fmt):
    eb, mb, fnuz = FORMATS[fmt]
    if fnuz:
        return rng.choice([1 << (eb + mb), word(fmt, 0, (1 << eb) - 1, (1 << mb) - 1),
                           word(fmt, 1, (1 << eb) - 1, (1 << mb) - 1), 0, 1])
    inf = (1 << eb) - 1
    return rng.choice([word(fmt, 0, inf, 0), word(fmt, 1, inf, 0), word(fmt, 0, inf, 1),
                       word(fmt, 1, inf, 1 << (mb - 1)), word(fmt, 0, inf - 1, (1 << mb) - 1),
                       word(fmt, 1, inf - 1, (1 << mb) - 1), 1 << (eb + mb), 0])


def case(rng, regime, profile):
    fa, fb, _, ks = PROFILES[profile]
    k = rng.choice(ks)
    if regime == "bits":
        a = [any_word(rng, fa) for _ in range(k)]
        b = [any_word(rng, fb) for _ in range(k)]
        c = any_word(rng, "f32")
    elif regime == "normal":
        a = [finite(rng, fa) for _ in range(k)]
        b = [finite(rng, fb) for _ in range(k)]
        c = finite(rng, "f32")
    elif regime == "narrow":
        def near(fmt):
            eb, _, _ = FORMATS[fmt]
            mid = rng.randint(1, (1 << eb) - 2)
            return lambda: finite(rng, fmt, mid - 3, mid + 3)
        na, nb = near(fa), near(fb)
        a = [na() for _ in range(k)]
        b = [nb() for _ in range(k)]
        ea = (a[0] >> FORMATS[fa][1]) % (1 << FORMATS[fa][0]) - ((1 << (FORMATS[fa][0] - 1)) - 1)
        eb_ = (b[0] >> FORMATS[fb][1]) % (1 << FORMATS[fb][0]) - ((1 << (FORMATS[fb][0] - 1)) - 1)
        ec = max(1, min(254, ea + eb_ + 127 + rng.randint(-30, 30)))
        c = word("f32", rng.randint(0, 1), ec, rng.randrange(1 << 23))
    elif regime == "tiny":
        a = [finite(rng, fa, 0, 2) for _ in range(k)]
        b = [finite(rng, fb, 0, 2) for _ in range(k)]
        c = rng.choice([0, 1 << 31, word("f32", rng.randint(0, 1), 0, rng.randrange(1 << 23))])
    else:
        a = [finite(rng, fa) for _ in range(k)]
        b = [finite(rng, fb) for _ in range(k)]
        c = finite(rng, "f32")
        for _ in range(rng.randint(1, 2)):
            slot = rng.randrange(2 * k + 1)
            if slot < k:
                a[slot] = extreme(rng, fa)
            elif slot < 2 * k:
                b[slot - k] = extreme(rng, fb)
            else:
                c = extreme(rng, "f32")
    hx = lambda ws: ",".join(f"{w:x}" for w in ws)
    return f"{profile} {hx(a)} {hx(b)} {c:x}"


def run(exe, lines):
    out = subprocess.run([str(exe)], input="\n".join(lines) + "\n", capture_output=True,
                         text=True, check=True).stdout.split("\n")
    return out[:len(lines)]


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--cases", type=int, default=5000, help="cases per model and regime")
    ap.add_argument("--seed", type=int, default=1)
    args = ap.parse_args()
    for d in (REPO, PORT):
        subprocess.run(["lake", "build", "mc_eval" if d == REPO else "mc_floatlib"], cwd=d,
                       check=True, capture_output=True)
    ref, flt = REPO / ".lake/build/bin/mc_eval", PORT / ".lake/build/bin/mc_floatlib"
    rng = random.Random(args.seed)
    total = bad = 0
    for profile in PROFILES:
        counts = []
        for regime in ("bits", "normal", "narrow", "tiny", "special"):
            lines = [case(rng, regime, profile) for _ in range(args.cases)]
            r, f = run(ref, lines), run(flt, lines)
            miss = [(l, x, y) for l, x, y in zip(lines, r, f) if x != y]
            total += len(lines)
            bad += len(miss)
            counts.append(f"{regime} {len(miss)}")
            for l, x, y in miss[:3]:
                print(f"  MISMATCH {l}\n    MatrixCore {x}   FloatLib {y}")
        print(f"{profile:14} " + "  ".join(counts))
    print(f"{total} inner products, {bad} mismatches")
    sys.exit(1 if bad else 0)


if __name__ == "__main__":
    main()
