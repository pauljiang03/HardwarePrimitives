#!/usr/bin/env python3
"""Differential test of the Lean model against the authors' MATLAB Matrix Core models.

Usage: python3 scripts/matlab_diff.py [--cases N] [--seed S] [--profiles p1,p2,...]
"""
import argparse
import hashlib
import json
import pathlib
import random
import subprocess
import sys
from fractions import Fraction

ROOT = pathlib.Path(__file__).resolve().parent.parent
WORK = ROOT / ".lake" / "matlab-diff"
MODEL = ROOT / ".lake" / "matlab-tensor-core"
PATCHED = ROOT / ".lake" / "matlab-tensor-core-patched"
REPO = "https://github.com/north-numerical-computing/MATLAB-tensor-core"
COMMIT = "79143bd"

# Special-value patch: an overflow takes the sign of the overflowing products; a NaN `c` stays NaN.
SPECIAL_OLD = """        if any(prd >= thr) && any(prd <= -thr)
            d = NaN;   % overflow on both positive and negative sides
        elseif (any(prd>=thr) && c<=-thr) || (any(prd<=-thr) && c>=thr)
            d = NaN;
        else
            d = max(prd)*Inf;   % overflow only on one side
        end"""
SPECIAL_NEW = """        if isnan(c) || (any(prd >= thr) && any(prd <= -thr))
            d = NaN;   % overflow on both positive and negative sides, or NaN c
        elseif (any(prd>=thr) && c<=-thr) || (any(prd<=-thr) && c>=thr)
            d = NaN;
        elseif any(prd >= thr)
            d = Inf;   % overflow only on the positive side
        else
            d = -Inf;  % overflow only on the negative side
        end"""

# (exponent bits, mantissa bits, bias, fnuz)
FP16 = (5, 10, 15, False)
BF16 = (8, 7, 127, False)
FP32 = (8, 23, 127, False)
E4M3 = (4, 3, 8, True)
E5M2 = (5, 2, 16, True)

# model: (a format, b format, k, normal exponent range, subnormal exponent range, xf32)
PROFILES = {
    "cdna1F16": (FP16, FP16, 16, (-14, 15), (-24, -14), False),
    "cdna1BF16": (BF16, BF16, 8, (-126, 63), (-133, -126), False),
    "cdna2F16": (FP16, FP16, 16, (-14, 15), (-24, -14), False),
    "cdna2BF16": (BF16, BF16, 16, (-126, 63), (-133, -126), False),
    "cdna2BF16_1k": (BF16, BF16, 16, (-126, 63), (-133, -126), False),
    "cdna3F16": (FP16, FP16, 16, (-14, 15), (-24, -14), False),
    "cdna3BF16": (BF16, BF16, 16, (-126, 63), (-133, -126), False),
    "cdna3XF32": (FP32, FP32, 8, (-126, 63), (-136, -126), True),
    "cdna3E4M3": (E4M3, E4M3, 16, (-7, 7), (-10, -7), False),
    "cdna3E5M2": (E5M2, E5M2, 16, (-15, 15), (-17, -15), False),
}
CDNA3 = [p for p in PROFILES if p.startswith("cdna3")]


def floor_log2(a):
    e = a.numerator.bit_length() - a.denominator.bit_length()
    while Fraction(2) ** e > a:
        e -= 1
    while Fraction(2) ** (e + 1) <= a:
        e += 1
    return e


def encode(fmt, v):
    """Word of `v` with its magnitude truncated to the format's grid (finite range assumed)."""
    eb, mb, bias, fnuz = fmt
    if v == 0:
        return 0
    sign = 1 if v < 0 else 0
    a = abs(v)
    e = max(floor_log2(a), 1 - bias)
    m = int(a / Fraction(2) ** (e - mb))
    if m == 0:
        return 0
    if m >= 2 ** mb:
        word = ((e + bias) << mb) | (m - 2 ** mb)
    else:
        word = m
    return (sign << (eb + mb)) | word


def decode(fmt, w):
    eb, mb, bias, fnuz = fmt
    s = (w >> (eb + mb)) & 1
    E = (w >> mb) & ((1 << eb) - 1)
    M = w & ((1 << mb) - 1)
    if fnuz and s and E == 0 and M == 0:
        return "nan"
    if not fnuz and E == (1 << eb) - 1:
        return "nan" if M else ("-inf" if s else "inf")
    v = Fraction(M, 1) * Fraction(2) ** (1 - bias - mb) if E == 0 else \
        Fraction((1 << mb) + M) * Fraction(2) ** (E - bias - mb)
    return -v if s else v


def to_hex64(v):
    import struct
    return struct.pack(">d", float(v)).hex()


def from_hex64(h):
    import struct
    return struct.unpack(">d", bytes.fromhex(h))[0]


def sample_value(rng, fmt, lo, hi):
    """Exponent-mantissa sampling: s uniform in (-(2 - 2^(1-f)), 2 - 2^(1-f)), e uniform."""
    f = fmt[1] + 1
    smax = 2 - 2.0 ** (1 - f)
    return Fraction(rng.uniform(-smax, smax)) * Fraction(2) ** rng.randint(lo, hi)


def sample_bits(rng, fmt):
    eb, mb, bias, fnuz = fmt
    while True:
        w = rng.getrandbits(1 + eb + mb)
        if decode(fmt, w) not in ("nan", "inf", "-inf"):
            return w


def generate(rng, profile, regime, n):
    fa, fb, k, normal, sub, xf32 = PROFILES[profile]
    cases = []
    for _ in range(n):
        if regime == "bits":
            a = [sample_bits(rng, fa) for _ in range(k)]
            b = [sample_bits(rng, fb) for _ in range(k)]
            c = sample_bits(rng, FP32)
        else:
            lo, hi = normal if regime == "normal" else sub
            clo, chi = (-126, 127) if regime == "normal" else (-149, -126)
            a = [encode(fa, sample_value(rng, fa, lo, hi)) for _ in range(k)]
            b = [encode(fb, sample_value(rng, fb, lo, hi)) for _ in range(k)]
            c = encode(FP32, Fraction(rng.uniform(-(2 - 2.0 ** -23), 2 - 2.0 ** -23)) *
                       Fraction(2) ** rng.randint(clo, chi))
        cases.append((a, b, c))
    return cases


def split_product(fmt, p):
    """Normal operands with a * b = p and e_a + e_b = floor(log2 |p|), as in the Lean tests."""
    if p == 0:
        return 0, encode(fmt, Fraction(1))
    h = -(floor_log2(abs(p)) // 2)
    return encode(fmt, p * Fraction(2) ** h), encode(fmt, Fraction(2) ** -h)


def two(e):
    return Fraction(2) ** e


def bits(lo, hi):
    return sum(two(-l) for l in range(lo, hi + 1))


def paper_cases(profile):
    """The paper's CDNA 3 vectors for the RD steps of Algorithm 1, as (products, c)."""
    if profile == "cdna3F16":
        vs = [([two(-22), two(-23) + two(-j)], 2 - two(-22)) for j in range(24, 33)]
        vs += [([-two(-21), -two(-22), -bits(24, j)], -2 + two(-21)) for j in range(28, 33)]
        vs += [([two(-24), two(-j)], Fraction(1)) for j in (31, 32)]
        vs += [([-two(-24), -bits(26, min(31, 30 + j))] + ([-bits(32, 30 + j)] if j >= 2 else []),
                Fraction(1)) for j in range(11)]
        vs += [([-two(-24), -bits(26, 32)], Fraction(1))]
    elif profile == "cdna3BF16":
        vs = [([two(-140), two(-150), two(-154 - j)], two(-127) - two(-140)) for j in range(11)]
        vs += [([s * two(-150), s * two(-152 - i)], Fraction(0)) for i in range(23) for s in (1, -1)]
    else:
        return []
    fmt = PROFILES[profile][0]
    k = PROFILES[profile][2]
    out = []
    for ps, c in vs:
        pairs = [split_product(fmt, p) for p in ps] + [(0, 0)] * (k - len(ps))
        out.append(([a for a, _ in pairs], [b for _, b in pairs], encode(FP32, c)))
    return out


def matlab_value(fmt, w, xf32):
    """The input value the MATLAB model receives: XF32 inputs arrive truncated to TF32."""
    if xf32:
        w &= ~((1 << 13) - 1)
    return decode(fmt, w)


def fetch_model():
    if not (MODEL / "models" / "tools" / "Generic_BFMA_TC.m").exists():
        subprocess.run(["git", "clone", "-q", REPO, str(MODEL)], check=True)
    subprocess.run(["git", "-C", str(MODEL), "checkout", "-q", COMMIT], check=True)
    hashes = {f: hashlib.sha256((MODEL / f).read_bytes()).hexdigest() for f in
              ["models/tools/Generic_BFMA_TC.m", "models/MI100MC.m", "models/MI210MC.m",
               "models/MI300AMC.m"]}
    src = (MODEL / "models" / "tools" / "Generic_BFMA_TC.m").read_text()
    if SPECIAL_OLD not in src:
        sys.exit("special-value block not found in Generic_BFMA_TC.m")
    (PATCHED / "models" / "tools").mkdir(parents=True, exist_ok=True)
    (PATCHED / "models" / "tools" / "Generic_BFMA_TC.m").write_text(src.replace(SPECIAL_OLD, SPECIAL_NEW))
    return hashes


def classify_lean(line):
    if line.startswith("F "):
        return decode(FP32, int(line[2:], 16))
    return {"I+": "inf", "I-": "-inf", "N": "nan"}.get(line, "error:" + line)


def classify_matlab(h):
    x = from_hex64(h)
    if x != x:
        return "nan"
    if x in (float("inf"), float("-inf")):
        return "inf" if x > 0 else "-inf"
    return Fraction(x)


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--cases", type=int, default=2000, help="cases per model and regime")
    ap.add_argument("--seed", type=int, default=0)
    ap.add_argument("--profiles", default=",".join(PROFILES))
    args = ap.parse_args()
    WORK.mkdir(parents=True, exist_ok=True)
    hashes = fetch_model()
    subprocess.run(["lake", "build", "mc_eval"], cwd=ROOT, check=True, capture_output=True)
    rng = random.Random(args.seed)
    report = {"commit": COMMIT, "sha256": hashes, "cases_per_regime": args.cases, "runs": []}
    for profile in args.profiles.split(","):
        fa, fb, k, _, _, xf32 = PROFILES[profile]
        cases = []
        for regime in ["normal", "subnormal", "bits"]:
            cases += [(regime,) + c for c in generate(rng, profile, regime, args.cases)]
        cases += [("paper",) + c for c in paper_cases(profile)]
        lean_in = WORK / f"{profile}.lean.txt"
        lean_in.write_text("".join(
            f"{profile} {','.join(f'{w:x}' for w in a)} {','.join(f'{w:x}' for w in b)} {c:x}\n"
            for _, a, b, c in cases))
        lean_out = subprocess.run([str(ROOT / ".lake" / "build" / "bin" / "mc_eval")],
                                  stdin=lean_in.open(), capture_output=True, text=True,
                                  check=True).stdout.split("\n")
        mat_in = WORK / f"{profile}.matlab.txt"
        mat_in.write_text("".join(
            f"{profile} {k} " + " ".join(to_hex64(matlab_value(fa, w, xf32)) for w in a) + " " +
            " ".join(to_hex64(matlab_value(fb, w, xf32)) for w in b) + " " +
            to_hex64(decode(FP32, c)) + "\n" for _, a, b, c in cases))
        variants = ["shipped"]
        if profile in CDNA3:
            variants += ["rdfix", "patched"]
        elif profile.startswith("cdna2"):
            variants += ["patched"]
        for variant in variants:
            mat_out_file = WORK / f"{profile}.{variant}.out.txt"
            model = PATCHED if variant == "patched" else MODEL
            flag = "rdfix" if variant == "patched" else variant
            subprocess.run(["octave", "--no-gui", "--quiet", "--eval",
                            f"cd('{ROOT / 'scripts' / 'matlab'}'); driver('{model}', "
                            f"'{mat_in}', '{mat_out_file}', '{flag}')"],
                           check=True, capture_output=True)
            mat_out = mat_out_file.read_text().split("\n")
            counts = {}
            examples = []
            for i, (regime, a, b, c) in enumerate(cases):
                lv, mv = classify_lean(lean_out[i]), classify_matlab(mat_out[i])
                key = regime
                counts.setdefault(key, [0, 0])
                counts[key][0] += 1
                if lv != mv:
                    counts[key][1] += 1
                    if len(examples) < 5:
                        examples.append({"regime": regime, "a": [f"{w:x}" for w in a],
                                         "b": [f"{w:x}" for w in b], "c": f"{c:x}",
                                         "lean": str(lv), "matlab": str(mv)})
            total = sum(v[1] for v in counts.values())
            print(f"{profile:14s} {variant:8s} " +
                  "  ".join(f"{r}: {m}/{n}" for r, (n, m) in counts.items()) +
                  f"   mismatches {total}")
            report["runs"].append({"profile": profile, "variant": variant, "counts": counts,
                                   "examples": examples})
    (WORK / "report.json").write_text(json.dumps(report, indent=1))
    print(f"report: {WORK / 'report.json'}")


if __name__ == "__main__":
    main()
