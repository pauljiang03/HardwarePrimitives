#!/usr/bin/env python3
"""Assemble the targeted hardware-validation suite from the Lean models' own predictions.

Every predicted output word comes from an `#eval` of the models, not from this script:

* `scripts/targeted/TensorCoreCases.lean` evaluates `TensorCore.runBlocks` (NVIDIA), run from the
  repository root;
* `scripts/targeted/MatrixCoreCases.lean` evaluates `MatrixCore.dotBits` (AMD), run from `amd/`.

This script runs both (or reads their saved output), formats the words as hex, attaches each
case's purpose, suggested instruction, Lean source and the meaning of a mismatch, and checks the
predictions against the values stated by the kernel-checked theorems the witnesses come from.

Usage (from `ozaki/`):

    python3 scripts/targeted_validation.py > data/targeted-validation.json
    python3 scripts/targeted_validation.py --tc tc.txt --mc mc.txt > data/targeted-validation.json
"""
import json
import os
import re
import subprocess
import sys
from fractions import Fraction

HERE = os.path.dirname(os.path.abspath(__file__))
OZAKI = os.path.dirname(HERE)
ROOT = os.path.dirname(OZAKI)

# --------------------------------------------------------------------------------------------
# Running the Lean scripts


def lean_lines(cwd, script):
    out = subprocess.run(["lake", "env", "lean", script], cwd=cwd, capture_output=True,
                         text=True, check=True).stdout
    return out.splitlines()


def read_lines(path):
    with open(path) as f:
        return f.read().splitlines()


# --------------------------------------------------------------------------------------------
# Formats

def input_format(vendor, model):
    p = model.lower()
    if vendor == "AMD":
        if p.startswith("sfma"):
            return "binary32"
        if "xf32" in p:
            return "xf32"
        if "fp8" in p:
            m = re.search(r"(e4m3fnuz|e5m2fnuz) (e4m3fnuz|e5m2fnuz)", model)
            return f"fp8 {m.group(1)}/{m.group(2)}" if m else "fp8"
        return "bf16" if "bf16" in p else "fp16"
    if "tf32" in p:
        return "tf32"
    return "bf16" if "bf16" in p else "fp16"


def hexw(n, bits):
    return f"0x{n:0{(bits + 3) // 4}X}"


WIDTH = {"fp16": 16, "bf16": 16, "tf32": 19, "binary32": 32, "xf32": 32}


def width(fmt):
    return 8 if fmt.startswith("fp8") else WIDTH[fmt]


def f32_hex(n):
    return f"0x{n:08X}"


def frac_str(s):
    """A rational printed by Lean (`n` or `n/d`), with a decimal approximation."""
    if s == "none":
        return None
    q = Fraction(s)
    if q.denominator == 1:
        return str(q.numerator)
    e = 0
    d = q.denominator
    while d % 2 == 0:
        d //= 2
        e += 1
    if d == 1:
        return f"{q.numerator} * 2^-{e}"
    return s


# --------------------------------------------------------------------------------------------
# Instructions and sources

NV_INSTR = {
    "v100F16F32": "V100: mma.sync.aligned.m8n8k4.row.col.f32.f16.f16.f32 (HMMA.884, k = 4, one "
                  "block FMA); or WMMA m16n16k16 (HMMA.844, four block FMAs of size 4) with the vector "
                  "in k = 0..3 and zeros elsewhere",
    "ampereF16F32": "A100: mma.sync.aligned.m16n8k8.row.col.f32.f16.f16.f32 (HMMA.1688, k = 8, one "
                    "block FMA); or m16n8k16 / WMMA m16n16k16 (two block FMAs of size 8) with the "
                    "vector in k = 0..7",
    "hopperF16F32": "H100: mma.sync.aligned.m16n8k16.row.col.f32.f16.f16.f32 or WMMA m16n16k16 "
                    "(HMMA.16816, k = 16, one block FMA)",
    "a100BF16F32": "A100: mma.sync.aligned.m16n8k8.row.col.f32.bf16.bf16.f32 (k = 8, one block FMA)",
    "hopperBF16F32": "H100: mma.sync.aligned.m16n8k16.row.col.f32.bf16.bf16.f32 (k = 16, one block "
                     "FMA)",
    "a100TF32F32": "A100: mma.sync.aligned.m16n8k4.row.col.f32.tf32.tf32.f32 (k = 4, one block FMA); "
                   "8-term vectors: m16n8k8 (two chained block FMAs of size 4)",
    "hopperTF32MmaF32": "H100: mma.sync.aligned.m16n8k8.row.col.f32.tf32.tf32.f32 (k = 8, one block "
                        "FMA of size 8)",
    "hopperTF32WmmaF32": "H100: wmma.mma.sync.aligned.m16n16k8.f32.tf32.tf32.f32 (k = 8, two chained "
                         "block FMAs of size 4); extend 4-term vectors with zeros",
}

MC_INSTR = {
    "sfmaF32": "CDNA 1/2/3: v_mfma_f32_16x16x4f32 (k = 4; an SFMA chain, so longer vectors chain "
               "D -> C over several instructions, k in increasing order); 1-term: v_mfma_f32_32x32x1f32",
    "cdna1F16": "MI100: v_mfma_f32_32x32x4f16 (k = 4, one block) for 4-term vectors; "
                "v_mfma_f32_32x32x8f16 (k = 8, two blocks of 4) for 8-term vectors",
    "cdna2F16": "MI210/MI250: v_mfma_f32_32x32x4f16 (k = 4, one pairwise block) for 4-term "
                "vectors; v_mfma_f32_32x32x8f16 (k = 8, two blocks of 4) for 8-term vectors",
    "cdna3F16": "MI300: v_mfma_f32_32x32x8_f16 (k = 8, one block of 8)",
    "cdna1BF16": "MI100: v_mfma_f32_32x32x2bf16 (k = 2, one block)",
    "cdna2BF16": "MI210/MI250: v_mfma_f32_32x32x2bf16 (k = 2, one block)",
    "cdna2BF16_1k": "MI210/MI250: v_mfma_f32_32x32x4bf16_1k (k = 4, one block)",
    "cdna3BF16": "MI300: v_mfma_f32_32x32x8_bf16 (k = 8, one block of 8)",
    "cdna3XF32": "MI300: v_mfma_f32_32x32x4_xf32 (k = 4, one block); or 16x16x8_xf32 with zeros in "
                 "k = 4..7",
    "cdna3FP8 e4m3fnuz e4m3fnuz": "MI300: v_mfma_f32_32x32x16_fp8_fp8 (k = 16, one block)",
    "cdna3FP8 e5m2fnuz e5m2fnuz": "MI300: v_mfma_f32_32x32x16_bf8_bf8 (k = 16, one block)",
}

ARCH = {
    "v100F16F32": "V100", "ampereF16F32": "A100", "hopperF16F32": "H100",
    "a100BF16F32": "A100", "hopperBF16F32": "H100", "a100TF32F32": "A100",
    "hopperTF32MmaF32": "H100", "hopperTF32WmmaF32": "H100",
    "sfmaF32": "CDNA 1/2/3", "cdna1F16": "CDNA 1 (MI100)", "cdna2F16": "CDNA 2 (MI210/MI250)",
    "cdna3F16": "CDNA 3 (MI300)", "cdna1BF16": "CDNA 1 (MI100)", "cdna2BF16": "CDNA 2 (MI210/MI250)",
    "cdna2BF16_1k": "CDNA 2 (MI210/MI250)", "cdna3BF16": "CDNA 3 (MI300)",
    "cdna3XF32": "CDNA 3 (MI300)", "cdna3FP8 e4m3fnuz e4m3fnuz": "CDNA 3 (MI300)",
    "cdna3FP8 e5m2fnuz e5m2fnuz": "CDNA 3 (MI300)",
}

TC_EVAL = "computed by #eval of TensorCore.runBlocks in ozaki/scripts/targeted/TensorCoreCases.lean"
MC_EVAL = "computed by #eval of MatrixCore.dotBits in ozaki/scripts/targeted/MatrixCoreCases.lean"
TC_MODELS = "TensorCore/TC/CanonicalDefs.lean, TensorCore/TC/CanonicalFormatDefs.lean"
MC_MODELS = "amd/MatrixCore/MC/Models.lean"

# Per-family metadata: (regex on the base id, category, purpose, Lean source, mismatch meaning).
FAMILIES = [
    # ---- full block FMAs
    (r"^nv-a100-f16-full-block$", "full-block-exactness",
     "Seven products 2047^2 (11-bit integers) in one A100 block FMA: the exact sum 29331463 needs 25 "
     "bits, so the FP32 output truncates it to 29331462.",
     "Ozaki.TC.a100_full_blockFMA (ozaki/OzakiTC/Limits.lean:51)",
     "0x4BDFC804 (29331464) means the final conversion rounds to nearest rather than truncating; "
     "any other value means that the FMA size, the alignment to F = 24 fraction bits or the exact "
     "sum inside the block FMA is wrong. This is the case that limits Ozaki slices to fewer bits on "
     "A100."),
    (r"^nv-h100-f16-full-block$", "full-block-exactness",
     "Fifteen products 2047^2 and one 2047*2046 in one H100 block FMA of size 16: exact sum "
     "67041297, truncated to 67041296.",
     "example at ozaki/OzakiTC/TwoPass.lean:565",
     "Truncation and round-to-nearest agree here (the binary32 neighbours are 67041296 and "
     "67041300), so the case tests the FMA size 16 and the exact sum: 0x4C7FBE05 (67041300) would "
     "mean rounding up, other values a different K or F = 25. Pass 2 of nv-h100-f16-two-pass "
     "tests the residual."),
    (r"^nv-h100-tf32mma-full-block$", "h100-tf32-mma",
     "The A100 full-block witness in TF32 on H100 MMA (K = 8, F = 25): 7 x 2047^2 = 29331463 "
     "truncated to 29331462.",
     "constructed; analogue of Ozaki.TC.a100_full_blockFMA",
     "Any other output means the H100 TF32 MMA model (K = 8, F = 25, truncation) is wrong."),
    (r"^nv-a100-f16-exact-not-binary32$", "full-block-exactness",
     "5 x 2047^2 + 1 - 2 x 2047^2 = 12570628: exact in one A100 block FMA, while left-to-right "
     "binary32 additions give 12570626.",
     "Ozaki.TC.a100_exact_where_binary32_is_not (ozaki/OzakiTC/Limits.lean:62)",
     "12570626 means the hardware accumulates in binary32 steps rather than with one wide "
     "alignment; the model's exact sum inside the block FMA would be wrong."),
    (r"^amd-cdna3-f16-full-block$", "full-block-exactness",
     "CDNA 3 version of the full block: 7 x 2047^2 = 29331463 is rounded to nearest (even) as "
     "29331464, where the A100 truncates to 29331462 (cross-vendor difference on identical inputs).",
     "Ozaki.MC.cdna3F16_full_blockFMA (ozaki/OzakiMC/Limits.lean:34)",
     "29331462 would mean truncation (as on NVIDIA); 29331463 is not representable in binary32."),
    (r"^amd-cdna[123]-f16-exact-not-sfma$", "full-block-exactness",
     "The 8-term vector 5 x 2047^2 + 1 - 2 x 2047^2 on the fp16 variant is exact (12570628).",
     "Ozaki.MC.fp16_exact_where_sfma_is_not (ozaki/OzakiMC/Limits.lean:51)",
     "Another value means the fp16 block (exact sum / pairwise sums in binary32 / global "
     "alignment) differs from the model."),
    (r"^amd-sfma-f32-not-exact$", "full-block-exactness",
     "The same vector as binary32 words on the f32 MFMA (sequential FMA): rounds to 12570626.",
     "Ozaki.MC.fp16_exact_where_sfma_is_not (ozaki/OzakiMC/Limits.lean:51)",
     "12570628 would mean the f32 MFMA does not round after each step (not an SFMA chain), or "
     "uses another order."),
    # ---- cancellation
    (r"^nv-a100-f16-cancel-zero$", "cancellation",
     "Four 2^22 and four -2^22 in one A100 block FMA (total magnitude 2^25, twice the 2^24 "
     "exactness bound): exact 0.",
     "Ozaki.TC.a100_cancel_zero (ozaki/OzakiTC/Cancellation.lean:349)",
     "A nonzero output means the sum inside the block FMA is not exact for large cancelling terms, "
     "which would invalidate the cancellation-exactness theorems."),
    (r"^nv-a100-f16-cancel-2047$", "cancellation",
     "Four 2047^2 and three -2047^2: magnitude 7 x 2047^2 > 2^24, result exactly 2047^2 = 4190209.",
     "Ozaki.TC.a100_cancel_2047 (ozaki/OzakiTC/Cancellation.lean:359)",
     "Another output means the aligned sum inside the block FMA loses bits when only the result "
     "fits in 24 bits."),
    (r"^nv-h100-f16-cancel-zero$", "cancellation",
     "Eight 2^22 and eight -2^22, a full H100 block FMA of size 16: exact 0.",
     "Ozaki.TC.h100_cancel_zero (ozaki/OzakiTC/Cancellation.lean:368)",
     "A nonzero output means the H100 sum inside the block FMA is not exact."),
    (r"^nv-h100-tf32mma-cancel-zero$", "h100-tf32-mma",
     "The cancellation witness in TF32 on H100 MMA: four 2^22, four -2^22, exact 0.",
     "constructed; analogue of Ozaki.TC.h100_cancel_zero",
     "A nonzero output means the H100 TF32 MMA sum inside the block FMA is not exact."),
    (r"^amd-cdna3-f16-cancel-zero$", "cancellation",
     "Four 2^22 and four -2^22 in one CDNA 3 block of 8: +0.",
     "Ozaki.MC.cdna3_cancel_zero (ozaki/OzakiMC/Cancellation.lean:327)",
     "A nonzero output means CDNA 3's global alignment loses the cancelling terms."),
    (r"^amd-cdna[12]-f16-cancel-c$", "cancellation",
     "c = 2^23 and products 2^22, -2^22, 2^22, -2^22: exactly 2^23 (on CDNA 2 every one of the "
     "pairwise sums cancels).",
     "Ozaki.MC.cdna12_cancel_c (ozaki/OzakiMC/Cancellation.lean:338)",
     "Another output means c is not combined exactly with cancelling products."),
    # ---- two passes
    (r"^nv-a100-f16-two-pass$", "two-pass",
     "Two passes of the A100 full block: pass 1 (c = +0) gives D1 = 29331462; pass 2 from "
     "c = -D1 gives D2 = 1; D1 + D2 = 29331463 exactly.",
     "examples at ozaki/OzakiTC/TwoPass.lean:557 and :560 (Ozaki.TC.twoPass)",
     "Pass 2 != 1.0 means the accumulator does not hold S - D1 exactly when c = -D1 "
     "(Ozaki.TC.twoPass_exact's hardware premise fails). Pass 2's c is the model's -D1; if pass 1 "
     "matches it is the device's own -D1."),
    (r"^nv-h100-f16-two-pass$", "two-pass",
     "Two passes of the H100 block FMA: D1 = 67041296, D2 = 1, sum 67041297.",
     "examples at ozaki/OzakiTC/TwoPass.lean:565 and :569",
     "Pass 2 != 1.0 means two-pass recovery fails on H100."),
    (r"^nv-h100-tf32mma-two-pass$", "h100-tf32-mma",
     "Two passes of the TF32 full block on H100 MMA: D1 = 29331462, D2 = 1.",
     "constructed; Ozaki.TC.twoPass on hopperTF32MmaF32",
     "Pass 2 != 1.0 means two-pass recovery fails on the H100 TF32 MMA variant."),
    (r"^amd-cdna3-f16-two-pass$", "two-pass",
     "Two passes of the CDNA 3 full block: D1 = 29331464, D2 = -1, sum 29331463.",
     "Ozaki.MC.cdna3F16_twoPass_full_blockFMA (ozaki/OzakiMC/TwoPass.lean:635)",
     "Pass 2 != -1.0 means CDNA 3's late-c alignment loses S - D1."),
    (r"^amd-sfma-f32-two-prod$", "two-pass",
     "SFMA two passes are TwoProdFMA: (2^24 - 1)^2 rounds to 2^48 - 2^25; pass 2 returns 1.",
     "Ozaki.MC.sfma_twoProd (ozaki/OzakiMC/TwoPass.lean:642)",
     "Pass 2 != 1.0 means the f32 MFMA does not compute c + a*b with one rounding (no fused "
     "product)."),
    (r"^amd-cdna2-f16-two-pass-fails$", "two-pass",
     "CDNA 2: products 2^22 and 2^-14; the pairwise sums round 2^22 + 2^-14 to 2^22 before c is "
     "added, so pass 2 from c = -2^22 returns 0 and two passes miss 2^-14.",
     "Ozaki.MC.cdna2_twoPass_fails (ozaki/OzakiMC/TwoPass.lean:653)",
     "Pass 2 = 2^-14 (0x38800000) would mean CDNA 2 adds c before rounding the product pair (no "
     "rounded pairwise sums), and two-pass recovery would hold on CDNA 2 after all."),
    (r"^amd-cdna1-f16-two-pass-recovers$", "two-pass",
     "The same block on CDNA 1, which sums exactly: pass 2 returns 2^-14 and two passes recover "
     "2^22 + 2^-14.",
     "Ozaki.MC.cdna2_twoPass_fails (ozaki/OzakiMC/TwoPass.lean:653)",
     "Pass 2 = 0 would mean CDNA 1 rounds inside the block."),
    # ---- non-monotonicity
    (r"^nv-v100-f16-nonmonotone$", "non-monotonicity",
     "Lowering c from 1 to 1 - 1ulp or 1 - 2ulp raises the V100 output from 0x3F800000 to "
     "0x3F800001 (TC-EFT Theorem III.4/III.5 at K = 4, p = 0); at 1 - 3ulp it is 1 again.",
     "TensorCore.nonmonotone_v100_family, range_witnesses (tests/TensorCoreTests/TC/"
     "Monotonicity.lean:11, :120)",
     "Monotone outputs mean the alignment exponent does not follow c's exponent as modeled."),
    (r"^nv-a100-f16-nonmonotone$", "non-monotonicity",
     "The A100 c-family (K = 8, p = 1, products 2^-25): c = 1 gives 1, c = 1 - 1ulp gives "
     "1 + 1ulp.",
     "TensorCore.nonmonotone_ampere_hopper_witnesses, range_witnesses (tests/TensorCoreTests/TC/"
     "Monotonicity.lean:102, :120)",
     "Monotone outputs mean A100's alignment differs from the model (K, F = 24 or truncation)."),
    (r"^nv-h100-f16-nonmonotone$", "non-monotonicity",
     "The H100 c-family (K = 16, p = 2, products 2^-26).",
     "TensorCore.nonmonotone_ampere_hopper_witnesses, range_witnesses (tests/TensorCoreTests/TC/"
     "Monotonicity.lean:102, :120)",
     "Monotone outputs mean H100's alignment differs from the model."),
    (r"^nv-h100-tf32mma-c-family$", "h100-tf32-mma",
     "The H100 FP16 c-family inputs in TF32 at the MMA FMA size 8 < 3 * 2^2: below the "
     "threshold of TC-EFT Theorem III.4, so the model predicts no inversion (both outputs 1.0).",
     "constructed; TensorCore.nonmonotone_encoded (TensorCore/TC/Monotonicity.lean:273), "
     "below_threshold_monotone (tests/TensorCoreTests/TC/Monotonicity.lean:113)",
     "0x3F800001 for c = 1 - 1ulp would mean an FMA size larger than 8 or fewer extra alignment "
     "bits on the TF32 MMA variant."),
    (r"^amd-cdna2-f16-nonmonotone$", "non-monotonicity",
     "CDNA 2 fp16: raising p1 from -2^-10 (subnormal operand, flushed) to -2^-11 (normal) lowers "
     "the output from 0 to -2^-11.",
     "MatrixCore.cdna2F16_nonmonotonic (amd/MatrixCore/MC/ProductMonotonicity.lean:146)",
     "x giving -2^-10 means subnormal fp16 inputs are not flushed on CDNA 2."),
    (r"^amd-cdna2-bf16-nonmonotone$", "non-monotonicity",
     "CDNA 2 bf16: -2^-27 (subnormal operand, flushed) rises to -2^-28; output falls 0 -> -2^-28.",
     "MatrixCore.cdna2BF16_nonmonotonic (amd/MatrixCore/MC/ProductMonotonicity.lean:152)",
     "x giving -2^-27 means subnormal bf16 inputs are not flushed on CDNA 2."),
    (r"^amd-cdna2-bf16_1k-nonmonotone$", "non-monotonicity",
     "The same on the CDNA 2 bf16 _1k variant (block of 4).",
     "MatrixCore.cdna2BF16_1k_nonmonotonic (amd/MatrixCore/MC/ProductMonotonicity.lean:156)",
     "x giving -2^-27 means subnormal bf16 inputs are not flushed on _1k."),
    (r"^amd-cdna3-f16-nonmonotone$", "non-monotonicity",
     "CDNA 3 fp16: p1 rises from 2^-9 - 2^-29 (e_p = -10) to 2^-9 (e_p = 1, subnormal times "
     "2^15); e_max rises and seven products 2^-24 are truncated away, so the output falls.",
     "MatrixCore.cdna3F16_nonmonotonic (amd/MatrixCore/MC/ProductMonotonicity.lean:164)",
     "Equal or rising outputs mean CDNA 3 aligns by the products' values, not by the exponents "
     "of the denormalized products."),
    (r"^amd-cdna3-bf16-nonmonotone$", "non-monotonicity",
     "CDNA 3 bf16 analogue (2^-6 - 2^-21 rises to 2^-6 = 2^-133 * 2^127).",
     "MatrixCore.cdna3BF16_nonmonotonic (amd/MatrixCore/MC/ProductMonotonicity.lean:172)",
     "As for fp16."),
    (r"^amd-cdna3-xf32-nonmonotone$", "non-monotonicity",
     "CDNA 3 XF32 analogue (2^-136 * 2^127).",
     "MatrixCore.cdna3XF32_nonmonotonic (amd/MatrixCore/MC/ProductMonotonicity.lean:179)",
     "As for fp16; also tests XF32 subnormal tf19 operands."),
    (r"^amd-cdna3-fp8-e4m3-nonmonotone$", "non-monotonicity",
     "CDNA 3 fp8 E4M3: equal products, the larger e_max rounds c = 2^-25 down to zero.",
     "MatrixCore.cdna3E4M3_nonmonotonic (amd/MatrixCore/MC/ProductMonotonicity.lean:187)",
     "Equal outputs mean c's late alignment (24, 32, RD) differs."),
    (r"^amd-cdna3-fp8-e5m2-nonmonotone$", "non-monotonicity",
     "CDNA 3 fp8 E5M2 analogue.",
     "MatrixCore.cdna3E5M2_nonmonotonic (amd/MatrixCore/MC/ProductMonotonicity.lean:194)",
     "As for E4M3."),
    (r"^amd-cdna3-f16-products-not-determined$", "non-monotonicity",
     "CDNA 3 with normal operands only: equal products 1.5 * 1.5 and 2.25 * 1 give different "
     "outputs (0x40100002 vs 0x40100000).",
     "MatrixCore.cdna3F16_products_not_determined (amd/MatrixCore/MC/ProductMonotonicity.lean:202)",
     "Equal outputs mean CDNA 3 aligns on product values, not on the exponent e_a + e_b of the "
     "denormalized product."),
    # ---- minimum alignment exponent
    (r"^nv-(a100|h100)-(bf16|tf32|tf32mma)-min-align-exp-kept$", "min-alignment-exponent",
     "Control half of the minimum-alignment-exponent probe: products 2^-140 and -2^-j with -2^-j "
     "exactly on the predicted grid 2^(eAlignMin - F) (A100: 2^-156; H100: 2^-158), so it is kept "
     "and the output is 2^-140 - 2^-149 (0x000001FF).",
     "constructed; Model.applyEAlignMin (TensorCore/TC/Defs.lean), PreparedBlock.alignExp "
     "(TensorCore/TC/Block.lean)",
     "0x00000200 means the grid is coarser: a minimum alignment exponent at least one above the "
     "model's (see alternatives)."),
    (r"^nv-(a100|h100)-(bf16|tf32|tf32mma)-min-align-exp-dropped$", "min-alignment-exponent",
     "Minimum-alignment-exponent probe: the maximum exponent (-140) is below the minimum alignment "
     "exponent, so the model aligns to it (A100 -132, H100 -133) and -2^-j, one step below the "
     "grid, is truncated away: output 2^-140 (0x00000200). Without a minimum alignment exponent "
     "(or with a lower one) it is kept: 0x000001FF.",
     "constructed; Model.applyEAlignMin (TensorCore/TC/Defs.lean), PreparedBlock.alignExp "
     "(TensorCore/TC/Block.lean)",
     "0x000001FF means no minimum alignment exponent, or one below the model's. Together with the "
     "-kept case the pair pins the minimum alignment exponent exactly."),
    # ---- signed zeros
    (r"negzero", "signed-zero",
     "Zero sums with -0 inputs. The model returns +0 for every zero sum, including c = -0 with -0 "
     "products, where IEEE addition gives -0.",
     "constructed; TensorCore.evalPrepared (round32 .truncate of the exact accumulator, "
     "TensorCore/TC/Block.lean) / MatrixCore fl32 (amd/MatrixCore/MC/Eval.lean)",
     "0x80000000 means the hardware keeps the IEEE sign of zero; the model (and the theorems that "
     "exclude c = -0, e.g. zero_products_passthrough) would need a sign rule. The Ozaki layer "
     "takes zero signs from the inputs, not from the outputs of the matrix multiplier "
     "(Ozaki/SignedZero.lean), so its results are unaffected."),
    # ---- subnormals
    (r"subnormal-c-passthrough", "subnormal",
     "All-zero products with a subnormal c (3 * 2^-149): the model returns c unchanged "
     "(CDNA 2 flushes it to +0).",
     "TensorCore.zero_products_passthrough (TensorCore/TC/Instruction.lean:147); MatrixCore "
     "subnormals := false on CDNA 2",
     "+0 on NVIDIA / CDNA 1 / CDNA 3 means subnormal c is flushed; 3 on CDNA 2 means it is not."),
    (r"subnormal-operand-beside-normal", "subnormal",
     "A subnormal fp16 operand (2^-24) times 65504 beside 2^-14 * 1: exact 2079 * 2^-19 if the "
     "subnormal is kept, 2^-14 if flushed (the model flushes only on CDNA 2).",
     "constructed",
     "2^-14 (0x38800000) where the model keeps subnormals means inputs are flushed; the reverse on "
     "CDNA 2 means they are not."),
    (r"subnormal-products$", "subnormal",
     "K products of the smallest fp16 subnormal (2^-24 * 2^-24 = 2^-48): exact.",
     "constructed",
     "0 means subnormal fp16 operands are flushed."),
    (r"subnormal-operand$", "subnormal",
     "One subnormal operand (bf16 2^-133, TF32 2^-136, fp16 2^-24) times a normal one: exact.",
     "constructed",
     "0 means subnormal operands of this format are flushed (expected on CDNA 2 only)."),
    (r"subnormal-output$", "subnormal",
     "A product 2^-126 * 2^-4 = 2^-130 whose output is an FP32 subnormal (0x00080000).",
     "constructed",
     "0 means subnormal outputs are flushed (expected on CDNA 2 only)."),
    # ---- TF32 exponent range
    (r"TF32.*-wide-spread$", "tf32-exponent-range",
     "Products 2^120, 2^-120, -2^120 (exponents far outside FP16's range): aligned to 2^120 the "
     "middle product is truncated away, so the output is 0 where the exact sum is 2^-120.",
     "constructed",
     "2^-120 means the TF32 variant keeps more than F bits below the maximum exponent (exact or "
     "order-dependent accumulation)."),
    (r"TF32.*-small-range$", "tf32-exponent-range",
     "Products 2^-120, 2^-123, 2^-126 (below FP16's range, normal in FP32): exact 73 * 2^-126.",
     "constructed",
     "Another value means TF32 exponents are narrowed or the minimum alignment exponent acts "
     "differently."),
    (r"TF32.*-above-fp32-max-in-block$", "tf32-exponent-range",
     "2^127 + 2^127 - 2^127: the partial sum 2^128 exceeds FP32's range but the aligned sum of the "
     "block FMA does not overflow, so the output is 2^127 (0x7F000000).",
     "constructed",
     "+Inf means the sum of the block FMA overflows at FP32 range (sequential binary32 additions, "
     "or a narrow accumulator exponent)."),
    (r"TF32.*-overflow$", "tf32-exponent-range",
     "2^127 + 2^127 = 2^128: outside the model's domain (accumulatorOutOfRange, no output). "
     "Recorded to see what the hardware returns (presumably +Inf), not as a model prediction.",
     "TensorCore.ModelError.accumulatorOutOfRange (TensorCore/TC/Block.lean)",
     "No model prediction; any finite output would be notable."),
    # ---- H100 TF32 MMA probes
    (r"^nv-tf32-k8-fma-size-probe$", "h100-tf32-mma",
     "FMA-size probe, k = 8: 2^23 + 2^23 + 1 + 0 | -2^23 - 2^23 + 0 + 0. One block FMA of size 8 "
     "(H100 TF32 MMA) returns the exact 1; two chained block FMAs of size 4 (H100 TF32 WMMA, A100 "
     "TF32) round the first one's 2^24 + 1 to 2^24 and return 0.",
     "constructed; TensorCore.runBlocks (TensorCore/TC/Composition.lean)",
     "0 on mma.sync.m16n8k8.tf32 means the FMA size of H100's TF32 MMA is 4, not 8."),
    (r"^nv-h100-tf32mma-align-bits-probe$", "h100-tf32-mma",
     "Extra-alignment-bits probe: c = 1 and eight products 1.5 * 2^-25. With F = 23 + p each "
     "product keeps floor(1.5 * 2^(p - 2)) grid units: p = 1 gives 1.0, p = 2 (model) 0x3F800002, "
     "p = 3 0x3F800003.",
     "constructed",
     "The output identifies p: see alternatives."),
    (r"-align-bits-probe$", "extra-alignment-bits",
     "The same extra-alignment-bits probe on another BF16 / TF32 variant (c = 1, products "
     "1.5 * 2^-25).",
     "constructed",
     "The output identifies the number of extra alignment bits p (see alternatives)."),
]


def family_of(case_id):
    base = case_id.split("@alt=")[0]
    return base.split("/")[0], base


def meta_for(fam):
    for pat, cat, purpose, src, mismatch in FAMILIES:
        if re.search(pat, fam):
            return cat, purpose, src, mismatch
    raise KeyError(fam)


# Values stated by kernel-checked theorems, to check the #eval output against.
THEOREM_WORDS = {
    "nv-a100-f16-full-block": 29331462, "nv-h100-f16-full-block": 67041296,
    "nv-a100-f16-exact-not-binary32": 12570628, "nv-a100-f16-cancel-zero": 0,
    "nv-a100-f16-cancel-2047": 4190209, "nv-h100-f16-cancel-zero": 0,
    "amd-cdna3-f16-full-block": 29331464, "amd-cdna1-f16-exact-not-sfma": 12570628,
    "amd-cdna2-f16-exact-not-sfma": 12570628, "amd-cdna3-f16-exact-not-sfma": 12570628,
    "amd-sfma-f32-not-exact": 12570626, "amd-cdna3-f16-cancel-zero": 0,
    "amd-cdna1-f16-cancel-c": 8388608, "amd-cdna2-f16-cancel-c": 8388608,
    "amd-sfma-f32-two-prod/pass1": 281474943156224,
}
THEOREM_BITS = {
    "nv-v100-f16-nonmonotone/c=1": 0x3F800000, "nv-v100-f16-nonmonotone/c=1-1ulp": 0x3F800001,
    "nv-a100-f16-nonmonotone/c=1": 0x3F800000, "nv-a100-f16-nonmonotone/c=1-1ulp": 0x3F800001,
    "nv-h100-f16-nonmonotone/c=1": 0x3F800000, "nv-h100-f16-nonmonotone/c=1-1ulp": 0x3F800001,
    "nv-v100-f16-nonmonotone/c=1-2ulp": 0x3F800001, "nv-v100-f16-nonmonotone/c=1-3ulp": 0x3F800000,
    "nv-a100-f16-nonmonotone/c=1-2ulp": 0x3F800001, "nv-a100-f16-nonmonotone/c=1-3ulp": 0x3F800000,
    "nv-h100-f16-nonmonotone/c=1-2ulp": 0x3F800001, "nv-h100-f16-nonmonotone/c=1-3ulp": 0x3F800000,
    "amd-cdna2-f16-nonmonotone/x": 0x00000000, "amd-cdna2-f16-nonmonotone/x'": 0xBA000000,
    "amd-cdna2-bf16-nonmonotone/x": 0x00000000, "amd-cdna2-bf16-nonmonotone/x'": 0xB1800000,
    "amd-cdna2-bf16_1k-nonmonotone/x": 0x00000000, "amd-cdna2-bf16_1k-nonmonotone/x'": 0xB1800000,
    "amd-cdna3-f16-nonmonotone/x": 0x3B0006F8, "amd-cdna3-f16-nonmonotone/x'": 0x3B000000,
    "amd-cdna3-bf16-nonmonotone/x": 0x3C8000BC, "amd-cdna3-bf16-nonmonotone/x'": 0x3C800000,
    "amd-cdna3-xf32-nonmonotone/x": 0x3B0002F8, "amd-cdna3-xf32-nonmonotone/x'": 0x3B000000,
    "amd-cdna3-fp8-e4m3-nonmonotone/x": 0x3E700002, "amd-cdna3-fp8-e4m3-nonmonotone/x'": 0x3E700000,
    "amd-cdna3-fp8-e5m2-nonmonotone/x": 0x3EE00001, "amd-cdna3-fp8-e5m2-nonmonotone/x'": 0x3EE00000,
    "amd-cdna3-f16-products-not-determined/1.5x1.5": 0x40100002,
    "amd-cdna3-f16-products-not-determined/2.25x1": 0x40100000,
}
# Two-pass sums stated by the theorems: pass1 value + pass2 value.
THEOREM_TWO_PASS = {
    "nv-a100-f16-two-pass": Fraction(29331463), "nv-h100-f16-two-pass": Fraction(67041297),
    "amd-cdna3-f16-two-pass": Fraction(29331463), "amd-sfma-f32-two-prod": Fraction(281474943156225),
    "amd-cdna2-f16-two-pass-fails": Fraction(2 ** 22),
    "amd-cdna1-f16-two-pass-recovers": Fraction(2 ** 22) + Fraction(1, 2 ** 14),
}


# --------------------------------------------------------------------------------------------
# Parsing


def parse_tc(line):
    _, cid, model, k, c, prods, out, val, exact = line.split("|")
    pairs = json.loads(prods)
    fmt = input_format("NVIDIA", model)
    w = width(fmt)
    case = {
        "vendor": "NVIDIA", "id": cid, "model": model, "fma_size_K": int(k),
        "input_format": fmt, "k": len(pairs),
        "inputs": {"c": f32_hex(int(c)), "a": [hexw(a, w) for a, _ in pairs],
                   "b": [hexw(b, w) for _, b in pairs]},
    }
    if fmt == "tf32":
        case["inputs"]["a_fp32_register"] = [f32_hex(a << 13) for a, _ in pairs]
        case["inputs"]["b_fp32_register"] = [f32_hex(b << 13) for _, b in pairs]
    return case, out, val, exact


def parse_mc(line):
    _, cid, model, c, a, b, out, val, exact = line.split("|")
    a, b = json.loads(a), json.loads(b)
    fmt = input_format("AMD", model)
    w = width(fmt)
    case = {
        "vendor": "AMD", "id": cid, "model": model, "input_format": fmt, "k": len(a),
        "inputs": {"c": f32_hex(int(c)), "a": [hexw(x, w) for x in a],
                   "b": [hexw(x, w) for x in b]},
    }
    return case, out, val, exact


def predicted(out, val):
    if out.startswith("ERR"):
        return {"status": "outside model domain", "model_error": out.split(".")[-1], "d": None,
                "value": None}
    return {"status": "ok", "d": f32_hex(int(out)), "value": frac_str(val)}


def build(tc_lines, mc_lines):
    cases, alts, raw = [], {}, {}
    for line in tc_lines + mc_lines:
        if not (line.startswith("TC|") or line.startswith("MC|")):
            continue
        case, out, val, exact = (parse_tc if line.startswith("TC|") else parse_mc)(line)
        raw[case["id"]] = (out, val)
        if "@alt=" in case["id"]:
            base, hyp = case["id"].split("@alt=")
            alts.setdefault(base, []).append({
                "hypothesis": f"{hyp} ({case['model']})",
                **{k: v for k, v in predicted(out, val).items() if k in ("d", "model_error")}})
            continue
        fam, base = family_of(case["id"])
        cat, purpose, src, mismatch = meta_for(fam)
        model = case["model"]
        case.update({
            "category": cat,
            "purpose": purpose,
            "architecture": ARCH.get(model, model),
            "instruction": (NV_INSTR if case["vendor"] == "NVIDIA" else MC_INSTR).get(model, ""),
            "predicted": predicted(out, val),
            "exact_sum": frac_str(exact),
            "lean_source": src,
            "mismatch_means": mismatch,
        })
        if "/" in case["id"]:
            case["family"] = fam
        cases.append(case)
    for case in cases:
        if case["id"] in alts:
            case["alternatives"] = alts.pop(case["id"])
    assert not alts, alts
    check_theorems(cases, raw)
    order = ["full-block-exactness", "cancellation", "two-pass", "non-monotonicity",
             "min-alignment-exponent", "signed-zero", "subnormal", "tf32-exponent-range",
             "h100-tf32-mma", "extra-alignment-bits"]
    cases.sort(key=lambda c: order.index(c["category"]))
    return cases


def check_theorems(cases, raw):
    """The #eval output agrees with every value the source theorems state."""
    for cid, v in THEOREM_WORDS.items():
        assert Fraction(raw[cid][1]) == v, (cid, raw[cid], v)
    for cid, bits in THEOREM_BITS.items():
        assert int(raw[cid][0]) == bits, (cid, raw[cid], hex(bits))
    for fam, total in THEOREM_TWO_PASS.items():
        got = Fraction(raw[fam + "/pass1"][1]) + Fraction(raw[fam + "/pass2"][1])
        assert got == total, (fam, got, total)
    for c in cases:
        if c["id"] in THEOREM_WORDS or c["id"] in THEOREM_BITS or c.get("family") in THEOREM_TWO_PASS:
            c["agrees_with_theorem"] = True


def main():
    args = sys.argv[1:]
    if "--tc" in args:
        tc = read_lines(args[args.index("--tc") + 1])
    else:
        tc = lean_lines(ROOT, "ozaki/scripts/targeted/TensorCoreCases.lean")
    if "--mc" in args:
        mc = read_lines(args[args.index("--mc") + 1])
    else:
        mc = lean_lines(os.path.join(ROOT, "amd"), "../ozaki/scripts/targeted/MatrixCoreCases.lean")
    cases = build(tc, mc)
    counts = {}
    for c in cases:
        counts[c["category"]] = counts.get(c["category"], 0) + 1
    doc = {
        "description": "Targeted hardware-validation suite: inputs that exercise the models' "
                       "distinguishing cases and the boundaries the earlier NVIDIA measurements did "
                       "not cover (minimum alignment exponents, signed zeros, subnormals, TF32's "
                       "exponent range, H100 TF32 MMA), with the outputs the Lean models predict. "
                       "See targeted-validation.md.",
        "generated_by": "ozaki/scripts/targeted_validation.py",
        "conventions": {
            "block": "d = c + sum_i a_i * b_i for one output element; a_i, b_i are input words "
                     "in k order, c and d binary32 words.",
            "words": "hex; fp16/bf16 16-bit, tf32 the 19-bit tf19 word (a_fp32_register / "
                     "b_fp32_register give the 32-bit register words, low 13 bits zero), binary32 "
                     "and xf32 32-bit, fp8 8-bit FNUZ.",
            "blocks": "NVIDIA: k is split into contiguous block FMAs of size fma_size_K, the FP32 "
                      "output of each block FMA the c of the next. AMD: blocks of N_FMA, chained "
                      "the same way.",
            "zero_fill": "On an instruction with a larger k, place the vector in k = 0..len-1 and "
                         "zeros elsewhere (a block FMA whose products are all zero returns c "
                         "unchanged when c is finite and not -0); signed-zero cases need k equal "
                         "to the vector length.",
            "alternatives": "the same input evaluated by the model under a nearby hypothesis "
                            "(another minimum alignment exponent, number of extra alignment bits or "
                            "FMA size): which one the hardware matches localises a mismatch.",
        },
        "predictions": {"NVIDIA": f"{TC_EVAL}; models in {TC_MODELS}",
                        "AMD": f"{MC_EVAL}; models in {MC_MODELS}"},
        "counts": counts,
        "cases": cases,
    }
    text = json.dumps(doc, indent=1)
    # One line per list of words.
    text = re.sub(r"\[\s+([^\[\]{}]*?)\s+\]", lambda m: "[" + " ".join(m.group(1).split()) + "]", text)
    sys.stdout.write(text + "\n")


if __name__ == "__main__":
    main()
