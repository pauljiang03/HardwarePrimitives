---
title: Modeling scope and limits
description: What the Lean Tensor Core model covers and what it deliberately leaves out.
---

## Covered

- One block FMA of FMA size `K` with FP32 `C`, for the eight
  FP16/BF16/TF32 → FP32 variants of V100, A100, and H100, plus arbitrary
  `K`, `p`, and minimum alignment exponent through the generic model
  constructors.
- Every finite input encoding, including subnormals and signed zeros.
- Exact products in denormalized form, alignment to the maximum exponent
  capped from below by the minimum alignment exponent, truncation
  of each term's magnitude, exact accumulation (and fixed-width accumulation proved
  equivalent at adequate width), and truncation of the result to FP32.
- Ordered chains of block FMAs, as in WMMA instructions, passing encoded FP32
  outputs between them.
- A general `InvocationSpec`, including FP64 fused DMMA and configurable
  rounding stages.

## Not covered, or covered differently from IEEE

- **NaN and infinity.** Nonfinite operands are rejected. The model doesn't
  propagate NaN.
- **Overflow.** Sums with `|accumulator| > maxFinite32` are rejected instead
  of producing infinity. This is also true of the round-to-nearest helper
  used by EFT: IEEE RNE would still round values slightly above
  `maxFinite32` down to it.
- **FP16 or BF16 output.** The validated variants all produce FP32.
- **FP8 and newer formats** (Blackwell and later) are not part of the
  supported variants.
- **Tiles, GEMMs, and scheduling.** The model covers single block FMAs and
  explicitly chained block FMAs. How a full GEMM is split across warps and
  instructions is outside the model.
- **Hardware correspondence** is evidence, not proof. See [hardware
  validation](/MMAlgebra/model/validation/) for which features the measured
  data exercises.
