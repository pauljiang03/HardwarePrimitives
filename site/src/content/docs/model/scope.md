---
title: Modeling scope and limits
description: What the Lean Tensor Core model covers and what it deliberately leaves out.
---

## Covered

- One block FMA of FMA size `K` with FP32 `C`, for the eight
  FP16/BF16/TF32 → FP32 variants of V100, A100, and H100, which are also the
  variants of Ada (A100's), H200 and B200 (H100's), plus arbitrary `K`, `p`,
  and minimum alignment exponent through the generic model constructors.
- The E4M3 and E5M2 → FP32 block FMAs of Ada and L40S, of H100 and H200
  through `wgmma`, and of B200 through `tcgen05.mma`, including the 13-bit
  block output of Ada and Hopper FP8; the FP8 `mma.sync` path of H100, H200
  and B200 (FP8 converted to FP16, two interleaved FP16 block FMAs, `C` added
  afterwards in FP32), and the RTX PRO 6000's FP8 `mma.sync` (B200's FP8
  block FMA).
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
- **FP16 or BF16 output.** The validated variants all produce FP32. The
  13-bit block output of Ada and Hopper FP8 is an FP32 word with its ten
  low mantissa bits zero.
- **FP4 and FP6** and the Blackwell instructions *Accurate Models* does not
  characterize are not modeled. GPUs after Blackwell B200 are not covered.
- **A nonzero `C` inside `wgmma` or `tcgen05.mma`** is modeled (`C` aligned
  and accumulated with the products, as on Ada) but has no recorded data: the
  recorded H100 and H200 FP8 outputs of the toolbox's commit 79143bd start
  from `C = 0`, and the B200 outputs and the H100 and H200 outputs of its
  release v0.1 come from `mma.sync`, which adds `C` after the FP16 block FMAs.
  The models agree there with the MMA-Sim simulator.
- **Tiles, GEMMs, and scheduling.** The model covers single block FMAs and
  explicitly chained block FMAs. How a full GEMM is split across warps and
  instructions is outside the model.
- **Hardware correspondence** is evidence, not proof. See [hardware
  validation](/HardwarePrimitives/model/validation/) for which features the measured
  data exercises.
