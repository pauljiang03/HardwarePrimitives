---
title: Modeling scope and limits
description: What the Lean model of AMD matrix cores covers, the modeling choices the paper leaves open, and what it leaves out.
---

## Covered

- One MFMA block, and inner products and `D = AB + C` built from chained
  blocks, on every variant of *Accurate Models of AMD Matrix Cores*: the FP32
  SFMA on CDNA 1, 2 and 3; CDNA 1 FP16 and BF16; CDNA 2 FP16, BF16 and BF16
  `_1k`; CDNA 3 FP16, BF16, XF32 and FP8 E4M3/E5M2 FNUZ in any mix.
- Every input word, including subnormals, infinities and NaN, through the
  observation `blockOutcome`.
- Fixed-width accumulation on CDNA 3, proved to give the model's output at
  the stated register widths.

## Choices the paper leaves open

The model fixes these, and the
[paper notes](https://github.com/pauljiang03/HardwarePrimitives/blob/main/amd/docs/paper-notes.md)
record why:

- **NaN.** The GPUs return a NaN with a negative sign; its payload is not
  characterized, so the model reports NaN without a word.
- **Zero signs.** An exact zero `S_acc` gives `+0`. A nonzero `S_acc` that
  rounds or flushes to zero keeps its sign. The paper does not test zero signs.
- **`∞ · 0`.** NaN, as in IEEE 754; the paper does not test it.
- **Inner dimension `k = 0`.** Not an instruction; `dotBits` returns `c`
  unchanged.
- **CDNA 2 special values.** Products are converted to FP32 and summed
  with FP32 additions, so an intermediate overflow is an infinity that
  propagates by IEEE 754 rules (`+∞ + −∞` is NaN). This reproduces the paper's
  `p₁ = 2^128, p₂ = −p₁` vector.
- **XF32 NaN words** are classified before the significand is truncated.
- **Zero products** take no part in `e_max`, and a group of odd or even
  FP8 products that is entirely zero has no exponent; a group whose
  nonzero products cancel keeps its exponent, as one of the paper's vectors
  requires.

## Not covered

- **Hardware correspondence** is evidence, not proof: the paper's
  observations are replayed as tests and the model is compared with the
  authors' MATLAB models, but no recorded AMD hardware measurements are
  published ([validation](/HardwarePrimitives/amd/validation/)).
- **The special-value layer** for non-finite inputs is a definition following
  the paper's description, checked against its vectors and the MATLAB models,
  not derived.
- **INT8 MFMA instructions** are not modeled.
- **Tiles, GEMMs and scheduling.** The model covers blocks and explicitly
  chained blocks; how a full GEMM is split across wavefronts and instructions
  is outside it.
