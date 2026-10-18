---
title: 8. Independent specification
description: A second transcription of Accurate Models of AMD Matrix Cores, written in the paper's fixed-point language without the model's definitions, and proved equal to the model on every variant.
---

[`Specification/Defs.lean`](https://github.com/pauljiang03/HardwarePrimitives/blob/main/matrix-core/MatrixCore/Specification/Defs.lean)
is a second transcription of the paper. It uses only the standard library's
integers and rationals, and it is written in the paper's fixed-point language
rather than the model's grid operations:

- the Table 1 layouts and IEEE/FNUZ field decoding (`Spec.decode`);
- products by multiplying significands and adding exponents (`Spec.mul`);
- `e_max` as the maximum over the nonzero products (`Spec.emax`);
- alignment to `e_max` with truncation to `F` mantissa bits as the integer
  `⌊M · 2^(e_p − f − (e_max − F))⌋` with the sign restored (`Spec.alignTrunc`);
- a shift with rounding down to `k` mantissa bits as a floor division by a power
  of two (`Spec.shiftRD`);
- the subnormal-aware normalization from the bit length of the integer
  `S_acc`;
- Algorithms 1 and 2 (`Spec.algorithm1`, `Spec.algorithm2`);
- the exact sum of CDNA 1;
- CDNA 2's Fig. 2, `fl{c + fl{fl{p₁ + p₂} + fl{p₃ + p₄}}}` and
  `fl{c + fl{p₁ + p₂}}`, with each `p_ℓ` converted by `fl{·}`, the inputs
  flushed, and `fl{·}` stated as round to nearest even with a subnormal result
  replaced by zero;
- FP32 round to nearest even as a property of the result word over all
  finite FP32 words, with the overflow threshold stated separately.

`Spec.Result S a b c w` (and `Spec.PairwiseResult` for CDNA 2) says that `w`
is the block output for the words `a`, `b`, `c`. The numerical features of
each variant are transcribed from the paper.

## Equivalence

```lean
import MatrixCore

open MatrixCore

example (x : BlockInput cdna3BF16) (w : F32) :
    blockBits x = .ok w ↔
      Spec.Result Spec.cdna3BF16 (x.a.map BitVec.toNat) (x.b.map BitVec.toNat) x.c w :=
  Spec.blockBits_eq_spec Spec.supported_cdna3BF16 x w
```

The proof ([`MatrixCore.Spec.blockBits_eq_spec`](https://github.com/pauljiang03/HardwarePrimitives/blob/main/matrix-core/MatrixCore/Specification/Equivalence.lean#L124)) bridges each operation,
proves that the specification's Algorithms 1 and 2 compute the model's
`S_acc`, and uses the uniqueness of the correctly rounded FP32 word
([`MatrixCore.rne32_iff`](https://github.com/pauljiang03/HardwarePrimitives/blob/main/matrix-core/MatrixCore/Numerics/Uniqueness.lean#L356)) to identify the output.

For CDNA 2, [`MatrixCore.Spec.pairwise_eq_spec`](https://github.com/pauljiang03/HardwarePrimitives/blob/main/matrix-core/MatrixCore/Specification/Pairwise.lean#L157) states the same for
`Spec.PairwiseResult`; its proof identifies the specification's `fl{·}` with
the model's and unfolds the model's pairwise sum.

```lean
import MatrixCore

open MatrixCore

example (x : BlockInput cdna2F16) (w : F32) :
    blockBits x = .ok w ↔
      Spec.PairwiseResult Spec.cdna2F16 (x.a.map BitVec.toNat) (x.b.map BitVec.toNat) x.c w :=
  Spec.pairwise_eq_spec Spec.supported_cdna2F16 x w
```

## Independence

The audit
([`tests/MatrixCoreTests/Audit.lean`](https://github.com/pauljiang03/HardwarePrimitives/blob/main/matrix-core/tests/MatrixCoreTests/Audit.lean))
checks that every declaration of the specification's module depends only on
the standard library and the notation module, and that it detects a
deliberately planted implementation dependency.

## Scope

The specification covers every variant of the paper: the SFMA, CDNA 1
fp16/bf16, CDNA 2 fp16/bf16/bf16 `_1k`, and CDNA 3 fp16/bf16/XF32/fp8 (any
mix of E4M3 and E5M2).
