# The independent specification

[`Specification/Defs.lean`](../../MatrixCore/Specification/Defs.lean) is a second transcription
of the paper. It uses only the standard library's integers and rationals and is written in the
paper's fixed-point language rather than the model's grid operations:

* Table 1 layouts and IEEE/FNUZ field decoding (`Spec.decode`);
* products by multiplying significands and adding exponents (`Spec.mul`);
* `e_max` as the maximum over the nonzero products (`Spec.emax`);
* alignment to `e_max` with truncation to `F` mantissa bits as the integer
  `⌊M · 2^(e_p − f − (e_max − F))⌋` with the sign restored (`Spec.alignTrunc`);
* a shift with RD to `k` mantissa bits as a floor division by a power of two (`Spec.shiftRD`);
* the subnormal-aware normalization from the bit length of the integer `S_acc`
  (`Spec.shiftedBranch`);
* Algorithms 1 and 2 (`Spec.algorithm1`, `Spec.algorithm2`, with `Spec.lateC` for lines 3–11);
* the exact sum of CDNA 1;
* CDNA 2's Fig. 2, `fl{c + fl{fl{p₁ + p₂} + fl{p₃ + p₄}}}` and `fl{c + fl{p₁ + p₂}}`, with each
  `p_ℓ` converted by `fl{·}`, the inputs flushed (`Spec.flushNum`), and `fl{·}` stated as RNE with
  a subnormal result replaced by zero (`Spec.Fl`, and `Spec.FlWord` for the output word);
* binary32 RNE as a property of the result word over all finite binary32 words
  (`Spec.RoundsNearestEven`), with the overflow threshold stated separately (`Spec.overflows`).

`Spec.Result S a b c w` (and `Spec.PairwiseResult` for CDNA 2) says that `w` is the block
output for the words `a`, `b`, `c`. The parameters of each variant are transcribed from the paper
(`Spec.cdna3F16`, `Spec.cdna3FP8`, `Spec.cdna2BF16_1k`, …).

## Equivalence

```lean
import MatrixCore

open MatrixCore

example (x : BlockInput cdna3BF16) (w : F32) :
    blockBits x = .ok w ↔
      Spec.Result Spec.cdna3BF16 (x.a.map BitVec.toNat) (x.b.map BitVec.toNat) x.c w :=
  Spec.blockBits_eq_spec Spec.supported_cdna3BF16 x w
```

The proof bridges each operation
([Bridge.lean](../../MatrixCore/Specification/Bridge.lean)), proves that the specification's
Algorithms 1 and 2 compute the model's `S_acc`
([Stages.lean](../../MatrixCore/Specification/Stages.lean)), and uses the uniqueness of the
correctly rounded binary32 word (`rne32_iff`) to identify the output
([Equivalence.lean](../../MatrixCore/Specification/Equivalence.lean)).

The audit (`tests/MatrixCoreTests/Audit.lean`) checks that every declaration of the
specification's module depends only on the standard library and the notation module, and that
it detects a deliberately planted implementation dependency.

For CDNA 2, `Spec.pairwise_eq_spec` states the same for `Spec.PairwiseResult`; its proof
identifies the specification's `fl{·}` with the model's (`Spec.fl_iff`, `Spec.flWord_iff`) and
unfolds the model's pairwise sums (`pairwiseSum_four`, `pairwiseSum_two`).

```lean
import MatrixCore

open MatrixCore

example (x : BlockInput cdna2F16) (w : F32) :
    blockBits x = .ok w ↔
      Spec.PairwiseResult Spec.cdna2F16 (x.a.map BitVec.toNat) (x.b.map BitVec.toNat) x.c w :=
  Spec.pairwise_eq_spec Spec.supported_cdna2F16 x w
```

## Scope

The specification covers every variant in the paper: the SFMA, CDNA 1 fp16/bf16, CDNA 2
fp16/bf16/bf16 `_1k`, and CDNA 3 fp16/bf16/XF32/fp8 (any mix of E4M3 and E5M2).
