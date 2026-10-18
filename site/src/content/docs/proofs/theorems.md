---
title: What is proven
description: Every headline theorem in plain language, with what it assumes, what it means, and how strong it is.
---

This page lists the main results that Lean has checked about the Tensor Core
model and the AMD matrix-core model. Each entry says, in
plain words, what the result means, what it assumes, and how much it really
establishes. The Lean name and a source link follow each entry for anyone
who wants to read the formal statement.

Every result here is checked by Lean's kernel. It relies only on Lean's three
standard axioms (`propext`, `Classical.choice`, `Quot.sound`), with no
`sorry` and no custom axioms. See [What is tested](/HardwarePrimitives/proofs/tested/)
for what is tested rather than proved.

**Classification.** Each entry is classified as one of:

- **Core theorem**: a non-trivial property of the model. It could have
  failed, and the proof shows that it holds.
- **Definitional identity**: follows directly from how the quantities
  involved are defined. Useful for bookkeeping, but not a claim about the
  model's behavior.
- **Partial reduction**: derives some of its conclusions and takes the rest
  as hypotheses, so it establishes less than its name suggests.

## The Tensor Core model

### Does the Lean model match the published model?

**Yes, for every possible input.** The executable model and an independently
written transcription of *Accurate Models* produce the same output bits, or
both reject the input. This holds on all eight FP16/BF16/TF32 variants, which
are also those of Ada, H200 and B200, and on every model whatever the width of
its block output: the specification truncates the accumulator to FP32 and
then to the model's number of output mantissa bits, so Ada and Hopper FP8 are
covered too. With at least 23 output mantissa bits it is the FP32
specification.

- **Assumes:** nothing (`evalBlock_eq_spec` states the FP32 case, for any
  model with `23 ≤ outputMantissaBits`; `evalBlock_eq_specM` drops that
  hypothesis).
- **Classification:** Core theorem. The transcription is mechanically checked not to reuse
  any model code, and a companion result shows it isn't vacuous.
- **Lean:** [`IndependentSpec.supported_eq_spec`](https://github.com/pauljiang03/HardwarePrimitives/blob/main/TensorCore/TC/Specification/Supported.lean#L28), [`IndependentSpec.blackwell_fp8_eq_spec`](https://github.com/pauljiang03/HardwarePrimitives/blob/main/TensorCore/TC/Specification/Supported.lean#L41),
  [`IndependentSpec.evalBlock_eq_specM`](https://github.com/pauljiang03/HardwarePrimitives/blob/main/TensorCore/TC/Specification/OutputWidth.lean#L103), [`IndependentSpec.bitsM_eq_bits`](https://github.com/pauljiang03/HardwarePrimitives/blob/main/TensorCore/TC/Specification/OutputWidth.lean#L124), [`IndependentSpec.fp8_eq_spec`](https://github.com/pauljiang03/HardwarePrimitives/blob/main/TensorCore/TC/Specification/OutputWidth.lean#L174)

### Which inputs does the model accept?

**Exactly those with the right number of products, no NaN or infinity, and a
sum that fits in FP32.** Anything else is rejected with a named error.

- **Assumes:** nothing; it holds for every model, FP8 included.
- **Classification:** Core theorem. It is an exact "if and only if".
- **Lean:** [`evalBlock_success_iff`](https://github.com/pauljiang03/HardwarePrimitives/blob/main/TensorCore/TC/AcceptedDomain.lean#L36)

### Is all the lost precision accounted for?

**Yes.** The exact sum of the inputs equals the model's output plus the parts
dropped by alignment and by the final rounding.

- **Assumes:** the model accepted the input.
- **Classification:** Core theorem. The exact sum is computed from the original input
  words, not from the model's own intermediate values.
- **Lean:** [`evalBlock_residual_identity`](https://github.com/pauljiang03/HardwarePrimitives/blob/main/TensorCore/TC/StageResiduals.lean#L91)

### How large can the error be?

**Less than (number of terms) × (alignment grid step) + (one unit in the last
place of the output).** The first part is the alignment loss and the second
is the rounding loss.

For a block output with `m` mantissa bits the second part is `2^(23 − m)`
units in the last place of the FP32 output word: on Ada and Hopper FP8
(`m = 13`) one unit in the last place of the 14-bit output significand.

- **Assumes:** the model accepted the input (`evalBlock_error_bound` states
  the FP32 case, for block outputs with at least 23 mantissa bits).
- **Classification:** Core theorem.
- **Lean:** [`evalBlock_error_bound`](https://github.com/pauljiang03/HardwarePrimitives/blob/main/TensorCore/TC/ErrorBounds.lean#L94), [`evalBlock_error_bound_any`](https://github.com/pauljiang03/HardwarePrimitives/blob/main/TensorCore/TC/OutputWidth.lean#L405), [`fp8_error_bound`](https://github.com/pauljiang03/HardwarePrimitives/blob/main/TensorCore/TC/OutputWidth.lean#L414)

### Does modeling the adder as exact hide anything?

**No.** A model with a fixed-width, wrapping two's-complement register gives
the same output for every input, as long as the register is wide enough:
29, 31 and 33 bits for the V100, A100 and H100 FP16 models, a sign bit
included. Every partial
sum is exact too, whatever the order of additions.

- **Assumes:** a register at least that wide.
- **Classification:** Core theorem.
- **Lean:** [`evalBlockMachine_eq`](https://github.com/pauljiang03/HardwarePrimitives/blob/main/TensorCore/TC/MachineRefinement.lean#L15), [`evalBlock_machinePrefix`](https://github.com/pauljiang03/HardwarePrimitives/blob/main/TensorCore/TC/AlignmentExponent.lean#L184)

### Can the whole model run in fixed-width bitvector registers?

**Yes.** A [bitvector datapath](/HardwarePrimitives/model/datapath/) decodes, multiplies,
aligns, sums and normalizes using bitvector operations only. Its registers
are sized from the model: `F + 2` bits per aligned term, an accumulator of
28 to 32 magnitude bits plus a sign bit (30 and 32 on A100 and H100 FP16, the
widths in *Accurate Models*), and 9-bit exponents. It returns the same output word as the model, or the same
error, for every input on all eight FP16/BF16/TF32 variants. A second
datapath covers the six FP8 block FMAs (Ada, Hopper and B200; E4M3 and E5M2):
on Ada and Hopper it aligns on 23 mantissa bits, shifts, drops the ten low bits
of each aligned term, and clears the ten low mantissa bits of the output.

- **Assumes:** nothing beyond the input being one of these variants.
- **Classification:** Core theorem. The datapath shares no arithmetic with the
  model: it uses shifts, a leading-zero count and wrapping additions where the
  model uses rationals and floors.
- **Lean:** [`Datapath.evalBlock_eq`](https://github.com/pauljiang03/HardwarePrimitives/blob/main/TensorCore/Kernels/Datapath/Correctness.lean#L208), [`Datapath.FP8.evalBlock8_eq`](https://github.com/pauljiang03/HardwarePrimitives/blob/main/TensorCore/Kernels/Datapath/FP8.lean#L463)

### Chained block FMAs

**For instructions made of several block FMAs, the same loss accounting holds
across the whole chain.**

- **Assumes:** each block's output is passed on as the next block's `C`.
- **Classification:** Core theorem.
- **Lean:** [`runBlocks_residual_ledger`](https://github.com/pauljiang03/HardwarePrimitives/blob/main/TensorCore/TC/Composition.lean#L93)

### FP8 encodings and the FP8 block FMAs

**E4M3 and E5M2 decode as specified, and the FP8 models need no minimum
alignment exponent.** E4M3 has no infinities, its only NaNs are `0x7f` and
`0xff`, and its largest value is 448; E5M2 has infinities at `0x7c` and
`0xfc`, six NaNs, and largest value 57344. The block model's 9-bit E4M3
layout decodes all 256 words as E4M3 does. On Ada and Hopper FP8 the output is
the FP32 truncation of the accumulator with its ten low mantissa bits
cleared. The toolbox's minimum alignment exponents (−132, −133) change no
output on the FP8 models.

- **Assumes:** nothing.
- **Classification:** Core theorems, checked by computation over every word
  for the encodings.
- **Lean:** [`e4m3_specials`](https://github.com/pauljiang03/HardwarePrimitives/blob/main/TensorCore/Numerics/FP8.lean#L45), [`e5m2_specials`](https://github.com/pauljiang03/HardwarePrimitives/blob/main/TensorCore/Numerics/FP8.lean#L51), [`e4m3_decode_widen`](https://github.com/pauljiang03/HardwarePrimitives/blob/main/TensorCore/Numerics/FP8.lean#L31),
  [`fp8_output_thirteen_bits`](https://github.com/pauljiang03/HardwarePrimitives/blob/main/TensorCore/TC/GPUs.lean#L73), [`fp8_eAlignMin_inactive`](https://github.com/pauljiang03/HardwarePrimitives/blob/main/TensorCore/TC/GPUs.lean#L169)

### FP8 through `mma.sync`

**The FP8 `mma.sync` path of H100, H200 and B200 is modeled, and its structure
is pinned down by kernel-checked consequences.** FP8 operands convert exactly
to FP16; the products at positions `k mod 4 ∈ {0, 1}` and `{2, 3}` go through
two chained Hopper FP16 block FMAs from `+0`; `C` is added afterwards in
FP32 with round-to-nearest-even. The model reproduces the interleaving
pattern *Accurate Models* reports, and the alternatives (the other group
order, one 32-product block, `C` inside the block, two independent blocks)
each give a different word on an explicit input, one of them a recorded B200
row.

- **Assumes:** nothing; the consequences are evaluations of the model on
  fixed inputs.
- **Classification:** Core theorems (exact conversions over every word) and
  kernel-checked witnesses. That GPUs follow the model is tested, not proved:
  see [hardware validation](/HardwarePrimitives/model/validation/).
- **Lean:** [`e4m3ToF16_exact`](https://github.com/pauljiang03/HardwarePrimitives/blob/main/TensorCore/Numerics/FP8.lean#L91), [`e5m2ToF16_exact`](https://github.com/pauljiang03/HardwarePrimitives/blob/main/TensorCore/Numerics/FP8.lean#L106), [`mmaSyncFP8`](https://github.com/pauljiang03/HardwarePrimitives/blob/main/TensorCore/TC/MmaSyncFP8.lean#L31),
  [`interleave_test_e5m2`](https://github.com/pauljiang03/HardwarePrimitives/blob/main/TensorCore/TC/MmaSyncFP8.lean#L60), [`interleave_test_reversed`](https://github.com/pauljiang03/HardwarePrimitives/blob/main/TensorCore/TC/MmaSyncFP8.lean#L74),
  [`interleave_test_single_block`](https://github.com/pauljiang03/HardwarePrimitives/blob/main/TensorCore/TC/MmaSyncFP8.lean#L79), [`late_c_witness`](https://github.com/pauljiang03/HardwarePrimitives/blob/main/TensorCore/TC/MmaSyncFP8.lean#L87), [`separate_groups_excluded`](https://github.com/pauljiang03/HardwarePrimitives/blob/main/TensorCore/TC/MmaSyncFP8.lean#L111)

## Tensor Core non-monotonicity

### Can a smaller C give a larger result?

**Yes, and exactly when the FMA size is at least 3·2^p.** Here p is
the GPU's number of padding bits. The proof uses a specific family:
K equal tiny products, with `C` lowered from 1 to the next FP32 value below 1.

- **Assumes:** that construction (products of exactly `2^-(24+p)`), a
  minimum alignment exponent, if any, of at most −1, and an FP32 block
  output.
- **Classification:** Core theorem. It is an exact threshold, and every GPU model has
  a checked concrete example.
- **Lean:** [`nonmonotone_encoded`](https://github.com/pauljiang03/HardwarePrimitives/blob/main/TensorCore/TC/Monotonicity.lean#L270)

### How large can the effect be?

**The result gives the exact range of perturbations that raise the output, a
formula for the output, and its maximum,** for `C = 1 − j·2^-24`.

- **Assumes:** the same construction, with `1 ≤ j ≤ 2^23`.
- **Classification:** Core theorem.
- **Lean:** [`nonmonotone_range_encoded`](https://github.com/pauljiang03/HardwarePrimitives/blob/main/TensorCore/TC/MonotonicityRange.lean#L262)

### When does it happen in general?

**For any inputs, the output can rise only if the products recovered by the
finer grid outweigh the change in `C`.** That condition is also sufficient
when both sums are exactly representable in FP32.

- **Assumes:** both evaluations succeed; FP32 representability for the
  "sufficient" direction.
- **Classification:** Core theorem.
- **Lean:** [`flowback_necessary`](https://github.com/pauljiang03/HardwarePrimitives/blob/main/TensorCore/TC/Flowback.lean#L198), [`flowback_sufficient`](https://github.com/pauljiang03/HardwarePrimitives/blob/main/TensorCore/TC/Flowback.lean#L217)

## TC-EFT correction

### Is the corrected result right?

**Yes. Whatever TC-EFT returns is the exact sum rounded to the nearest FP32
value, ties to even.** It returns a value exactly when that rounded sum is
finite.

- **Assumes:** nothing about `D`, which can be any finite FP32 word.
- **Classification:** Core theorem. Note that the result doesn't depend on `D`
  being the real Tensor Core output.
- **Lean:** [`tcEftEncoded_correct`](https://github.com/pauljiang03/HardwarePrimitives/blob/main/TensorCore/EFT/Encoded.lean#L113), [`tcEftEncoded_bits_isSome_iff`](https://github.com/pauljiang03/HardwarePrimitives/blob/main/TensorCore/EFT/Encoded.lean#L127)

### Does the fast FP32 path give the right answer?

**Yes, whenever its safety check passes.** The check ensures every
intermediate FP32 operation is exact, so only the final rounding remains.

- **Assumes:** the scalar safety check holds.
- **Classification:** Core theorem. The core is a proof that naive FP32 summation is
  exact when all the bits fit within a span of 24 bits.
- **Lean:** [`scalarCorrected_correct`](https://github.com/pauljiang03/HardwarePrimitives/blob/main/TensorCore/EFT/Extraction.lean#L154), [`naiveSumBinary_exact_of_bitSpan`](https://github.com/pauljiang03/HardwarePrimitives/blob/main/TensorCore/Numerics/Binary/ScalarSum.lean#L162)

### Recovering the exact sum from D

**The exact sum equals `D` minus the overlap plus the low parts.**

- **Classification:** Definitional identity. The overlap is *defined* as `D` minus the
  retained part, so the identity is a rearrangement.
- **Lean:** [`overlap_recovery`](https://github.com/pauljiang03/HardwarePrimitives/blob/main/TensorCore/EFT/Extraction.lean#L20)

### Does the paper's input-based precondition imply the safety check?

**Partly.** For FP32 correction it derives five of the check's nine
conditions: format, grid, a span of at most 24 bits, magnitude range, and `D` fitting in
FP32. It assumes the other four: a grid no lower than `2^-149`, the overlap
and `H` fitting in FP32, and the sum in range. A concrete block satisfies all
of them.

- **Classification:** Partial reduction. The four remaining conditions depend
  on the particular sum, not only the input bound.
- **Lean:** [`ExtractionGrid.inputGrid_scalarPredicate`](https://github.com/pauljiang03/HardwarePrimitives/blob/main/TensorCore/EFT/ExtractionGrid.lean#L173), [`ExtractionGrid.inputGrid_scalarPredicate_fp32`](https://github.com/pauljiang03/HardwarePrimitives/blob/main/TensorCore/EFT/ExtractionGrid.lean#L190)

### Does the fixed-size implementation agree?

**Yes.** The 576-bit implementation never overflows on supported inputs,
returns a result exactly when the rounded sum is finite, and returns the
same bits as the reference version. Swapping in Lean's native `Float32`
additions changes nothing.

- **Assumes:** supported, finite, correctly shaped inputs.
- **Classification:** Core theorem. The native-float part holds relative to Lean's
  specification of `Float32`.
- **Lean:** [`EFMachine.tcEft_success`](https://github.com/pauljiang03/HardwarePrimitives/blob/main/TensorCore/Kernels/EFT/Correctness.lean#L89), [`EFMachine.tcEft_range_iff`](https://github.com/pauljiang03/HardwarePrimitives/blob/main/TensorCore/Kernels/EFT/Correctness.lean#L99), [`EFMachine.tcEft_agrees`](https://github.com/pauljiang03/HardwarePrimitives/blob/main/TensorCore/Kernels/EFT/Refinement.lean#L9), [`EFMachine.tcEftWithLean_eq`](https://github.com/pauljiang03/HardwarePrimitives/blob/main/TensorCore/Kernels/EFT/Native.lean#L105)

### Does passing the fast-path check guarantee the fast path?

**Yes.** In the 576-bit implementation the fast path is plain FP32
operations. Whenever the check passes, every one of those operations is
exact, so the fast path is taken and returns the correctly rounded sum. No
run-time comparison against exact values is needed.

- **Assumes:** a supported, finite input that passes the check and is not all
  zeros.
- **Classification:** Core theorem.
- **Lean:** [`EFMachine.Components.scalar_of_guard`](https://github.com/pauljiang03/HardwarePrimitives/blob/main/TensorCore/Kernels/EFT/ScalarGuard.lean#L184), [`EFMachine.tcEft_scalar_of_guard`](https://github.com/pauljiang03/HardwarePrimitives/blob/main/TensorCore/Kernels/EFT/ScalarGuard.lean#L217)

### Does FP64 DMMA follow IEEE 754 for signed zero?

**Yes.** An exactly zero result `a·b + c` gets the IEEE 754 sign: addends
with the same sign keep it; otherwise `+0`, or `−0` when rounding toward
negative. A nonzero result that rounds to zero keeps its own sign.

- **Classification:** Core theorem.
- **Lean:** [`fp64FmaBits_of_eq_zero`](https://github.com/pauljiang03/HardwarePrimitives/blob/main/TensorCore/TC/FusedRounding.lean#L78), [`fp64FmaBits_of_ne_zero`](https://github.com/pauljiang03/HardwarePrimitives/blob/main/TensorCore/TC/FusedRounding.lean#L68)

## Tensor Core number formats and rounding

### Is FP32 rounding implemented correctly?

**Yes.** The rounding function returns the nearest FP32 value, ties to even, for every
input in range. This also holds for any binary format and any rounding
direction.

- **Classification:** Core theorem. One gap: the specification doesn't fix the sign of a
  zero result.
- **Lean:** [`round32_nearestEven_correct`](https://github.com/pauljiang03/HardwarePrimitives/blob/main/TensorCore/Numerics/CorrectRounding.lean#L153), [`roundBinary_correct`](https://github.com/pauljiang03/HardwarePrimitives/blob/main/TensorCore/Numerics/Binary/RoundingContract.lean#L17)

### Is decoding of bit patterns consistent?

**Yes.** Finite bit patterns and representable values correspond one to one,
including subnormals and both zeros.

- **Classification:** Core theorem.
- **Lean:** [`signedFiniteBinaryBijection`](https://github.com/pauljiang03/HardwarePrimitives/blob/main/TensorCore/Numerics/Binary/SignedBijection.lean#L130)

## The matrix core model

### Does the Lean model match the published model?

**Yes, for every possible input.** The executable model and an independently
written transcription of *Accurate Models of AMD Matrix Cores*, in the paper's
fixed-point language, give the same output word, or both reject the input, on
every variant: the SFMA, CDNA 1 FP16 and BF16, CDNA 2 FP16, BF16 and BF16
`_1k`, and CDNA 3 FP16, BF16, XF32 and FP8 in any mix of formats.

- **Assumes:** nothing.
- **Classification:** Core theorem. An audit checks that the transcription
  depends only on the standard library and the notation module, and that it
  detects a deliberately planted implementation dependency.
- **Lean:** [`MatrixCore.Spec.blockBits_eq_spec`](https://github.com/pauljiang03/HardwarePrimitives/blob/main/amd/MatrixCore/Specification/Equivalence.lean#L124), [`MatrixCore.Spec.pairwise_eq_spec`](https://github.com/pauljiang03/HardwarePrimitives/blob/main/amd/MatrixCore/Specification/Pairwise.lean#L157)

### Which inputs does the model accept?

**Exactly those with `N_FMA` operands, no NaN or infinity, an accumulation
that succeeds, and an `S_acc` below the overflow threshold `2^128 − 2^103`.**
On CDNA 1 and the SFMA this is an exact sum below the threshold; products may
exceed `2^128` inside the block.

- **Assumes:** nothing.
- **Classification:** Core theorem. It is an exact "if and only if".
- **Lean:** [`MatrixCore.evalBlock_success_iff`](https://github.com/pauljiang03/HardwarePrimitives/blob/main/amd/MatrixCore/MC/AcceptedDomain.lean#L36), [`MatrixCore.correctRounding_success_iff`](https://github.com/pauljiang03/HardwarePrimitives/blob/main/amd/MatrixCore/MC/CorrectRounding.lean#L38)

### How large can the error be?

**On CDNA 1 and the SFMA, at most half an ulp of the exact sum.** On CDNA 3, at
most the loss of `S_acc` in its branch of Algorithms 1 and 2 (about
`(n + 2)·2^(e_max − 24)` from the products and `2^(e_max − 24)` from `c`) plus
one final rounding. On CDNA 2, at most the effect of flushing plus one
rounding for each product conversion, each pairwise sum and the final `fl{·}`.
The library also bounds each error from the inputs alone.

- **Assumes:** the model accepted the input.
- **Classification:** Core theorems.
- **Lean:** [`MatrixCore.correctRounding_error`](https://github.com/pauljiang03/HardwarePrimitives/blob/main/amd/MatrixCore/MC/ErrorBounds.lean#L77), [`MatrixCore.aligned_error`](https://github.com/pauljiang03/HardwarePrimitives/blob/main/amd/MatrixCore/MC/ErrorBounds.lean#L292), [`MatrixCore.pairwise_error`](https://github.com/pauljiang03/HardwarePrimitives/blob/main/amd/MatrixCore/MC/ErrorBounds.lean#L219),
  [`MatrixCore.correctRounding_apriori`](https://github.com/pauljiang03/HardwarePrimitives/blob/main/amd/MatrixCore/MC/AprioriBounds.lean#L67), [`MatrixCore.aligned_apriori`](https://github.com/pauljiang03/HardwarePrimitives/blob/main/amd/MatrixCore/MC/AprioriBounds.lean#L227), [`MatrixCore.pairwise_apriori`](https://github.com/pauljiang03/HardwarePrimitives/blob/main/amd/MatrixCore/MC/AprioriBounds.lean#L460)

### Does modeling the adder as exact hide anything?

**No.** A model of the CDNA 3 product accumulation with fixed-width, wrapping
two's-complement registers gives the same output for every input: 30 bits
for FP16 and BF16, 29 for XF32 and 31 for FP8, a sign bit included. Every
partial sum is exact too, whatever the order of additions.

- **Assumes:** a register at least that wide.
- **Classification:** Core theorem.
- **Lean:** [`MatrixCore.evalBlockMachine_eq`](https://github.com/pauljiang03/HardwarePrimitives/blob/main/amd/MatrixCore/MC/MachineRefinement.lean#L162), [`MatrixCore.machinePrefix_exact`](https://github.com/pauljiang03/HardwarePrimitives/blob/main/amd/MatrixCore/MC/MachineRefinement.lean#L185)

### Inner products and `D = AB + C`

**For inner products of any length and every finite entry of `D = AB + C`,
the exact sum equals the output plus the residuals of all the blocks, and the
error is at most the sum of the blocks' bounds.** Every accepted block also
satisfies a contract bundling what is proved about it.

- **Assumes:** each block's output is passed on as the next block's `c`.
- **Classification:** Core theorems.
- **Lean:** [`MatrixCore.dotBits_exact_ledger`](https://github.com/pauljiang03/HardwarePrimitives/blob/main/amd/MatrixCore/MC/InnerProduct.lean#L166), [`MatrixCore.dotBits_exact_error`](https://github.com/pauljiang03/HardwarePrimitives/blob/main/amd/MatrixCore/MC/InnerProduct.lean#L176), [`MatrixCore.mfma_error`](https://github.com/pauljiang03/HardwarePrimitives/blob/main/amd/MatrixCore/MC/MFMA.lean#L44),
  [`MatrixCore.evalBlock_contract`](https://github.com/pauljiang03/HardwarePrimitives/blob/main/amd/MatrixCore/MC/Contract.lean#L36)

### Special values

**The observation for any input words reports a finite word exactly when the
finite model accepts, with the same word; otherwise an infinity or NaN.**

- **Assumes:** nothing.
- **Classification:** Core theorem about a definition: the special-value
  layer itself follows the paper's description and is checked against its
  vectors and the MATLAB models, not derived.
- **Lean:** [`MatrixCore.blockOutcome_finite_iff`](https://github.com/pauljiang03/HardwarePrimitives/blob/main/amd/MatrixCore/MC/SpecialAgreement.lean#L161)

## Matrix core monotonicity

### Can a smaller `c` give a larger result?

**No, on every configuration.** For the same `a` and `b`, a larger `c` never
gives a smaller output, and the same holds for inner products of any length.
On a Tensor Core `C` takes part in alignment and can trigger
non-monotonicity; on AMD `c` never sets the products' alignment.

- **Assumes:** the model is one of the paper's (all are proved to qualify).
- **Classification:** Core theorem.
- **Lean:** [`MatrixCore.evalBlock_c_monotone`](https://github.com/pauljiang03/HardwarePrimitives/blob/main/amd/MatrixCore/MC/Monotonicity.lean#L605), [`MatrixCore.dotBits_c_monotone`](https://github.com/pauljiang03/HardwarePrimitives/blob/main/amd/MatrixCore/MC/Monotonicity.lean#L629), [`MatrixCore.paper_models_monotone`](https://github.com/pauljiang03/HardwarePrimitives/blob/main/amd/MatrixCore/MC/Monotonicity.lean#L650)

### Can larger products give a smaller result?

**Not on CDNA 1 or the SFMA; yes on CDNA 2 and CDNA 3, on every input
format.** CDNA 1 and the SFMA depend only on the exact sum, monotonically. On
CDNA 2 a product with a subnormal operand is flushed while a slightly larger
one with normal operands is not. On CDNA 3 raising a product can raise
`e_max` and truncate the others by more than it gains.

- **Assumes:** nothing.
- **Classification:** Core theorem for CDNA 1 and the SFMA; kernel-checked
  witnesses for CDNA 2 and CDNA 3.
- **Lean:** [`MatrixCore.correctRounding_not_nonmonotone`](https://github.com/pauljiang03/HardwarePrimitives/blob/main/amd/MatrixCore/MC/ProductMonotonicity.lean#L100), [`MatrixCore.cdna2F16_nonmonotonic`](https://github.com/pauljiang03/HardwarePrimitives/blob/main/amd/MatrixCore/MC/ProductMonotonicity.lean#L125),
  [`MatrixCore.cdna3F16_nonmonotonic`](https://github.com/pauljiang03/HardwarePrimitives/blob/main/amd/MatrixCore/MC/ProductMonotonicity.lean#L141), [`MatrixCore.cdna3E4M3_nonmonotonic`](https://github.com/pauljiang03/HardwarePrimitives/blob/main/amd/MatrixCore/MC/ProductMonotonicity.lean#L162)

### When does it happen in general?

**On CDNA 3, only when a product changes an alignment exponent; on CDNA 2, only
through flushing.** With the alignment exponents fixed, CDNA 3 is monotone in
the products, so every non-monotone pair changes `e_max` (or a group exponent
on FP8). On CDNA 2, larger products never give a smaller output when no
operand is subnormal. On every configuration an output decrease requires the
accumulation loss to grow by more than the gain in the exact sum, and that is
sufficient when both accumulated values are FP32 values. The drop is at
most the two blocks' error bounds less the gain.

- **Assumes:** the model accepted both inputs; the same `c`; for the sufficient
  direction, subnormals and FP32 accumulated values.
- **Classification:** Core theorems.
- **Lean:** [`MatrixCore.aligned_product_monotone`](https://github.com/pauljiang03/HardwarePrimitives/blob/main/amd/MatrixCore/MC/AlignmentMonotonicity.lean#L272), [`MatrixCore.aligned_nonmonotone_alignment_changes`](https://github.com/pauljiang03/HardwarePrimitives/blob/main/amd/MatrixCore/MC/AlignmentMonotonicity.lean#L291),
  [`MatrixCore.pairwise_product_monotone`](https://github.com/pauljiang03/HardwarePrimitives/blob/main/amd/MatrixCore/MC/AlignmentMonotonicity.lean#L461), [`MatrixCore.output_decrease_iff`](https://github.com/pauljiang03/HardwarePrimitives/blob/main/amd/MatrixCore/MC/LossCondition.lean#L94), [`MatrixCore.aligned_output_drop_le`](https://github.com/pauljiang03/HardwarePrimitives/blob/main/amd/MatrixCore/MC/LossCondition.lean#L120)

### Is there an exact threshold, as on Tensor Cores?

**Yes, for a family on CDNA 3 FP16.** A block holds a lead product with
`e_a + e_b = −10` and value `m_a m_b · 2^-30`, `n ≤ 7` products `2^-24`, and
`c = 0`; raising the lead to `2^-24 · 2^15 = 2^-9` (exponent 1) lowers the
output exactly when `2^21 − m_a m_b < 64n`. The theorem holds for every lead
and every `n`.

- **Assumes:** the lead's operands have the same sign and a nonzero product.
- **Classification:** Core theorem, an exact "if and only if".
- **Lean:** [`MatrixCore.cdna3F16LeadBlock_nonmonotone_iff`](https://github.com/pauljiang03/HardwarePrimitives/blob/main/amd/MatrixCore/MC/NonmonotoneFamily.lean#L325), [`MatrixCore.cdna3F16LeadBlock_decrease_iff`](https://github.com/pauljiang03/HardwarePrimitives/blob/main/amd/MatrixCore/MC/NonmonotoneFamily.lean#L265)

## Matrix core correct rounding

### Is the output ever the correctly rounded sum?

**Always on CDNA 1 and the SFMA.** An accepted block returns the FP32 value
nearest to the exact `Σ a_ℓ b_ℓ + c`, ties to even, and each SFMA step is the
value nearest to `c + a·b`.

- **Assumes:** the model accepted the input.
- **Classification:** Core theorem.
- **Lean:** [`MatrixCore.correctRounding_nearestEven`](https://github.com/pauljiang03/HardwarePrimitives/blob/main/amd/MatrixCore/MC/CorrectRounding.lean#L27), [`MatrixCore.sfma_step_nearestEven`](https://github.com/pauljiang03/HardwarePrimitives/blob/main/amd/MatrixCore/MC/CompositionProperties.lean#L79)

### When is CDNA 3 correctly rounded?

**Whenever alignment loses nothing.** If every product lies on the alignment
grid and the late alignment of `c` loses nothing in its branch, `S_acc` is the
exact sum and the output is its nearest-even rounding. On CDNA 2 the same holds
when nothing is flushed and every conversion and pairwise sum is exact.

- **Assumes:** the stated condition on the inputs (`LosslessAlignment`).
- **Classification:** Core theorems.
- **Lean:** [`MatrixCore.aligned_nearestEven_of_lossless`](https://github.com/pauljiang03/HardwarePrimitives/blob/main/amd/MatrixCore/MC/LosslessAlignment.lean#L184), [`MatrixCore.alignedAccumulation_of_lossless`](https://github.com/pauljiang03/HardwarePrimitives/blob/main/amd/MatrixCore/MC/LosslessAlignment.lean#L159),
  [`MatrixCore.pairwise_fl_exact_of_lossless`](https://github.com/pauljiang03/HardwarePrimitives/blob/main/amd/MatrixCore/MC/LosslessAlignment.lean#L222)

## Matrix core product order

### Does the order of the products matter?

**Not on CDNA 1 or CDNA 3 Algorithm 1, which depend on the products only as a
multiset; yes on CDNA 2 and CDNA 3 FP8.** On FP8 the parity law says
exactly how much: the output depends on the slots only through the unordered
pair {multiset of the odd slots, multiset of the even slots}, and a
permutation preserves it on every input exactly when it preserves the parity
partition. The parity law is proved in `wip/mmalgebra`, a work-in-progress
project that builds on the model.

- **Assumes:** nothing.
- **Classification:** Core theorems; kernel-checked witnesses for the order
  dependence.
- **Lean:** [`MatrixCore.accumulate_perm`](https://github.com/pauljiang03/HardwarePrimitives/blob/main/amd/MatrixCore/MC/Order.lean#L29), [`MatrixCore.pairWiseSum_order_dependent`](https://github.com/pauljiang03/HardwarePrimitives/blob/main/amd/MatrixCore/MC/Order.lean#L41),
  [`MatrixCore.oddEvenGrouping_order_dependent`](https://github.com/pauljiang03/HardwarePrimitives/blob/main/amd/MatrixCore/MC/Order.lean#L48), [`MMAlgebra.MC.cdna3FP8_parityEquiv`](https://github.com/pauljiang03/HardwarePrimitives/blob/main/wip/mmalgebra/MMAlgebraMC/ParityLaw.lean#L173), [`MMAlgebra.MC.cdna3FP8_permute_iff`](https://github.com/pauljiang03/HardwarePrimitives/blob/main/wip/mmalgebra/MMAlgebraMC/ParityLaw.lean#L523)

## MC-EFT correction

[MC-EFT](/HardwarePrimitives/amd/properties/eft/) is TC-EFT carried over to the
AMD matrix cores.

### Is the corrected result right?

**Yes, on every generation. Whatever the correction returns is the exact sum
rounded to the nearest FP32 value, ties to even.** It returns a value exactly
when that rounded sum is finite.

- **Assumes:** finite inputs and a finite `D`; nothing else about `D`.
- **Classification:** Core theorems.
- **Lean:** [`MatrixCore.mcEft_correct`](https://github.com/pauljiang03/HardwarePrimitives/blob/main/amd/MatrixCore/EFT/Encoded.lean#L108), [`MatrixCore.mcEft_isSome_iff`](https://github.com/pauljiang03/HardwarePrimitives/blob/main/amd/MatrixCore/EFT/Encoded.lean#L115)

### Does the fast FP32 path give the right answer?

**Yes, whenever its check passes.** Every FP32 step before the final rounding
is then exact.

- **Assumes:** the check holds.
- **Classification:** Core theorem. The core is a proof that FP32 summation is
  exact when all the bits fit within one span of 24 bits.
- **Lean:** [`MatrixCore.EftSplit.fastPath_sound`](https://github.com/pauljiang03/HardwarePrimitives/blob/main/amd/MatrixCore/EFT/Core.lean#L155), [`MatrixCore.naiveSum32_exact_of_bitSpan`](https://github.com/pauljiang03/HardwarePrimitives/blob/main/amd/MatrixCore/EFT/Sum32.lean#L119)

### What does the matrix core's output buy?

**On CDNA 1 the correction returns the output itself. On CDNA 2 the overlap is
exactly the low parts plus every rounding error of the block, minus what
flushing removed. On CDNA 3 it is what alignment kept of the low parts plus the
final rounding error, less than `N_FMA + 6` units of the cut-off.**

- **Assumes:** `D` is the block's own output.
- **Classification:** Core theorems; the CDNA 2 identity is exact, and its
  bound goes through the CDNA 2 error bound.
- **Lean:** [`MatrixCore.correctRounding_eft`](https://github.com/pauljiang03/HardwarePrimitives/blob/main/amd/MatrixCore/EFT/CDNA1.lean#L11), [`MatrixCore.pairwise_eft`](https://github.com/pauljiang03/HardwarePrimitives/blob/main/amd/MatrixCore/EFT/CDNA2.lean#L109),
  [`MatrixCore.aligned_eft`](https://github.com/pauljiang03/HardwarePrimitives/blob/main/amd/MatrixCore/EFT/CDNA3.lean#L632), [`MatrixCore.globalAlignment_exact_rounding`](https://github.com/pauljiang03/HardwarePrimitives/blob/main/amd/MatrixCore/EFT/CDNA3.lean#L706)

## Matrix core number formats and rounding

### Is FP32 rounding implemented correctly?

**Yes.** `fl{x}` is the nearest value among all finite FP32 words, ties to
an even last bit, and is finite exactly when `|x| < 2^128 − 2^103`. Within that
range the correctly rounded word with the sign of `x` is unique.

- **Classification:** Core theorems.
- **Lean:** [`MatrixCore.rne32_nearestEven`](https://github.com/pauljiang03/HardwarePrimitives/blob/main/amd/MatrixCore/Numerics/RoundingContract.lean#L312), [`MatrixCore.rne32_isSome_iff`](https://github.com/pauljiang03/HardwarePrimitives/blob/main/amd/MatrixCore/Numerics/RoundingContract.lean#L389), [`MatrixCore.rne32_iff`](https://github.com/pauljiang03/HardwarePrimitives/blob/main/amd/MatrixCore/Numerics/Uniqueness.lean#L356)

## What is not proved

- **That real GPUs behave like the models.** For the Tensor Cores that rests on
  replaying recorded measurements (see [hardware
  validation](/HardwarePrimitives/model/validation/)). No recorded AMD hardware
  measurements are published, so the AMD model rests on the paper's test
  vectors, the authors' MATLAB models and MMA-Sim (see [hardware
  validation](/HardwarePrimitives/amd/validation/)).
- **The AMD special-value layer** is a definition following the paper's
  description, not derived.
- **No theorem here is a finite list of cases dressed up as a general result.**
  Concrete `decide` checks are used only for worked examples and regression
  witnesses.
