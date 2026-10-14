---
title: What is proven
description: Every headline theorem in plain language, with what it assumes, what it means, and how strong it is.
---

This page lists the main results that Lean has checked. Each entry says, in
plain words, what the result means, what it assumes, and how much it really
establishes. The Lean name and a source link follow each entry for anyone
who wants to read the formal statement.

Every result here is checked by Lean's kernel. It relies only on Lean's three
standard axioms (`propext`, `Classical.choice`, `Quot.sound`), with no
`sorry` and no custom axioms. See [What is tested](/MMAlgebra/proofs/tested/)
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
are also those of Ada, H200 and B200, and on every model with a binary32 block
output, so on B200 FP8 too.

- **Assumes:** nothing beyond the input being one of these variants
  (`evalBlock_eq_spec` takes any model with `23 ≤ outputMantissaBits`).
- **Classification:** Core theorem. The transcription is mechanically checked not to reuse
  any model code, and a companion result shows it isn't vacuous.
- **Lean:** [`IndependentSpec.supported_eq_spec`](https://github.com/pauljiang03/MMAlgebra/blob/main/TensorCore/TC/Specification/Supported.lean#L28), [`IndependentSpec.blackwell_fp8_eq_spec`](https://github.com/pauljiang03/MMAlgebra/blob/main/TensorCore/TC/Specification/Supported.lean#L42)

### Which inputs does the model accept?

**Exactly those with the right number of products, no NaN or infinity, and a
sum that fits in FP32.** Anything else is rejected with a named error.

- **Assumes:** nothing; it holds for every model, FP8 included.
- **Classification:** Core theorem. It is an exact "if and only if".
- **Lean:** [`evalBlock_success_iff`](https://github.com/pauljiang03/MMAlgebra/blob/main/TensorCore/TC/AcceptedDomain.lean#L37)

### Is all the lost precision accounted for?

**Yes.** The exact sum of the inputs equals the model's output plus the parts
dropped by alignment and by the final rounding.

- **Assumes:** the model accepted the input.
- **Classification:** Core theorem. The exact sum is computed from the original input
  words, not from the model's own intermediate values.
- **Lean:** [`evalBlock_residual_identity`](https://github.com/pauljiang03/MMAlgebra/blob/main/TensorCore/TC/StageResiduals.lean#L92)

### How large can the error be?

**Less than (number of terms) × (alignment grid step) + (one unit in the last
place of the output).** The first part is the alignment loss and the second
is the rounding loss.

- **Assumes:** the model accepted the input, and its block output is binary32
  (every variant except Ada and Hopper FP8, whose 13-bit output is coarser).
- **Classification:** Core theorem.
- **Lean:** [`evalBlock_error_bound`](https://github.com/pauljiang03/MMAlgebra/blob/main/TensorCore/TC/ErrorBounds.lean#L98)

### Does modeling the adder as exact hide anything?

**No.** A model with a fixed-width, wrapping two's-complement register gives
the same output for every input, as long as the register is wide enough:
29, 31 and 33 bits for the V100, A100 and H100 FP16 models, a sign bit
included. Every partial
sum is exact too, whatever the order of additions.

- **Assumes:** a register at least that wide.
- **Classification:** Core theorem.
- **Lean:** [`evalBlockMachine_eq`](https://github.com/pauljiang03/MMAlgebra/blob/main/TensorCore/TC/MachineRefinement.lean#L15), [`evalBlock_machinePrefix`](https://github.com/pauljiang03/MMAlgebra/blob/main/TensorCore/TC/AlignmentExponent.lean#L186)

### Can the whole model run in fixed-width bitvector registers?

**Yes.** A [bitvector datapath](/MMAlgebra/model/datapath/) decodes, multiplies,
aligns, sums and normalizes using bitvector operations only. Its registers
are sized from the model: `F + 2` bits per aligned term, an accumulator of
28 to 32 magnitude bits plus a sign bit (30 and 32 on A100 and H100 FP16, the
widths in *Accurate Models*), and 9-bit exponents. It returns the same output word as the model, or the same
error, for every input on all eight FP16/BF16/TF32 variants.

- **Assumes:** nothing beyond the input being one of the eight FP16/BF16/TF32
  variants. The datapath does not cover FP8.
- **Classification:** Core theorem. The datapath shares no arithmetic with the
  model: it uses shifts, a leading-zero count and wrapping additions where the
  model uses rationals and floors.
- **Lean:** [`Datapath.evalBlock_eq`](https://github.com/pauljiang03/MMAlgebra/blob/main/TensorCore/Kernels/Datapath/Correctness.lean#L208)

### Chained block FMAs

**For instructions made of several block FMAs, the same loss accounting holds
across the whole chain.**

- **Assumes:** each block's output is passed on as the next block's `C`.
- **Classification:** Core theorem.
- **Lean:** [`runBlocks_residual_ledger`](https://github.com/pauljiang03/MMAlgebra/blob/main/TensorCore/TC/Composition.lean#L95)

### FP8 encodings and the FP8 block FMAs

**E4M3 and E5M2 decode as specified, and the FP8 models need no minimum
alignment exponent.** E4M3 has no infinities, its only NaNs are `0x7f` and
`0xff`, and its largest value is 448; E5M2 has infinities at `0x7c` and
`0xfc`, six NaNs, and largest value 57344. The block model's 9-bit E4M3
layout decodes all 256 words as E4M3 does. On Ada and Hopper FP8 the output is
the binary32 truncation of the accumulator with its ten low mantissa bits
cleared. The toolbox's minimum alignment exponents (−132, −133) change no
output on the FP8 models.

- **Assumes:** nothing.
- **Classification:** Core theorems, checked by computation over every word
  for the encodings.
- **Lean:** [`e4m3_specials`](https://github.com/pauljiang03/MMAlgebra/blob/main/TensorCore/Numerics/FP8.lean#L58), [`e5m2_specials`](https://github.com/pauljiang03/MMAlgebra/blob/main/TensorCore/Numerics/FP8.lean#L64), [`e4m3_decode_widen`](https://github.com/pauljiang03/MMAlgebra/blob/main/TensorCore/Numerics/FP8.lean#L43),
  [`fp8_output_thirteen_bits`](https://github.com/pauljiang03/MMAlgebra/blob/main/TensorCore/TC/GPUs.lean#L97), [`fp8_eAlignMin_inactive`](https://github.com/pauljiang03/MMAlgebra/blob/main/TensorCore/TC/GPUs.lean#L199)

## Non-monotonicity

### Can a smaller C give a larger result?

**Yes, and exactly when the FMA size is at least 3·2^p.** Here p is
the GPU's number of padding bits. The proof uses a specific family:
K equal tiny products, with `C` lowered from 1 to the next FP32 value below 1.

- **Assumes:** that construction (products of exactly `2^-(24+p)`), a
  minimum alignment exponent, if any, of at most −1, and a binary32 block
  output.
- **Classification:** Core theorem. It is an exact threshold, and every GPU model has
  a checked concrete example.
- **Lean:** [`nonmonotone_encoded`](https://github.com/pauljiang03/MMAlgebra/blob/main/TensorCore/TC/Monotonicity.lean#L274)

### How large can the effect be?

**The result gives the exact range of perturbations that raise the output, a
formula for the output, and its maximum,** for `C = 1 − j·2^-24`.

- **Assumes:** the same construction, with `1 ≤ j ≤ 2^23`.
- **Classification:** Core theorem.
- **Lean:** [`nonmonotone_range_encoded`](https://github.com/pauljiang03/MMAlgebra/blob/main/TensorCore/TC/MonotonicityRange.lean#L266)

### When does it happen in general?

**For any inputs, the output can rise only if the products recovered by the
finer grid outweigh the change in `C`.** That condition is also sufficient
when both sums are exactly representable in FP32.

- **Assumes:** both evaluations succeed; FP32 representability for the
  "sufficient" direction.
- **Classification:** Core theorem.
- **Lean:** [`flowback_necessary`](https://github.com/pauljiang03/MMAlgebra/blob/main/TensorCore/TC/Flowback.lean#L201), [`flowback_sufficient`](https://github.com/pauljiang03/MMAlgebra/blob/main/TensorCore/TC/Flowback.lean#L220)

## TC-EFT correction

### Is the corrected result right?

**Yes. Whatever TC-EFT returns is the exact sum rounded to the nearest FP32
value, ties to even.** It returns a value exactly when that rounded sum is
finite.

- **Assumes:** nothing about `D`, which can be any finite FP32 word.
- **Classification:** Core theorem. Note that the result doesn't depend on `D`
  being the real Tensor Core output.
- **Lean:** [`tcEftEncoded_correct`](https://github.com/pauljiang03/MMAlgebra/blob/main/TensorCore/EFT/Encoded.lean#L114), [`tcEftEncoded_bits_isSome_iff`](https://github.com/pauljiang03/MMAlgebra/blob/main/TensorCore/EFT/Encoded.lean#L128)

### Does the fast FP32 path give the right answer?

**Yes, whenever its safety check passes.** The check ensures every
intermediate FP32 operation is exact, so only the final rounding remains.

- **Assumes:** the scalar safety check holds.
- **Classification:** Core theorem. The core is a proof that naive FP32 summation is
  exact when all the bits fit within a span of 24 bits.
- **Lean:** [`scalarCorrected_correct`](https://github.com/pauljiang03/MMAlgebra/blob/main/TensorCore/EFT/Extraction.lean#L160), [`naiveSumBinary_exact_of_bitSpan`](https://github.com/pauljiang03/MMAlgebra/blob/main/TensorCore/Numerics/Binary/ScalarSum.lean#L166)

### Recovering the exact sum from D

**The exact sum equals `D` minus the overlap plus the low parts.**

- **Classification:** Definitional identity. The overlap is *defined* as `D` minus the
  retained part, so the identity is a rearrangement.
- **Lean:** [`overlap_recovery`](https://github.com/pauljiang03/MMAlgebra/blob/main/TensorCore/EFT/Extraction.lean#L20)

### Does the paper's input-based precondition imply the safety check?

**Partly.** For FP32 correction it derives five of the check's nine
conditions: format, grid, a span of at most 24 bits, magnitude range, and `D` fitting in
FP32. It assumes the other four: a grid no lower than `2^-149`, the overlap
and `H` fitting in FP32, and the sum in range. A concrete block satisfies all
of them.

- **Classification:** Partial reduction. The four remaining conditions depend
  on the particular sum, not only the input bound.
- **Lean:** [`ExtractionGrid.inputGrid_scalarPredicate`](https://github.com/pauljiang03/MMAlgebra/blob/main/TensorCore/EFT/ExtractionGrid.lean#L174), [`ExtractionGrid.inputGrid_scalarPredicate_fp32`](https://github.com/pauljiang03/MMAlgebra/blob/main/TensorCore/EFT/ExtractionGrid.lean#L191)

### Does the fixed-size implementation agree?

**Yes.** The 576-bit implementation never overflows on supported inputs,
returns a result exactly when the rounded sum is finite, and returns the
same bits as the reference version. Swapping in Lean's native `Float32`
additions changes nothing.

- **Assumes:** supported, finite, correctly shaped inputs.
- **Classification:** Core theorem. The native-float part holds relative to Lean's
  specification of `Float32`.
- **Lean:** [`EFMachine.tcEft_success`](https://github.com/pauljiang03/MMAlgebra/blob/main/TensorCore/Kernels/EFT/Correctness.lean#L91), [`EFMachine.tcEft_range_iff`](https://github.com/pauljiang03/MMAlgebra/blob/main/TensorCore/Kernels/EFT/Correctness.lean#L101), [`EFMachine.tcEft_agrees`](https://github.com/pauljiang03/MMAlgebra/blob/main/TensorCore/Kernels/EFT/Refinement.lean#L9), [`EFMachine.tcEftWithLean_eq`](https://github.com/pauljiang03/MMAlgebra/blob/main/TensorCore/Kernels/EFT/Native.lean#L105)

### Does passing the fast-path check guarantee the fast path?

**Yes.** In the 576-bit implementation the fast path is plain FP32
operations. Whenever the check passes, every one of those operations is
exact, so the fast path is taken and returns the correctly rounded sum. No
run-time comparison against exact values is needed.

- **Assumes:** a supported, finite input that passes the check and is not all
  zeros.
- **Classification:** Core theorem.
- **Lean:** [`EFMachine.Components.scalar_of_guard`](https://github.com/pauljiang03/MMAlgebra/blob/main/TensorCore/Kernels/EFT/ScalarGuard.lean#L190), [`EFMachine.tcEft_scalar_of_guard`](https://github.com/pauljiang03/MMAlgebra/blob/main/TensorCore/Kernels/EFT/ScalarGuard.lean#L224)

### Does FP64 DMMA follow IEEE 754 for signed zero?

**Yes.** An exactly zero result `a·b + c` gets the IEEE 754 sign: addends
with the same sign keep it; otherwise `+0`, or `−0` when rounding toward
negative. A nonzero result that rounds to zero keeps its own sign.

- **Classification:** Core theorem.
- **Lean:** [`binary64FmaBits_of_eq_zero`](https://github.com/pauljiang03/MMAlgebra/blob/main/TensorCore/TC/FusedRounding.lean#L78), [`binary64FmaBits_of_ne_zero`](https://github.com/pauljiang03/MMAlgebra/blob/main/TensorCore/TC/FusedRounding.lean#L68)

## Number formats and rounding

### Is FP32 rounding implemented correctly?

**Yes.** The rounding function returns the nearest FP32 value, ties to even, for every
input in range. This also holds for any binary format and any rounding
direction.

- **Classification:** Core theorem. One gap: the specification doesn't fix the sign of a
  zero result.
- **Lean:** [`round32_nearestEven_correct`](https://github.com/pauljiang03/MMAlgebra/blob/main/TensorCore/Numerics/CorrectRounding.lean#L155), [`roundBinary_correct`](https://github.com/pauljiang03/MMAlgebra/blob/main/TensorCore/Numerics/Binary/RoundingContract.lean#L17)

### Is decoding of bit patterns consistent?

**Yes.** Finite bit patterns and representable values correspond one to one,
including subnormals and both zeros.

- **Classification:** Core theorem.
- **Lean:** [`signedFiniteBinaryBijection`](https://github.com/pauljiang03/MMAlgebra/blob/main/TensorCore/Numerics/Binary/SignedBijection.lean#L130)

## What is not proved

- **That real GPUs behave like the model.** That rests on replaying recorded
  measurements. See [hardware validation](/MMAlgebra/model/validation/).
- **No theorem here is a finite list of cases dressed up as a general result.**
  Concrete `decide` checks are used only for worked examples and regression
  witnesses.
