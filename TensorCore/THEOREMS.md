# What is proven

This page lists the main results that Lean has checked, in plain language. Each row says what the
result means. The linked file has the exact statement and every assumption. All results depend
only on Lean's standard axioms (`propext`, `Classical.choice`, `Quot.sound`).

Two papers are cited in docstrings: *Accurate Models* (Khattak and Mikaitis, arXiv 2512.07004v4)
for the Tensor Core model, and *the TC-EFT paper* for non-monotonicity and the TC-EFT algorithm.

## The Tensor Core model

| What it says | Lean name | File |
| --- | --- | --- |
| The model and an independently written transcription of *Accurate Models* give the same output bits, or both reject, for every input on all 8 supported GPU variants. | `IndependentSpec.supported_eq_spec` | [TC/Specification/Supported.lean](TC/Specification/Supported.lean) |
| The model accepts an input exactly when it has the right number of products, no NaN or infinity, and a sum that fits in FP32. | `evalBlock_success_iff` | [TC/AcceptedDomain.lean](TC/AcceptedDomain.lean) |
| The exact sum of the inputs equals the output plus everything lost to alignment and rounding. | `evalBlock_residual_identity` | [TC/StageResiduals.lean](TC/StageResiduals.lean) |
| The error is less than (number of terms) × (alignment grid step) + (one output ulp). | `evalBlock_error_bound` | [TC/ErrorBounds.lean](TC/ErrorBounds.lean) |
| A fixed-width wrapping accumulator gives the same output for every input when it is wide enough (29/31/33 bits for V100/A100/H100 FP16, a sign bit included). | `evalBlockMachine_eq` | [TC/MachineRefinement.lean](TC/MachineRefinement.lean) |
| Every partial sum in that accumulator is exact, in any order. | `evalBlock_machinePrefix` | [TC/AlignmentExponent.lean](TC/AlignmentExponent.lean) |
| A bitvector datapath (9-bit exponents, aligned terms of F + 2 bits, an accumulator of 28 to 32 magnitude bits plus a sign bit, shifts and a leading-zero count) returns the same output word, or the same error, as the model for every input on all 8 supported GPU variants. | `Datapath.evalBlock_eq` | [Kernels/Datapath/Correctness.lean](Kernels/Datapath/Correctness.lean) |
| The guarantees above, bundled for any model. | `model_contract` | [TC/CanonicalFormats.lean](TC/CanonicalFormats.lean) |
| For chained block FMAs, the loss accounting holds across the whole chain. | `runBlocks_residual_ledger` | [TC/Composition.lean](TC/Composition.lean) |

## Non-monotonicity

| What it says | Lean name | File |
| --- | --- | --- |
| Lowering C from 1 to the next FP32 value below raises the output exactly when the block FMA has at least 3·2^p products (K equal products of `2^-(24+p)`; minimum alignment exponent at most −1). | `nonmonotone_encoded` | [TC/Monotonicity.lean](TC/Monotonicity.lean) |
| For `C = 1 − j·2^-24`: exactly which j raise the output, the output formula, and its maximum. | `nonmonotone_range_encoded` | [TC/MonotonicityRange.lean](TC/MonotonicityRange.lean) |
| For any inputs, an output increase needs the recovered products to outweigh the change in C; this suffices when both sums are FP32-representable. | `flowback_necessary`, `flowback_sufficient` | [TC/Flowback.lean](TC/Flowback.lean) |

## TC-EFT correction

| What it says | Lean name | File |
| --- | --- | --- |
| Any result TC-EFT returns is the exact sum rounded to nearest-even FP32, for any finite D. | `tcEftEncoded_correct` | [EFT/Encoded.lean](EFT/Encoded.lean) |
| TC-EFT returns a result exactly when that rounded sum is finite. | `tcEftEncoded_bits_isSome_iff` | [EFT/Encoded.lean](EFT/Encoded.lean) |
| When the scalar safety check passes, the fast FP32 path gives the correctly rounded sum. | `scalarCorrected_correct` | [EFT/Extraction.lean](EFT/Extraction.lean) |
| Exact sum = D − overlap + low parts. A definitional identity: the overlap is defined as D minus the retained part. | `overlap_recovery` | [EFT/Extraction.lean](EFT/Extraction.lean) |
| The input-based precondition establishes some of the fast-path check's conditions; for FP32 it derives five of the nine and assumes the other four (grid at least `2^-149`, overlap and H fit in FP32, sum in range). A concrete block satisfies all of them. | `ExtractionGrid.inputGrid_scalarPredicate`, `ExtractionGrid.inputGrid_scalarPredicate_fp32` | [EFT/ExtractionGrid.lean](EFT/ExtractionGrid.lean) |
| The 576-bit implementation succeeds exactly when the rounded sum is finite, and never overflows. | `EFMachine.tcEft_success`, `EFMachine.tcEft_range_iff` | [Kernels/EFT/Correctness.lean](Kernels/EFT/Correctness.lean) |
| The 576-bit implementation returns the same bits as the reference algorithm. | `EFMachine.tcEft_agrees` | [Kernels/EFT/Refinement.lean](Kernels/EFT/Refinement.lean) |
| Using Lean's native `Float32` additions changes nothing (relative to Lean's `Float32` specification). | `EFMachine.tcEftWithLean_eq` | [Kernels/EFT/Native.lean](Kernels/EFT/Native.lean) |
| In the 576-bit implementation, whenever the fast-path check passes, every FP32 step of the fast path is exact: the fast path is taken and returns the correctly rounded sum. | `EFMachine.Components.scalar_of_guard`, `EFMachine.tcEft_scalar_of_guard` | [Kernels/EFT/ScalarGuard.lean](Kernels/EFT/ScalarGuard.lean) |

## Number formats and rounding

| What it says | Lean name | File |
| --- | --- | --- |
| Rounding to FP32 returns the nearest value, ties to even, for every in-range input. | `round32_nearestEven_correct` | [Numerics/CorrectRounding.lean](Numerics/CorrectRounding.lean) |
| The same holds for any binary format and rounding direction. | `roundBinary_correct` | [Numerics/Binary/RoundingContract.lean](Numerics/Binary/RoundingContract.lean) |
| Rounding succeeds exactly when the input is within the format's finite range. | `roundBinary_isSome_iff` | [Numerics/Binary/RoundingContract.lean](Numerics/Binary/RoundingContract.lean) |
| Finite bit patterns and representable values correspond one to one, including subnormals and both zeros. | `signedFiniteBinaryBijection` | [Numerics/Binary/SignedBijection.lean](Numerics/Binary/SignedBijection.lean) |
| Naive floating-point summation is exact when the summands fit within a bounded bit span. | `naiveSumBinary_exact_of_bitSpan` | [Numerics/Binary/ScalarSum.lean](Numerics/Binary/ScalarSum.lean) |
| FP64 DMMA gives an exactly zero result the IEEE 754 sign, and keeps the correctly rounded bits otherwise. | `binary64FmaBits_of_eq_zero`, `binary64FmaBits_of_ne_zero` | [TC/FusedRounding.lean](TC/FusedRounding.lean) |

## Not proved

- That real GPUs behave like the model. That is tested by replaying recorded GPU outputs.

The [FloatLib correspondence](../floatlib-port/COMPARISON.md) covers the independent second
implementation. This block keeps every name above connected to the actual API:

```lean
import TensorCore

open TensorCore

#check IndependentSpec.supported_eq_spec
#check evalBlock_success_iff
#check evalBlock_residual_identity
#check evalBlock_error_bound
#check evalBlockMachine_eq
#check evalBlock_machinePrefix
#check Datapath.evalBlock_eq
#check model_contract
#check runBlocks_residual_ledger
#check nonmonotone_encoded
#check nonmonotone_range_encoded
#check flowback_necessary
#check flowback_sufficient
#check tcEftEncoded_correct
#check tcEftEncoded_bits_isSome_iff
#check scalarCorrected_correct
#check overlap_recovery
#check ExtractionGrid.inputGrid_scalarPredicate
#check ExtractionGrid.inputGrid_scalarPredicate_fp32
#check EFMachine.tcEft_success
#check EFMachine.tcEft_range_iff
#check EFMachine.tcEft_agrees
#check EFMachine.tcEftWithLean_eq
#check EFMachine.Components.scalar_of_guard
#check EFMachine.tcEft_scalar_of_guard
#check round32_nearestEven_correct
#check roundBinary_correct
#check roundBinary_isSome_iff
#check signedFiniteBinaryBijection
#check naiveSumBinary_exact_of_bitSpan
#check binary64FmaBits_of_eq_zero
#check binary64FmaBits_of_ne_zero
```
