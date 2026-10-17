# What is proven

This page lists the main results that Lean has checked, in plain language. Each row says what the
result means. The linked file has the exact statement and every assumption. All results depend
only on Lean's standard axioms (`propext`, `Classical.choice`, `Quot.sound`).

Two papers are cited in docstrings: *Accurate Models* (Khattak and Mikaitis, arXiv 2512.07004v4)
for the Tensor Core model, and *the TC-EFT paper* for non-monotonicity and the TC-EFT algorithm.

## The Tensor Core model

| What it says | Lean name | File |
| --- | --- | --- |
| The model and an independently written transcription of *Accurate Models* give the same output bits, or both reject, for every input on all 8 FP16/BF16/TF32 variants (which are also Ada's, H200's and B200's), and on any model with a binary32 block output, B200 FP8 included. | `IndependentSpec.supported_eq_spec`, `IndependentSpec.evalBlock_eq_spec`, `IndependentSpec.blackwell_fp8_eq_spec` | [TC/Specification/Supported.lean](TC/Specification/Supported.lean) |
| The model accepts an input exactly when it has the right number of products, no NaN or infinity, and a sum that fits in FP32, whatever the width of its block output. | `evalBlock_success_iff` | [TC/AcceptedDomain.lean](TC/AcceptedDomain.lean) |
| The exact sum of the inputs equals the output plus everything lost to alignment and rounding. | `evalBlock_residual_identity` | [TC/StageResiduals.lean](TC/StageResiduals.lean) |
| With a binary32 block output, the error is less than (number of terms) × (alignment grid step) + (one output ulp). | `evalBlock_error_bound` | [TC/ErrorBounds.lean](TC/ErrorBounds.lean) |
| For every block-output width `m`, the error is less than (number of terms) × (alignment grid step) + `2^(23 − m)` units in the last place of the binary32 output word; on Ada and Hopper FP8 (`m = 13`) that is one unit in the last place of the 14-bit output significand. | `evalBlock_error_bound_any`, `fp8_error_bound` | [TC/OutputWidth.lean](TC/OutputWidth.lean) |
| The model's output word is the one an independent specification selects for every block-output width (the accumulator truncated to binary32 and then to `m` mantissa bits), with the same rejections; for `m ≥ 23` that specification is the binary32 one. Ada and Hopper FP8 included. | `IndependentSpec.evalBlock_eq_specM`, `IndependentSpec.bitsM_eq_bits`, `IndependentSpec.fp8_eq_spec` | [TC/Specification/OutputWidth.lean](TC/Specification/OutputWidth.lean) |
| For chained block FMAs, the loss accounting holds across the whole chain. | `runBlocks_residual_ledger` | [TC/Composition.lean](TC/Composition.lean) |
| The output word is the accumulator truncated to binary32 and then to the model's block-output mantissa bits (23 except on Ada and Hopper FP8). | `evalPrepared_output_mantissa`, `evalBlock_output` | [TC/ErrorBounds.lean](TC/ErrorBounds.lean) |
| A fixed-width wrapping accumulator gives the same output for every input when it is wide enough (29/31/33 bits for V100/A100/H100 FP16, a sign bit included). | `evalBlockMachine_eq` | [TC/MachineRefinement.lean](TC/MachineRefinement.lean) |
| Every partial sum in that accumulator is exact, in any order. | `evalBlock_machinePrefix` | [TC/AlignmentExponent.lean](TC/AlignmentExponent.lean) |
| A bitvector datapath (9-bit exponents, aligned terms of F + 2 bits, an accumulator of 28 to 32 magnitude bits plus a sign bit, shifts and a leading-zero count) returns the same output word, or the same error, as the model for every input on all 8 FP16/BF16/TF32 variants. | `Datapath.evalBlock_eq` | [Kernels/Datapath/Correctness.lean](Kernels/Datapath/Correctness.lean) |
| A bitvector datapath for the six FP8 block FMAs (Ada, Hopper and B200; E4M3 and E5M2) returns the same output word, or the same error, as the model for every input: on Ada and Hopper it aligns on 23 mantissa bits, shifts, drops the ten low bits, and clears the ten low mantissa bits of the output. | `Datapath.FP8.evalBlock8_eq` | [Kernels/Datapath/FP8.lean](Kernels/Datapath/FP8.lean) |
| The guarantees above, bundled for any model with a binary32 block output. | `model_contract` | [TC/CanonicalFormats.lean](TC/CanonicalFormats.lean) |

## Ada, H200, B200 and FP8

Ada's FP16, BF16 and TF32 models are A100's and B200's are H100's (`adaF16F32`, `blackwellF16F32`, …);
H200 uses the Hopper models. Every theorem about those models therefore holds for these GPUs. The
FP8 block FMAs are `adaE4M3F32`, `adaE5M2F32`, `hopperE4M3F32`, `hopperE5M2F32` (`wgmma`),
`blackwellE4M3F32` and `blackwellE5M2F32` (`tcgen05.mma`), in [TC/GPUs.lean](TC/GPUs.lean). The
FP8 `mma.sync` path of H100, H200 and B200 is `mmaSyncFP8` (one instruction) and `mmaSyncFP8Dot`
(a K loop), and the RTX PRO 6000's FP8 `mma.sync` is `rtxPro6000E4M3F32`, `rtxPro6000E5M2F32`, in
[TC/MmaSyncFP8.lean](TC/MmaSyncFP8.lean).

| What it says | Lean name | File |
| --- | --- | --- |
| E4M3 has no infinities, its only NaNs are `0x7f` and `0xff`, and its largest value is 448; E5M2 has the infinities `0x7c`, `0xfc`, six NaNs, and largest value 57344. | `e4m3_specials`, `e4m3_max`, `e5m2_specials`, `e5m2_max` | [Numerics/FP8.lean](Numerics/FP8.lean) |
| The block model's 9-bit E4M3 layout decodes every one of the 256 E4M3 words as E4M3 does. | `e4m3_decode_widen`, `prepareProducts_widenE4M3` | [Numerics/FP8.lean](Numerics/FP8.lean), [TC/GPUs.lean](TC/GPUs.lean) |
| On Ada and Hopper FP8 the output is the binary32 truncation of the accumulator with its ten low mantissa bits cleared. | `fp8_output_thirteen_bits` | [TC/GPUs.lean](TC/GPUs.lean) |
| A minimum alignment exponent of at most −126 changes no output when the input format's bias is at most 64; so the toolbox's −132 and −133 change nothing on the FP8 models, which follow Table 3 in having none. | `evalBlock_eAlignMin_inactive`, `fp8_eAlignMin_inactive` | [TC/GPUs.lean](TC/GPUs.lean) |
| Recursive summation of N_FMA-product block FMAs is one block FMA for N_FMA products; adding `c` afterwards in binary32 rounds to nearest even. | `Model.dot_one_block`, `addBinary32_nearestEven` | [TC/GPUs.lean](TC/GPUs.lean) |
| The FP8 invocation descriptors are well formed. | `fp8_descriptors_valid` | [TC/GPUs.lean](TC/GPUs.lean) |
| Converting E4M3 or E5M2 to FP16 keeps every value, every NaN and infinity, and the sign. | `e4m3ToF16_exact`, `e5m2ToF16_exact` | [Numerics/FP8.lean](Numerics/FP8.lean) |
| The FP8 `mma.sync` model (two interleaved FP16 block FMAs, the second from the first's output, then `c` added in binary32) reproduces the interleaving pattern *Accurate Models* reports, and the order with the second group first and a single 32-product block do not. | `interleave_test_e5m2`, `interleave_test_reversed`, `interleave_test_single_block` | [TC/MmaSyncFP8.lean](TC/MmaSyncFP8.lean) |
| `c` added after the products is rounded to nearest, not truncated: one input separates the `mma.sync` path from a block FMA that holds `c`. | `late_c_witness` | [TC/MmaSyncFP8.lean](TC/MmaSyncFP8.lean) |
| On a recorded B200 E5M2 row, the `mma.sync` model returns the recorded word, and two independent FP16 block FMAs added in binary32 return another. | `separate_groups_excluded` | [TC/MmaSyncFP8.lean](TC/MmaSyncFP8.lean) |

The results that hold for any model hold for the FP8 models: the residual identity, the accepted
domain, the chain ledger, the fixed-width accumulator, the error bound and the specification
equality for every block-output width (`evalBlock_error_bound_any`, `evalBlock_eq_specM`), and the
FP8 bitvector datapath. The binary32 statements `evalBlock_error_bound` and `evalBlock_eq_spec`
keep the hypothesis `23 ≤ p.outputMantissaBits`, as do the block contracts, exact alignment,
flowback and the non-monotonicity theorems (which also need `F ≥ 23`); the Ada and Hopper FP8
models do not meet it.

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

- That real GPUs behave like the model. That is tested by replaying recorded GPU outputs: 35,000
  rows of V100, A100 and H100, 125,000 of Ada, L40S, H100, H200 and B200, and 20,000 H100 and H200
  FP8 rows of the toolbox's release v0.1, all bit-identical. The B200 FP8 rows, recorded with the
  toolbox's `mma.sync` harness, agree with `mmaSyncFP8Dot` (and with `Model.dotThenAdd`); the H100
  and H200 FP8 rows of commit 79143bd agree with the Hopper block FMA from `c = 0`, and those of
  v0.1 with `mmaSyncFP8Dot` with `c`. No recorded data has a nonzero `c` accumulated inside
  `wgmma` or `tcgen05.mma`; there the evidence is a cross-check against MMA-Sim, a simulator.
- FP4, FP6 and the Blackwell instructions *Accurate Models* does not characterize are not
  modeled.

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
#check evalPrepared_output_mantissa
#check evalBlock_output
#check IndependentSpec.evalBlock_eq_spec
#check IndependentSpec.blackwell_fp8_eq_spec
#check e4m3_specials
#check e4m3_max
#check e5m2_specials
#check e5m2_max
#check e4m3_decode_widen
#check prepareProducts_widenE4M3
#check fp8_output_thirteen_bits
#check evalBlock_eAlignMin_inactive
#check fp8_eAlignMin_inactive
#check Model.dot_one_block
#check addBinary32_nearestEven
#check fp8_descriptors_valid
#check e4m3ToF16_exact
#check e5m2ToF16_exact
#check interleave_test_e5m2
#check interleave_test_reversed
#check interleave_test_single_block
#check late_c_witness
#check separate_groups_excluded
#check evalBlock_error_bound_any
#check fp8_error_bound
#check IndependentSpec.evalBlock_eq_specM
#check IndependentSpec.bitsM_eq_bits
#check IndependentSpec.fp8_eq_spec
#check Datapath.FP8.evalBlock8_eq
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
