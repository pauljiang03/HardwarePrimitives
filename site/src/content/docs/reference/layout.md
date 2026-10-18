---
title: Repository layout
description: Where each part of the development lives.
---

Each hardware primitive has its own folder, holding its Lake project, tests,
examples, scripts and FloatLib implementation.

| Path | Contents |
| --- | --- |
| [`tensor-core/`](https://github.com/pauljiang03/HardwarePrimitives/tree/main/tensor-core) | NVIDIA Tensor Cores: the `TensorCore` library |
| [`matrix-core/`](https://github.com/pauljiang03/HardwarePrimitives/tree/main/matrix-core) | AMD Matrix Cores: the `MatrixCore` library (CDNA 1, 2 and 3) |
| [`site/`](https://github.com/pauljiang03/HardwarePrimitives/tree/main/site) | This website (Astro Starlight) |
| [`wip/`](https://github.com/pauljiang03/HardwarePrimitives/tree/main/wip) | Work in progress that builds on the models, not covered by this website |

The two libraries are independent: `MatrixCore` does not import `TensorCore`.

## Tensor Core

| Path | Contents |
| --- | --- |
| [`TensorCore/Numerics/`](https://github.com/pauljiang03/HardwarePrimitives/tree/main/tensor-core/TensorCore/Numerics) | Formats, encodings, exact arithmetic, truncation, rounding and its correctness |
| [`TensorCore/TC/`](https://github.com/pauljiang03/HardwarePrimitives/tree/main/tensor-core/TensorCore/TC) | Models, `evalBlock`, invocations, accumulator width, error bounds, non-monotonicity, chaining |
| [`TensorCore/TC/Specification/`](https://github.com/pauljiang03/HardwarePrimitives/tree/main/tensor-core/TensorCore/TC/Specification) | Independent *Accurate Models* specification (`IndependentSpec`) and the equality proof |
| [`TensorCore/EFT/`](https://github.com/pauljiang03/HardwarePrimitives/tree/main/tensor-core/TensorCore/EFT) | Extraction, scalar predicate, reference Algorithm 1 (TC-EFT paper) |
| [`TensorCore/Kernels/Datapath/`](https://github.com/pauljiang03/HardwarePrimitives/tree/main/tensor-core/TensorCore/Kernels/Datapath) | Bitvector Tensor Core datapath and its equality with `evalBlock` |
| [`TensorCore/Kernels/EFT/`](https://github.com/pauljiang03/HardwarePrimitives/tree/main/tensor-core/TensorCore/Kernels/EFT) | 576-bit bounded EFT and refinement proofs |
| [`TensorCore/Scalar/`](https://github.com/pauljiang03/HardwarePrimitives/tree/main/tensor-core/TensorCore/Scalar) | IEEE scalar operations and the Lean Float32 bridge |
| [`tests/`](https://github.com/pauljiang03/HardwarePrimitives/tree/main/tensor-core/tests) | Regression witnesses and trust audits (`TensorCoreTests`) |
| [`examples/`](https://github.com/pauljiang03/HardwarePrimitives/tree/main/tensor-core/examples) | Worked, self-checking Lean files |
| [`Main/`](https://github.com/pauljiang03/HardwarePrimitives/tree/main/tensor-core/Main) | Native batch adapters |
| [`scripts/`](https://github.com/pauljiang03/HardwarePrimitives/tree/main/tensor-core/scripts) | Validation runners and exact-arithmetic oracles |
| [`data/`](https://github.com/pauljiang03/HardwarePrimitives/tree/main/tensor-core/data) | Example inputs and recorded reports |
| [`vendor/`](https://github.com/pauljiang03/HardwarePrimitives/tree/main/tensor-core/vendor) | Pinned GPU vectors and reference models |
| [`floatlib-port/`](https://github.com/pauljiang03/HardwarePrimitives/tree/main/tensor-core/floatlib-port) | Independent FloatLib implementation |

Paths are relative to `tensor-core/`.

## Matrix Core

| Path | Contents |
| --- | --- |
| [`MatrixCore/Numerics/`](https://github.com/pauljiang03/HardwarePrimitives/tree/main/matrix-core/MatrixCore/Numerics) | Formats, decoding, grids, FP32 rounding and its correctness |
| [`MatrixCore/MC/`](https://github.com/pauljiang03/HardwarePrimitives/tree/main/matrix-core/MatrixCore/MC) | Models, block stages, evaluation, special values, chaining, theorems |
| [`MatrixCore/Specification/`](https://github.com/pauljiang03/HardwarePrimitives/tree/main/matrix-core/MatrixCore/Specification) | Independent transcription of the paper and the equality proofs |
| [`MatrixCore/EFT/`](https://github.com/pauljiang03/HardwarePrimitives/tree/main/matrix-core/MatrixCore/EFT) | MC-EFT for every generation |
| [`tests/`](https://github.com/pauljiang03/HardwarePrimitives/tree/main/matrix-core/tests) | The paper's test vectors, regressions and the audit (`MatrixCoreTests`) |
| [`examples/`](https://github.com/pauljiang03/HardwarePrimitives/tree/main/matrix-core/examples) | Worked examples |
| [`Main/`](https://github.com/pauljiang03/HardwarePrimitives/tree/main/matrix-core/Main) | `mc_eval`, which evaluates inner products from words |
| [`scripts/`](https://github.com/pauljiang03/HardwarePrimitives/tree/main/matrix-core/scripts) | Validation runner and differential tests |
| [`docs/`](https://github.com/pauljiang03/HardwarePrimitives/tree/main/matrix-core/docs) | Notes on the paper's vectors and on the differential tests |
| [`floatlib-port/`](https://github.com/pauljiang03/HardwarePrimitives/tree/main/matrix-core/floatlib-port) | Independent FloatLib implementation |

Paths are relative to `matrix-core/`. Where each part of the model is defined:

| Topic | Declarations | File |
| --- | --- | --- |
| Formats and decoding | `Format`, `fp16`, `bf16`, `e4m3fnuz`, `e5m2fnuz`, `InputFormat.read` | [Format.lean](https://github.com/pauljiang03/HardwarePrimitives/blob/main/matrix-core/MatrixCore/Numerics/Format.lean) |
| Truncation and round-down | `truncGrid`, `truncMantissa`, `rdGrid`, `rdMantissa` | [Grid.lean](https://github.com/pauljiang03/HardwarePrimitives/blob/main/matrix-core/MatrixCore/Numerics/Grid.lean) |
| `fl{·}` | `rne32`, `fl32`, `normExp` | [Round32.lean](https://github.com/pauljiang03/HardwarePrimitives/blob/main/matrix-core/MatrixCore/Numerics/Round32.lean) |
| Models | `Model`, `Accumulation`, `cdna1F16`, … | [Defs.lean](https://github.com/pauljiang03/HardwarePrimitives/blob/main/matrix-core/MatrixCore/MC/Defs.lean), [Models.lean](https://github.com/pauljiang03/HardwarePrimitives/blob/main/matrix-core/MatrixCore/MC/Models.lean) |
| Stages | `pairwiseSum`, `productSum`, `lateSum`, `shiftedSum` | [Stages.lean](https://github.com/pauljiang03/HardwarePrimitives/blob/main/matrix-core/MatrixCore/MC/Stages.lean) |
| Evaluation | `evalBlock`, `blockBits`, `accumulate` | [Eval.lean](https://github.com/pauljiang03/HardwarePrimitives/blob/main/matrix-core/MatrixCore/MC/Eval.lean) |
| Special values | `blockOutcome`, `Outcome` | [Special.lean](https://github.com/pauljiang03/HardwarePrimitives/blob/main/matrix-core/MatrixCore/MC/Special.lean) |
| Chaining | `dotBits`, `dotOutcome`, `mfma` | [Composition.lean](https://github.com/pauljiang03/HardwarePrimitives/blob/main/matrix-core/MatrixCore/MC/Composition.lean) |
| Runs of blocks | `runBlocks`, `Chain`, `runBlocks_all` | [Chain.lean](https://github.com/pauljiang03/HardwarePrimitives/blob/main/matrix-core/MatrixCore/MC/Chain.lean) |
| Output error | `correctRounding_error`, `pairwise_error`, `aligned_error`, `dotBits_error_bound` | [ErrorBounds.lean](https://github.com/pauljiang03/HardwarePrimitives/blob/main/matrix-core/MatrixCore/MC/ErrorBounds.lean) |
| Bounds from the inputs | `correctRounding_apriori`, `pairwise_apriori`, `aligned_apriori` | [AprioriBounds.lean](https://github.com/pauljiang03/HardwarePrimitives/blob/main/matrix-core/MatrixCore/MC/AprioriBounds.lean) |
| Monotonicity | `evalBlock_c_monotone`, `dotBits_c_monotone`, `cdna3F16_nonmonotonic`, … | [Monotonicity.lean](https://github.com/pauljiang03/HardwarePrimitives/blob/main/matrix-core/MatrixCore/MC/Monotonicity.lean), [ProductMonotonicity.lean](https://github.com/pauljiang03/HardwarePrimitives/blob/main/matrix-core/MatrixCore/MC/ProductMonotonicity.lean) |
| Inner products and `D = AB + C` | `dotBits_exact_error`, `mfma_error` | [InnerProduct.lean](https://github.com/pauljiang03/HardwarePrimitives/blob/main/matrix-core/MatrixCore/MC/InnerProduct.lean), [MFMA.lean](https://github.com/pauljiang03/HardwarePrimitives/blob/main/matrix-core/MatrixCore/MC/MFMA.lean) |
| Contracts | `BlockContract`, `cdna1F16_contract`, …, `dotBits_blocks` | [Contract.lean](https://github.com/pauljiang03/HardwarePrimitives/blob/main/matrix-core/MatrixCore/MC/Contract.lean) |
| Fixed-width accumulation | `alignedBits`, `machineAccumulate`, `evalBlockMachine` | [Accumulator.lean](https://github.com/pauljiang03/HardwarePrimitives/blob/main/matrix-core/MatrixCore/MC/Accumulator.lean), [MachineRefinement.lean](https://github.com/pauljiang03/HardwarePrimitives/blob/main/matrix-core/MatrixCore/MC/MachineRefinement.lean) |
| MC-EFT correction | `mcEft`, `eftSplit`, `mcEft_correct`, `pairwise_eft`, `aligned_eft` | [Core.lean](https://github.com/pauljiang03/HardwarePrimitives/blob/main/matrix-core/MatrixCore/EFT/Core.lean), [Encoded.lean](https://github.com/pauljiang03/HardwarePrimitives/blob/main/matrix-core/MatrixCore/EFT/Encoded.lean), [CDNA1.lean](https://github.com/pauljiang03/HardwarePrimitives/blob/main/matrix-core/MatrixCore/EFT/CDNA1.lean), [CDNA2.lean](https://github.com/pauljiang03/HardwarePrimitives/blob/main/matrix-core/MatrixCore/EFT/CDNA2.lean), [CDNA3.lean](https://github.com/pauljiang03/HardwarePrimitives/blob/main/matrix-core/MatrixCore/EFT/CDNA3.lean) |
| MC-EFT on inner products | `mcEftDot`, `mcEftDot_correct`, `dot_overlap` | [Dot.lean](https://github.com/pauljiang03/HardwarePrimitives/blob/main/matrix-core/MatrixCore/EFT/Dot.lean) |
| MC-EFT from the inputs | `InputFast`, `guard_of_inputs`, `aligned_fast`, `pairwise_fast`, `correctRounding_fast` | [Inputs.lean](https://github.com/pauljiang03/HardwarePrimitives/blob/main/matrix-core/MatrixCore/EFT/Inputs.lean) |
| MC-EFT in a 576-bit register | `roundReg`, `mcEftFixed`, `mcEftFixed_eq`, `paper_models_fitRun` | [Register.lean](https://github.com/pauljiang03/HardwarePrimitives/blob/main/matrix-core/MatrixCore/EFT/Register.lean), [Fixed.lean](https://github.com/pauljiang03/HardwarePrimitives/blob/main/matrix-core/MatrixCore/EFT/Fixed.lean) |
| Independent specification | `Spec.Result`, `Spec.blockBits_eq_spec`, `Spec.pairwise_eq_spec` | [Defs.lean](https://github.com/pauljiang03/HardwarePrimitives/blob/main/matrix-core/MatrixCore/Specification/Defs.lean), [Equivalence.lean](https://github.com/pauljiang03/HardwarePrimitives/blob/main/matrix-core/MatrixCore/Specification/Equivalence.lean) |
