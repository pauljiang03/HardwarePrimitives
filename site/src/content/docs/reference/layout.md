---
title: Repository layout
description: Where each part of the development lives.
---

| Path | Contents |
| --- | --- |
| [`TensorCore/Numerics/`](https://github.com/pauljiang03/HardwarePrimitives/tree/main/TensorCore/Numerics) | Formats, encodings, exact arithmetic, truncation, rounding and its correctness |
| [`TensorCore/TC/`](https://github.com/pauljiang03/HardwarePrimitives/tree/main/TensorCore/TC) | Models, `evalBlock`, invocations, accumulator width, error bounds, non-monotonicity, chaining |
| [`TensorCore/TC/Specification/`](https://github.com/pauljiang03/HardwarePrimitives/tree/main/TensorCore/TC/Specification) | Independent *Accurate Models* specification (`IndependentSpec`) and the equality proof |
| [`TensorCore/EFT/`](https://github.com/pauljiang03/HardwarePrimitives/tree/main/TensorCore/EFT) | Extraction, scalar predicate, reference Algorithm 1 (TC-EFT paper) |
| [`TensorCore/Kernels/Datapath/`](https://github.com/pauljiang03/HardwarePrimitives/tree/main/TensorCore/Kernels/Datapath) | Bitvector Tensor Core datapath and its equality with `evalBlock` |
| [`TensorCore/Kernels/EFT/`](https://github.com/pauljiang03/HardwarePrimitives/tree/main/TensorCore/Kernels/EFT) | 576-bit bounded EFT and refinement proofs |
| [`TensorCore/Scalar/`](https://github.com/pauljiang03/HardwarePrimitives/tree/main/TensorCore/Scalar) | IEEE scalar operations and the Lean Float32 bridge |
| [`tests/`](https://github.com/pauljiang03/HardwarePrimitives/tree/main/tests) | Regression witnesses and trust audits (`TensorCoreTests`) |
| [`examples/`](https://github.com/pauljiang03/HardwarePrimitives/tree/main/examples) | Worked, self-checking Lean files |
| [`Main/`](https://github.com/pauljiang03/HardwarePrimitives/tree/main/Main) | Native batch adapters |
| [`scripts/`](https://github.com/pauljiang03/HardwarePrimitives/tree/main/scripts) | Validation runners and exact-arithmetic oracles |
| [`data/`](https://github.com/pauljiang03/HardwarePrimitives/tree/main/data) | Example inputs and recorded reports |
| [`vendor/`](https://github.com/pauljiang03/HardwarePrimitives/tree/main/vendor) | Pinned GPU vectors and reference models |
| [`amd/`](https://github.com/pauljiang03/HardwarePrimitives/tree/main/amd) | The AMD matrix-core model `MatrixCore` (CDNA 1, 2 and 3), a standalone Lake project with its own tests and FloatLib implementation |
| [`floatlib-port/`](https://github.com/pauljiang03/HardwarePrimitives/tree/main/floatlib-port) | Independent FloatLib implementation |
| [`site/`](https://github.com/pauljiang03/HardwarePrimitives/tree/main/site) | This website (Astro Starlight) |
| [`wip/`](https://github.com/pauljiang03/HardwarePrimitives/tree/main/wip) | Work in progress that builds on the models, not covered by this website |

## The AMD model

The matrix-core model `MatrixCore` lives in [`amd/`](https://github.com/pauljiang03/HardwarePrimitives/tree/main/amd), a standalone Lake project with its own tests, examples and FloatLib implementation.

| Topic | Declarations | File |
| --- | --- | --- |
| Formats and decoding | `Format`, `binary16`, `bfloat16`, `e4m3fnuz`, `e5m2fnuz`, `InputFormat.read` | [Format.lean](https://github.com/pauljiang03/HardwarePrimitives/blob/main/amd/MatrixCore/Numerics/Format.lean) |
| Truncation and round-down | `truncGrid`, `truncMantissa`, `rdGrid`, `rdMantissa` | [Grid.lean](https://github.com/pauljiang03/HardwarePrimitives/blob/main/amd/MatrixCore/Numerics/Grid.lean) |
| `fl{·}` | `rne32`, `fl32`, `normExp` | [Round32.lean](https://github.com/pauljiang03/HardwarePrimitives/blob/main/amd/MatrixCore/Numerics/Round32.lean) |
| Models | `Model`, `Accumulation`, `cdna1F16`, … | [Defs.lean](https://github.com/pauljiang03/HardwarePrimitives/blob/main/amd/MatrixCore/MC/Defs.lean), [Models.lean](https://github.com/pauljiang03/HardwarePrimitives/blob/main/amd/MatrixCore/MC/Models.lean) |
| Stages | `pairwiseSum`, `productSum`, `lateSum`, `shiftedSum` | [Stages.lean](https://github.com/pauljiang03/HardwarePrimitives/blob/main/amd/MatrixCore/MC/Stages.lean) |
| Evaluation | `evalBlock`, `blockBits`, `accumulate` | [Eval.lean](https://github.com/pauljiang03/HardwarePrimitives/blob/main/amd/MatrixCore/MC/Eval.lean) |
| Special values | `blockOutcome`, `Outcome` | [Special.lean](https://github.com/pauljiang03/HardwarePrimitives/blob/main/amd/MatrixCore/MC/Special.lean) |
| Chaining | `dotBits`, `dotOutcome`, `mfma` | [Composition.lean](https://github.com/pauljiang03/HardwarePrimitives/blob/main/amd/MatrixCore/MC/Composition.lean) |
| Runs of blocks | `runBlocks`, `Chain`, `runBlocks_all` | [Chain.lean](https://github.com/pauljiang03/HardwarePrimitives/blob/main/amd/MatrixCore/MC/Chain.lean) |
| Output error | `correctRounding_error`, `pairwise_error`, `aligned_error`, `dotBits_error_bound` | [ErrorBounds.lean](https://github.com/pauljiang03/HardwarePrimitives/blob/main/amd/MatrixCore/MC/ErrorBounds.lean) |
| Bounds from the inputs | `correctRounding_apriori`, `pairwise_apriori`, `aligned_apriori` | [AprioriBounds.lean](https://github.com/pauljiang03/HardwarePrimitives/blob/main/amd/MatrixCore/MC/AprioriBounds.lean) |
| Monotonicity | `evalBlock_c_monotone`, `dotBits_c_monotone`, `cdna3F16_nonmonotonic`, … | [Monotonicity.lean](https://github.com/pauljiang03/HardwarePrimitives/blob/main/amd/MatrixCore/MC/Monotonicity.lean), [ProductMonotonicity.lean](https://github.com/pauljiang03/HardwarePrimitives/blob/main/amd/MatrixCore/MC/ProductMonotonicity.lean) |
| Inner products and `D = AB + C` | `dotBits_exact_error`, `mfma_error` | [InnerProduct.lean](https://github.com/pauljiang03/HardwarePrimitives/blob/main/amd/MatrixCore/MC/InnerProduct.lean), [MFMA.lean](https://github.com/pauljiang03/HardwarePrimitives/blob/main/amd/MatrixCore/MC/MFMA.lean) |
| Contracts | `BlockContract`, `cdna1F16_contract`, …, `dotBits_blocks` | [Contract.lean](https://github.com/pauljiang03/HardwarePrimitives/blob/main/amd/MatrixCore/MC/Contract.lean) |
| Fixed-width accumulation | `alignedBits`, `machineAccumulate`, `evalBlockMachine` | [Accumulator.lean](https://github.com/pauljiang03/HardwarePrimitives/blob/main/amd/MatrixCore/MC/Accumulator.lean), [MachineRefinement.lean](https://github.com/pauljiang03/HardwarePrimitives/blob/main/amd/MatrixCore/MC/MachineRefinement.lean) |
| Independent specification | `Spec.Result`, `Spec.blockBits_eq_spec`, `Spec.pairwise_eq_spec` | [Defs.lean](https://github.com/pauljiang03/HardwarePrimitives/blob/main/amd/MatrixCore/Specification/Defs.lean), [Equivalence.lean](https://github.com/pauljiang03/HardwarePrimitives/blob/main/amd/MatrixCore/Specification/Equivalence.lean) |
