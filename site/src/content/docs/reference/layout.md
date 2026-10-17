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
