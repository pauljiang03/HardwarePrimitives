---
title: Quick start
description: Build the Lean project and run the worked examples.
---

Install [elan](https://github.com/leanprover/elan), Python 3, and Git. The
repository pins its Lean version in
[`lean-toolchain`](https://github.com/pauljiang03/TC-EFT/blob/main/lean-toolchain).
The checks need no GPU, CUDA, or MATLAB.

```sh
git clone https://github.com/pauljiang03/TC-EFT.git
cd TC-EFT
lake build                                  # library, regression library, native adapters
lake env lean examples/GettingStarted.lean
lake env lean examples/NonMonotonicity.lean
```

`lake build TensorCore` builds only the production library.

## What the examples print

The examples print encoded words. `Except.ok` means success, and `some` means
an optional result is present. Decoded, the values are:

| Calculation | FP32 value |
| --- | --- |
| Four FP16 products `1 × 1`, `C = 0` (V100) | `4.0` |
| Four products `2^-12 × 2^-12`, `C = 1` (V100 model) | `1.0` |
| TC-EFT correction of that result | `1 + 2^-22` |
| Same block with `C = 1 − 2^-24` (model) | `1 + 2^-23` (larger, although `C` is smaller) |

Each `#eval` in these files is paired with a `decide +kernel` assertion of the
exact bits, so the files check their own answers.

## Full validation

```sh
python3 scripts/check_clean_build.py
```

This builds a fresh snapshot with no cache and audits the axioms of every
theorem. It also checks every example and documentation code block, and
compares the executables with independent exact-arithmetic oracles and the
recorded hardware vectors. It writes `data/regressions/clean-build.json`.

The FloatLib implementation is a separate Lake project:

```sh
cd floatlib-port
python3 scripts/check_all.py
python3 scripts/check_equivalence.py
```

## Using the library

| Import | Contents |
| --- | --- |
| `TensorCore.Numerics` | Formats, encodings, exact arithmetic, rounding |
| `TensorCore.TC` | Tensor Core models, block model, specification, error and non-monotonicity theory |
| `TensorCore.EFT` | Reference EFT, scalar preconditions, Algorithm 1 of the TC-EFT paper |
| `TensorCore.Kernels.EFT` | Bounded 576-bit EFT and its refinement proofs |
| `TensorCore` | All of the above |
