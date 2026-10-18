---
title: Quick start
description: Build the Lean project and run the worked examples.
---

Install [elan](https://github.com/leanprover/elan), Python 3, and Git. Each
hardware primitive has its own folder and Lake project, `tensor-core/` and
`matrix-core/`, and each pins its Lean version in its own
[`lean-toolchain`](https://github.com/pauljiang03/HardwarePrimitives/blob/main/tensor-core/lean-toolchain).
The checks need no GPU, CUDA, or MATLAB.

```sh
git clone https://github.com/pauljiang03/HardwarePrimitives.git
cd HardwarePrimitives/tensor-core
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

From `tensor-core/`:

```sh
python3 scripts/check_clean_build.py
```

This builds a fresh snapshot with no cache and audits the axioms of every
theorem. It also checks every example and documentation code block, and
compares the executables with independent exact-arithmetic oracles and the
recorded hardware vectors. It writes `data/regressions/clean-build.json`.

The FloatLib implementation is a separate Lake project in
`tensor-core/floatlib-port/`:

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

## The AMD model

The AMD Matrix Core model is a standalone Lake project in `matrix-core/`, with
its own pinned toolchain. From the repository root:

```sh
cd matrix-core
lake build                                  # library, paper regressions, audit
lake env lean examples/GettingStarted.lean
python3 scripts/check.py                    # clean build, examples, documentation blocks
```

`lake build` builds the library (`MatrixCore`) and the regression library
(`MatrixCoreTests`): every test vector of the paper is checked by kernel
evaluation during the build, and an audit checks the axioms.

A block has the vectors `a`, `b` (`N_FMA` words each, in the model's input
formats) and the FP32 word `c`. `blockBits` returns the FP32 word `d`
or a `ModelError`, and `evalBlock` a trace with the decoded inputs, `S_acc`
and `d`:

```lean
import MatrixCore

open MatrixCore

-- CDNA 3 FP16: c = 1 (0x3F800000), p₁ = 2^-12 · 2^-12 = 2^-24 (0x0C00), other products zero.
def x : BlockInput cdna3F16 :=
  ⟨0x0C00 :: List.replicate 7 0, 0x0C00 :: List.replicate 7 0, 0x3F800000⟩

-- S_acc = 1 + 2^-24 is exactly halfway between 1 and 1 + 2^-23; RNE gives 1.
example : blockBits x = .ok 0x3F800000 := by decide +kernel

-- The decoded value and the intermediate S_acc.
#eval (evalBlock x).map fun t => (t.sAcc, value32 t.d)
```

| Import | Contents |
| --- | --- |
| `MatrixCore.Numerics` | Formats, decoding, grids, FP32 rounding and its correctness |
| `MatrixCore.MC` | Models, block evaluation, special values, chaining, error bounds, monotonicity |
| `MatrixCore.Specification` | The independent transcription of the paper and the equality proofs |
| `MatrixCore` | All of the above |

## Comparing the two

The `cross-vendor/` project imports both libraries and proves the comparisons
between them, one theorem each
([Tensor Cores and Matrix Cores compared](/HardwarePrimitives/proofs/cross-vendor/)):

```sh
cd cross-vendor
lake build                  # CrossVendor and the axiom audit
python3 scripts/check.py    # build, audit, documentation blocks
```

`TensorCore` and `MatrixCore` scope their `ℕ`, `ℤ` and `ℚ` notation to their
own namespaces, so `open TensorCore` or `open MatrixCore` brings it into scope,
and one file can import both.
