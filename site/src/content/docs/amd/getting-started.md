---
title: 1. Getting started
description: Build Matrix-Core, evaluate an MFMA block from encoded words, read its result and errors, and chain blocks into inner products.
---

## Build

Install [elan](https://github.com/leanprover/elan); the project pins its Lean
version in `lean-toolchain`. From the `amd/` directory:

```sh
lake build
lake env lean examples/GettingStarted.lean
python3 scripts/check.py
```

`lake build` builds the library (`MatrixCore`) and the regression library
(`MatrixCoreTests`): every test vector of the paper is checked by kernel
evaluation during the build, and an audit checks the axioms.
`scripts/check.py` does a clean build and then checks the examples and every
Lean code block in the documentation.

## Evaluate a block

A block has the vectors `a`, `b` (`N_FMA` words each, in the model's input
formats) and the binary32 word `c`. [`MatrixCore.blockBits`](https://github.com/pauljiang03/MMAlgebra/blob/main/amd/MatrixCore/MC/Eval.lean#L64) returns the
binary32 word `d` or a `ModelError`:

```lean
import MatrixCore

open MatrixCore

-- CDNA 3 fp16: c = 1 (0x3F800000), p₁ = 2^-12 · 2^-12 = 2^-24 (0x0C00), other products zero.
def x : BlockInput cdna3F16 :=
  ⟨0x0C00 :: List.replicate 7 0, 0x0C00 :: List.replicate 7 0, 0x3F800000⟩

-- S_acc = 1 + 2^-24 is exactly halfway between 1 and 1 + 2^-23; RNE gives 1.
example : blockBits x = .ok 0x3F800000 := by decide +kernel

-- The decoded value and the intermediate S_acc.
#eval (evalBlock x).map fun t => (t.sAcc, value32 t.d)
```

[`MatrixCore.evalBlock`](https://github.com/pauljiang03/MMAlgebra/blob/main/amd/MatrixCore/MC/Eval.lean#L50) returns a trace with the decoded inputs, `S_acc` and
`d`. The errors:

| `ModelError` | Meaning | Observed by the hardware as |
| --- | --- | --- |
| `wrongLength` | `a` or `b` does not have `N_FMA` words | not an input |
| `nonfiniteInput` | an operand is an infinity or NaN | infinity or NaN |
| `productOverflow` | CDNA 3: some `\|p_ℓ\| ≥ 2^128` | infinity or NaN |
| `intermediateOverflow` | CDNA 2: an intermediate `fl{·}` overflowed | infinity or NaN |
| `outputOverflow` | `fl{S_acc}` overflowed | infinity of the sign of `S_acc` |

[`MatrixCore.blockOutcome`](https://github.com/pauljiang03/MMAlgebra/blob/main/amd/MatrixCore/MC/Special.lean#L134) gives the observation for every input word: a
finite word, an infinity of either sign, or NaN.

## Longer inner products and `D = AB + C`

An instruction with inner dimension `k` evaluates each element in
`⌈k / N_FMA⌉` blocks, padding with zeros, each block's `d` becoming the next
block's `c` ([`MatrixCore.dotBits`](https://github.com/pauljiang03/MMAlgebra/blob/main/amd/MatrixCore/MC/Composition.lean#L29)):

```lean
import MatrixCore

open MatrixCore

-- SFMA on binary32 inputs: c = 1, p₁ = 2^-24, p₂ = 2^-23 (each as p · 1).
-- (c + p₁) ties to 1; adding 2^-23 then gives 1 + 2^-23.
example : dotBits sfmaF32 [0x33800000, 0x34000000] [0x3F800000, 0x3F800000] 0x3F800000 =
    .ok 0x3F800001 := by decide +kernel
```

[`MatrixCore.dotOutcome`](https://github.com/pauljiang03/MMAlgebra/blob/main/amd/MatrixCore/MC/Composition.lean#L43) is the observation for any words, and
[`MatrixCore.mfma`](https://github.com/pauljiang03/MMAlgebra/blob/main/amd/MatrixCore/MC/Composition.lean#L52) applies it to every element of `D = AB + C`.

## Input words by value

`Format.encodeExact` and `InputFormat.encodeExact` return the word of a value
the format represents exactly, and `none` otherwise. The tests build every
input this way, so an input a format cannot represent fails the test instead
of being rounded silently.

## Finding the source

| Topic | Declarations | File |
| --- | --- | --- |
| Formats and decoding | `Format`, `binary16`, `bfloat16`, `e4m3fnuz`, `e5m2fnuz`, `InputFormat.read` | [Numerics/Format.lean](https://github.com/pauljiang03/MMAlgebra/blob/main/amd/MatrixCore/Numerics/Format.lean) |
| Truncation and round-down | `truncGrid`, `truncFrac`, `rdGrid`, `rdFrac` | [Numerics/Grid.lean](https://github.com/pauljiang03/MMAlgebra/blob/main/amd/MatrixCore/Numerics/Grid.lean) |
| `fl{·}` | `rne32`, `fl32`, `normExp` | [Numerics/Round32.lean](https://github.com/pauljiang03/MMAlgebra/blob/main/amd/MatrixCore/Numerics/Round32.lean) |
| Models | `Model`, `Accumulation`, `cdna1F16`, … | [MC/Defs.lean](https://github.com/pauljiang03/MMAlgebra/blob/main/amd/MatrixCore/MC/Defs.lean), [MC/Models.lean](https://github.com/pauljiang03/MMAlgebra/blob/main/amd/MatrixCore/MC/Models.lean) |
| Stages | `pairwiseSum`, `productSum`, `lateSum`, `shiftedSum` | [MC/Stages.lean](https://github.com/pauljiang03/MMAlgebra/blob/main/amd/MatrixCore/MC/Stages.lean) |
| Evaluation | `evalBlock`, `blockBits`, `accumulate` | [MC/Eval.lean](https://github.com/pauljiang03/MMAlgebra/blob/main/amd/MatrixCore/MC/Eval.lean) |
| Special values | `blockOutcome`, `Outcome` | [MC/Special.lean](https://github.com/pauljiang03/MMAlgebra/blob/main/amd/MatrixCore/MC/Special.lean) |
| Chaining | `dotBits`, `dotOutcome`, `mfma` | [MC/Composition.lean](https://github.com/pauljiang03/MMAlgebra/blob/main/amd/MatrixCore/MC/Composition.lean) |
| Runs of blocks | `runBlocks`, `Chain`, `runBlocks_all` | [MC/Chain.lean](https://github.com/pauljiang03/MMAlgebra/blob/main/amd/MatrixCore/MC/Chain.lean) |
| Output error | `correctRounding_error`, `pairwise_error`, `aligned_error`, `dotBits_error_bound` | [MC/ErrorBounds.lean](https://github.com/pauljiang03/MMAlgebra/blob/main/amd/MatrixCore/MC/ErrorBounds.lean) |
| Bounds from the inputs | `correctRounding_apriori`, `pairwise_apriori`, `aligned_apriori` | [MC/AprioriBounds.lean](https://github.com/pauljiang03/MMAlgebra/blob/main/amd/MatrixCore/MC/AprioriBounds.lean) |
| Monotonicity | `evalBlock_c_monotone`, `dotBits_c_monotone`, `cdna3F16_nonmonotonic`, … | [MC/Monotonicity.lean](https://github.com/pauljiang03/MMAlgebra/blob/main/amd/MatrixCore/MC/Monotonicity.lean), [MC/ProductMonotonicity.lean](https://github.com/pauljiang03/MMAlgebra/blob/main/amd/MatrixCore/MC/ProductMonotonicity.lean) |
| Inner products and `D = AB + C` | `dotBits_exact_error`, `mfma_error` | [MC/InnerProduct.lean](https://github.com/pauljiang03/MMAlgebra/blob/main/amd/MatrixCore/MC/InnerProduct.lean), [MC/MFMA.lean](https://github.com/pauljiang03/MMAlgebra/blob/main/amd/MatrixCore/MC/MFMA.lean) |
| Contracts | `BlockContract`, `cdna1F16_contract`, …, `dotBits_blocks` | [MC/Contract.lean](https://github.com/pauljiang03/MMAlgebra/blob/main/amd/MatrixCore/MC/Contract.lean) |
| Fixed-width accumulation | `alignedBits`, `machineAccumulate`, `evalBlockMachine` | [MC/Accumulator.lean](https://github.com/pauljiang03/MMAlgebra/blob/main/amd/MatrixCore/MC/Accumulator.lean) |
