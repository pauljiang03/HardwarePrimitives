# Getting started

## Build

```sh
lake build
```

This builds the library (`MatrixCore`) and the regression library (`MatrixCoreTests`): every
test vector of the paper is checked by kernel evaluation during the build.

## Evaluate a block

A block has the vectors `a`, `b` (`N_FMA` words each, in the model's input formats) and the
binary32 word `c`. `blockBits` returns the binary32 word `d` or a `ModelError`:

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

`evalBlock` returns a `BlockTrace` with the decoded inputs, `S_acc`, and `d`. Errors:

| `ModelError` | Meaning | Observed by the hardware as |
| --- | --- | --- |
| `wrongLength` | `a` or `b` does not have `N_FMA` words | not an input |
| `nonfiniteInput` | an operand is an infinity or NaN | infinity or NaN |
| `productOverflow` | CDNA 3: some `|p_ℓ| ≥ 2^128` | infinity or NaN |
| `intermediateOverflow` | CDNA 2: an intermediate `fl{·}` overflowed | infinity or NaN |
| `outputOverflow` | `fl{S_acc}` overflowed | infinity of the sign of `S_acc` |

`blockOutcome` gives the observation for every input word, as `Outcome.finite d`,
`Outcome.infinity negative` or `Outcome.nan`.

## Longer inner products and MFMA

An instruction with inner dimension `k` evaluates each element in `⌈k / N_FMA⌉` blocks, completing
the last block with zero products, each block's `d` becoming the next block's `c`:

```lean
import MatrixCore

open MatrixCore

-- SFMA on binary32 inputs: c = 1, p₁ = 2^-24, p₂ = 2^-23 (each as p · 1).
-- (c + p₁) ties to 1; adding 2^-23 then gives 1 + 2^-23.
example : dotBits sfmaF32 [0x33800000, 0x34000000] [0x3F800000, 0x3F800000] 0x3F800000 =
    .ok 0x3F800001 := by decide +kernel
```

`dotOutcome` is the observation for any words, and `mfma` applies it to every element of
`D = AB + C`.

## Input words by value

`Format.encodeExact` and `InputFormat.encodeExact` return the word of a value the format
represents exactly, and `none` otherwise. The tests build every input this way
([Support.lean](../../tests/MatrixCoreTests/Support.lean)).

## Finding the source

| Topic | Declarations | File |
| --- | --- | --- |
| Formats and decoding | `Format`, `binary16`, `bfloat16`, `e4m3fnuz`, `e5m2fnuz`, `InputFormat.read` | [Numerics/Format.lean](../../MatrixCore/Numerics/Format.lean) |
| Truncation and RD | `truncGrid`, `truncMantissa`, `rdGrid`, `rdMantissa` | [Numerics/Grid.lean](../../MatrixCore/Numerics/Grid.lean) |
| `fl{·}` | `rne32`, `fl32`, `normExp` | [Numerics/Round32.lean](../../MatrixCore/Numerics/Round32.lean) |
| Models | `Model`, `Accumulation`, `cdna1F16`, …, `Architecture.model` | [MC/Defs.lean](../../MatrixCore/MC/Defs.lean), [MC/Models.lean](../../MatrixCore/MC/Models.lean) |
| Stages | `pairwiseSum`, `productSum`, `lateSum`, `shiftedSum` | [MC/Stages.lean](../../MatrixCore/MC/Stages.lean) |
| Evaluation | `evalBlock`, `blockBits`, `accumulate` | [MC/Eval.lean](../../MatrixCore/MC/Eval.lean) |
| Special values | `blockOutcome`, `Outcome`, `XVal` | [MC/Special.lean](../../MatrixCore/MC/Special.lean) |
| Chaining | `dotBits`, `dotOutcome`, `mfma` | [MC/Composition.lean](../../MatrixCore/MC/Composition.lean) |
| Facts about decoded blocks | `prepare_lengths`, `prepare_bounded`, `products_bounded`, `maxExp_le`, `sumQ_odd_even` | [MC/Prepared.lean](../../MatrixCore/MC/Prepared.lean) |
| Runs of blocks | `runBlocks`, `Chain`, `lastOutput`, `runBlocks_all`, `dotBits_residual_ledger` | [MC/Chain.lean](../../MatrixCore/MC/Chain.lean) |
| Output error | `halfUlp32`, `flBound`, `correctRounding_error`, `pairwise_error`, `aligned_error`, `dotBits_error_bound` | [MC/ErrorBounds.lean](../../MatrixCore/MC/ErrorBounds.lean) |
| Bounds from the inputs | `Prepared.absSum`, `correctRounding_apriori`, `pairwise_apriori`, `aligned_apriori` | [MC/AprioriBounds.lean](../../MatrixCore/MC/AprioriBounds.lean) |
| Monotonicity in `c` | `evalBlock_c_monotone`, `dotBits_c_monotone`, `paper_models_monotone` | [MC/Monotonicity.lean](../../MatrixCore/MC/Monotonicity.lean) |
| Monotonicity in the products | `correctRounding_exact_monotone`, `ProductNonmonotone`, `cdna3F16_nonmonotonic`, … | [MC/ProductMonotonicity.lean](../../MatrixCore/MC/ProductMonotonicity.lean) |
| Exact inner products | `exactDot`, `runBlocks_products`, `dotBits_exact_error` | [MC/InnerProduct.lean](../../MatrixCore/MC/InnerProduct.lean) |
| `D = AB + C` | `mfma_entry`, `mfma_finite`, `mfma_error` | [MC/MFMA.lean](../../MatrixCore/MC/MFMA.lean) |
| Per-model contracts | `BlockContract`, `CorrectRoundingContract`, `PairwiseContract`, `AlignedContract`, `cdna1F16_contract`, …, `dotBits_blocks` | [MC/Contract.lean](../../MatrixCore/MC/Contract.lean) |
| Fixed-width accumulation | `alignedBits`, `machineAccumulate`, `evalBlockMachine` | [MC/Accumulator.lean](../../MatrixCore/MC/Accumulator.lean) |
| Integer sums and list lemmas | `sumZ`, `magnitudeSum`, `truncBits`, `rdBits`; `mapM_length_option`, `mem_zipWith'`, `sumQ_perm` | [Numerics/Sum.lean](../../MatrixCore/Numerics/Sum.lean), [Numerics/Lists.lean](../../MatrixCore/Numerics/Lists.lean) |
