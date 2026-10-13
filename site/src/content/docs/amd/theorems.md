---
title: 5. What is proved
description: The main results about the AMD matrix-core model - the accepted domain, error bounds, monotonicity, fixed-width accumulation, inner products, contracts and binary32 rounding.
---

These are the main results Lean has checked about the model. Every theorem
depends only on Lean's standard axioms (`propext`, `Classical.choice`,
`Quot.sound`); an audit in the test library checks this for every theorem.
The full list, with every Lean name and file, is in
[`amd/MatrixCore/THEOREMS.md`](https://github.com/pauljiang03/TC-EFT/blob/main/amd/MatrixCore/THEOREMS.md).

## The model

| What it says | Lean |
| --- | --- |
| On every variant and for every input, the model returns a word exactly when an independently written transcription of the paper's algorithms specifies it. | [`MatrixCore.Spec.blockBits_eq_spec`](https://github.com/pauljiang03/TC-EFT/blob/main/amd/MatrixCore/Specification/Equivalence.lean#L129), [`MatrixCore.Spec.pairwise_eq_spec`](https://github.com/pauljiang03/TC-EFT/blob/main/amd/MatrixCore/Specification/Pairwise.lean#L161) |
| A block is accepted exactly when `a` and `b` have `N_FMA` entries, every operand is finite, accumulation succeeds, and `S_acc` is below the overflow threshold. | [`MatrixCore.evalBlock_success_iff`](https://github.com/pauljiang03/TC-EFT/blob/main/amd/MatrixCore/MC/AcceptedDomain.lean#L41) |
| On every model with subnormals, the output is `fl{S_acc}`: the nearest binary32 value, ties to even. | [`MatrixCore.evalBlock_nearestEven`](https://github.com/pauljiang03/TC-EFT/blob/main/amd/MatrixCore/MC/AcceptedDomain.lean#L60) |
| The observation for any input words reports a finite word exactly when the model accepts, with the same word; otherwise an infinity or NaN. | [`MatrixCore.blockOutcome_finite_iff`](https://github.com/pauljiang03/TC-EFT/blob/main/amd/MatrixCore/MC/SpecialAgreement.lean#L169) |

## Output error

The bounds compare `d` with the exact `Σ a_ℓ b_ℓ + c` of the decoded inputs.

| What it says | Lean |
| --- | --- |
| SFMA and CDNA 1: `\|exact − d\|` is at most half a binary32 ulp of the exact sum. | [`MatrixCore.correctRounding_error`](https://github.com/pauljiang03/TC-EFT/blob/main/amd/MatrixCore/MC/ErrorBounds.lean#L85) |
| CDNA 2: at most the effect of flushing subnormal inputs plus one rounding bound for each product conversion, each pairwise sum and the final `fl{·}`. | [`MatrixCore.pairwise_error`](https://github.com/pauljiang03/TC-EFT/blob/main/amd/MatrixCore/MC/ErrorBounds.lean#L229) |
| CDNA 3: at most the error of `S_acc` in its branch of Algorithm 1 or 2 plus half an ulp of `S_acc`. | [`MatrixCore.aligned_error`](https://github.com/pauljiang03/TC-EFT/blob/main/amd/MatrixCore/MC/ErrorBounds.lean#L302) |
| From the inputs alone, with `A = Σ\|p_ℓ\| + \|c\|`: `2^-24 A + 2^-150` on SFMA and CDNA 1; `2^-23 A + (n + 4)·2^(e_max − 24) + 2^-149` on CDNA 3, where denormalized products make `2^(e_max)` exceed every `\|p_ℓ\|`. | [`MatrixCore.correctRounding_apriori`](https://github.com/pauljiang03/TC-EFT/blob/main/amd/MatrixCore/MC/AprioriBounds.lean#L76), [`MatrixCore.aligned_apriori`](https://github.com/pauljiang03/TC-EFT/blob/main/amd/MatrixCore/MC/AprioriBounds.lean#L238), [`MatrixCore.pairwise_apriori`](https://github.com/pauljiang03/TC-EFT/blob/main/amd/MatrixCore/MC/AprioriBounds.lean#L473) |
| An inner product is within the sum of its blocks' bounds of `c` plus all products. | [`MatrixCore.dotBits_error_bound`](https://github.com/pauljiang03/TC-EFT/blob/main/amd/MatrixCore/MC/Contract.lean#L225) |

## Monotonicity

| What it says | Lean |
| --- | --- |
| For the same `a` and `b`, a larger `c` never gives a smaller `d`, on every configuration; the same for inner products of any length. On NVIDIA Tensor Cores `c` takes part in alignment and can trigger non-monotonicity; on AMD it never sets the products' alignment. | [`MatrixCore.evalBlock_c_monotone`](https://github.com/pauljiang03/TC-EFT/blob/main/amd/MatrixCore/MC/Monotonicity.lean#L633), [`MatrixCore.dotBits_c_monotone`](https://github.com/pauljiang03/TC-EFT/blob/main/amd/MatrixCore/MC/Monotonicity.lean#L657) |
| SFMA and CDNA 1 depend only on the exact sum, monotonically, so they are monotone in every product. | [`MatrixCore.correctRounding_exact_monotone`](https://github.com/pauljiang03/TC-EFT/blob/main/amd/MatrixCore/MC/ProductMonotonicity.lean#L58) |
| CDNA 2 is not monotone in the products: a product with a subnormal operand is flushed, a slightly larger one with normal operands is not. | [`MatrixCore.cdna2F16_nonmonotonic`](https://github.com/pauljiang03/TC-EFT/blob/main/amd/MatrixCore/MC/ProductMonotonicity.lean#L146) |
| CDNA 3 is not monotone in the products, on every input format: raising a product with a subnormal operand can raise `e_max` and truncate the others by more than it gains. | [`MatrixCore.cdna3F16_nonmonotonic`](https://github.com/pauljiang03/TC-EFT/blob/main/amd/MatrixCore/MC/ProductMonotonicity.lean#L164), [`MatrixCore.cdna3E4M3_nonmonotonic`](https://github.com/pauljiang03/TC-EFT/blob/main/amd/MatrixCore/MC/ProductMonotonicity.lean#L187) |
| CDNA 3 with normal operands: equal products `1.5 · 1.5` and `2.25 · 1` give different outputs. | [`MatrixCore.cdna3F16_products_not_determined`](https://github.com/pauljiang03/TC-EFT/blob/main/amd/MatrixCore/MC/ProductMonotonicity.lean#L202) |

## Fixed-width accumulation (CDNA 3)

Each aligned product is an integer number of grid steps; `evalBlockMachine w`
adds them in `w`-bit wrapping registers.

| What it says | Lean |
| --- | --- |
| The fixed-width accumulator gives the model's output for every input at 30 bits (fp16, bf16), 29 (XF32) and 31 (binary8). | [`MatrixCore.evalBlockMachine_eq`](https://github.com/pauljiang03/TC-EFT/blob/main/amd/MatrixCore/MC/MachineRefinement.lean#L176) |
| Every partial sum in that accumulator is exact, in any order. | [`MatrixCore.machinePrefix_exact`](https://github.com/pauljiang03/TC-EFT/blob/main/amd/MatrixCore/MC/MachineRefinement.lean#L199) |

The tests show these widths are needed: eight fp16 products just below 4 wrap
in a 29-bit register.

## Inner products, `D = AB + C` and contracts

| What it says | Lean |
| --- | --- |
| The exact `c + Σ_ℓ a_ℓ b_ℓ` of the whole vectors equals the output plus the blocks' residuals, and is within the sum of their error bounds of the output. | [`MatrixCore.dotBits_exact_error`](https://github.com/pauljiang03/TC-EFT/blob/main/amd/MatrixCore/MC/InnerProduct.lean#L184) |
| Each entry of `D = AB + C` is the observed inner product of its row and column, and a finite entry is within the sum of its blocks' bounds of the exact `c_ij + Σ_ℓ a_iℓ b_ℓj`. | [`MatrixCore.mfma_error`](https://github.com/pauljiang03/TC-EFT/blob/main/amd/MatrixCore/MC/MFMA.lean#L50) |
| Every accepted block satisfies a contract bundling what is proved about it, with its output error bound; any such property carries to every block of an inner product. | [`MatrixCore.evalBlock_contract`](https://github.com/pauljiang03/TC-EFT/blob/main/amd/MatrixCore/MC/Contract.lean#L52), [`MatrixCore.cdna1F16_contract`](https://github.com/pauljiang03/TC-EFT/blob/main/amd/MatrixCore/MC/Contract.lean#L161), [`MatrixCore.dotBits_blocks`](https://github.com/pauljiang03/TC-EFT/blob/main/amd/MatrixCore/MC/Contract.lean#L203) |

## binary32 rounding

| What it says | Lean |
| --- | --- |
| `fl{x}` is the nearest value among all finite binary32 words, ties to an even last bit, and is finite exactly when `\|x\| < 2^128 − 2^103`. | [`MatrixCore.rne32_nearestEven`](https://github.com/pauljiang03/TC-EFT/blob/main/amd/MatrixCore/Numerics/RoundingContract.lean#L322), [`MatrixCore.rne32_isSome_iff`](https://github.com/pauljiang03/TC-EFT/blob/main/amd/MatrixCore/Numerics/RoundingContract.lean#L400) |
| Within that range, the correctly rounded word with the sign of `x` is unique. | [`MatrixCore.rne32_iff`](https://github.com/pauljiang03/TC-EFT/blob/main/amd/MatrixCore/Numerics/Uniqueness.lean#L370) |

## Not proved

- That AMD GPUs behave like the model. The paper's hardware observations are
  replayed as tests, and the model is compared with the authors' MATLAB models
  ([validation](/TC-EFT/amd/validation/)).
- The special-value layer for non-finite inputs is a definition (detection at
  the input, as the paper describes it), checked against the paper's vectors
  and the MATLAB models, not derived.
