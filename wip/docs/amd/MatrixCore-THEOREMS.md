# What is proven

The main results Lean has checked, in plain language. The linked file has the exact statement
and every assumption. All results depend only on Lean's standard axioms (`propext`,
`Classical.choice`, `Quot.sound`); `tests/MatrixCoreTests/Audit.lean` checks this for every
theorem. *The paper* is Khattak, Mikaitis and Graziani, *Accurate Models of AMD Matrix Cores*
(arXiv 2609.14845).

## The matrix-core model

| What it says | Lean name | File |
| --- | --- | --- |
| On every variant in the paper (SFMA, CDNA 1 fp16/bf16, CDNA 3 fp16/bf16/XF32/fp8) and for every input, the model returns a word exactly when an independently written transcription of the paper's algorithms specifies that word. | `Spec.blockBits_eq_spec`, `Spec.supported_*` | [Specification/Equivalence.lean](Specification/Equivalence.lean) |
| The same for CDNA 2 (fp16, bf16, bf16 `_1k`) against a transcription of Fig. 2 with `fl{·}` stated as RNE with flush to zero. | `Spec.pairwise_eq_spec`, `Spec.supported_cdna2*` | [Specification/Pairwise.lean](Specification/Pairwise.lean) |
| A block is accepted exactly when `a` and `b` have `N_FMA` entries, every operand is finite, accumulation succeeds, and `S_acc` is below the overflow threshold. | `evalBlock_success_iff` | [MC/AcceptedDomain.lean](MC/AcceptedDomain.lean) |
| On every model that supports subnormals, the output is `fl{S_acc}`: the nearest binary32 value, ties to even. | `evalBlock_nearestEven` | [MC/AcceptedDomain.lean](MC/AcceptedDomain.lean) |
| The observation for any input words reports a finite word exactly when the model accepts, with the same word; otherwise an infinity or NaN. | `blockOutcome_finite_iff` | [MC/SpecialAgreement.lean](MC/SpecialAgreement.lean) |
| The specification's CDNA 2 `fl{·}` (value and output word) is the model's. | `Spec.fl_iff`, `Spec.flWord_iff` | [Specification/Pairwise.lean](Specification/Pairwise.lean) |

## CDNA 1 and the SFMA (`correct_rounding`)

| What it says | Lean name | File |
| --- | --- | --- |
| The output is the binary32 value nearest to the exact `Σ a_ℓ b_ℓ + c`, ties to even. | `correctRounding_nearestEven`, `cdna1F16_nearestEven`, `cdna1BF16_nearestEven`, `sfmaF32_nearestEven` | [MC/CorrectRounding.lean](MC/CorrectRounding.lean) |
| It succeeds exactly when the inputs are finite and the exact sum is below `2^128 − 2^103`; products may exceed `2^128`. | `correctRounding_success_iff` | [MC/CorrectRounding.lean](MC/CorrectRounding.lean) |
| Negating the exact sum negates the output value. | `correctRounding_neg` | [MC/CorrectRounding.lean](MC/CorrectRounding.lean) |
| binary32 inputs form an SFMA: one correctly rounded fused step per product, `c` first. | `dotBits_sfma_cons`, `sfma_step_nearestEven` | [MC/CompositionProperties.lean](MC/CompositionProperties.lean) |

## CDNA 2 (`pair_wise_sum`)

| What it says | Lean name | File |
| --- | --- | --- |
| A group of four is `c + fl{fl{p₁ + p₂} + fl{p₃ + p₄}}` with each `p_ℓ = fl{a_ℓ b_ℓ}`, and a group of two is `c + fl{p₁ + p₂}`; the block output rounds that with `fl{·}`. | `pairwiseSum_four`, `pairwiseSum_two` | [MC/PairWiseSum.lean](MC/PairWiseSum.lean) |
| `fl{·}` with flush to zero returns the RNE value when it is zero or normal, and zero when the RNE value is subnormal. | `flValue_true`, `flValue_false` | [MC/PairWiseSum.lean](MC/PairWiseSum.lean) |

## CDNA 3 (`global_alignment`, `odd_even_grouping`)

| What it says | Lean name | File |
| --- | --- | --- |
| Error of `S_acc` against the exact sum in each branch of Algorithms 1 and 2: below `(n + 2)·2^(e_max − 24) + 2^(e_max − 24)` when `e_c ≤ e_max`; when `e_c > e_max`, `S_acc` rounds down by less than `2^(e_c − 32) + 2^(e′ − 31)` beyond the product error. | `alignedAccumulation_error` | [MC/LateAccumulation.lean](MC/LateAccumulation.lean) |
| Each stage: product alignment, `s′_c`, and the RD steps of the shifted branch. | `productSum_error`, `shiftedC_error`, `shiftedSum_bounds` | [MC/LateAccumulation.lean](MC/LateAccumulation.lean) |

## Fixed-width accumulation (CDNA 3)

Each aligned product is an integer number of grid steps (`alignedBits`); `evalBlockMachine w`
adds them in `w`-bit wrapping registers (`machineAccumulate`).

| What it says | Lean name | File |
| --- | --- | --- |
| A fixed-width wrapping accumulator gives the same output for every input when it is wide enough: `23 + padding + 2` bits per product, carry bits for `N_FMA`, and a sign bit (30/30/29/31 bits for CDNA 3 fp16/bf16/XF32/binary8). | `evalBlockMachine_eq`, `cdna3F16_machine_eq`, `cdna3BF16_machine_eq`, `cdna3XF32_machine_eq`, `cdna3FP8_machine_eq` | [MC/MachineRefinement.lean](MC/MachineRefinement.lean) |
| Every partial sum in that accumulator is exact, in any order. | `machinePrefix_exact` | [MC/MachineRefinement.lean](MC/MachineRefinement.lean) |
| Odd/even grouping's RD of a group sum to the common `e_max` is an arithmetic right shift of its register. | `shiftRegister_spec` | [MC/MachineRefinement.lean](MC/MachineRefinement.lean) |

## Output error

`halfUlp32 x` is half a binary32 ulp of `x`; `flBound ftz x` adds `2^-126` where subnormal results
are flushed. The bounds use the exact `Σ a_ℓ b_ℓ + c` of the decoded inputs.

| What it says | Lean name | File |
| --- | --- | --- |
| `fl{x}` is within half an ulp of `x`, which is at most `2^-24 |x| + 2^-150`; with flushing, within `flBound true x`. | `rneValue_error`, `halfUlp32_le`, `flValue_error` | [Numerics/RoundingError.lean](Numerics/RoundingError.lean), [MC/ErrorBounds.lean](MC/ErrorBounds.lean) |
| SFMA and CDNA 1: `|exact − d| ≤ halfUlp32 exact`. | `correctRounding_error` | [MC/ErrorBounds.lean](MC/ErrorBounds.lean) |
| CDNA 2: `|exact − d|` is at most the effect of flushing subnormal inputs, plus one `flBound` for each product conversion, each pairwise sum, and the final `fl{·}`, at the computed values. | `pairwise_error`, `pairwiseBound`, `pairwiseGroupSum_error` | [MC/ErrorBounds.lean](MC/ErrorBounds.lean) |
| CDNA 3: `|exact − d|` is at most the error of `S_acc` in its branch of Algorithm 1 or 2, plus half an ulp of `S_acc`. | `aligned_error`, `alignedBound`, `alignedAccumulation_abs_error` | [MC/ErrorBounds.lean](MC/ErrorBounds.lean) |
| An inner product is within the sum of its blocks' bounds of `c` plus all products. | `dotBits_error_bound`, `correctRounding_dot_error` | [MC/Contract.lean](MC/Contract.lean) |

## Bounds from the inputs alone

`A = Σ|p_ℓ| + |c|` of the decoded inputs (`Prepared.absSum`); `e_max` is the largest product
exponent `e_a + e_b`.

| What it says | Lean name | File |
| --- | --- | --- |
| SFMA and CDNA 1: `|exact − d| ≤ 2^-24 A + 2^-150`. | `correctRounding_apriori` | [MC/AprioriBounds.lean](MC/AprioriBounds.lean) |
| CDNA 3: `|exact − d| ≤ 2^-23 A + (n + 4)·2^(e_max − 24) + 2^-149`. Products are kept in denormalized form, so `2^(e_max)` can exceed every `|p_ℓ|` and the alignment term is measured against it. | `aligned_apriori`, `alignedAccumulation_apriori` | [MC/AprioriBounds.lean](MC/AprioriBounds.lean) |
| CDNA 2 (`N_FMA ≤ 4`): `|exact − d| ≤ |exact − exact'| + 2^-21 A' + 2^-120`, with `exact'`, `A'` those of the flushed inputs. | `pairwise_apriori` | [MC/AprioriBounds.lean](MC/AprioriBounds.lean) |
| A balanced pairwise sum of depth `h` is within `((1 + 2^-24)^h − 1) Σ|x| + κ_h η` of the exact sum of its terms. | `pairwiseGroupSum_apriori` | [MC/AprioriBounds.lean](MC/AprioriBounds.lean) |

## Monotonicity in `c`

On NVIDIA Tensor Cores any term holding the alignment exponent, a product or `c`, can trigger non-monotonicity (the TC-EFT paper's construction perturbs `c`). On AMD `c` never sets the products' alignment, so the output is monotone in `c`; the non-monotonicity is in the products (next section).

| What it says | Lean name | File |
| --- | --- | --- |
| For the same `a` and `b`, a larger `c` never gives a smaller `d`, on every configuration of the paper. | `evalBlock_c_monotone`, `paper_models_monotone` | [MC/Monotonicity.lean](MC/Monotonicity.lean) |
| The same for inner products of any length. | `dotBits_c_monotone` | [MC/Monotonicity.lean](MC/Monotonicity.lean) |
| CDNA 3's late addition is monotone in `c` within each branch and across the switch at `e_c = e_max`. | `lateSum_mono` | [MC/Monotonicity.lean](MC/Monotonicity.lean) |
| RNE, flushing, and normalization followed by RD are monotone. | `rneValue_mono`, `flushValue_mono`, `normalizeRD_mono` | [Numerics/RoundingError.lean](Numerics/RoundingError.lean), [MC/Monotonicity.lean](MC/Monotonicity.lean) |

## Monotonicity in the products

| What it says | Lean name | File |
| --- | --- | --- |
| SFMA and CDNA 1: the output depends only on the exact `Σ a_ℓ b_ℓ + c`, monotonically, so it is monotone in every product and in `c`; the same for inner products of any length. | `correctRounding_exact_monotone`, `correctRounding_product_monotone`, `runBlocks_correctRounding_monotone`, `cdna1F16_not_nonmonotone` | [MC/ProductMonotonicity.lean](MC/ProductMonotonicity.lean) |
| CDNA 2 is not monotone in the products: a product with a subnormal operand is flushed, a slightly larger one with normal operands is not (fp16, bf16, bf16 `_1k`). | `cdna2F16_nonmonotonic`, `cdna2BF16_nonmonotonic`, `cdna2BF16_1k_nonmonotonic` | [MC/ProductMonotonicity.lean](MC/ProductMonotonicity.lean) |
| CDNA 3 is not monotone in the products: a product with a subnormal operand has a small value but a large exponent `e_a + e_b`; raising it slightly can raise `e_max` and truncate the other products (or RD `c`) by more than it gains (fp16, bf16, XF32, fp8 E4M3, E5M2). | `cdna3F16_nonmonotonic`, `cdna3BF16_nonmonotonic`, `cdna3XF32_nonmonotonic`, `cdna3E4M3_nonmonotonic`, `cdna3E5M2_nonmonotonic` | [MC/ProductMonotonicity.lean](MC/ProductMonotonicity.lean) |
| CDNA 3 with normal operands: equal products `1.5 · 1.5` and `2.25 · 1` give different outputs. | `cdna3F16_products_not_determined` | [MC/ProductMonotonicity.lean](MC/ProductMonotonicity.lean) |

## Inner products and `D = AB + C`

| What it says | Lean name | File |
| --- | --- | --- |
| The blocks of an accepted inner product have exact products `Σ_ℓ a_ℓ b_ℓ` over the whole vectors; the zero padding adds nothing. | `runBlocks_products` | [MC/InnerProduct.lean](MC/InnerProduct.lean) |
| The exact `c + Σ_ℓ a_ℓ b_ℓ` equals the output plus the blocks' residuals, and is within the sum of their error bounds of the output. | `dotBits_exact_ledger`, `dotBits_exact_error` | [MC/InnerProduct.lean](MC/InnerProduct.lean) |
| Each entry of `D = AB + C` is the observed inner product of its row and column; a finite entry is the finite-domain inner product, satisfies the contracts, and is within the sum of its blocks' bounds of the exact `c_ij + Σ_ℓ a_iℓ b_ℓj`. | `mfma_entry`, `mfma_finite`, `mfma_error`, `mfma_length` | [MC/MFMA.lean](MC/MFMA.lean) |

## Contracts and chaining

| What it says | Lean name | File |
| --- | --- | --- |
| Every accepted block on every model satisfies `BlockContract`: right shape, decoded operands with significands below 2 (products below 4), `S_acc` below the overflow threshold, `d = fl{S_acc}` finite and within `flBound` of `S_acc`, and nearest-even where subnormals are supported. | `evalBlock_contract` | [MC/Contract.lean](MC/Contract.lean) |
| Each model's bundle, with its output error bound (`error`) and its bound from the inputs alone (`apriori`): SFMA and CDNA 1 round the exact sum to nearest (`CorrectRoundingContract`); CDNA 2 evaluates the pairwise sums (`PairwiseContract`); CDNA 3 computes Algorithm 1 or 2 with its error bounds and register width (`AlignedContract`). | `sfmaF32_contract`, `cdna1F16_contract`, …, `cdna3FP8_contract` | [MC/Contract.lean](MC/Contract.lean) |
| An inner product is the last output of its run of blocks; the blocks are linked through the words they pass on. | `dotBits_eq_runBlocks`, `runBlocks_chain` | [MC/Chain.lean](MC/Chain.lean) |
| Any property of accepted blocks holds for every block of an inner product, and the initial `c` plus every block's products equal the output plus every block's residual. | `runBlocks_all`, `dotBits_blocks`, `dotBits_residual_ledger` | [MC/Chain.lean](MC/Chain.lean), [MC/Contract.lean](MC/Contract.lean) |

## Order and sign

| What it says | Lean name | File |
| --- | --- | --- |
| CDNA 1 and CDNA 3 global alignment depend on the products only as a multiset. | `accumulate_perm` | [MC/Order.lean](MC/Order.lean) |
| CDNA 2 and CDNA 3 binary8 depend on positions: a permutation of the products changes `d`. | `pairWiseSum_order_dependent`, `oddEvenGrouping_order_dependent` | [MC/Order.lean](MC/Order.lean) |
| CDNA 3 is sign-asymmetric: negating every input does not negate `d`. | `globalAlignment_sign_asymmetric` | [MC/Order.lean](MC/Order.lean) |

How much of the order matters on CDNA 3 binary8 is proven in the work-in-progress project
[`wip/mmalgebra/`](../../wip/mmalgebra/README.md), which builds on this library:

| What it says | Lean name | File |
| --- | --- | --- |
| The parity law: a binary8 block depends on its 16 operand pairs only through the unordered pair {multiset of the odd slots, multiset of the even slots}, for every accumulator input and every mix of E4M3 and E5M2 FNUZ operands. | `MMAlgebra.MC.blockBits_parityEquiv`, `MMAlgebra.MC.cdna3FP8_parityEquiv` | [ParityLaw.lean](../../wip/mmalgebra/MMAlgebraMC/ParityLaw.lean) |
| A permutation of the 16 slots preserves the output on every input exactly when it preserves the parity partition of the slots: `2·(8!)² = 3,251,404,800` of the `16!` orders, for every mix of formats. | `MMAlgebra.MC.cdna3FP8_permute_iff`, `MMAlgebra.MC.blockBits_permute_iff` | [ParityLaw.lean](../../wip/mmalgebra/MMAlgebraMC/ParityLaw.lean) |
| For every mix of formats, two products in one parity class give a different word from the same two products in different classes. | `MMAlgebra.MC.cdna3FP8_sep_e4m3`, `…_sep_e5m2`, `…_sep_e4m3_e5m2`, `…_sep_e5m2_e4m3` | [ParityLaw.lean](../../wip/mmalgebra/MMAlgebraMC/ParityLaw.lean) |

## binary32 rounding

| What it says | Lean name | File |
| --- | --- | --- |
| `fl{x}` is the nearest value among all finite binary32 words, ties to an even last bit. | `rne32_nearestEven` | [Numerics/RoundingContract.lean](Numerics/RoundingContract.lean) |
| `fl{x}` is finite exactly when `|x| < 2^128 − 2^103`. | `rne32_isSome_iff` | [Numerics/RoundingContract.lean](Numerics/RoundingContract.lean) |
| Within that range, the correctly rounded word with the sign of `x` is unique and is `fl{x}`. | `rne32_iff`, `roundsNearestEven32_unique` | [Numerics/Uniqueness.lean](Numerics/Uniqueness.lean) |
| Finite binary32 words with equal sign bit and value are equal. | `value32_injective` | [Numerics/Uniqueness.lean](Numerics/Uniqueness.lean) |

## The FloatLib implementation

Proven in the separate project [`floatlib-port/`](../floatlib-port/README.md), which builds with
mathlib and FloatLib.

| What it says | Lean name | File |
| --- | --- | --- |
| For every model and any input words, a block of the FloatLib implementation gives the same observation (finite word, infinity, NaN) as `blockOutcome`, and an inner product of any length the same as `dotOutcome`. | `MCFloat.Equivalence.block_agree`, `dot_agree` | [Equivalence/Block.lean](../floatlib-port/MCFloat/Equivalence/Block.lean), [Equivalence/Dot.lean](../floatlib-port/MCFloat/Equivalence/Dot.lean) |
| Every model's contract (with its output error bound) and the chaining theorems hold for the FloatLib implementation: a finite FloatLib output is FloatLib's own `fl{S_acc}` (on SFMA and CDNA 1, FloatLib's nearest-even rounding of the exact sum), and a finite FloatLib inner product is a run of linked blocks satisfying the contracts. | `MCFloat.Equivalence.floatlib_contract`, `floatlib_cdna1F16`, …, `floatlib_dot_blocks`, `floatlib_dot_error`, `floatlib_dot_exact_error`, `floatlib_c_monotone` | [Contracts.lean](../floatlib-port/MCFloat/Contracts.lean) |
| FloatLib's binary32 round-to-nearest-even of any rational is `rne32`'s word, with `±∞` exactly where `rne32` overflows. | `MCFloat.Equivalence.round32_bits` | [Equivalence/Rounding.lean](../floatlib-port/MCFloat/Equivalence/Rounding.lean) |

## Not proven

* That AMD GPUs behave like the model. The paper's hardware observations are replayed as tests,
  and the model is compared with the authors' MATLAB models ([differential testing](../docs/differential.md)).
* The special-value layer for non-finite inputs is a definition (input-level detection as the
  paper describes it), checked against the paper's vectors and the MATLAB models, not derived.

This block keeps every name above connected to the API:

```lean
import MatrixCore

open MatrixCore

#check @Spec.blockBits_eq_spec
#check @Spec.supported_cdna3FP8
#check @Spec.pairwise_eq_spec
#check @Spec.supported_cdna2F16
#check @Spec.supported_cdna2BF16
#check @Spec.supported_cdna2BF16_1k
#check @Spec.fl_iff
#check @Spec.flWord_iff
#check @evalBlock_success_iff
#check @evalBlock_nearestEven
#check @blockOutcome_finite_iff
#check @correctRounding_nearestEven
#check @cdna1F16_nearestEven
#check @cdna1BF16_nearestEven
#check @sfmaF32_nearestEven
#check @correctRounding_success_iff
#check @correctRounding_neg
#check @dotBits_sfma_cons
#check @sfma_step_nearestEven
#check @pairwiseSum_four
#check @pairwiseSum_two
#check @flValue_true
#check @flValue_false
#check @alignedAccumulation_error
#check @productSum_error
#check @shiftedC_error
#check @shiftedSum_bounds
#check @evalBlockMachine_eq
#check @cdna3F16_machine_eq
#check @cdna3BF16_machine_eq
#check @cdna3XF32_machine_eq
#check @cdna3FP8_machine_eq
#check @machinePrefix_exact
#check @shiftRegister_spec
#check @rneValue_error
#check @halfUlp32_le
#check @flValue_error
#check @correctRounding_error
#check @pairwise_error
#check @aligned_error
#check @dotBits_error_bound
#check @correctRounding_dot_error
#check @correctRounding_apriori
#check @aligned_apriori
#check @alignedAccumulation_apriori
#check @pairwise_apriori
#check @pairwiseGroupSum_apriori
#check @evalBlock_c_monotone
#check @paper_models_monotone
#check @dotBits_c_monotone
#check @lateSum_mono
#check @rneValue_mono
#check @flushValue_mono
#check @normalizeRD_mono
#check @correctRounding_exact_monotone
#check @correctRounding_product_monotone
#check @runBlocks_correctRounding_monotone
#check @cdna1F16_not_nonmonotone
#check @cdna2F16_nonmonotonic
#check @cdna2BF16_nonmonotonic
#check @cdna2BF16_1k_nonmonotonic
#check @cdna3F16_nonmonotonic
#check @cdna3BF16_nonmonotonic
#check @cdna3XF32_nonmonotonic
#check @cdna3E4M3_nonmonotonic
#check @cdna3E5M2_nonmonotonic
#check @cdna3F16_products_not_determined
#check @runBlocks_products
#check @dotBits_exact_ledger
#check @dotBits_exact_error
#check @mfma_entry
#check @mfma_finite
#check @mfma_error
#check @mfma_length
#check @evalBlock_contract
#check @sfmaF32_contract
#check @cdna1F16_contract
#check @cdna3FP8_contract
#check @dotBits_eq_runBlocks
#check @runBlocks_chain
#check @runBlocks_all
#check @dotBits_blocks
#check @dotBits_residual_ledger
#check @accumulate_perm
#check @pairWiseSum_order_dependent
#check @oddEvenGrouping_order_dependent
#check @globalAlignment_sign_asymmetric
#check @rne32_nearestEven
#check @rne32_isSome_iff
#check @rne32_iff
#check @roundsNearestEven32_unique
#check @value32_injective
```
