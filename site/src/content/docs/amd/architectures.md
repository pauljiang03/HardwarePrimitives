---
title: 3. The three architectures
description: The block semantics of CDNA 1, CDNA 2 and CDNA 3 (correct rounding, pairwise sums, global alignment and odd/even grouping), the Lean definitions, and the theorems that characterize them.
---

Each section gives the block semantics in the paper's terms, the Lean
definitions, and the theorems that characterize them. The final step is
always `d = fl{S_acc}`, round to nearest even into binary32.

## fp32 inputs on CDNA 1, 2 and 3: SFMA

The binary32 MFMA instructions are a sequential FMA,
`(…((c + p₁) + p₂) + …)`, each product kept exact and each step rounded to
nearest even. In Lean this is `sfmaF32`, a `correct_rounding` block with
`N_FMA = 1`, chained by `dotBits`:

- `c` and `p₁` are combined first, and the result is the `c` of the rest
  ([`MatrixCore.dotBits_sfma_cons`](https://github.com/pauljiang03/HardwarePrimitives/blob/main/amd/MatrixCore/MC/CompositionProperties.lean#L62));
- each step is the binary32 value nearest to `c + a·b`
  ([`MatrixCore.sfma_step_nearestEven`](https://github.com/pauljiang03/HardwarePrimitives/blob/main/amd/MatrixCore/MC/CompositionProperties.lean#L80)).

## CDNA 1 (MI100): `correct_rounding`

Products are kept in full precision, `c` is accumulated with them, the sum is
exact, and the only rounding is the final one. `N_FMA = 4` for fp16 and `2`
for bf16. Subnormals are supported in input and output, and products may
exceed `2^128` inside a block; only the final conversion can overflow.

| Fact | Lean |
| --- | --- |
| `d` is the binary32 value nearest to the exact `Σ a_ℓ b_ℓ + c`, ties to even. | [`MatrixCore.correctRounding_nearestEven`](https://github.com/pauljiang03/HardwarePrimitives/blob/main/amd/MatrixCore/MC/CorrectRounding.lean#L30) |
| A block is accepted exactly when the inputs are finite and the exact sum is below `2^128 − 2^103`. | [`MatrixCore.correctRounding_success_iff`](https://github.com/pauljiang03/HardwarePrimitives/blob/main/amd/MatrixCore/MC/CorrectRounding.lean#L42) |
| Negating the exact sum negates the output. | [`MatrixCore.correctRounding_neg`](https://github.com/pauljiang03/HardwarePrimitives/blob/main/amd/MatrixCore/MC/CorrectRounding.lean#L97) |
| The result depends on the products only as a multiset. | [`MatrixCore.accumulate_perm`](https://github.com/pauljiang03/HardwarePrimitives/blob/main/amd/MatrixCore/MC/Order.lean#L37) |

## CDNA 2 (MI210, MI250): `pair_wise_sum`

Inputs and outputs have no subnormals: subnormal inputs are flushed to zero,
and every `fl{·}` flushes a subnormal result to zero. Each product is
converted to binary32 (`fl{a_ℓ b_ℓ}`), and the products are summed pairwise:

```text
groups of 4 (fp16, bf16 _1k):   d = fl{c + fl{fl{p₁ + p₂} + fl{p₃ + p₄}}}
groups of 2 (bf16):             d = fl{c + fl{p₁ + p₂}}
```

| Fact | Lean |
| --- | --- |
| The model computes exactly these formulas. | [`MatrixCore.pairwiseSum_four`](https://github.com/pauljiang03/HardwarePrimitives/blob/main/amd/MatrixCore/MC/PairWiseSum.lean#L24), [`MatrixCore.pairwiseSum_two`](https://github.com/pauljiang03/HardwarePrimitives/blob/main/amd/MatrixCore/MC/PairWiseSum.lean#L42) |
| `fl{·}` with flushing returns the nearest-even value when it is zero or normal, and zero when it is subnormal. | [`MatrixCore.flValue_true`](https://github.com/pauljiang03/HardwarePrimitives/blob/main/amd/MatrixCore/MC/PairWiseSum.lean#L117) |
| A permutation of the products can change `d`. | [`MatrixCore.pairWiseSum_order_dependent`](https://github.com/pauljiang03/HardwarePrimitives/blob/main/amd/MatrixCore/MC/Order.lean#L53) |
| The model equals an independent transcription of the paper's Fig. 2. | [`MatrixCore.Spec.pairwise_eq_spec`](https://github.com/pauljiang03/HardwarePrimitives/blob/main/amd/MatrixCore/Specification/Pairwise.lean#L161) |

Product conversion and every pairwise sum can overflow to an infinity, which
`blockOutcome` propagates with binary32 special-value arithmetic, so
`p₁ = 2^128, p₂ = −2^128` gives NaN, as the paper observes.

## CDNA 3 (MI300A, MI300X): Algorithms 1 and 2

### fp16, bf16 and XF32: Algorithm 1 (`global_alignment`)

```text
e_max = max{e_{p_i}}  over nonzero products
S_{p_i,sum} = Σ s_{p_i} aligned to e_max, truncated to 24 mantissa bits
e_c = −126 if c = 0
if e_max ≥ e_c:
    s′_c = s_c shifted right by e_max − e_c, rounded down to 24 mantissa bits
    S_acc = S_{p_i,sum} + s′_c
else:
    S′_{p_i,sum} = S_{p_i,sum} shifted right by e_c − e_max, rounded down to 32 mantissa bits
    S_acc = S′_{p_i,sum} + s_c, normalized (subnormal-aware), rounded down to 31 mantissa bits
d = fl{S_acc}
```

Products are kept denormalized (`s_p ∈ [0, 4)`), and a product with
`|p_ℓ| ≥ 2^128` is an infinity before accumulation. XF32 truncates each
binary32 input to ten mantissa bits and uses `N_FMA = 4`. In Lean:
`productSum` (with `alignedSum`), `cExp`, `shiftedC`, `shiftedSum`,
`normalizeRD` and `lateSum`; `alignedAccumulation` composes them.

### binary8: Algorithm 2 (`odd_even_grouping`)

Odd- and even-indexed products (`p₁, p₃, …` and `p₂, p₄, …`) are aligned to
their own maximum exponents and truncated to 24 mantissa bits. The sum with
the smaller exponent is shifted to `e_max` and rounded down to 24 mantissa
bits, and the two are added without normalization. `c` is then added as in
Algorithm 1, except that `s′_c = 0` once `e_max − e_c > 25`. Any combination
of fp8-E4M3 and fp8-E5M2 FNUZ operands is allowed; `N_FMA = 16`.

### Theorems

| Fact | Lean |
| --- | --- |
| The error of `S_acc` against the exact sum, in each branch of Algorithms 1 and 2. | [`MatrixCore.alignedAccumulation_error`](https://github.com/pauljiang03/HardwarePrimitives/blob/main/amd/MatrixCore/MC/LateAccumulation.lean#L228) |
| Algorithm 1 is independent of the product order; Algorithm 2 is not. | [`MatrixCore.accumulate_perm`](https://github.com/pauljiang03/HardwarePrimitives/blob/main/amd/MatrixCore/MC/Order.lean#L37), [`MatrixCore.oddEvenGrouping_order_dependent`](https://github.com/pauljiang03/HardwarePrimitives/blob/main/amd/MatrixCore/MC/Order.lean#L61) |
| The parity law: Algorithm 2 depends on the products only through the unordered pair {multiset of the odd slots, multiset of the even slots}, and a permutation of the 16 slots preserves the output on every input exactly when it preserves the parity partition, for every mix of E4M3 and E5M2 FNUZ (proved in `wip/mmalgebra`, a work-in-progress project of the repository that builds on this model). | [`MMAlgebra.MC.cdna3FP8_parityEquiv`](https://github.com/pauljiang03/HardwarePrimitives/blob/main/wip/mmalgebra/MMAlgebraMC/ParityLaw.lean#L173), [`MMAlgebra.MC.cdna3FP8_permute_iff`](https://github.com/pauljiang03/HardwarePrimitives/blob/main/wip/mmalgebra/MMAlgebraMC/ParityLaw.lean#L523) |
| The rounding-down steps make CDNA 3 sign-asymmetric: `c = 1, p₁ = 2^-24 + 2^-32` gives `1`, while the negated input gives `−(1 + 2^-23)`. | [`MatrixCore.globalAlignment_sign_asymmetric`](https://github.com/pauljiang03/HardwarePrimitives/blob/main/amd/MatrixCore/MC/Order.lean#L71) |
| A fixed-width wrapping accumulator of 30 bits (fp16, bf16), 29 (XF32) or 31 (binary8) gives the model's output for every input. | [`MatrixCore.evalBlockMachine_eq`](https://github.com/pauljiang03/HardwarePrimitives/blob/main/amd/MatrixCore/MC/MachineRefinement.lean#L176) |
| The model equals an independent transcription of Algorithms 1 and 2. | [`MatrixCore.Spec.blockBits_eq_spec`](https://github.com/pauljiang03/HardwarePrimitives/blob/main/amd/MatrixCore/Specification/Equivalence.lean#L129) |

## Special values

The paper reports that infinities are detected at the input, that `+∞` with
`−∞` gives NaN (with a negative sign), and that CDNA 3 maps `|p_ℓ| ≥ 2^128` to
an infinity by magnitude. `blockOutcome` implements these rules. Finite
inputs follow the model, with its overflows; when an operand or `c` is
infinite or NaN, the result is decided at the input from the operands, `c`,
and the products that overflow, as in a chained inner product whose earlier
block overflowed. `blockOutcome` agrees with `evalBlock` wherever the result
is finite ([`MatrixCore.blockOutcome_finite_iff`](https://github.com/pauljiang03/HardwarePrimitives/blob/main/amd/MatrixCore/MC/SpecialAgreement.lean#L169)).
