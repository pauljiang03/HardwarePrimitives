# The three architectures

Each section gives the block semantics in the paper's terms, the Lean definitions, and the
theorems that characterize them. The final step is always `d = fl{S_acc}`, RNE into binary32.

## fp32 inputs on CDNA 1, 2 and 3: SFMA

The binary32 MFMA instructions are a sequential FMA: `(…((c + p₁) + p₂) + …)`, each product
kept exact and each step rounded with RNE. In Lean this is `sfmaF32`, a `correct_rounding` block
with `N_FMA = 1`, chained by `dotBits`:

* `dotBits_sfma_cons`: `c` and `p₁` are combined first, then the result is the `c` of the rest;
* `sfma_step_nearestEven`: each step is the binary32 value nearest to `c + a·b`.

## CDNA 1 (MI100): `correct_rounding`

Products are kept in full precision, `c` is accumulated with them, the sum is exact, and the only
rounding is the final RNE. `N_FMA = 4` for fp16 and `2` for bf16. Subnormals are supported in
input and output. Products may exceed `2^128` inside a block; only the final conversion can
overflow.

* `correctRounding_nearestEven`: `d` is the binary32 value nearest to the exact `Σ a_ℓ b_ℓ + c`;
* `correctRounding_success_iff`: accepted exactly when the exact sum is below `2^128 − 2^103`;
* `correctRounding_neg`: sign symmetry; `accumulate_perm`: independent of the product order.

## CDNA 2 (MI210, MI250): `pair_wise_sum`

Inputs and outputs have no subnormals: subnormal inputs are flushed to zero, and every `fl{·}`
flushes a subnormal result to zero. Each product is converted to binary32 (`fl{a_ℓ b_ℓ}`), and
the products are summed pairwise:

```
groups of 4 (fp16, bf16 _1k):   d = fl{c + fl{fl{p₁ + p₂} + fl{p₃ + p₄}}}
groups of 2 (bf16):             d = fl{c + fl{p₁ + p₂}}
```

`pairwiseSum` implements these pairwise sums, with `pairwiseGroupSum` for the balanced sum of a
group; `pairwiseSum_four` and `pairwiseSum_two` state the
formulas above for the model, and `flValue_true` states what flushing does. Product conversion
and every pairwise sum can overflow to an infinity, which `blockOutcome` propagates with binary32
special-value arithmetic (so `p₁ = 2^128, p₂ = −2^128` gives NaN, as observed).
`pairWiseSum_order_dependent` shows a permutation of the products that changes `d`, and
`Spec.pairwise_eq_spec` connects the model to an independent transcription of Fig. 2.

## CDNA 3 (MI300A, MI300X): Algorithms 1 and 2

### fp16, bf16 and XF32: Algorithm 1 (`global_alignment`)

```
e_max = max{e_{p_i}}  over nonzero products
S_{p_i,sum} = Σ s_{p_i} aligned to e_max, truncated to 24 fractional bits
e_c = −126 if c = 0
if e_max ≥ e_c:
    s′_c = s_c shifted right by e_max − e_c, RD to 24 fractional bits
    S_acc = S_{p_i,sum} + s′_c
else:
    S′_{p_i,sum} = S_{p_i,sum} shifted right by e_c − e_max, RD to 32 fractional bits
    S_acc = S′_{p_i,sum} + s_c, normalized (subnormal-aware), RD to 31 fractional bits
d = fl{S_acc}
```

Products are kept in denormalized form (`s_p ∈ [0, 4)`), and a product with `|p_ℓ| ≥ 2^128` is an
infinity before accumulation. XF32 truncates each binary32 input to ten fraction bits and uses
`N_FMA = 4`.

In Lean: `productSum` (with `alignedSum`), `cExp`, `shiftedC`, `shiftedSum`, `normalizeRD`, and
`lateSum`; `alignedAccumulation` composes them.

### binary8: Algorithm 2 (`odd_even_grouping`)

Odd- and even-indexed products (`p₁, p₃, …` and `p₂, p₄, …`) are aligned to their own maximum
exponents and truncated to 24 fractional bits. The sum with the smaller exponent is shifted to
`e_max` and RD to 24 fractional bits, and the two are added without normalization. `c` is then
added as in Algorithm 1, except that `s′_c = 0` once `e_max − e_c > 25`. Any combination of
fp8-E4M3 and fp8-E5M2 FNUZ operands is allowed; `N_FMA = 16`.

### Theorems

* `alignedAccumulation_error`: the error of `S_acc` in each branch;
* `accumulate_perm`: Algorithm 1 is independent of the product order;
  `oddEvenGrouping_order_dependent`: Algorithm 2 is not. It depends on the order only through the
  parity of the slots: a block depends on its operand pairs only through the unordered pair
  {multiset of the odd slots, multiset of the even slots}, and a permutation of the 16 slots
  preserves the output on every input exactly when it preserves the parity partition (the parity
  law, proved in the reduction algebra:
  [`MMAlgebra.MC.cdna3FP8_parityEquiv`, `cdna3FP8_permute_iff`](../../../mmalgebra/MMAlgebraMC/ParityLaw.lean));
* `globalAlignment_sign_asymmetric`: the RD steps make CDNA 3 sign-asymmetric
  (`c = 1, p₁ = 2^-24 + 2^-32` gives `1`, while the negated input gives `−(1 + 2^-23)`);
* `Spec.blockBits_eq_spec`: Algorithms 1 and 2 as transcribed independently.

## Special values

The paper reports that infinities are detected at the input, that `+∞` with `−∞` gives NaN (with
a negative sign), and that CDNA 3 maps `|p_ℓ| ≥ 2^128` to an infinity by magnitude. `blockOutcome`
implements these rules. Finite inputs follow the model, with its overflows; when an operand or
`c` is infinite or NaN, the result is decided at the input from the operands, `c`, and the
products that overflow (`|p_ℓ| ≥ 2^128` on CDNA 3, binary32 conversion on CDNA 2), as in a chained
inner product whose earlier block overflowed. `blockOutcome_finite_iff` shows that it agrees
with `evalBlock` wherever the result is finite.
