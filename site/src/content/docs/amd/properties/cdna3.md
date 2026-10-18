---
title: CDNA 3
description: Properties of the CDNA 3 model - error bounds, monotonicity in c, an exact characterization of non-monotonicity in the products, correct rounding when alignment loses nothing, and the order of the products.
---

CDNA 3 aligns its products to their largest exponent, truncates them, and adds
`c` late with rounding down ([semantics](/HardwarePrimitives/amd/cdna3/)).
Unless stated otherwise, the theorems hold for every model with
`globalAlignment` (FP16, BF16, XF32) or `oddEvenGrouping` (FP8), and are
instantiated for `cdna3F16`, `cdna3BF16`, `cdna3XF32` and `cdna3FP8 fa fb`.

## Error bounds

The block loses in three places: the alignment truncation of the products,
the late alignment of `c`, and the final rounding. With `n` products and
`F = 23 + padding`, the accumulation loss is bounded branch by branch: when
`e_c ≤ e_max`,

```text
|S_acc − (Σ p_ℓ + c)|  <  (n + 2) · 2^(e_max − F)  +  2^(e_max − 24)
                           alignment of the products   late alignment of c
```

and when `e_c > e_max`, `S_acc` is below the exact sum, up to the product
error, by less than `(n + 2)·2^(e_max − F) + 2^(e_c − 32) + 2^(e′ − 31)`, where
`e′` is the normalized exponent of `S′_{p_i,sum} + s_c`
([`MatrixCore.alignedAccumulation_error`](https://github.com/pauljiang03/HardwarePrimitives/blob/main/amd/MatrixCore/MC/LateAccumulation.lean#L211)).
`alignedBound P x` collects the branches, and with the final rounding:

```lean
theorem aligned_error {P : Model}
    (hacc : P.accumulation = .globalAlignment ∨ P.accumulation = .oddEvenGrouping)
    (hcut : ∀ n, P.late.cCutoff = some n → P.late.cMantissaBits ≤ n) (hcz : P.cZeroExp ≠ none)
    {x : BlockInput P} {t : BlockTrace P} (h : evalBlock x = .ok t) :
    absQ (t.prepared.exact - wordValue t.d) ≤
      alignedBound P t.prepared + flBound (!P.subnormals) t.sAcc
```

From the inputs alone, with `A = Σ|p_ℓ| + |c|`, the error is at most
`2^-23 · A + (n + 4) · 2^(e_max − 24) + 2^-149`
([`MatrixCore.aligned_apriori`](https://github.com/pauljiang03/HardwarePrimitives/blob/main/amd/MatrixCore/MC/AprioriBounds.lean#L227)).
The alignment term depends on `e_max`, the largest **exponent** of the
products, not on the size of the result. Products are in denormalized form,
so `2^(e_max)` can exceed every `|p_ℓ|`, and when large products cancel the
relative error is large.

## Non-monotonicity

### In `c`: monotone

For the same `a` and `b`, a larger `c` never gives a smaller output, on every
configuration, and the same holds for inner products
([`MatrixCore.evalBlock_c_monotone`](https://github.com/pauljiang03/HardwarePrimitives/blob/main/amd/MatrixCore/MC/Monotonicity.lean#L605),
[`MatrixCore.dotBits_c_monotone`](https://github.com/pauljiang03/HardwarePrimitives/blob/main/amd/MatrixCore/MC/Monotonicity.lean#L629)).
On a Tensor Core `C` takes part in the alignment, and lowering it can raise
the output; on CDNA 3 `c` never sets the products' alignment.

### In the products: the mechanism, concretely

On CDNA 3 FP16, take seven products `2^-12 × 2^-12 = 2^-24` and raise a lead
product from `2^-9 − 2^-29` (`1025/1024 · 2046/1024 · 2^-10`, `e_p = −10`) to
`2^-9` (`2^-24 · 2^15`, a subnormal operand, `e_p = 1`):

| Lead | `e_max` | Grid | The seven products `2^-24` | Output |
| --- | ---: | --- | --- | --- |
| `2^-9 − 2^-29` | −10 | `2^-34` | kept | `2^-9 + 223·2^-29` (`0x3B0006F8`) |
| `2^-9` | 1 | `2^-23` | truncated away | `2^-9` (`0x3B000000`) |

The lead rises by `2^-29`, and the output falls by `223·2^-29`
([`MatrixCore.cdna3F16_nonmonotonic`](https://github.com/pauljiang03/HardwarePrimitives/blob/main/amd/MatrixCore/MC/ProductMonotonicity.lean#L141)).
Every input format has such a pair: BF16, XF32, E4M3 and E5M2
([`MatrixCore.cdna3E4M3_nonmonotonic`](https://github.com/pauljiang03/HardwarePrimitives/blob/main/amd/MatrixCore/MC/ProductMonotonicity.lean#L162)
and its neighbours). Even with normal operands, equal products `1.5 · 1.5` and
`2.25 · 1` give different outputs
([`MatrixCore.cdna3F16_products_not_determined`](https://github.com/pauljiang03/HardwarePrimitives/blob/main/amd/MatrixCore/MC/ProductMonotonicity.lean#L176)).

### Monotone while the alignment exponents stay the same

The mechanism is the only one. With the alignment exponents fixed (`e_max` on
Algorithm 1, the exponents of the odd and the even group on Algorithm 2),
every stage is monotone: truncation on a fixed grid, the exact sum, the round
down of `c` and of the other group, and the final `fl{·}`.

```lean
def alignmentExponents (P : Model) (ps : List Unpacked) : List (Option ℤ)
  -- [maxExp ps] on Algorithm 1; [maxExp (oddIndexed ps), maxExp (evenIndexed ps)] on Algorithm 2

theorem aligned_product_monotone {P : Model}
    (hacc : P.accumulation = .globalAlignment ∨ P.accumulation = .oddEvenGrouping)
    {x x' : BlockInput P} {t t' : BlockTrace P} (h : evalBlock x = .ok t)
    (h' : evalBlock x' = .ok t') (hp : productsLE x x' = true) (hc : x.c = x'.c)
    (he : alignmentExponents P t.prepared.p = alignmentExponents P t'.prepared.p) :
    wordValue t.d ≤ wordValue t'.d
```

So every pair of inputs where larger products give a smaller output changes an
alignment exponent
([`MatrixCore.aligned_nonmonotone_alignment_changes`](https://github.com/pauljiang03/HardwarePrimitives/blob/main/amd/MatrixCore/MC/AlignmentMonotonicity.lean#L291)).
The per-model forms are `cdna3F16_product_monotone`, `cdna3BF16_product_monotone`,
`cdna3XF32_product_monotone` and `cdna3FP8_product_monotone`.

### The general family theorem

The pair above belongs to a family with an exact threshold, the CDNA 3
counterpart of the TC-EFT paper's family on Tensor Cores. On `cdna3F16`, a
block holds a lead product `a₁b₁`, `n ≤ 7` products `2^-24`, zeros and
`c = 0`. Compare a lead `L = a₁b₁` with `e_a + e_b = −10` and integer
significands `m_a`, `m_b`, so `L = m_a m_b · 2^-30`, with the lead
`L′ = 2^-24 · 2^15 = 2^-9` of exponent 1:

```lean
theorem cdna3F16LeadBlock_nonmonotone_iff {wa wb : BitVec 16} {ua ub : Unpacked}
    (ha : fp16.decode wa = .finite ua) (hb : fp16.decode wb = .finite ub)
    (hs : ua.negative = ub.negative) (hm : 0 < ua.m * ub.m) (he : ua.e + ub.e = -10)
    {n : ℕ} (hn : n ≤ 7) :
    ProductNonmonotone (cdna3F16LeadBlock wa wb n) (cdna3F16LeadBlock 0x0001 0x7800 n) ↔
      ua.m * ub.m ≤ 2 ^ 21 ∧ (2 ^ 21 : ℤ) - (ua.m * ub.m : ℕ) < 64 * n
```

With `L`, `e_max = −10`, every product is kept and `d = (m_a m_b + 64n)·2^-30`;
with `L′`, `e_max = 1` and `d′ = 2^-9`
([`MatrixCore.cdna3F16LeadBlock_outputs`](https://github.com/pauljiang03/HardwarePrimitives/blob/main/amd/MatrixCore/MC/NonmonotoneFamily.lean#L201)).
So the output falls exactly when **the lead's deficit `2^21 − m_a m_b` is less
than `64n`**, the weight of the small products in units of `2^-30`, and the
pair is non-monotone when, in addition, `L ≤ L′`. The theorem holds for every
lead, subnormal operands included, and every `n`:

| Lead `a₁ · b₁` | `2^21 − m_a m_b` | Non-monotone for |
| --- | ---: | --- |
| `0x3C01 · 0x17FE` | 2 | `n ≥ 1` |
| `0x3C30 · 0x17A4` | 320 | `n ≥ 6` |
| `0x3DA8 · 0x15A8` | 448 | no `n ≤ 7` |

Each row is also checked by kernel evaluation on both sides of its threshold
([`tests/MatrixCoreTests/ProductProperties.lean`](https://github.com/pauljiang03/HardwarePrimitives/blob/main/amd/tests/MatrixCoreTests/ProductProperties.lean)).

### Necessary and sufficient conditions in general

For arbitrary inputs, let the gain `Δ = exact′ − exact` be how much the exact
sum rises, and `R = exact − S_acc` the accumulation loss of each block. An
output decrease **requires** that the loss grows by more than the gain,
`R′ − R > Δ`; the condition is **sufficient** when both `S_acc` are FP32
values, so that the final rounding returns them:

```lean
theorem output_decrease_requires_loss {P : Model} {x x' : BlockInput P} {t t' : BlockTrace P}
    (h : evalBlock x = .ok t) (h' : evalBlock x' = .ok t') (hlt : wordValue t'.d < wordValue t.d) :
    t'.sAcc < t.sAcc ∧ t.gain t' < t'.accumulationLoss - t.accumulationLoss

theorem output_decrease_of_loss {P : Model} (hs : P.subnormals = true) {x x' : BlockInput P}
    {t t' : BlockTrace P} (h : evalBlock x = .ok t) (h' : evalBlock x' = .ok t')
    (hv : FiniteValue32 t.sAcc) (hv' : FiniteValue32 t'.sAcc)
    (hgt : t.gain t' < t'.accumulationLoss - t.accumulationLoss) :
    wordValue t'.d < wordValue t.d
```

On CDNA 3, `R′ − R > Δ` with larger products and the same `c` needs a change
of alignment exponent
([`MatrixCore.aligned_loss_exceeds_gain_changes_alignment`](https://github.com/pauljiang03/HardwarePrimitives/blob/main/amd/MatrixCore/MC/LossCondition.lean#L101)).
In the pair above, `Δ = 2^-29`, `R = 0` and `R′ = 7·2^-24`.

### How large the drop can be

The drop is at most the two blocks' error bounds less the gain:

```lean
theorem aligned_output_drop_le {P : Model}
    (hacc : P.accumulation = .globalAlignment ∨ P.accumulation = .oddEvenGrouping)
    (hcut : ∀ n, P.late.cCutoff = some n → P.late.cMantissaBits ≤ n) (hcz : P.cZeroExp ≠ none)
    {x x' : BlockInput P} {t t' : BlockTrace P} (h : evalBlock x = .ok t)
    (h' : evalBlock x' = .ok t') :
    wordValue t.d - wordValue t'.d ≤
      (alignedBound P t.prepared + flBound (!P.subnormals) t.sAcc) +
        (alignedBound P t'.prepared + flBound (!P.subnormals) t'.sAcc) - t.gain t'
```

From the inputs alone, it is at most `2^-23 (A + A′) + (n + 4)·2^(e_max − 24) +
(n′ + 4)·2^(e′_max − 24) + 2^-148 − Δ`
([`MatrixCore.aligned_output_drop_apriori`](https://github.com/pauljiang03/HardwarePrimitives/blob/main/amd/MatrixCore/MC/LossCondition.lean#L131)).
For the pair above the drop is `223·2^-29` and the first bound `22511·2^-34`.

## Correct rounding

CDNA 3 returns the correctly rounded sum whenever alignment loses nothing:
every product lies on the alignment grid `2^(e_max − 23 − padding)`, and the
late alignment of `c` loses nothing in its branch. `LosslessAlignment P x`
states the condition for every branch; `of_early` builds it when `e_c ≤ e_max`
and `c` lies on the grid `2^(e_max − 24)`, and `of_c_zero` when `c = 0`.

```lean
theorem alignedAccumulation_of_lossless (P : Model) (x : Prepared)
    (hcut : ∀ n, P.late.cCutoff = some n → P.late.cMantissaBits ≤ n)
    (hc : ∀ eC, cExp P x.c = some eC → absQ x.c.value < pow2 (eC + 1))
    (hl : LosslessAlignment P x) : alignedAccumulation P x = x.exact

theorem aligned_nearestEven_of_lossless {P : Model}
    (hacc : P.accumulation = .globalAlignment ∨ P.accumulation = .oddEvenGrouping)
    (hcut : ∀ n, P.late.cCutoff = some n → P.late.cMantissaBits ≤ n) (hs : P.subnormals = true)
    {x : BlockInput P} {t : BlockTrace P} (h : evalBlock x = .ok t)
    (hl : LosslessAlignment P t.prepared) :
    t.sAcc = t.prepared.exact ∧ NearestEven32 t.prepared.exact t.d
```

A product lies on the grid when its own last bit is at or above it
([`MatrixCore.Unpacked.onGrid_of_le`](https://github.com/pauljiang03/HardwarePrimitives/blob/main/amd/MatrixCore/MC/LosslessAlignment.lean#L22)):
for example, eight FP16 products whose exponents are within 4 of `e_max` lose
nothing, since each has 20 mantissa bits and the grid keeps 24. The output is
then the correctly rounded sum, as on CDNA 1.

## Order of the products

- **Algorithm 1** depends on the products only as a multiset: every product is
  aligned to the same `e_max`
  ([`MatrixCore.accumulate_perm`](https://github.com/pauljiang03/HardwarePrimitives/blob/main/amd/MatrixCore/MC/Order.lean#L29)).
- **Algorithm 2** depends on positions: moving a product between the odd and
  the even group can change `d`
  ([`MatrixCore.oddEvenGrouping_order_dependent`](https://github.com/pauljiang03/HardwarePrimitives/blob/main/amd/MatrixCore/MC/Order.lean#L48)).
  The parity law says exactly how much: an FP8 block depends on its 16
  operand pairs only through the unordered pair {multiset of the odd slots,
  multiset of the even slots}, for every `c` and every mix of E4M3 and E5M2
  FNUZ. A permutation of the slots preserves the output on every input exactly
  when it preserves the parity partition: `2·(8!)² = 3,251,404,800` of the
  `16!` orders. For every mix of formats, two products in one parity class give
  a different word from the same two in different classes
  ([`MMAlgebra.MC.cdna3FP8_parityEquiv`](https://github.com/pauljiang03/HardwarePrimitives/blob/main/wip/mmalgebra/MMAlgebraMC/ParityLaw.lean#L173),
  [`MMAlgebra.MC.cdna3FP8_permute_iff`](https://github.com/pauljiang03/HardwarePrimitives/blob/main/wip/mmalgebra/MMAlgebraMC/ParityLaw.lean#L523),
  [`MMAlgebra.MC.cdna3FP8_sep_e4m3`](https://github.com/pauljiang03/HardwarePrimitives/blob/main/wip/mmalgebra/MMAlgebraMC/ParityLaw.lean#L201);
  proved in `wip/mmalgebra`, a work-in-progress project that builds on this
  model).
- **Sign.** The round-down steps make CDNA 3 asymmetric under negation:
  `c = 1, p₁ = 2^-24 + 2^-32` gives `1`, while the negated input gives
  `−(1 + 2^-23)`
  ([`MatrixCore.globalAlignment_sign_asymmetric`](https://github.com/pauljiang03/HardwarePrimitives/blob/main/amd/MatrixCore/MC/Order.lean#L57)).

## Fixed-width accumulation

A two's-complement register of 30 bits (FP16, BF16), 29 (XF32) or 31
(FP8), wrapping on overflow, gives the model's output for every input, and
every prefix of the accumulation is exact at that width
([`MatrixCore.evalBlockMachine_eq`](https://github.com/pauljiang03/HardwarePrimitives/blob/main/amd/MatrixCore/MC/MachineRefinement.lean#L162),
[`MatrixCore.machinePrefix_exact`](https://github.com/pauljiang03/HardwarePrimitives/blob/main/amd/MatrixCore/MC/MachineRefinement.lean#L185);
see [the register model](/HardwarePrimitives/amd/cdna3/#a-fixed-width-register-model)).

## MC-EFT correction

The [MC-EFT correction](/HardwarePrimitives/amd/properties/eft/) returns the
correctly rounded sum for any finite `D`, with the cut-off at the higher of the
last bit of `D` and the alignment grid. With `D` the block's output, `S_acc` is
the high sum plus the part of the low parts that alignment kept, and the overlap
is that kept part plus the final rounding error, less than `(N_FMA + 6)` units of
the cut-off
([`MatrixCore.aligned_eft`](https://github.com/pauljiang03/HardwarePrimitives/blob/main/amd/MatrixCore/EFT/CDNA3.lean#L632)).
On the block whose seven products `2^-24` are truncated away, the hardware
returns `0x40100000` and the correction `0x40100002`, on the fast path.
