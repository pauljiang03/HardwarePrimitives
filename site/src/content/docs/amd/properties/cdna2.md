---
title: CDNA 2
description: Properties of the CDNA 2 model - error bounds, monotonicity in c, non-monotonicity in the products caused only by flushing, correct rounding when every intermediate rounding is exact, and order dependence.
---

CDNA 2 flushes subnormal inputs, converts each product to FP32, and adds
the products in a balanced tree of FP32 additions, `c` last
([semantics](/HardwarePrimitives/amd/cdna2/)). Every `fl{·}` rounds to nearest
even and flushes subnormal results. The theorems hold for every model with the
`pairWiseSum` configuration and are instantiated for `cdna2F16`, `cdna2BF16`
and `cdna2BF16_1k`.

## Error bounds

The block loses in flushing the subnormal inputs, in each product conversion,
in each pairwise sum and in the final rounding. `pairwiseBound P x` is the
effect of flushing plus one `fl{·}` error (half an ulp, and `2^-126` more for
flushing) for each conversion and each pairwise sum, at the values the model
computes:

```lean
theorem pairwise_error {P : Model} (hacc : P.accumulation = .pairWiseSum)
    {x : BlockInput P} {t : BlockTrace P} (h : evalBlock x = .ok t) :
    absQ (t.prepared.exact - wordValue t.d) ≤
      pairwiseBound P t.prepared + flBound (!P.subnormals) t.sAcc
```

From the inputs alone (`N_FMA ≤ 4`), with `x′` the inputs after flushing and
`A′ = Σ|p′_ℓ| + |c′|`, the error is at most `|exact − exact′| + 2^-21 · A′ + 2^-120`
([`MatrixCore.pairwise_apriori`](https://github.com/pauljiang03/HardwarePrimitives/blob/main/matrix-core/MatrixCore/MC/AprioriBounds.lean#L460)).
The flushing term is not small in relative terms: a product with a subnormal
operand is lost whole.

## Non-monotonicity

### In `c`: monotone

For the same `a` and `b`, a larger `c` never gives a smaller output
([`MatrixCore.evalBlock_c_monotone`](https://github.com/pauljiang03/HardwarePrimitives/blob/main/matrix-core/MatrixCore/MC/Monotonicity.lean#L605)).

### In the products: flushing is the only cause

CDNA 2 is not monotone in the products. On FP16, raise a product from
`−2^-10` (`2^-15 · −2^5`, a subnormal operand) to `−2^-11` (`2^-14 · −2^3`,
normal operands): the first is flushed to zero and the second is kept, so the
output falls from `0` to `−2^-11`
([`MatrixCore.cdna2F16_nonmonotonic`](https://github.com/pauljiang03/HardwarePrimitives/blob/main/matrix-core/MatrixCore/MC/ProductMonotonicity.lean#L125);
the BF16 variants have such pairs too).

Flushing is the only mechanism. Every conversion, every pairwise sum and the
final rounding are monotone, so without subnormal operands larger products
never give a smaller output:

```lean
def Prepared.NormalOperands (x : Prepared) : Prop :=
  ∀ u ∈ x.a ++ x.b, u.m = 0 ∨ 2 ^ u.t ≤ u.m

theorem pairwise_product_monotone {P : Model} (hacc : P.accumulation = .pairWiseSum)
    {x x' : BlockInput P} {t t' : BlockTrace P} (h : evalBlock x = .ok t)
    (h' : evalBlock x' = .ok t') (hp : productsLE x x' = true) (hc : x.c = x'.c)
    (hn : t.prepared.NormalOperands) (hn' : t'.prepared.NormalOperands) :
    wordValue t.d ≤ wordValue t'.d
```

The per-model forms are `cdna2F16_product_monotone`, `cdna2BF16_product_monotone`
and `cdna2BF16_1k_product_monotone`. The condition concerns `a` and `b` only;
`c` is the same in both blocks.

### Necessary condition in general

As on every configuration, an output decrease requires that the accumulation
loss `R = exact − S_acc` grows by more than the gain in the exact sum
([`MatrixCore.output_decrease_requires_loss`](https://github.com/pauljiang03/HardwarePrimitives/blob/main/matrix-core/MatrixCore/MC/LossCondition.lean#L42)).
On CDNA 2 that loss is the flushing and rounding of the inputs and partial
sums.

## Correct rounding

When nothing is flushed and every product conversion and every pairwise
`fl{·}` is exact, `S_acc` is the exact sum and the output is that sum rounded
once:

```lean
theorem pairwise_fl_exact_of_lossless {P : Model} (hacc : P.accumulation = .pairWiseSum)
    {x : BlockInput P} {t : BlockTrace P} (h : evalBlock x = .ok t)
    (hf : P.subnormals = true ∨ t.prepared.flushed = t.prepared)
    (hconv : t.prepared.p.mapM (fun p => flValue (!P.subnormals) p.value) =
      some (t.prepared.p.map Unpacked.value))
    (hsum : pairwiseGroupSum (!P.subnormals) t.prepared.p.length
      (t.prepared.p.map Unpacked.value) = some (sumQ (t.prepared.p.map Unpacked.value))) :
    t.sAcc = t.prepared.exact ∧ fl32 (!P.subnormals) t.prepared.exact = some t.d
```

The final rounding is the flushing `fl{·}` of CDNA 2: round to nearest even,
with a subnormal result replaced by a zero of the same sign
([normalization and final rounding](/HardwarePrimitives/amd/normalization/#flushing-cdna-2)).

## Order of the products

The pairs are rounded separately, so the output depends on the positions of
the products: `1, s, s, 0` and `s, s, 1, 0` with `s = 2^-23 + 2^-24` give
`1 + 2^-21` and `1 + 2^-22 + 2^-23`
([`MatrixCore.pairWiseSum_order_dependent`](https://github.com/pauljiang03/HardwarePrimitives/blob/main/matrix-core/MatrixCore/MC/Order.lean#L41);
[example](/HardwarePrimitives/amd/cdna2/#example)).

## MC-EFT correction

The [MC-EFT correction](/HardwarePrimitives/amd/properties/eft/) returns the
correctly rounded sum of the inputs before flushing, for any finite `D`. Its
cut-off is the last bit of `D`. With `D` the block's output, the overlap
`D − H` is exactly the low parts plus every rounding error of the block (each
conversion, each pairwise addition and the final rounding) minus what flushing
removed
([`MatrixCore.pairwise_eft`](https://github.com/pauljiang03/HardwarePrimitives/blob/main/matrix-core/MatrixCore/EFT/CDNA2.lean#L109)).
On the order example above the hardware returns `1 + 2^-21`, and the
correction returns `1 + 3·2^-23`.
