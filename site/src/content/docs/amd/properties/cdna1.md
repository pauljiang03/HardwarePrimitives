---
title: CDNA 1
description: Properties of the CDNA 1 model and of the SFMA - correct rounding, an error of at most half an ulp, monotonicity in every input, and independence of the order of the products.
---

CDNA 1 forms the exact sum of a block and rounds it once
([semantics](/HardwarePrimitives/amd/cdna1/)), and so does every step of the
SFMA of the FP32 instructions. Every property on this page follows from that:
the output depends on the inputs only through the exact `Σ a_ℓ b_ℓ + c`, and
it does so as `fl{·}` does. The theorems hold for every model with the
`correct_rounding` configuration, subnormals and no product overflow, which
are `cdna1F16`, `cdna1BF16` and `sfmaF32`.

## Correct rounding

An accepted block returns the FP32 value nearest to the exact sum, ties
to even:

```lean
theorem correctRounding_nearestEven {P : Model} (hacc : P.accumulation = .correctRounding)
    (hov : P.productOverflow = false) (hs : P.subnormals = true)
    {x : BlockInput P} {t : BlockTrace P} (h : evalBlock x = .ok t) :
    t.sAcc = t.prepared.exact ∧ NearestEven32 t.prepared.exact t.d
```

Each SFMA step is the value nearest to `c + a·b`
([`MatrixCore.sfma_step_nearestEven`](https://github.com/pauljiang03/HardwarePrimitives/blob/main/matrix-core/MatrixCore/MC/CompositionProperties.lean#L79)),
so an FP32 inner product is a chain of correctly rounded fused multiply-adds,
`c` and `p₁` first. A chain is not the correctly rounded inner product: it
rounds after every product ([example](/HardwarePrimitives/amd/cdna1/#the-sfma)).

## Error bounds

Only the final rounding loses, by at most half an ulp of the exact sum:

```lean
theorem correctRounding_error {P : Model} (hacc : P.accumulation = .correctRounding)
    (hov : P.productOverflow = false) (hs : P.subnormals = true)
    {x : BlockInput P} {t : BlockTrace P} (h : evalBlock x = .ok t) :
    absQ (t.prepared.exact - wordValue t.d) ≤ halfUlp32 t.prepared.exact
```

From the inputs alone, with `A = Σ|p_ℓ| + |c|`, the error is at most
`2^-24 · A + 2^-150`
([`MatrixCore.correctRounding_apriori`](https://github.com/pauljiang03/HardwarePrimitives/blob/main/matrix-core/MatrixCore/MC/AprioriBounds.lean#L67)).
For inner products of any length the blocks' bounds add up
([instructions and chaining](/HardwarePrimitives/amd/instructions/#proved-properties-of-chains)).

## Monotonicity

The output is monotone in the exact sum, hence in every product and in `c`:

```lean
theorem correctRounding_exact_monotone {P : Model} (hacc : P.accumulation = .correctRounding)
    (hov : P.productOverflow = false) (hs : P.subnormals = true)
    {x x' : BlockInput P} {t t' : BlockTrace P} (h : evalBlock x = .ok t) (h' : evalBlock x' = .ok t')
    (he : exactDot P x.a x.b x.c ≤ exactDot P x'.a x'.b x'.c) : wordValue t.d ≤ wordValue t'.d
```

- [`MatrixCore.correctRounding_product_monotone`](https://github.com/pauljiang03/HardwarePrimitives/blob/main/matrix-core/MatrixCore/MC/ProductMonotonicity.lean#L58):
  raising any products and `c` never lowers the output.
- [`MatrixCore.correctRounding_not_nonmonotone`](https://github.com/pauljiang03/HardwarePrimitives/blob/main/matrix-core/MatrixCore/MC/ProductMonotonicity.lean#L100),
  with instances `cdna1F16_not_nonmonotone`, `cdna1BF16_not_nonmonotone` and
  `sfmaF32_not_nonmonotone`: no pair of inputs has larger products, the same
  `c`, and a smaller output.
- [`MatrixCore.runBlocks_correctRounding_monotone`](https://github.com/pauljiang03/HardwarePrimitives/blob/main/matrix-core/MatrixCore/MC/ProductMonotonicity.lean#L76):
  the same for inner products of any length, block by block.

This is the contrast with CDNA 2, CDNA 3 and the NVIDIA Tensor Cores, which
are all non-monotone in some input.

## Order of the products and sign

The exact sum does not depend on the order of the products, so neither does
the output
([`MatrixCore.accumulate_perm`](https://github.com/pauljiang03/HardwarePrimitives/blob/main/matrix-core/MatrixCore/MC/Order.lean#L29)).
Rounding to nearest even is symmetric, so negating the exact sum negates the
output:

```lean
theorem correctRounding_neg {P : Model} (hacc : P.accumulation = .correctRounding)
    (hov : P.productOverflow = false) (hs : P.subnormals = true)
    {x y : BlockInput P} {t u : BlockTrace P} (hx : evalBlock x = .ok t)
    (hy : evalBlock y = .ok u) (hneg : u.prepared.exact = -t.prepared.exact) :
    value32 u.d = (value32 t.d).map (- ·)
```

## Accepted inputs

A block is accepted exactly when its inputs are finite and the exact sum is
below the overflow threshold `2^128 − 2^103`; products may exceed `2^128`
inside the block
([`MatrixCore.correctRounding_success_iff`](https://github.com/pauljiang03/HardwarePrimitives/blob/main/matrix-core/MatrixCore/MC/CorrectRounding.lean#L38)).

## MC-EFT correction

The [MC-EFT correction](/HardwarePrimitives/amd/properties/eft/) from the
block's output returns that output, since it is already the correctly rounded
sum
([`MatrixCore.correctRounding_eft`](https://github.com/pauljiang03/HardwarePrimitives/blob/main/matrix-core/MatrixCore/EFT/CDNA1.lean#L11)).
