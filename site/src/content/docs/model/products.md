---
title: 2. Exact unnormalized products
description: Products are formed exactly and kept in denormalized form, and the sum of the input exponents decides alignment.
---

Each product `aᵢ · bᵢ` is computed **exactly**, and the hardware keeps it in
**denormalized form**: it does not normalize the product. The significand of a product of two values in `[1, 2)` lies
in `[1, 4)`, and the exponent the alignment unit sees is the plain **sum of
the input exponents**. The model keeps that distinction.

## `UnnormalizedProduct` and `unnormalizedMul`

```lean
structure UnnormalizedProduct where
  significand : ℤ
  unnormalizedExp : ℤ
  mantissaBits : ℤ

def UnnormalizedProduct.value (x : UnnormalizedProduct) : ℚ :=
  (x.significand : ℚ) * pow2 (x.unnormalizedExp - x.mantissaBits)

def unnormalizedMul (a b : Decoded) : UnnormalizedProduct :=
  ⟨a.significand * b.significand, a.unnormalizedExp + b.unnormalizedExp,
    a.mantissaBits + b.mantissaBits⟩
```

[`unnormalizedMul`](https://github.com/pauljiang03/TC-EFT/blob/main/TensorCore/Numerics/UnnormalizedProduct.lean#L20)
multiplies the significands exactly (no bits dropped), adds unnormalized exponents, and adds mantissa widths
(an FP16 × FP16 product has 20 mantissa bits). Nothing is rounded. The value is exact:

```lean
theorem unnormalizedProduct_value (a b : Decoded) :
    (unnormalizedMul a b).value = a.value * b.value
```

## The accumulator input is a term too

`C` enters the same list of terms, with its own decoded unnormalized exponent:

```lean
def PreparedBlock.terms (b : PreparedBlock) : List UnnormalizedProduct :=
  ⟨b.c.significand, b.c.unnormalizedExp, b.c.mantissaBits⟩ ::
    b.products.map fun (a, b) => unnormalizedMul a b
```

So `C` competes with the products for the
[alignment exponent](/TC-EFT/model/alignment/), and it is truncated on the
same grid. This is why changing `C` can change how the products are rounded.

## Why "unnormalized" matters

Two products with the same value can have different unnormalized exponents. Take FP16
`1.5 × 1.5 = 2.25`:

| View | Significand | Exponent | Value |
| --- | --- | --- | --- |
| Denormalized form (what the model uses) | `1.5 × 1.5 = 2.25`, in `[1, 4)` | `0 + 0 = 0` | `2.25` |
| Normalized | `1.125`, in `[1, 2)` | `1` | `2.25` |

If this product has the largest exponent in its block FMA, the denormalized form puts the
grid one bit **finer** than a normalized view would. A model that normalized
products would truncate the other terms differently and give a different
answer. The worked examples and the independent specification both pin down
the unnormalized-exponent convention. The specification states it explicitly:

```lean
/-- Unnormalized exponents are added, even when the resulting significand is at least two. -/
def product (a b : Term) : Term := ⟨a.value * b.value, a.exponent + b.exponent⟩
```

## A bound used later

```lean
def UnnormalizedProduct.Bounded (t : UnnormalizedProduct) : Prop := absQ t.value < 4 * pow2 t.unnormalizedExp
theorem unnormalizedMul_bounded (a b : Decoded) (ha : a.Bounded) (hb : b.Bounded) :
    (unnormalizedMul a b).Bounded
```

Every unnormalized product is less than `4 · 2^unnormalizedExp` in magnitude, and `C` is less
than `2 · 2^unnormalizedExp`. After alignment, this gives each term at most `F + 2`
magnitude bits. The [accumulator-width theorems](/TC-EFT/model/accumulation/)
rely on that.
