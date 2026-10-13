---
title: 2. Exact products in denormalized form
description: Products are formed exactly and kept in denormalized form, and the sum of the input exponents decides alignment.
---

Each product `aᵢ · bᵢ` is computed **exactly**, and the hardware keeps it in
**denormalized form**: it does not normalize the product. The significand of a product of two values in `[1, 2)` lies
in `[1, 4)`, and the exponent the alignment unit sees is the plain **sum of
the input exponents**. The model keeps that distinction.

## `DenormalizedProduct` and `denormalizedMul`

```lean
structure DenormalizedProduct where
  significand : ℤ
  exponent : ℤ
  mantissaBits : ℤ

def DenormalizedProduct.value (x : DenormalizedProduct) : ℚ :=
  (x.significand : ℚ) * pow2 (x.exponent - x.mantissaBits)

def denormalizedMul (a b : Decoded) : DenormalizedProduct :=
  ⟨a.significand * b.significand, a.exponent + b.exponent,
    a.mantissaBits + b.mantissaBits⟩
```

[`denormalizedMul`](https://github.com/pauljiang03/TC-EFT/blob/main/TensorCore/Numerics/DenormalizedProduct.lean#L25)
multiplies the significands exactly (no bits dropped), adds exponents, and adds mantissa widths
(an FP16 × FP16 product has 20 mantissa bits). Nothing is rounded. The value is exact:

```lean
theorem denormalizedProduct_value (a b : Decoded) :
    (denormalizedMul a b).value = a.value * b.value
```

## The accumulator input is a term too

`C` enters the same list of terms, with its own decoded exponent:

```lean
def PreparedBlock.terms (b : PreparedBlock) : List DenormalizedProduct :=
  ⟨b.c.significand, b.c.exponent, b.c.mantissaBits⟩ ::
    b.products.map fun (a, b) => denormalizedMul a b
```

So `C` competes with the products for the
[alignment exponent](/TC-EFT/model/alignment/), and it is truncated on the
same grid. This is why changing `C` can change how the products are rounded.

## Why the denormalized form matters

Here *denormalized* means *not normalized*, as in *Accurate Models* ("the
products remain denormalised"); it does not mean subnormal. Two products
with the same value can have different exponents. Take FP16
`1.5 × 1.5 = 2.25`:

| View | Significand | Exponent | Value |
| --- | --- | --- | --- |
| Denormalized form (what the model uses) | `1.5 × 1.5 = 2.25`, in `[1, 4)` | `0 + 0 = 0` | `2.25` |
| Normalized | `1.125`, in `[1, 2)` | `1` | `2.25` |

If this product has the largest exponent in its block FMA, the denormalized form puts the
grid one bit **finer** than a normalized view would. A model that normalized
products would truncate the other terms differently and give a different
answer. The worked examples and the independent specification both pin down
the convention for the exponent of a denormalized product. The specification states it explicitly:

```lean
/-- Exponents are added, even when the resulting significand is at least two. -/
def product (a b : Term) : Term := ⟨a.value * b.value, a.exponent + b.exponent⟩
```

## A bound used later

```lean
def DenormalizedProduct.Bounded (t : DenormalizedProduct) : Prop := absQ t.value < 4 * pow2 t.exponent
theorem denormalizedMul_bounded (a b : Decoded) (ha : a.Bounded) (hb : b.Bounded) :
    (denormalizedMul a b).Bounded
```

Every product in denormalized form is less than `4 · 2^exponent` in magnitude, and `C` is less
than `2 · 2^exponent`. After alignment, this gives each term at most `F + 2`
magnitude bits. The [accumulator-width theorems](/TC-EFT/model/accumulation/)
rely on that.
