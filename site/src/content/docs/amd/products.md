---
title: 2. Exact products in denormalized form
description: Products are formed exactly and kept in denormalized form, and the sum of the input exponents decides alignment on CDNA 3.
---

Each product `p_ℓ = a_ℓ · b_ℓ` is computed **exactly**, and the hardware keeps
it in **denormalized form**: it does not normalize the product. The
significand of a product of two significands in `[0, 2)` lies in `[0, 4)`,
and the exponent the alignment sees is the plain **sum of the input
exponents**, `e_p = e_a + e_b`. The model keeps that distinction.

## `Unpacked.mul`

```lean
def Unpacked.mul (a b : Unpacked) : Unpacked :=
  ⟨a.negative != b.negative, a.m * b.m, a.e + b.e, a.t + b.t⟩

def Prepared.p (x : Prepared) : List Unpacked := List.zipWith Unpacked.mul x.a x.b
```

[`Unpacked.mul`](https://github.com/pauljiang03/HardwarePrimitives/blob/main/amd/MatrixCore/Numerics/Format.lean#L88)
multiplies the integer significands exactly, adds the exponents and adds the
mantissa widths (an fp16 × fp16 product has 20 mantissa bits). Nothing is
rounded, and the value is exact:

```lean
theorem Unpacked.value_mul (a b : Unpacked) : (a.mul b).value = a.value * b.value
```

The exact `Σ p_ℓ + c` of the paper's Eq. (1) is `Prepared.exact`. Every error
bound and every correctness statement compares the output with it.

## The accumulator input is not a product

On a Tensor Core, `C` enters the same list of terms as the products and
competes with them for the alignment exponent. On the AMD matrix cores it
does not:

- **CDNA 1** adds `c` to the products exactly, in the same sum.
- **CDNA 2** adds `c` last, in the final binary32 addition of the pairwise sum.
- **CDNA 3** aligns the products among themselves and adds `c` **late**, in a
  separate two-operand alignment ([CDNA 3](/HardwarePrimitives/amd/cdna3/#late-accumulation-of-c)).

This is why the AMD output is monotone in `c` on every configuration, while
the Tensor Core output is not
([CDNA 3 properties](/HardwarePrimitives/amd/properties/cdna3/#non-monotonicity)).

## Why the denormalized form matters

Two products with the same value can have different exponents. Take fp16
`1.5 × 1.5 = 2.25` and `2.25 × 1 = 2.25`:

| Product | Significand `s_p` | Exponent `e_p` | Value |
| --- | --- | --- | --- |
| `1.5 × 1.5` | `1.5 × 1.5 = 2.25`, in `[1, 4)` | `0 + 0 = 0` | `2.25` |
| `2.25 × 1` | `1.125 × 1 = 1.125` | `1 + 0 = 1` | `2.25` |

On CDNA 3 the first puts the alignment grid one bit **finer** than the second,
so the other products keep a bit more, and the two blocks of
[the worked trace](/HardwarePrimitives/amd/#a-worked-trace) give different outputs
([`MatrixCore.cdna3F16_products_not_determined`](https://github.com/pauljiang03/HardwarePrimitives/blob/main/amd/MatrixCore/MC/ProductMonotonicity.lean#L202)).
The output of CDNA 3 is therefore not a function of the products' values.

A **subnormal operand** makes the difference extreme. Its significand is below
one but its exponent is the minimum normal exponent, so a product with a
subnormal operand can have a tiny value and a large exponent sum. fp16
`2^-24 × 2^15` has the value `2^-9` but the exponent `−14 + 15 = 1`. Raising a
product to such a representation can coarsen the grid for every other product
of the block, which is the mechanism of CDNA 3's non-monotonicity in the
products.

## Product overflow

The products are exact rationals, so they never overflow inside the model by
themselves. The architectures differ in what they do with a large product:

- **CDNA 3** treats a product with `|p_ℓ| ≥ 2^128` as an infinity before
  accumulation (`Model.productOverflow`); the finite model reports
  `productOverflow`, and `blockOutcome` the infinity.
- **CDNA 1** keeps products above `2^128` exact inside the block; only the final
  conversion can overflow.
- **CDNA 2** converts each product to binary32, and that conversion can
  overflow (`intermediateOverflow`).

## A bound used later

```lean
theorem products_bounded {px : Prepared} (ha : ∀ u ∈ px.a, u.m < 2 ^ (u.t + 1))
    (hb : ∀ u ∈ px.b, u.m < 2 ^ (u.t + 1)) : ∀ p ∈ px.p, p.m < 2 ^ (p.t + 2)

theorem Unpacked.absQ_value_lt2 {u : Unpacked} (hm : u.m < 2 ^ (u.t + 2)) :
    absQ u.value < pow2 (u.e + 2)
```

Every product in denormalized form is less than `4 · 2^(e_p)` in magnitude.
After alignment, this gives each product at most `23 + padding + 2` magnitude
bits, which the [accumulator-width theorems](/HardwarePrimitives/amd/cdna3/#a-fixed-width-register-model)
rely on.
