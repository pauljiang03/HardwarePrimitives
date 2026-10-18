---
title: "3. CDNA 1: correct rounding"
description: The block semantics of CDNA 1 (MI100) and of the FP32 instructions of every generation - full-precision products, an exact sum, one final rounding.
---

CDNA 1 keeps the products in full precision, adds `c` with them, adds
exactly, and rounds once. The paper calls this configuration
`correct_rounding` (a Kulisch accumulator). The FP32 instructions of all
three generations use the same configuration with one product per block, a
sequential FMA (SFMA).

## Variants

| Variant | Lean model | Inputs | `N_FMA` | Notes |
| --- | --- | --- | ---: | --- |
| CDNA 1 FP16 | `cdna1F16` | FP16 | 4 | |
| CDNA 1 BF16 | `cdna1BF16` | BF16 | 2 | products may exceed `2^128` inside a block |
| FP32 on CDNA 1, 2 and 3 | `sfmaF32` | FP32 | 1 | chained one product at a time |

```lean
def cdna1F16 : Model :=
  { a := .packed fp16, b := .packed fp16, nfma := 4, accumulation := .correctRounding }

def cdna1BF16 : Model :=
  { a := .packed bf16, b := .packed bf16, nfma := 2, accumulation := .correctRounding }

def sfmaF32 : Model :=
  { a := .packed fp32, b := .packed fp32, nfma := 1, accumulation := .correctRounding }
```

Subnormals are supported in input and output.

## The exact sum

There is no alignment and no intermediate rounding: `S_acc` is the exact
`Σ p_ℓ + c` of the paper's Eq. (1).

```lean
def Prepared.exact (x : Prepared) : ℚ := sumQ (x.p.map Unpacked.value) + x.c.value

-- in accumulate
    | .correctRounding => .ok x.exact
```

The final `fl{·}` then rounds the exact sum to nearest even
([normalization and final rounding](/HardwarePrimitives/matrix-core/normalization/)), so
the output is the correctly rounded sum of the block.

## Range

The products are exact rationals and may exceed `2^128` inside the block; only
the final conversion can overflow.
A block is accepted exactly when its inputs are finite and the exact sum is
below the overflow threshold:

```lean
theorem correctRounding_success_iff {P : Model} (hacc : P.accumulation = .correctRounding)
    (hov : P.productOverflow = false) (x : BlockInput P) :
    (∃ t, evalBlock x = .ok t) ↔
      x.a.length = P.nfma ∧ x.b.length = P.nfma ∧
        ∃ px, prepare x = some px ∧ absQ px.exact < overflowThreshold32
```

## The SFMA

The FP32 instructions compute `(…((c + p₁) + p₂) + …)`: `sfmaF32` blocks of one
product, chained through `c` by `dotBits`. `c` and `p₁` are combined first,
and the result is the `c` of the rest
([`MatrixCore.dotBits_sfma_cons`](https://github.com/pauljiang03/HardwarePrimitives/blob/main/matrix-core/MatrixCore/MC/CompositionProperties.lean#L61)).
Each step is one correctly rounded fused multiply-add:

```lean
import MatrixCore

open MatrixCore

-- c = 1, p₁ = 2^-24, p₂ = 2^-23 (each as p · 1).
-- (c + p₁) ties to 1; adding 2^-23 then gives 1 + 2^-23.
example : dotBits sfmaF32 [0x33800000, 0x34000000] [0x3F800000, 0x3F800000] 0x3F800000 =
    .ok 0x3F800001 := by decide +kernel
```

Rounding after every product, the SFMA loses `p₁` here, which a single
`correct_rounding` block of two products would keep: `fl{1 + 2^-24 + 2^-23}`
is `1 + 2^-22`.

## Example

Four FP16 products `1 · 1` (`0x3C00 = 1`) with `c = 0`:

```lean
import MatrixCore

open MatrixCore

def ones : BlockInput cdna1F16 := ⟨List.replicate 4 0x3C00, List.replicate 4 0x3C00, 0⟩

example : blockBits ones = .ok 0x40800000 := by decide +kernel
```

The result is the FP32 encoding of `4`. The [CDNA 1
properties](/HardwarePrimitives/matrix-core/properties/cdna1/) follow from the exact
sum: correct rounding, an error of at most half an ulp, monotonicity in every
input, and independence of the order of the products.
