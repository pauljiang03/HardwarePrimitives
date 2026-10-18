---
title: "4. CDNA 2: pairwise sums"
description: The block semantics of CDNA 2 (MI210, MI250) - flushed inputs, products converted to FP32, and a balanced tree of FP32 additions with c added last.
---

CDNA 2 does not align its products. It converts each product to FP32 and
adds the products in a balanced tree of FP32 additions, then adds `c`. The
paper calls this configuration `pair_wise_sum`. Inputs and outputs have no
subnormals: subnormal inputs are flushed to zero, and every `fl{·}` flushes a
subnormal result to zero.

## Variants

| Variant | Lean model | Inputs | `N_FMA` | Formula |
| --- | --- | --- | ---: | --- |
| CDNA 2 FP16 | `cdna2F16` | FP16 | 4 | `fl{c + fl{fl{p₁ + p₂} + fl{p₃ + p₄}}}` |
| CDNA 2 BF16 | `cdna2BF16` | BF16 | 2 | `fl{c + fl{p₁ + p₂}}` |
| CDNA 2 BF16 `_1k` | `cdna2BF16_1k` | BF16 | 4 | `fl{c + fl{fl{p₁ + p₂} + fl{p₃ + p₄}}}` |

Each `p_ℓ` in the formulas is `fl{a_ℓ b_ℓ}` of the flushed inputs. The FP32
instructions of CDNA 2 are the SFMA ([CDNA 1](/HardwarePrimitives/amd/cdna1/#the-sfma)).

```lean
def cdna2F16 : Model :=
  { a := .packed fp16, b := .packed fp16, nfma := 4, accumulation := .pairWiseSum,
    subnormals := false }
```

## Flushing the inputs

```lean
/-- Flush a subnormal (significand below one) to a zero of the same sign. -/
def Unpacked.flush (x : Unpacked) : Unpacked := if x.m < 2 ^ x.t then { x with m := 0 } else x

def Prepared.flushed (x : Prepared) : Prepared := ⟨x.a.map Unpacked.flush, x.b.map Unpacked.flush, x.c.flush⟩
```

A product with a subnormal operand counts as zero, however large the other
operand is.

## The pairwise tree

```lean
/-- `fl{x}` as a value: FP32 RNE, subnormal results flushed when `ftz`; `none` on overflow. -/
def flValue (ftz : Bool) (x : ℚ) : Option ℚ := (fl32 ftz x).bind value32

def pairwiseGroupSum (ftz : Bool) : ℕ → List ℚ → Option ℚ
  | _, [] => some 0
  | _, [x] => some x
  | 0, _ => none
  | depth + 1, xs => do
    let h := xs.length / 2
    let u ← pairwiseGroupSum ftz depth (xs.take h)
    let v ← pairwiseGroupSum ftz depth (xs.drop h)
    flValue ftz (u + v)

def pairwiseSum (P : Model) (x : Prepared) : Option ℚ := do
  let x' := if P.subnormals then x else x.flushed
  let ps ← x'.p.mapM fun p => flValue (!P.subnormals) p.value
  let t ← pairwiseGroupSum (!P.subnormals) ps.length ps
  return x'.c.value + t
```

`pairwiseSum` returns `S_acc = c + t`, the exact sum of `c` and the pairwise
sum; the final `fl{·}` rounds it. The model computes exactly the formulas of
the table:

```lean
theorem pairwiseSum_four (P : Model) (x : Prepared) (p₁ p₂ p₃ p₄ : Unpacked)
    (hp : (if P.subnormals then x else x.flushed).p = [p₁, p₂, p₃, p₄]) :
    pairwiseSum P x = do
      let q₁ ← flValue (!P.subnormals) p₁.value
      let q₂ ← flValue (!P.subnormals) p₂.value
      let q₃ ← flValue (!P.subnormals) p₃.value
      let q₄ ← flValue (!P.subnormals) p₄.value
      let u ← flValue (!P.subnormals) (q₁ + q₂)
      let v ← flValue (!P.subnormals) (q₃ + q₄)
      let t ← flValue (!P.subnormals) (u + v)
      return (if P.subnormals then x else x.flushed).c.value + t
```

([`MatrixCore.pairwiseSum_four`](https://github.com/pauljiang03/HardwarePrimitives/blob/main/amd/MatrixCore/MC/PairWiseSum.lean#L21),
[`MatrixCore.pairwiseSum_two`](https://github.com/pauljiang03/HardwarePrimitives/blob/main/amd/MatrixCore/MC/PairWiseSum.lean#L39).)

## Intermediate overflow

A product conversion or a pairwise sum can overflow, which the finite model
reports as `intermediateOverflow`. On the hardware the overflow is an
infinity that propagates by IEEE 754 rules, which `blockOutcome` follows, so
`p₁ = 2^128, p₂ = −2^128` gives NaN, as the paper observes.

## Example

With `s = 2^-23 + 2^-24` (`1.5·2^-12 × 2^-11`), the products `1, s, s, 0` and
`s, s, 1, 0` give different words, because the pairs are rounded separately:

```text
1, s, s, 0:   fl{fl{1 + s} + fl{s + 0}}  =  1 + 2^-21
s, s, 1, 0:   fl{fl{s + s} + fl{1 + 0}}  =  1 + 2^-22 + 2^-23
```

```lean
import MatrixCore

open MatrixCore

example :
    blockBits (P := cdna2F16) ⟨[0x3C00, 0x0E00, 0x0E00, 0], [0x3C00, 0x1000, 0x1000, 0], 0⟩ =
      .ok 0x3F800004 ∧
    blockBits (P := cdna2F16) ⟨[0x0E00, 0x0E00, 0x3C00, 0], [0x1000, 0x1000, 0x3C00, 0], 0⟩ =
      .ok 0x3F800003 := by decide +kernel
```

The [CDNA 2 properties](/HardwarePrimitives/amd/properties/cdna2/) bound the
error of each rounding and say when the output can fall as a product rises.
