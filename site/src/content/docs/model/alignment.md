---
title: 3. Alignment
description: The alignment exponent η, the minimum alignment exponent, the grid 2^(η−F), and truncation.
---

Alignment is where a Tensor Core loses information, and it is the core of the
model. All terms (`C` and the `K` products in denormalized form) are put on one fixed-point
grid. Anything below the grid is discarded.

## Step 1: the alignment exponent η

```lean
/-- A nonempty maximum ignores zero terms; none explicitly represents an all-zero block. -/
def maxTermExp (ts : List DenormalizedProduct) : Option ℤ :=
  (ts.filterMap fun t => if t.significand = 0 then none else some t.exponent).foldl
    (fun acc e => some (match acc with | none => e | some v => max v e)) none

/-- The minimum alignment exponent only raises a nonempty maximum; an all-zero block stays `none`. -/
def Model.applyEAlignMin (p : Model) : Option ℤ → Option ℤ
  | none => none
  | some e => some (match p.eAlignMin with | none => e | some f => max e f)

def PreparedBlock.alignExp (b : PreparedBlock) : Option ℤ :=
  b.model.applyEAlignMin (maxTermExp b.terms)
```

- η is the **largest exponent among the nonzero terms**. Zero terms are
  skipped, so a zero product never coarsens the grid.
- If every term is zero, η is `none`. The accumulator is then exactly zero
  and the output is `+0`.
- Ampere and Hopper have a **minimum alignment exponent** `e_align^min`
  (`−132` and `−133`): η is capped from below by it. It only matters when every
  term is tiny, for example products of subnormals. It then coarsens the grid
  and flushes those terms to zero. V100 has no minimum alignment exponent.

## Step 2: the grid

```lean
def PreparedBlock.alignGridExponent (b : PreparedBlock) : ℤ :=
  b.alignExp.getD 0 - b.model.alignMantissaBits
```

The grid spacing is `2^(η − F)`, where `F = alignMantissaBits = 23 + p`. Here `p`
is the number of **padding bits** the architecture keeps
beyond FP32's 23-bit mantissa: 0 on V100, 1 on A100, 2 on H100. A larger `p` gives
a finer grid, so less is lost.

## Step 3: truncation

```lean
/-- Signed magnitude truncation. -/
def truncBits (x : ℚ) (e : ℤ) : ℤ :=
  if x < 0 then -((-x / pow2 e).floor) else (x / pow2 e).floor

def truncGrid (x : ℚ) (e : ℤ) : ℚ := (truncBits x e : ℚ) * pow2 e

def PreparedBlock.alignedBits (b : PreparedBlock) : List ℤ :=
  b.terms.map fun t => truncBits t.value b.alignGridExponent
```

[`truncBits`](https://github.com/pauljiang03/HardwarePrimitives/blob/main/TensorCore/Numerics/Exact.lean#L70)
takes the floor of the **magnitude** and restores the sign. This is the
sign-magnitude shifter of the hardware: it **truncates** the magnitude and
keeps the sign. For a negative term this is not the same as rounding down
(toward −∞). Each term keeps only its bits at or above the grid's lowest bit
`2^(η − F)`. `truncBits` returns those kept bits, with the sign, counted in
units of that lowest bit; `alignedBits` lists them for every term.

## What is lost

The discarded parts are named and tracked:

```lean
def PreparedBlock.alignmentResiduals (b : PreparedBlock) : List ℚ :=
  b.terms.map fun t => t.value - truncGrid t.value b.alignGridExponent
```

Each residual is strictly smaller in magnitude than one grid step, and has the
same sign as its term:

```lean
theorem alignment_residual_bounds (x : ℚ) (e : ℤ) :
    -pow2 e < x - truncGrid x e ∧ x - truncGrid x e < pow2 e
```

These residuals are what [TC-EFT](/HardwarePrimitives/properties/eft/) recovers, and the
first half of the [error bound](/HardwarePrimitives/properties/error-bounds/).

## Example: a small term disappears

V100, `F = 23`, `C = 1.0`, one product `2^-24`:

- η = max(exponent of `C` = 0, exponent of the product = −24) = 0.
- Grid = `2^(0 − 23) = 2^-23`.
- The product's only bit is at `2^-24`, below the grid's lowest bit `2^-23`,
  so all its bits are dropped and the product is lost.

Four such products are lost the same way, although together they are
`2^-22`, which an FP32 result near 1 could represent. Lowering `C` slightly
moves η to −1 and keeps all four: that is the
[non-monotonicity](/HardwarePrimitives/properties/non-monotonicity/) mechanism.
