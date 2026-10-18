---
title: 7. Instructions and chaining
description: MFMA instructions as chains of blocks, inner products of any length, the SFMA, and D = AB + C.
---

An MFMA instruction usually covers more products than one block. Each element
of `D = AB + C` is an inner product of length `k`, evaluated in `⌈k / N_FMA⌉`
blocks, with zeros padding the last one; each block's FP32 output becomes
the next block's `c`. The instruction shapes `m × n × k` do not change the
arithmetic of an element, only how many elements there are.

## Running a chain

```lean
def runBlocks (P : Model) :
    F32 → List (List P.a.Word × List P.b.Word) → Except ModelError (List (BlockTrace P))
  | _, [] => .ok []
  | c, ab :: rest =>
    match evalBlock (P := P) ⟨ab.1, ab.2, c⟩ with
    | .error e => .error e
    | .ok t =>
      match runBlocks P t.d rest with
      | .error e => .error e
      | .ok ts => .ok (t :: ts)
```

The value passed along the chain is the encoded **output word**, not an exact
rational, so the rounding between blocks is part of the model, as it is on
hardware.

## Inner products of any length

```lean
def padToBlocks (n : ℕ) (xs : List (BitVec w)) : List (BitVec w) :=
  xs ++ List.replicate ((n - xs.length % n) % n) 0

def dotBits (P : Model) (a : List P.a.Word) (b : List P.b.Word) (c : F32) :
    Except ModelError F32 :=
  if a.length ≠ b.length then .error .wrongLength
  else (blocks P a b).foldlM (fun c ab => blockBits (P := P) ⟨ab.1, ab.2, c⟩) c
```

`blocks P a b` pads `a` and `b` with zero words to a multiple of `N_FMA` and
cuts them into consecutive blocks. For `k = 0`, which is not an instruction,
`dotBits` returns `c` unchanged. `dotOutcome` is the observation for any words,
infinities and NaN included, and `mfma` applies it to every element:

```lean
/-- `D = AB + C` with `A` given by rows, `B` by columns, and `C` by rows. -/
def mfma (P : Model) (A : List (List P.a.Word)) (B : List (List P.b.Word))
    (C : List (List F32)) : List (List (Option Outcome)) :=
  List.zipWith (fun row cRow => List.zipWith (fun col c => dotOutcome P row col c) B cRow) A C
```

## SFMA: one rounding per product

The FP32 instructions of CDNA 1, 2 and 3 are a sequential FMA,
`(…((c + p₁) + p₂) + …)`: `sfmaF32` is a `correct_rounding` block with
`N_FMA = 1`, chained by `dotBits`. `c` and `p₁` are combined first, and the
result is the `c` of the rest
([`MatrixCore.dotBits_sfma_cons`](https://github.com/pauljiang03/HardwarePrimitives/blob/main/matrix-core/MatrixCore/MC/CompositionProperties.lean#L61));
each step is the FP32 value nearest to `c + a·b`, ties to even
([`MatrixCore.sfma_step_nearestEven`](https://github.com/pauljiang03/HardwarePrimitives/blob/main/matrix-core/MatrixCore/MC/CompositionProperties.lean#L79)):

```lean
import MatrixCore

open MatrixCore

-- SFMA on FP32 inputs: c = 1, p₁ = 2^-24, p₂ = 2^-23 (each as p · 1).
-- (c + p₁) ties to 1; adding 2^-23 then gives 1 + 2^-23.
example : dotBits sfmaF32 [0x33800000, 0x34000000] [0x3F800000, 0x3F800000] 0x3F800000 =
    .ok 0x3F800001 := by decide +kernel
```

## Instruction shapes

`MatrixCore.instructions` lists the instruction shapes the paper gives, such as
`mfma_f32_32x32x8f16` and `mfma_f32_16x16x32_fp8_fp8`, with their architectures
and input kinds. Every output element of an instruction is one inner product
of length `k`; `m` and `n` do not change the arithmetic.

## Proved properties of chains

- [`MatrixCore.dotBits_exact_ledger`](https://github.com/pauljiang03/HardwarePrimitives/blob/main/matrix-core/MatrixCore/MC/InnerProduct.lean#L166):
  the exact `c + Σ_ℓ a_ℓ b_ℓ` of the whole vectors equals the output plus the
  residuals `exact − d` of all the blocks.
- [`MatrixCore.dotBits_exact_error`](https://github.com/pauljiang03/HardwarePrimitives/blob/main/matrix-core/MatrixCore/MC/InnerProduct.lean#L176):
  if every accepted block's residual is bounded by `B`, the output is within
  the sum of the blocks' bounds of the exact inner product.
- [`MatrixCore.mfma_error`](https://github.com/pauljiang03/HardwarePrimitives/blob/main/matrix-core/MatrixCore/MC/MFMA.lean#L44):
  each entry of `D = AB + C` is the observed inner product of its row and
  column, and a finite entry is within the sum of its blocks' bounds of the
  exact `c_ij + Σ_ℓ a_iℓ b_ℓj`.
- [`MatrixCore.evalBlock_contract`](https://github.com/pauljiang03/HardwarePrimitives/blob/main/matrix-core/MatrixCore/MC/Contract.lean#L36)
  and [`MatrixCore.dotBits_blocks`](https://github.com/pauljiang03/HardwarePrimitives/blob/main/matrix-core/MatrixCore/MC/Contract.lean#L178):
  every accepted block satisfies a contract bundling what is proved about it,
  with its output error bound, and any such property carries to every block of
  an inner product.
- [`MatrixCore.dotBits_c_monotone`](https://github.com/pauljiang03/HardwarePrimitives/blob/main/matrix-core/MatrixCore/MC/Monotonicity.lean#L629):
  an inner product of any length is monotone in its initial `c`.
