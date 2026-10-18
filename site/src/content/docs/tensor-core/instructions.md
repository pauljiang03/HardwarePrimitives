---
title: 7. Instructions and chaining
description: Instructions made of several block FMAs are modeled as an ordered sequence of blocks, each feeding its FP32 output to the next as C.
---

A single MMA instruction often covers more products than one block FMA. A
WMMA `m16n16k16` FP16 tile, for example, has inner dimension `k = 16`. On
V100 (FMA size `K = 4`) that is four block FMAs. The model treats such an
instruction as a **left-to-right chain of blocks**: each block's FP32 output
becomes the next block's `C`.

## Running a chain

```lean
def runBlocks (p : Model) :
    F32 → List (List (p.Word × p.Word)) → Except ModelError (List BlockTrace)
  | _, [] => .ok []
  | c, ps :: rest =>
    match evalBlock (p := p) ⟨ps, c⟩ with
    | .error e => .error e
    | .ok t => match runBlocks p t.output.bits rest with
      | .error e => .error e
      | .ok ts => .ok (t :: ts)
```

The value passed along the chain is the encoded **output word**, not an
exact rational. Rounding between block FMAs is therefore part of the model,
as it is on hardware.

## Instruction variants

```lean
structure InstructionVariant where
  name : String
  k : ℕ                 -- inner dimension of the instruction
  nfma : ℕ              -- K, the FMA size N_FMA
  padding : ℕ           -- p, the padding bits
  eAlignMin : Option ℤ  -- the minimum alignment exponent
  evidence : String     -- where the parameters come from
  nfmaPos : 0 < nfma
  kDiv : nfma ∣ k

def InstructionVariant.schedule (p : InstructionVariant) (pairs : List (F16 × F16)) :=
  chunks p.nfma p.blocks pairs              -- k / K contiguous block FMAs, increasing k
```

| Variant | Lowering | Block FMAs × K |
| --- | --- | --- |
| `v100Wmma16` | `HMMA.884` | 4 × 4 |
| `ampereWmma16` (A100, Ada) | `HMMA.1688` | 2 × 8 |
| `hopperWmma16` (H100, H200, B200) | `HMMA.16816` | 1 × 16 |

## Inner products of any length

`Model.dot` sums any number of products the way the *Accurate Models*
toolbox's `GEMM.m` does: the products, in increasing `k`, are padded with
zero pairs to a multiple of `K` and cut into consecutive block FMAs, chained
through `C`. A recorded FP8 row of 32 products is two block FMAs on Ada
(`K = 16`) and one on Hopper and B200 (`K = 32`). `Model.dot_one_block`
proves that `K` products are one block FMA.

`Model.dotThenAdd` runs the block FMAs from `C = 0` and adds `C` afterwards in
FP32, rounded to nearest even (`addFp32_nearestEven`). This is not
how a block FMA adds `C`. On the recorded B200 FP8 outputs, from `mma.sync`,
it agrees with the FP8 `mma.sync` model (`mmaSyncFP8Dot`: two interleaved
FP16 block FMAs, then `C` added the same way), and the
[replay](/HardwarePrimitives/tensor-core/validation/) checks both.

## Proven properties of chains

- [`runBlocks_residual_ledger`](https://github.com/pauljiang03/HardwarePrimitives/blob/main/tensor-core/TensorCore/TC/Composition.lean#L93):
  the exact sum of all inputs equals the final output plus the sum of the
  losses recorded by every block FMA, alignment and final rounding included.
- `zero_products_passthrough`: a block FMA whose products are all zero returns its
  finite `C` unchanged. The theorem excludes `C = −0`.
- `single_block_output`: if only the first block FMA has nonzero products, the
  instruction returns that block's output.
- `InstructionVariant.schedule_flatten`: the schedule is a partition of the
  inputs in order.

`Conforms p device` is a predicate, not a theorem: whenever the model
produces an output, the device function produces the same bits. Hardware
conformance is checked by testing, not proven.
