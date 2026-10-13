---
title: 7. Instructions and chaining
description: Multi-group instructions are modeled as an ordered sequence of blocks, each feeding its FP32 output to the next as C.
---

A single MMA instruction often covers more products than one normalization
group. A WMMA `m16n16k16` FP16 tile, for example, has inner dimension
`k = 16`. On V100 (`K = 4`) that is four groups. The model treats such an
instruction as a **left-to-right chain of blocks**: each group's FP32 output
becomes the next group's `C`.

## Running a chain

```lean
def runBlocks (p : Profile) :
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
exact rational. Rounding between groups is therefore part of the model, as
it is on hardware.

## Instruction paths

```lean
structure InstructionVariant where
  name : String
  k : ℕ                 -- inner dimension of the instruction
  products : ℕ          -- K, products per group
  extraBits : ℕ
  floor : Option ℤ
  evidence : String     -- where the parameters come from
  nfmaPos : 0 < products
  kDiv : products ∣ k

def InstructionVariant.schedule (p : InstructionVariant) (pairs : List (F16 × F16)) :=
  chunks p.products p.groups pairs          -- k / K contiguous groups, increasing k
```

| Path | Lowering | Groups × K |
| --- | --- | --- |
| `v100Wmma16` | `HMMA.844` | 4 × 4 |
| `ampereWmma16` | `HMMA.1688` | 2 × 8 |
| `hopperWmma16` | `HMMA.16816` | 1 × 16 |

## Proved properties of chains

- [`runBlocks_residual_ledger`](https://github.com/pauljiang03/TC-EFT/blob/main/TensorCore/TC/Composition.lean#L95):
  the exact sum of all inputs equals the final output plus the sum of the
  losses recorded by every group, alignment and final rounding included.
- `zero_products_passthrough`: a group whose products are all zero returns its
  finite `C` unchanged. The theorem excludes `C = −0`.
- `single_group_output`: if only the first group has nonzero products, the
  instruction returns that group's output.
- `InstructionVariant.schedule_flatten`: the schedule is a partition of the
  inputs in order.

`Conforms p device` is a predicate, not a theorem: whenever the model
produces an output, the device function produces the same bits. Hardware
conformance is checked by testing, not proved.
