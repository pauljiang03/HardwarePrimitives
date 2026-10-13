---
title: 4. Accumulation
description: The aligned terms are added exactly, and a fixed-width register model is proved to agree at adequate width.
---

After alignment every term is a run of bits whose lowest bit is at `2^(η−F)`.
The hardware adds these bit strings in a single multi-term addition, in a
fixed-point adder. The model adds them exactly:

```lean
def PreparedBlock.accumulator (b : PreparedBlock) : ℚ :=
  (sumZ b.alignedBits : ℚ) * pow2 b.alignGridExponent
```

Accumulation is exact and does not depend on order. All the loss happens in
[alignment](/TC-EFT/model/alignment/) and in the final
[normalization and final rounding](/TC-EFT/model/normalization/). Exactness is a modeling choice, so
the library also models a finite register and proves the two agree.

## A fixed-width register model

[`TensorCore/TC/Accumulator.lean`](https://github.com/pauljiang03/TC-EFT/blob/main/TensorCore/TC/Accumulator.lean)
describes accumulation as a hardware register would perform it: `w`-bit
two's-complement additions that wrap on overflow, applied one aligned term at
a time.

```lean
/-- Actual modular signed-word additions, starting from a supplied register. -/
def machineAccumulate (w : ℕ) (acc : BitVec w) : List ℤ → BitVec w
  | [] => acc
  | z :: zs => machineAccumulate w (acc + BitVec.ofInt w z) zs

def evalBlockMachine (w : ℕ) {p : Model} (x : BlockInput p) : Except ModelError BlockTrace
  -- identical to evalBlock, but accumulates with machineAccumulate w
```

## The width theorem

Each aligned term has at most `F + 2` magnitude bits (products in denormalized
form have a significand below 4, hence two integer bits). There are `K + 1` terms, counting `C`. So `F + 2`
magnitude bits, plus `⌈log₂(K+1)⌉` extra carry bits, plus one sign bit, are always
enough:

```lean
/-- All encoded inputs have identical reference and machine results at any adequate width. -/
theorem evalBlockMachine_eq {p : Model} (x : BlockInput p) (w F carryBits : ℕ)
    (hF : p.alignFracBits = F) (hcount : p.nfma + 1 ≤ 2 ^ carryBits)
    (hw : F + 2 + carryBits + 1 ≤ w) : evalBlockMachine w x = evalBlock x
```

For the FP16 models this gives concrete widths, which hold for **every**
encoded input:

| Theorem | Model | Register width |
| --- | --- | --- |
| `v100_machine_eq` | V100 FP16, K = 4, F = 23 | 29 bits |
| `ampere_machine_eq` | A100 FP16, K = 8, F = 24 | 31 bits |
| `hopper_machine_eq` | H100 FP16, K = 16, F = 25 | 33 bits |

These widths count the two's complement sign bit. Without it they are 28, 30
and 32 bits; the A100 and H100 values are the adder widths *Accurate Models*
reports (§4.1.2 and §4.1.6).

[`evalBlock_machinePrefix`](https://github.com/pauljiang03/TC-EFT/blob/main/TensorCore/TC/AlignmentExponent.lean#L186)
goes further. Every **prefix** of the accumulation is exact at that width,
so the result does not depend on the order of additions, even with
cancellation.

## Why this matters

The exact accumulator is a sound abstraction of a real adder **at any
adequate width**. The theorems identify that width. The model neither assumes
nor proves which width a particular GPU uses. It shows that any adder of at
least this width yields the same output word, so the exact sum is a safe
abstraction rather than an extra assumption.
