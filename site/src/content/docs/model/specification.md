---
title: 8. Independent specification
description: A second, separately written formalization of the Accurate Models Tensor Core model, and the proof that evalBlock agrees with it on every encoded input.
---

An executable model can be wrong in subtle ways: an off-by-one exponent, a
truncation in the wrong direction, a mishandled subnormal. To guard against
this, TC-EFT contains a **second formalization**, written independently,
that follows *Accurate Models* (Khattak and Mikaitis) §4.1 (Figures 2, 3, 5
and Table 3) as closely as possible. In Lean it is the `IndependentSpec`
namespace, and the theorems relating it to the model end in `_eq_spec`. Lean proves the two agree on **every** encoded input.

## How the specification differs

[`TensorCore/TC/Specification/Defs.lean`](https://github.com/pauljiang03/TC-EFT/blob/main/TensorCore/TC/Specification/Defs.lean)
imports only Lean's standard library and a notation file. It shares no
definitions with the implementation and is written in a different style:

| Concern | Implementation (`evalBlock`) | Specification (`IndependentSpec`) |
| --- | --- | --- |
| Decoding | `classifyNat` → `Decoded` (significand, unnormalized exponent, mantissa bits) | `decode` → `Term` (rational value, exponent) |
| Products | `unnormalizedMul` on significand bits | `product`: value product, exponent sum |
| Largest exponent | left fold with `filterMap` | right fold, `joinExponent` |
| Truncation | `truncBits` | `keptBits`: sign × ⌊‖v‖ / q⌋ |
| FP32 rounding | algorithm `round32 .truncate` | **relation** `Rounds`: the largest-magnitude finite FP32 value between 0 and `x`, with the sign bit fixed |
| Output | computable `Except` | `noncomputable` `Classical.choose` of the unique word satisfying `Result` |

The rounding entry matters most. The specification does not describe *how*
to round. It describes *what* the rounded value is, by quantifying over every
finite FP32 encoding:

```lean
def Rounds (x : ℚ) (bits : BitVec 32) : Prop :=
  (bits.toNat / 2147483648 != 0) = decide (x < 0) ∧
  ∃ d, value32 bits = some d ∧ Between x d ∧
    ∀ other y, value32 other = some y → Between x y → magnitude y ≤ magnitude d
```

## The equality theorem

```lean
/-- Every supported GPU path and every input, with failures observed as none. -/
theorem supported_eq_spec (path : Path) (x : BlockInput (implementationModel path)) :
    (evalBlock x).toOption.map (fun t => t.output.bits) =
      bits (parameters path) (supportedInput path x)
```

- This holds **for all inputs**. It is a universal theorem, not a test over
  samples.
- **Rejections are included.** When `evalBlock` fails, the specification
  also has no valid output, and both sides are `none`.
- **It is not vacuous.** `supported_valid_success` shows that every input
  valid under the specification's own domain predicate makes `evalBlock`
  succeed with the specified bits.
- **Signed zero is covered.** The result is unique at the bit level,
  including the sign of zero.
- `tf32_eq_spec` extends the result to padded TF32 register words, and
  `machine_eq_spec` extends it to fixed-width accumulators of adequate
  width.

## Checking independence

Independence is checked mechanically. The audit in
[`tests/TensorCoreTests/Specification/Audit.lean`](https://github.com/pauljiang03/TC-EFT/blob/main/tests/TensorCoreTests/Specification/Audit.lean)
walks every constant used by the specification's types **and proof terms**,
transitively, and fails if any comes from the implementation rather than
`Init`, `Std`, or `Lean`. The recorded run audited 181 specification
declarations and found no implementation dependencies. A negative control
confirms that the audit rejects a deliberately contaminated definition.

## What this does and doesn't establish

The equality shows that the executable model **is** the *Accurate Models*
model, as transcribed. Both rest on the same reading of *Accurate Models*.
If that model differs from the hardware in some region, both formalizations inherit
that difference. That risk is what the [hardware
replay](/TC-EFT/model/validation/) addresses.
