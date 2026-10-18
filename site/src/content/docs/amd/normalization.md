---
title: 6. Normalization and final rounding
description: S_acc is normalized and rounded to nearest even in FP32, with explicit range, flushing, signed-zero and special-value behavior.
---

Every configuration ends the same way: `d = fl{S_acc}`. The accumulated value
is **normalized** (its leading 1 becomes the top bit of a 24-bit significand,
but never below FP32's minimum normal exponent) and **rounded to nearest
even**. This is the main difference from the Tensor Cores, whose final step is
a truncation. Because `S_acc` is an exact rational, one function does both:

```lean
/-- Binade exponent of a nonzero magnitude, not below `−126` (subnormal-aware normalization). -/
def normExp (a : ℚ) : ℤ := max (log2Floor a) (-126)

def rneFields (a : ℚ) : ℤ × ℕ :=
  let e := normExp a
  let k := rneInt (a / pow2 (e - 23))
  if k = 16777216 then (e + 1, 8388608) else (e, k.toNat)

/-- `fl{x}`: FP32 RNE; `none` exactly when the rounded magnitude exceeds the finite range. -/
def rne32 (x : ℚ) : Option F32 :=
  if x = 0 then some 0
  else
    let (e, m) := rneFields (absQ x)
    if e > 127 then none else some (encode32 (decide (x < 0)) e m)

/-- `fl{x}` with optional flushing of subnormal results to a zero of the same sign (CDNA 2). -/
def fl32 (ftz : Bool) (x : ℚ) : Option F32 :=
  match rne32 x with
  | none => none
  | some w => some (if ftz && isSubnormal32 w then signedZero32 w else w)
```

The algorithm finds the exponent of `|x|`, clamped at `−126` so that subnormal
results use the fixed grid `2^-149`; scales `|x|` onto the grid `2^(e − 23)`;
rounds to the nearest integer with ties to even (`rneInt`); carries a
significand of `2^24` into the next binade; and fails if the exponent passes
127. `evalBlock` applies it to `S_acc`, with flushing on the models without
subnormals:

```lean
      | .ok s =>
        match fl32 (!P.subnormals) s with
        | none => .error .outputOverflow
        | some d => .ok ⟨px, s, d⟩
```

## Round to nearest even, after the earlier losses

The final rounding is IEEE round to nearest even, but the result is not the
exact `Σ p_ℓ + c` rounded to nearest even except on CDNA 1 and the SFMA: on
CDNA 2 the products and partial sums were rounded before, and on CDNA 3 the
products were truncated and `c` rounded down before. The model rounds `S_acc`,
and the error bounds of each generation
([CDNA 2](/HardwarePrimitives/amd/properties/cdna2/#error-bounds),
[CDNA 3](/HardwarePrimitives/amd/properties/cdna3/#error-bounds)) account for
all the losses.

## Range: the model is finite-only

`fl{x}` is finite exactly below the IEEE overflow threshold
`2^128 − 2^103`:

```lean
theorem rne32_isSome_iff (x : ℚ) : (rne32 x).isSome ↔ absQ x < overflowThreshold32
```

Beyond it, the block is rejected with `outputOverflow`; the infinity the
hardware returns comes from `blockOutcome` ([below](#special-values)). The
accepted domain is stated exactly:

```lean
theorem evalBlock_success_iff {P : Model} (x : BlockInput P) :
    (∃ t, evalBlock x = .ok t) ↔
      x.a.length = P.nfma ∧ x.b.length = P.nfma ∧
        ∃ px s, prepare x = some px ∧ accumulate P px = .ok s ∧ absQ s < overflowThreshold32
```

| `ModelError` | Meaning | Observed by the hardware as |
| --- | --- | --- |
| `wrongLength` | `a` or `b` does not have `N_FMA` words | not an input |
| `nonfiniteInput` | an operand is an infinity or NaN | infinity or NaN |
| `productOverflow` | CDNA 3: some `\|p_ℓ\| ≥ 2^128` | infinity or NaN |
| `intermediateOverflow` | CDNA 2: an intermediate `fl{·}` overflowed | infinity or NaN |
| `outputOverflow` | `fl{S_acc}` overflowed | infinity of the sign of `S_acc` |

## Flushing (CDNA 2)

On CDNA 2 every `fl{·}`, the final one included, replaces a subnormal result
by a zero of the same sign:

```lean
theorem flValue_true {x v : ℚ} (h : flValue true x = some v) :
    (v = rneValue x ∧ (v = 0 ∨ pow2 (-126) ≤ absQ v)) ∨
      (v = 0 ∧ rneValue x ≠ 0 ∧ absQ (rneValue x) < pow2 (-126))
```

That is, it returns the nearest-even value when that value is zero or normal,
and zero when it is subnormal.

## Signed zero

- An exact zero `S_acc` gives `+0`.
- A nonzero `S_acc` that rounds or flushes to zero keeps its sign.

The paper does not test zero signs; the [paper
notes](https://github.com/pauljiang03/HardwarePrimitives/blob/main/matrix-core/docs/paper-notes.md)
record the choice.

## How the rounding is specified

`rne32` is an algorithm. Its correctness is proved against a specification
that does not mention it:

- **Nearest even:** `NearestEven32 x w` says that `w` decodes to a finite value
  at least as close to `x` as any finite FP32 value, with an even last bit
  when two are equally close.
  [`MatrixCore.rne32_nearestEven`](https://github.com/pauljiang03/HardwarePrimitives/blob/main/matrix-core/MatrixCore/Numerics/RoundingContract.lean#L312)
  proves that every result of `rne32` meets it.
- **Uniqueness:** within the finite range, the correctly rounded word with the
  sign of the input is unique
  ([`MatrixCore.rne32_iff`](https://github.com/pauljiang03/HardwarePrimitives/blob/main/matrix-core/MatrixCore/Numerics/Uniqueness.lean#L356)).
- **The block output:** on every model with subnormals, `d` is the nearest
  FP32 value to `S_acc`, ties to even
  ([`MatrixCore.evalBlock_nearestEven`](https://github.com/pauljiang03/HardwarePrimitives/blob/main/matrix-core/MatrixCore/MC/AcceptedDomain.lean#L54)).

## Special values

The paper reports that infinities are detected at the input, that `+∞` with
`−∞` gives NaN (with a negative sign), and that CDNA 3 maps `|p_ℓ| ≥ 2^128`
to an infinity by magnitude. `blockOutcome` implements these rules. Finite
inputs follow the model, with its overflows; when an operand or `c` is
infinite or NaN, the result is decided at the input from the operands, `c`,
and the products that overflow, as in a chained inner product whose earlier
block overflowed. On CDNA 2 an intermediate overflow is an infinity that
propagates by IEEE 754 rules, so `p₁ = 2^128, p₂ = −2^128` gives NaN, as the
paper observes.

`blockOutcome` agrees with `evalBlock` wherever the result is finite:

```lean
theorem blockOutcome_finite_iff {P : Model} (x : BlockInput P) (d : F32) :
    blockOutcome x = some (.finite d) ↔ blockBits x = .ok d
```

The special-value layer is a definition following the paper's description,
checked against its vectors and the MATLAB models, not derived.
