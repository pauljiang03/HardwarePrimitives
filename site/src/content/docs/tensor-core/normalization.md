---
title: 5. Normalization and final rounding
description: The aligned sum is normalized and then truncated to an FP32 word, with explicit range and signed-zero behavior.
---

*Accurate Models* describes the last step as **normalization followed by the
final rounding mode**: "the rounding mode at both the alignment and
post-normalization stages is truncation", and on Hopper "upon normalization,
results are truncated rather than rounded". In its MATLAB code this is
`norm_helper` (the "Normalisation Helper Function") with the final rounding
mode `frmode = 'rz'`.

The step has two parts:

1. **Normalization** shifts the aligned sum so that its leading 1
   becomes the top bit of the significand, and adjusts the exponent to match.
   This loses nothing.
2. **Final rounding** is **truncation**: it keeps the 24 most significant
   bits of the magnitude, drops the rest, and keeps the sign. The code calls
   this mode `.truncate`. For a negative number this is not rounding down
   (floor). This is the second lossy step of the model, after alignment.

Because the model keeps the sum as an exact rational, both parts are done by
one function, `round32`. It finds the exponent of the sum (normalization) and
truncates the significand to 24 bits (final rounding):

```lean
def evalPrepared (b : PreparedBlock) : Except ModelError BlockTrace :=
  match round32 .truncate b.accumulator with
  | none => .error .accumulatorOutOfRange
  | some bits => match finite32 (truncateMantissa32 b.model.outputMantissaBits bits) with
    | none => .error .nonfiniteOutput
    | some d => .ok ⟨b, d⟩
```

`truncateMantissa32 m` keeps the leading `m` mantissa bits of the FP32 word and
clears the others, a truncation to `m` mantissa bits for normal and subnormal
words alike. Every variant has `m = 23`, which changes nothing, except the FP8
block FMAs of Ada and Hopper: their block output is truncated to a 13-bit
mantissa, as the *Accurate Models* toolbox's `GEMM.m` sets (`NoManBitsOut = 13`). Truncating to 24 bits and then to 14 is the same as truncating
to 14 once, so the FP8 output is still a single truncation of the exact sum.

## `round32`: normalize and round an exact rational to FP32

[`round32`](https://github.com/pauljiang03/HardwarePrimitives/blob/main/tensor-core/TensorCore/Numerics/RoundOp.lean#L52)
supports two modes, `truncate` and `nearestEven`. EFT uses the second. The
algorithm is:

1. If `x = 0`, return `+0`.
2. **Normalize:** find the binary exponent `e` of `|x|` (`magnitudeExponent`), clamped below
   at `−126` so that subnormals use the fixed grid `2^-149` (`normExp`).
3. **Final rounding:** scale `|x|` onto the grid `2^(e−23)` and keep 24 bits:
   the floor of the magnitude for truncation, `rneInt` for nearest-even
   (`roundedSignificand`).
4. If rounding produced `2^24`, carry into the next binade (`carry`).
5. If the exponent passes 127, fail. Otherwise assemble sign, exponent, and
   mantissa bits (`encode32`).

```lean
def round32Core (mode : RoundingMode) (x : ℚ) : Option F32 :=
  if x = 0 then some 0
  else
    let (e', k') := carry (normExp (absQ x)) (roundedSignificand mode (absQ x))
    if e' > 127 then none else some (encode32 (decide (x < 0)) e' k')

def round32 (mode : RoundingMode) (x : ℚ) : Option F32 :=
  if absQ x > maxFinite32 then none else round32Core mode x
```

## Truncation, not IEEE round toward zero

*Accurate Models* calls this step truncation; its MATLAB code configures it
with `frmode = 'rz'`. The model uses the word truncation and does not claim
IEEE 754 round-toward-zero behavior. Valpey et al.,
[*An SMT Formalization of Mixed-Precision Matrix Multiplication: Modeling
Three Generations of Tensor Cores*](https://arxiv.org/abs/2502.15999), showed
that Tensor Core results follow none of the IEEE 754 rounding modes,
round toward zero included. Bits are already truncated during alignment,
before the addition, so the result can differ from the exact sum rounded
toward zero. In this model the final truncation acts on the aligned sum,
which is exact at that point. The overall result is *not* the exact input
sum rounded toward zero, and the [error bound](/HardwarePrimitives/tensor-core/properties/error-bounds/)
accounts for both truncations.

## Range: the model is finite-only

An accumulator larger in magnitude than `maxFinite32 = (2^24 − 1)·2^104`
**rejects** the block with `accumulatorOutOfRange`. The model does not
produce infinity. This is a deliberate restriction of scope: the *Accurate Models*
model and the validation data cover finite outputs. The accepted domain is
stated exactly:

```lean
theorem evalBlock_success_iff (p : Model) (x : BlockInput p) :
    (∃ t, evalBlock x = .ok t) ↔
      x.products.length = p.nfma ∧
        ∃ b, prepare x = some b ∧ absQ b.accumulator ≤ maxFinite32
```

## Signed zero

- An accumulator that is exactly zero produces `+0`. Input zeros were already
  unsigned on decoding.
- A negative nonzero accumulator that truncates to zero produces `−0`
  (`encode32` keeps the sign bit with all significand bits zero).

The independent specification states the sign bit explicitly, and the
equality proof covers it bit for bit.

## How the rounding is specified

`round32` is an algorithm. Its correctness is proven against
specifications that do not mention it:

- **Truncation:** the [independent
  specification](/HardwarePrimitives/tensor-core/specification/) describes truncation by ordering:
  the result is the finite FP32 value with the largest magnitude lying
  between 0 and `x`. `supported_eq_spec` proves `round32 .truncate` meets
  this on every supported input.
- **Nearest even:** `NearestEven32 x b` says that `b` decodes to a finite
  value at least as close to `x` as any finite FP32 value, and that `b` has
  an even final bit whenever a different value is equally close.
  [`round32_nearestEven_correct`](https://github.com/pauljiang03/HardwarePrimitives/blob/main/tensor-core/TensorCore/Numerics/CorrectRounding.lean#L153)
  proves `round32 .nearestEven` meets it on the whole finite range.
- **Any binary format:**
  [`roundBinary_correct`](https://github.com/pauljiang03/HardwarePrimitives/blob/main/tensor-core/TensorCore/Numerics/Binary/RoundingContract.lean#L17)
  gives the same contract for well-formed formats and modes in general. FP64
  (DMMA) and multi-stage rounding use it.
