---
title: 1. Formats and decoding
description: How encoded FP16, BF16, TF32, FP8, and FP32 words become exact values with exponent metadata.
---

The model starts from bit patterns, not real numbers. Decoding has two jobs:
classify the word as zero, subnormal, normal, infinity, or NaN, and keep the
**exponent** that the hardware uses for alignment (for a subnormal, the
minimum normal exponent).

## Formats

A [`Format`](https://github.com/pauljiang03/MMAlgebra/blob/main/TensorCore/Numerics/Defs.lean#L7)
is a triple of stored mantissa bits, exponent bits, and bias:

```lean
structure Format where
  mantissaBits : ℕ
  exponentBits : ℕ
  bias : ℤ

def fp16 : Format := ⟨10, 5, 15⟩
def bf16 : Format := ⟨7, 8, 127⟩
def tf19 : Format := ⟨10, 8, 127⟩    -- TF32's 19 value bits
def fp32 : Format := ⟨23, 8, 127⟩
def fp64 : Format := ⟨52, 11, 1023⟩
def e5m2 : Format := ⟨2, 5, 15⟩      -- FP8 E5M2
def e4m3 : Format := ⟨3, 4, 7⟩       -- FP8 E4M3 layout (decoded by its own rule)
def e4m3x : Format := ⟨3, 5, 7⟩      -- E4M3 values, one more exponent bit
```

The width is `1 + exponentBits + mantissaBits`, so a word of format `f` has
type `BitVec f.width`.

## Decoded values keep their exponent

```lean
structure Decoded where
  significand : ℤ      -- significand bits, hidden bit included, with the sign
  exponent : ℤ         -- unbiased exponent as stored in the word
  mantissaBits : ℤ     -- how many low bits of `significand` lie after the binary point

def Decoded.value (x : Decoded) : ℚ :=
  (x.significand : ℚ) * pow2 (x.exponent - x.mantissaBits)
```

A `Decoded` stores the value as **significand, exponent, and mantissa
width**, not as a single rational. For an input, `mantissaBits` is simply its
format's mantissa width: 10 for FP16, 7 for BF16, 23 for FP32. For example
FP16 `1.5` is significand `1536`, exponent `0`, 10 mantissa bits:
`1536 · 2^(0 − 10) = 1.5`. `value` recovers the rational exactly,
and alignment reads `exponent`.

[`classifyNat`](https://github.com/pauljiang03/MMAlgebra/blob/main/TensorCore/Numerics/Encoding.lean#L8)
implements standard IEEE field extraction:

```lean
def classifyNat (f : Format) (n : ℕ) : Classification :=
  let mantissa := n % 2 ^ f.mantissaBits
  let exponent := n / 2 ^ f.mantissaBits % 2 ^ f.exponentBits
  let negative := n / 2 ^ (f.mantissaBits + f.exponentBits) != 0
  let signed (m : ℕ) : ℤ := if negative then -(m : ℤ) else m
  if exponent = 2 ^ f.exponentBits - 1 then
    if mantissa = 0 then .infinity negative else .nan
  else if exponent = 0 then
    if mantissa = 0 then .zero negative
    else .subnormal ⟨signed mantissa, 1 - f.bias, f.mantissaBits⟩
  else .normal ⟨signed (2 ^ f.mantissaBits + mantissa),
    (exponent : ℤ) - f.bias, f.mantissaBits⟩
```

Points to note:

- **Subnormals** get exponent `1 − bias`, the minimum normal exponent, and no
  hidden bit. A subnormal therefore aligns as the hardware treats it: at the
  format's minimum exponent, with a small significand.
- **Zero** decodes to `⟨0, 0, 0⟩`. Its sign is discarded on input. Because the
  significand is zero, zero never takes part in choosing the
  [alignment exponent](/MMAlgebra/model/alignment/).
- **Infinity and NaN** map to `none` through
  [`Classification.finite`](https://github.com/pauljiang03/MMAlgebra/blob/main/TensorCore/Numerics/Encoding.lean#L23),
  and the block is rejected with `ModelError.nonfiniteInput`. The model covers
  finite arithmetic only.

## Preparing a block

`prepare` decodes `C` as FP32 and every operand in the model's input format. If
any of them is nonfinite, it returns `none`:

```lean
def prepareProducts (p : Model) (ps : List (p.Word × p.Word)) :
    Option (List (Decoded × Decoded)) :=
  ps.mapM fun (a, b) => do
    return (← p.decode a, ← p.decode b)

def prepare {p : Model} (x : BlockInput p) : Option PreparedBlock :=
  match decode32 x.c, prepareProducts p x.products with
  | some c, some ps => some ⟨p, ps, c⟩
  | _, _ => none
```

The result, a `PreparedBlock`, records the model, the decoded pairs, and the
decoded `C`. Every later stage is a function of a `PreparedBlock`.

## TF32: register words and packed values

On the GPU, a TF32 operand sits in a 32-bit register whose low 13 bits are
ignored. The model separates the two concerns:

- `tf19 : Format` is the 19-bit value format (1 sign, 8 exponent, 10 mantissa
  bits) that the block model uses.
- [`tf32Register`](https://github.com/pauljiang03/MMAlgebra/blob/main/TensorCore/Numerics/Format.lean#L51)
  is an `OperandEncoding` whose 32-bit words must have 13 zero low bits.
  `tf32Unpack` extracts the 19 value bits.

The theorem
[`tf32_eq_spec`](https://github.com/pauljiang03/MMAlgebra/blob/main/TensorCore/TC/Specification/Supported.lean#L57)
proves that, on register words whose low 13 bits are zero, the register-level
invocation gives the same bits as the *Accurate Models* specification (`IndependentSpec`). Words whose low
bits are not zero are rejected rather than silently masked.

## FP8: E5M2 and E4M3

The two FP8 formats differ at the top of their range.

- **E5M2** follows IEEE 754, so `classifyNat e5m2` decodes it: exponent
  `11111` is `±∞` (`0x7c`, `0xfc`) or NaN (`0x7d`–`0x7f`, `0xfd`–`0xff`), and
  the largest value is 57344 (`0x7b`).
- **E4M3** is the variant without infinities. Its all-ones exponent `1111`
  holds finite values (256 to 448, the largest at `0x7e`), and its only NaNs
  are `S.1111.111` (`0x7f`, `0xff`). The IEEE rule would make `0x78` an
  infinity, so E4M3 is decoded by the `finiteTopNaN` rule of
  [`ValueFormat`](https://github.com/pauljiang03/MMAlgebra/blob/main/TensorCore/Numerics/Format.lean#L13),
  as the operand encoding `e4m3Encoding`.

[`e4m3_specials`](https://github.com/pauljiang03/MMAlgebra/blob/main/TensorCore/Numerics/FP8.lean#L58), [`e4m3_max`](https://github.com/pauljiang03/MMAlgebra/blob/main/TensorCore/Numerics/FP8.lean#L71), [`e5m2_specials`](https://github.com/pauljiang03/MMAlgebra/blob/main/TensorCore/Numerics/FP8.lean#L64) and [`e5m2_max`](https://github.com/pauljiang03/MMAlgebra/blob/main/TensorCore/Numerics/FP8.lean#L78) prove these facts by computation over all 256 words of each format, and the
replay compares both decoders with an independent Python decoder on all 512
words.

The block model decodes its operands with the IEEE rule, so it takes E4M3
values in `e4m3x`, a 9-bit layout with one more exponent bit and E4M3's bias:
E4M3's top binade is then an ordinary binade, and subnormals keep the minimum
exponent −6. `widenE4M3` maps each E4M3 word to its `e4m3x` word (the NaNs to
NaNs), and the decodings agree on all 256
words ([`e4m3_decode_widen`](https://github.com/pauljiang03/MMAlgebra/blob/main/TensorCore/Numerics/FP8.lean#L43)), as `tf32Unpack` does for TF32.

## Proved properties of the encoding layer

- [`signedFiniteBinaryBijection`](https://github.com/pauljiang03/MMAlgebra/blob/main/TensorCore/Numerics/Binary/SignedBijection.lean#L130):
  finite encodings correspond one to one with representable values paired
  with a zero sign. Subnormals and both zeros are included, and both inverse
  laws are proved.
- `Decoded.Bounded`: every decoded significand, subnormal or not, is less
  than 2 in magnitude relative to its exponent. The accumulator-width proofs
  use this bound.
