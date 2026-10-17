---
title: 1. Formats and decoding
description: How encoded fp32, fp16, bf16, XF32 and fp8 FNUZ words become exact values with exponent metadata on the AMD model.
---

The model starts from bit patterns, not real numbers. Decoding has two jobs:
classify the word as a finite value, an infinity or NaN, and keep the
**exponent** that the hardware uses for alignment (for a subnormal or a zero,
the minimum normal exponent).

## Formats

A [`Format`](https://github.com/pauljiang03/HardwarePrimitives/blob/main/TensorCore/Numerics/Defs.lean#L7)
is a layout of exponent bits, stored mantissa bits and bias, with its rule for
special values:

```lean
structure Format where
  exponentBits : ℕ
  mantissaBits : ℕ
  bias : ℤ
  specials : Specials := .ieee     -- .ieee, or .fnuz: no infinities and no negative zero

def binary32 : Format := ⟨8, 23, 127, .ieee⟩   -- c and d on every variant
def binary16 : Format := ⟨5, 10, 15, .ieee⟩    -- fp16
def bfloat16 : Format := ⟨8, 7, 127, .ieee⟩    -- bf16
def tf19 : Format := ⟨8, 10, 127, .ieee⟩       -- the values of XF32
def e4m3fnuz : Format := ⟨4, 3, 8, .fnuz⟩      -- fp8-E4M3 FNUZ
def e5m2fnuz : Format := ⟨5, 2, 16, .fnuz⟩     -- fp8-E5M2 FNUZ
```

The width is `1 + exponentBits + mantissaBits`, so a word of format `f` has
type `BitVec f.width`.

| Paper | Lean | Precision | Minimum normal | Maximum |
| --- | --- | --- | --- | --- |
| binary32 (fp32) | `binary32` | 24 | `2^-126` | `(2 − 2^-23)·2^127` |
| tf19 (XF32) | `tf19`, `InputFormat.xf32` | 11 | `2^-126` | `(2 − 2^-10)·2^127` |
| bfloat16 (bf16) | `bfloat16` | 8 | `2^-126` | `(2 − 2^-7)·2^127` |
| binary16 (fp16) | `binary16` | 11 | `2^-14` | `65504` |
| fp8-E4M3 FNUZ | `e4m3fnuz` | 4 | `2^-7` | `240` |
| fp8-E5M2 FNUZ | `e5m2fnuz` | 3 | `2^-15` | `57344` |

## Decoded values keep their exponent

```lean
structure Unpacked where
  negative : Bool   -- the sign bit; it distinguishes the two zeros
  m : ℕ             -- the significand as an integer: s = m / 2^t
  e : ℤ             -- the exponent; the minimum normal exponent for subnormals and zero
  t : ℕ             -- mantissa bits of the significand

def Unpacked.value (x : Unpacked) : ℚ :=
  (if x.negative then -(x.m : ℚ) else (x.m : ℚ)) * pow2 (x.e - x.t)
```

An `Unpacked` value stores the significand `s = m / 2^t`, the exponent `e` and
the sign, not a single rational. For an input, `t` is its format's stored
mantissa width: 10 for fp16, 7 for bf16, 23 for binary32. For example fp16
`1.5` is `m = 1536`, `e = 0`, `t = 10`: `1536 · 2^(0 − 10) = 1.5`. `value`
recovers the rational exactly, and alignment reads `e`.

[`Format.decodeNat`](https://github.com/pauljiang03/HardwarePrimitives/blob/main/amd/MatrixCore/Numerics/Format.lean#L165)
extracts the fields and applies the format's rule for special values:

```lean
def unpackFields (f : Format) (negative : Bool) (E M : ℕ) : Unpacked :=
  if E = 0 then ⟨negative, M, f.emin, f.mantissaBits⟩
  else ⟨negative, 2 ^ f.mantissaBits + M, (E : ℤ) - f.bias, f.mantissaBits⟩

def decodeNat (f : Format) (n : ℕ) : Datum :=
  let M := n % 2 ^ f.mantissaBits
  let E := n / 2 ^ f.mantissaBits % 2 ^ f.exponentBits
  let negative := n / 2 ^ (f.mantissaBits + f.exponentBits) % 2 == 1
  match f.specials with
  | .ieee =>
    if E = 2 ^ f.exponentBits - 1 then (if M = 0 then .infinity negative else .nan)
    else .finite (f.unpackFields negative E M)
  | .fnuz =>
    if negative ∧ E = 0 ∧ M = 0 then .nan else .finite (f.unpackFields negative E M)
```

- **Subnormals and zero** get the minimum normal exponent `emin = 1 − bias`
  and no hidden bit, so their significand is below one.
- **IEEE formats** (binary32, fp16, bf16, tf19) reserve the top exponent
  field for infinities and NaN.
- **FNUZ formats** (the fp8 formats of CDNA 3) have no infinities: the top
  exponent field holds finite values, and the word that would be negative
  zero is the only NaN.

## XF32: binary32 words, truncated values

CDNA 3's XF32 instructions read binary32 words and keep ten mantissa bits.
An `InputFormat` says how an instruction reads an operand word:

```lean
inductive InputFormat where
  | packed (f : Format)   -- the word is a value of the format
  | xf32                  -- a binary32 word truncated to tf19

def InputFormat.truncateXF32 (x : Unpacked) : Unpacked := ⟨x.negative, x.m / 2 ^ 13, x.e, 10⟩

def InputFormat.read : (i : InputFormat) → i.Word → Datum
  | .packed f, w => f.decode w
  | .xf32, w =>
    match binary32.decode w with
    | .finite x => .finite (truncateXF32 x)
    | d => d
```

The significand is truncated toward zero, and NaN words are classified before
the truncation.

## Preparing a block

```lean
structure Prepared where
  a : List Unpacked
  b : List Unpacked
  c : Unpacked

def prepare {P : Model} (x : BlockInput P) : Option Prepared := do
  let a ← x.a.mapM fun w => (P.a.read w).toFinite
  let b ← x.b.mapM fun w => (P.b.read w).toFinite
  let c ← (binary32.decode x.c).toFinite
  return ⟨a, b, c⟩
```

`prepare` succeeds only when every operand and `c` is finite. On CDNA 2,
`Prepared.flushed` then replaces every subnormal input by a zero of the same
sign before the products are formed.

## Input words by value

`Format.encodeExact` and `InputFormat.encodeExact` return the word of a value
the format represents exactly, and `none` otherwise. The tests build every
input this way, so an input a format cannot represent fails the test instead
of being rounded silently.

## Proved properties of the encoding layer

- [`MatrixCore.decodeNat_bounded`](https://github.com/pauljiang03/HardwarePrimitives/blob/main/amd/MatrixCore/MC/Prepared.lean#L134)
  and [`MatrixCore.read_bounded`](https://github.com/pauljiang03/HardwarePrimitives/blob/main/amd/MatrixCore/MC/Prepared.lean#L148):
  every decoded significand, subnormal or not, is below `2^(t + 1)`, so a
  decoded value is less than 2 in magnitude relative to its exponent. The
  accumulator-width proofs use this bound.
- [`MatrixCore.Unpacked.value_onGrid`](https://github.com/pauljiang03/HardwarePrimitives/blob/main/amd/MatrixCore/Numerics/Format.lean#L129):
  a decoded value is an integer multiple of `2^(e − t)`.
- [`MatrixCore.rne32_iff`](https://github.com/pauljiang03/HardwarePrimitives/blob/main/amd/MatrixCore/Numerics/Uniqueness.lean#L370):
  within the finite range the correctly rounded binary32 word with the sign of
  the input is unique, which the [independent
  specification](/HardwarePrimitives/amd/specification/) uses to identify the output word.
