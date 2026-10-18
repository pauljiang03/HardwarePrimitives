import MatrixCore.Numerics.Grid

/-! # Floating-point formats and decoding

The formats of Table 1 and the decoding of words into exact values `(−1)^σ · (m / 2^t) · 2^e`. -/

namespace MatrixCore

/-- How a format uses its extreme encodings. -/
inductive Specials where
  /-- IEEE 754: the all-ones exponent field holds ±∞ (zero mantissa) and NaN. -/
  | ieee
  /-- FNUZ (CDNA 3 FP8): every exponent field is finite; the negative-zero word is the only NaN. -/
  | fnuz
  deriving Repr, DecidableEq

/-- A binary layout: a sign bit, a biased exponent field, and the stored mantissa bits. -/
structure Format where
  exponentBits : ℕ
  mantissaBits : ℕ
  bias : ℤ
  specials : Specials := .ieee
  deriving Repr, DecidableEq

namespace Format

@[implicit_reducible] def width (f : Format) : ℕ := 1 + f.exponentBits + f.mantissaBits

/-- Precision `f` of Table 1: stored mantissa bits plus the hidden bit. -/
def precision (f : Format) : ℕ := f.mantissaBits + 1

/-- Minimum normal exponent. -/
def emin (f : Format) : ℤ := 1 - f.bias

/-- Maximum finite exponent: the top field is finite only in FNUZ formats. -/
def emax (f : Format) : ℤ :=
  match f.specials with
  | .ieee => ((2 ^ f.exponentBits - 2 : ℕ) : ℤ) - f.bias
  | .fnuz => ((2 ^ f.exponentBits - 1 : ℕ) : ℤ) - f.bias

end Format

/-- FP32: the format of `c` and `d` on every variant. -/
@[implicit_reducible] def fp32 : Format := ⟨8, 23, 127, .ieee⟩
@[implicit_reducible] def fp16 : Format := ⟨5, 10, 15, .ieee⟩
@[implicit_reducible] def bf16 : Format := ⟨8, 7, 127, .ieee⟩
/-- TF32 values (AMD XF32): FP32's exponent range with 10 mantissa bits. -/
@[implicit_reducible] def tf19 : Format := ⟨8, 10, 127, .ieee⟩
/-- FP8 E4M3 FNUZ: precision 4, minimum normal `2^-7`, maximum `240`. -/
@[implicit_reducible] def e4m3fnuz : Format := ⟨4, 3, 8, .fnuz⟩
/-- FP8 E5M2 FNUZ: precision 3, minimum normal `2^-15`, maximum `57344`. -/
@[implicit_reducible] def e5m2fnuz : Format := ⟨5, 2, 16, .fnuz⟩

abbrev F32 := BitVec 32

/-- An unpacked finite value `(−1)^σ · (m / 2^t) · 2^e`. -/
structure Unpacked where
  /-- Sign bit `σ`; it distinguishes the two zeros. -/
  negative : Bool
  /-- Significand as an integer: `s = m / 2^t`. -/
  m : ℕ
  /-- Exponent `e`; the minimum normal exponent for subnormals and zero. -/
  e : ℤ
  /-- Mantissa bits of the significand. -/
  t : ℕ
  deriving Repr, DecidableEq

namespace Unpacked

def value (x : Unpacked) : ℚ :=
  (if x.negative then -(x.m : ℚ) else (x.m : ℚ)) * pow2 (x.e - x.t)

/-- Significand `s` of the paper. -/
def sig (x : Unpacked) : ℚ := (x.m : ℚ) / pow2 x.t

def isZero (x : Unpacked) : Bool := x.m == 0

/-- Exact product, not normalized: `s_p = s_a s_b ∈ [0, 4)` and `e_p = e_a + e_b`. -/
def mul (a b : Unpacked) : Unpacked :=
  ⟨a.negative != b.negative, a.m * b.m, a.e + b.e, a.t + b.t⟩

/-- Flush a subnormal (significand below one) to a zero of the same sign. -/
def flush (x : Unpacked) : Unpacked := if x.m < 2 ^ x.t then { x with m := 0 } else x

theorem value_eq_zero_iff (x : Unpacked) : x.value = 0 ↔ x.m = 0 := by
  unfold value
  have hp := pow2_ne_zero (x.e - x.t)
  constructor
  · intro h
    have h' : (x.m : ℚ) = 0 := by
      cases hn : x.negative <;> simp only [hn, Bool.false_eq_true, ↓reduceIte] at h <;>
        rcases Rat.mul_eq_zero.mp h with h | h <;> grind
    exact_mod_cast h'
  · intro h; simp [h]

theorem value_mul (a b : Unpacked) : (a.mul b).value = a.value * b.value := by
  unfold mul value
  have hexp : a.e + b.e - ((a.t + b.t : ℕ) : ℤ) = (a.e - a.t) + (b.e - b.t) := by omega
  simp only [hexp, pow2_add, Rat.natCast_mul]
  cases a.negative <;> cases b.negative <;> simp <;> grind

theorem value_neg_iff (x : Unpacked) : x.value < 0 ↔ x.negative = true ∧ x.m ≠ 0 := by
  unfold value
  have hp := pow2_pos (x.e - x.t)
  have hm : (0 : ℚ) ≤ x.m := Rat.natCast_nonneg
  cases hn : x.negative
  · simp only [Bool.false_eq_true, ↓reduceIte, false_and, iff_false]
    exact Rat.not_lt.mpr (Rat.mul_nonneg hm (Rat.le_of_lt hp))
  · simp only [↓reduceIte, true_and]
    constructor
    · intro h hz; simp [hz] at h
    · intro hz
      have : (0 : ℚ) < x.m := by
        have : 0 < x.m := Nat.pos_of_ne_zero hz
        exact_mod_cast this
      have := Rat.mul_pos this hp
      grind

theorem value_onGrid (x : Unpacked) : OnGrid x.value (x.e - x.t) := by
  unfold value
  cases x.negative
  · exact ⟨x.m, by simp [Rat.intCast_natCast]⟩
  · exact ⟨-(x.m : ℤ), by simp [Rat.intCast_neg, Rat.intCast_natCast]⟩

theorem absQ_value (x : Unpacked) : absQ x.value = (x.m : ℚ) * pow2 (x.e - x.t) := by
  unfold value
  have hp := pow2_pos (x.e - x.t)
  have hm : (0 : ℚ) ≤ x.m := Rat.natCast_nonneg
  cases x.negative
  · exact absQ_of_nonneg (Rat.mul_nonneg hm (Rat.le_of_lt hp))
  · simp only [↓reduceIte, Rat.neg_mul, absQ_neg]
    exact absQ_of_nonneg (Rat.mul_nonneg hm (Rat.le_of_lt hp))

end Unpacked

/-- Outcome of decoding a word. -/
inductive Datum where
  | finite (x : Unpacked)
  | infinity (negative : Bool)
  | nan
  deriving Repr, DecidableEq

def Datum.toFinite : Datum → Option Unpacked
  | .finite x => some x
  | _ => none

namespace Format

/-- Unpack the fields of a word whose exponent field is finite. -/
def unpackFields (f : Format) (negative : Bool) (E M : ℕ) : Unpacked :=
  if E = 0 then ⟨negative, M, f.emin, f.mantissaBits⟩
  else ⟨negative, 2 ^ f.mantissaBits + M, (E : ℤ) - f.bias, f.mantissaBits⟩

/-- Decode a word given as a natural number below `2 ^ f.width`. -/
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

def decode (f : Format) (w : BitVec f.width) : Datum := f.decodeNat w.toNat

end Format

/-- Finite value of an FP32 word, if any. -/
def value32 (w : F32) : Option ℚ := (fp32.decode w).toFinite.map Unpacked.value

/-! ## Matrix Core operand formats -/

/-- How an MFMA instruction reads an input word of `A` or `B`. -/
inductive InputFormat where
  /-- The word is a value of the format (FP32, FP16, BF16, FP8 FNUZ). -/
  | packed (f : Format)
  /-- CDNA 3 XF32: an FP32 word truncated to `tf19`'s 10 mantissa bits. -/
  | xf32
  deriving Repr, DecidableEq

namespace InputFormat

@[implicit_reducible] def width : InputFormat → ℕ
  | .packed f => f.width
  | .xf32 => 32

abbrev Word (i : InputFormat) := BitVec i.width

/-- Format whose values the hardware multiplies. -/
def format : InputFormat → Format
  | .packed f => f
  | .xf32 => tf19

/-- Truncate an FP32 significand to 10 mantissa bits, toward zero. -/
def truncateXF32 (x : Unpacked) : Unpacked := ⟨x.negative, x.m / 2 ^ 13, x.e, 10⟩

def read : (i : InputFormat) → i.Word → Datum
  | .packed f, w => f.decode w
  | .xf32, w =>
    match fp32.decode w with
    | .finite x => .finite (truncateXF32 x)
    | d => d

end InputFormat

end MatrixCore
