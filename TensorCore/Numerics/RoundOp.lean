import TensorCore.Numerics.Encoding

/-! Normalization and final rounding to FP32. -/

namespace TensorCore

inductive RoundingMode where
  | truncate
  | nearestEven
  deriving Repr, DecidableEq

def emin32 : ℤ := -126
def maxFinite32 : ℚ := (2 ^ 24 - 1 : ℕ) * pow2 104

/-- Nearest integer with ties to even: floor, then a doubled-remainder comparison. -/
def rneInt (t : ℚ) : ℤ :=
  if 1 < 2 * (t - t.floor) ∨ (2 * (t - t.floor) = 1 ∧ t.floor % 2 = 1) then t.floor + 1
  else t.floor

/-- Integer coefficient selected on a nonnegative scaled magnitude. -/
def roundSignificand : RoundingMode → ℚ → ℤ
  | .truncate, t => t.floor
  | .nearestEven, t => rneInt t

/-- Called on positive magnitudes only; the public converter branches on zero first. -/
def magnitudeExponent (x : ℚ) : ℤ :=
  let e : ℤ := (x.num.natAbs.log2 : ℤ) - (x.den.log2 : ℤ)
  if x < pow2 e then e - 1 else e

/-- Bit pattern for sign, exponent `e`, and coefficient `k` on `2^(e-23)`. -/
def encode32 (negative : Bool) (e k : ℤ) : F32 :=
  BitVec.ofNat 32 ((if negative then 2 ^ 31 else 0) +
    (if k < 2 ^ 23 then k.toNat else (e + 127).toNat * 2 ^ 23 + (k - 2 ^ 23).toNat))

/-- Normalization: exponent of the leading 1, clamped to the subnormal range. -/
def normExp (m : ℚ) : ℤ := max (magnitudeExponent m) emin32

/-- Final rounding: the 24-bit significand on the grid `2^(normExp m - 23)`. -/
def roundedSignificand (mode : RoundingMode) (m : ℚ) : ℤ :=
  roundSignificand mode (m / pow2 (normExp m - 23))

/-- A coefficient of `2^24` carries into the next binade. -/
def carry (e k : ℤ) : ℤ × ℤ := if k = 2 ^ 24 then (e + 1, k / 2) else (e, k)

def round32Core (mode : RoundingMode) (x : ℚ) : Option F32 :=
  if x = 0 then some 0
  else
    let (e', k') := carry (normExp (absQ x)) (roundedSignificand mode (absQ x))
    if e' > 127 then none else some (encode32 (decide (x < 0)) e' k')

/-- Finite-range reference conversion. -/
def round32 (mode : RoundingMode) (x : ℚ) : Option F32 :=
  if absQ x > maxFinite32 then none else round32Core mode x

/-- Quantum exponent of an FP32 word: `E - 150` for a normal exponent field `E`, else `-149`. -/
def outputUlpExponent (b : F32) : ℤ :=
  max (((b.toNat / 2 ^ 23 % 2 ^ 8 : ℕ) : ℤ) - 127) emin32 - 23

theorem round32_range {mode : RoundingMode} {x : ℚ} {b : F32}
    (h : round32 mode x = some b) : absQ x ≤ maxFinite32 := by
  unfold round32 at h
  split at h
  · contradiction
  · grind

def magnitudeRounded (mode : RoundingMode) (m : ℚ) : ℚ :=
  (roundedSignificand mode m : ℚ) * pow2 (normExp m - 23)

def signedRounded (mode : RoundingMode) (x : ℚ) : ℚ :=
  if x < 0 then -magnitudeRounded mode (absQ x) else magnitudeRounded mode (absQ x)

/-- Nearest finite FP32 value, ties to an even low bit. -/
def NearestEven32 (x : ℚ) (b : F32) : Prop :=
  ∃ d : ℚ, value32 b = some d ∧
    (∀ y : ℚ, FiniteValue32 y → absQ (x - d) ≤ absQ (x - y)) ∧
    (∀ y : ℚ, FiniteValue32 y → y ≠ d →
      absQ (x - y) = absQ (x - d) → b.toNat % 2 = 0)

end TensorCore
