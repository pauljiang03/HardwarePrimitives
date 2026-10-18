import TensorCore.Numerics.Exact

/-! Binary formats and their exact decoded values. -/

namespace TensorCore

structure Format where
  mantissaBits : ℕ
  exponentBits : ℕ
  bias : ℤ
  deriving Repr, DecidableEq

@[implicit_reducible] def fp16 : Format := ⟨10, 5, 15⟩
@[implicit_reducible] def fp32 : Format := ⟨23, 8, 127⟩
@[implicit_reducible] def Format.width (f : Format) : ℕ := 1 + f.exponentBits + f.mantissaBits
abbrev F16 := BitVec 16
abbrev F32 := BitVec 32

/-- A finite value: `significand · 2^(exponent − mantissaBits)`. -/
structure Decoded where
  /-- Signed integer significand, hidden bit included (e.g. `1.5` in FP16 is `1536`). -/
  significand : ℤ
  /-- Unbiased exponent as stored in the word; the minimum normal exponent for subnormals. -/
  exponent : ℤ
  /-- Bits of `significand` after the binary point; the format's mantissa width for an input. -/
  mantissaBits : ℤ
  deriving Repr, DecidableEq

def Decoded.value (x : Decoded) : ℚ :=
  (x.significand : ℚ) * pow2 (x.exponent - x.mantissaBits)

inductive Classification where
  | zero (negative : Bool)
  | subnormal (value : Decoded)
  | normal (value : Decoded)
  | infinity (negative : Bool)
  | nan
  deriving Repr, DecidableEq

/-- A nonempty normal range and at least one stored mantissa bit. -/
def Format.WellFormed (f : Format) : Prop := 0 < f.mantissaBits ∧ 1 < f.exponentBits

instance (f : Format) : Decidable f.WellFormed := inferInstanceAs (Decidable (_ ∧ _))

@[implicit_reducible] def bf16 : Format := ⟨7, 8, 127⟩
/-- TF32 values as a 19-bit format; the 32-bit register layout is `tf32Register`. -/
@[implicit_reducible] def tf19 : Format := ⟨10, 8, 127⟩
@[implicit_reducible] def fp64 : Format := ⟨52, 11, 1023⟩

def Format.emin (f : Format) : ℤ := 1 - f.bias
def Format.emax (f : Format) : ℤ := ((2 ^ f.exponentBits - 2 : ℕ) : ℤ) - f.bias
def Format.maxFinite (f : Format) : ℚ :=
  ((2 ^ (f.mantissaBits + 1) - 1 : ℕ) : ℚ) * pow2 (f.emax - f.mantissaBits)

/-- A decoded significand, including a subnormal, has magnitude below two. -/
def Decoded.Bounded (d : Decoded) : Prop := absQ d.value < 2 * pow2 d.exponent

/-- Finite FP32 values in arithmetic form. -/
def FiniteValue32 (z : ℚ) : Prop :=
  ∃ k e : ℤ, -126 ≤ e ∧ e ≤ 127 ∧ k.natAbs < 2 ^ 24 ∧ z = (k : ℚ) * pow2 (e - 23)

/-- Finite values of a format in arithmetic form. -/
def Format.FiniteValue (f : Format) (z : ℚ) : Prop :=
  ∃ k e : ℤ, f.emin ≤ e ∧ e ≤ f.emax ∧ k.natAbs < 2 ^ (f.mantissaBits + 1) ∧
    z = (k : ℚ) * pow2 (e - f.mantissaBits)

structure BinaryBijection (α β : Type) where
  encode : α → β
  decode : β → α
  decode_encode : ∀ a, decode (encode a) = a
  encode_decode : ∀ b, encode (decode b) = b

end TensorCore
