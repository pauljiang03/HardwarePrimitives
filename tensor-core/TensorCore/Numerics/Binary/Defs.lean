import TensorCore.Numerics.Encoding

/-! Canonical algebraic representations and their finite encoded domain. -/

namespace TensorCore

/-- Canonical arithmetic data, including a sign for either zero. -/
structure BinaryRep (f : Format) where
  negative : Bool
  exponent : ℤ
  significand : ℕ
  exponent_min : f.emin ≤ exponent
  exponent_max : exponent ≤ f.emax
  significand_lt : significand < 2 ^ (f.mantissaBits + 1)
  normalized : 2 ^ f.mantissaBits ≤ significand ∨ exponent = f.emin
  deriving DecidableEq

theorem BinaryRep.ext {f : Format} {a b : BinaryRep f}
    (hs : a.negative = b.negative) (he : a.exponent = b.exponent)
    (hk : a.significand = b.significand) : a = b := by
  cases a
  cases b
  simp_all

def BinaryRep.value {f : Format} (r : BinaryRep f) : ℚ :=
  (if r.negative then -(r.significand : ℚ) else r.significand) *
    pow2 (r.exponent - f.mantissaBits)

/-- Words whose IEEE classification is finite, including both zeros. -/
abbrev FiniteBinaryWord (f : Format) := { bits : BitVec f.width // ∃ d, (classify f bits).finite = some d }

structure SignedFiniteValue (f : Format) where
  value : ℚ
  negative : Bool
  finite : f.FiniteValue value
  sign_nonzero : value ≠ 0 → negative = decide (value < 0)

end TensorCore
