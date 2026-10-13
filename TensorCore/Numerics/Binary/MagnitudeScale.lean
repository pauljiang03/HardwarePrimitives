import TensorCore.Numerics.Binary.Encoding

/-! Magnitude bounds from decoded exponents. -/

namespace TensorCore

theorem decoded_normal_magnitude_lower (negative : Bool) (mantissa : ℕ) (f : ℕ) (e : ℤ) :
    pow2 e ≤ absQ (Decoded.mk
      (if negative then -((2 ^ f + mantissa : ℕ) : ℤ) else (2 ^ f + mantissa : ℕ)) e f).value := by
  have hq := pow2_pos (e - f)
  have hm : ((2 ^ f : ℕ) : ℚ) ≤ ((2 ^ f + mantissa : ℕ) : ℚ) :=
    Rat.natCast_le_natCast.mpr (by omega)
  have hmul := Rat.mul_le_mul_of_nonneg_right hm (Rat.le_of_lt hq)
  have heq : ((2 ^ f : ℕ) : ℚ) * pow2 (e - f) = pow2 e := by
    rw [← pow2_natCast, ← pow2_add]
    congr 1
    omega
  rw [heq] at hmul
  unfold Decoded.value
  cases negative <;> simp only [Bool.false_eq_true, ↓reduceIte, Rat.intCast_neg,
    Rat.intCast_natCast, Rat.neg_mul]
  · rw [absQ_mul_pos _ _ hq, absQ_of_nonneg Rat.natCast_nonneg]
    exact hmul
  · rw [absQ_neg, absQ_mul_pos _ _ hq, absQ_of_nonneg Rat.natCast_nonneg]
    exact hmul

theorem classifyNat_scale_le_of_magnitude (f : Format) (n : ℕ) (d : Decoded)
    (hd : (classifyNat f n).finite = some d) (E : ℤ) (hE : f.emin ≤ E)
    (hm : absQ d.value < pow2 (E + 1)) (hn : d.significand ≠ 0) : d.exponent ≤ E := by
  unfold classifyNat at hd
  dsimp only at hd
  split at hd
  · split at hd <;> simp [Classification.finite] at hd
  · split at hd
    · split at hd
      · simp only [Classification.finite, Option.some.injEq] at hd
        subst d
        exact absurd rfl hn
      · simp only [Classification.finite, Option.some.injEq] at hd
        subst d
        exact hE
    · simp only [Classification.finite, Option.some.injEq] at hd
      subst d
      have hl := decoded_normal_magnitude_lower
        (n / 2 ^ (f.mantissaBits + f.exponentBits) != 0) (n % 2 ^ f.mantissaBits)
        f.mantissaBits (((n / 2 ^ f.mantissaBits % 2 ^ f.exponentBits : ℕ) : ℤ) - f.bias)
      change ((n / 2 ^ f.mantissaBits % 2 ^ f.exponentBits : ℕ) : ℤ) - f.bias ≤ E
      apply Classical.byContradiction
      intro hne
      have hp := pow2_le_of_le (show E + 1 ≤
        ((n / 2 ^ f.mantissaBits % 2 ^ f.exponentBits : ℕ) : ℤ) - f.bias by omega)
      grind

end TensorCore
