import TensorCore.Numerics.FormatProperties

/-! Exact products kept in denormalized form, with unnormalized exponents. -/

namespace TensorCore

/-- An exact product kept in denormalized form: `value = significand · 2^(unnormalizedExp − mantissaBits)`. -/
structure UnnormalizedProduct where
  /-- Product of the two integer significands (may be ≥ 2 after the binary point is placed). -/
  significand : ℤ
  /-- Sum of the two inputs' exponents. -/
  unnormalizedExp : ℤ
  /-- Sum of the two inputs' mantissa widths (20 for FP16 × FP16). -/
  mantissaBits : ℤ
  deriving Repr, DecidableEq

def UnnormalizedProduct.value (x : UnnormalizedProduct) : ℚ :=
  (x.significand : ℚ) * pow2 (x.unnormalizedExp - x.mantissaBits)

def unnormalizedMul (a b : Decoded) : UnnormalizedProduct :=
  ⟨a.significand * b.significand, a.unnormalizedExp + b.unnormalizedExp,
    a.mantissaBits + b.mantissaBits⟩

theorem unnormalizedProduct_value (a b : Decoded) :
    (unnormalizedMul a b).value = a.value * b.value := by
  simp only [unnormalizedMul, UnnormalizedProduct.value, Decoded.value, Rat.intCast_mul]
  have h : a.unnormalizedExp + b.unnormalizedExp - (a.mantissaBits + b.mantissaBits) =
      (a.unnormalizedExp - a.mantissaBits) + (b.unnormalizedExp - b.mantissaBits) := by omega
  rw [h, pow2_add]
  grind

/-- A common bound for c (significand below two) and denormalized products (below four). -/
def UnnormalizedProduct.Bounded (t : UnnormalizedProduct) : Prop := absQ t.value < 4 * pow2 t.unnormalizedExp

theorem unnormalizedMul_bounded (a b : Decoded) (ha : a.Bounded) (hb : b.Bounded) :
    (unnormalizedMul a b).Bounded := by
  have hpa := pow2_pos a.unnormalizedExp
  have hpb := pow2_pos b.unnormalizedExp
  have hna := absQ_nonneg a.value
  have hnb := absQ_nonneg b.value
  have hm : absQ (a.value * b.value) = absQ a.value * absQ b.value := by
    by_cases hz : b.value = 0
    · simp [hz, absQ]
    · by_cases hpos : 0 < b.value
      · rw [absQ_mul_pos _ _ hpos, absQ_of_nonneg (Rat.le_of_lt hpos)]
      · have hneg : b.value < 0 := by grind
        have hm := absQ_mul_pos a.value (-b.value) (by grind)
        rw [Rat.mul_neg, absQ_neg] at hm
        rw [hm, absQ_of_neg hneg]
  change absQ (unnormalizedMul a b).value < 4 * pow2 (a.unnormalizedExp + b.unnormalizedExp)
  rw [unnormalizedProduct_value, hm, pow2_add]
  unfold Decoded.Bounded at ha hb
  have h1 := Rat.mul_le_mul_of_nonneg_right (Rat.le_of_lt ha) hnb
  have h2 := Rat.mul_lt_mul_of_pos_left hb (show 0 < 2 * pow2 a.unnormalizedExp by grind)
  grind

theorem c_term_bounded (c : Decoded) (hc : c.Bounded) :
    (UnnormalizedProduct.mk c.significand c.unnormalizedExp c.mantissaBits).Bounded := by
  have hp := pow2_pos c.unnormalizedExp
  change absQ c.value < 4 * pow2 c.unnormalizedExp
  unfold Decoded.Bounded at hc
  grind

end TensorCore
