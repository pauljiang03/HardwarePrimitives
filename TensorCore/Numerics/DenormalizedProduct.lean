import TensorCore.Numerics.FormatProperties

/-! Exact products kept in denormalized form.

Here *denormalized* means *not normalized*, as in Khattak and Mikaitis's *Accurate Models*
papers ("the products remain denormalised"): a product keeps the full product of the two
significands, which may be 2 or more, and the sum of the two input exponents. It does not mean
*subnormal*. -/

namespace TensorCore

/-- An exact product kept in denormalized form: `value = significand · 2^(exponent − mantissaBits)`. -/
structure DenormalizedProduct where
  /-- Product of the two integer significands (may be ≥ 2 after the binary point is placed). -/
  significand : ℤ
  /-- Sum of the two inputs' exponents. -/
  exponent : ℤ
  /-- Sum of the two inputs' mantissa widths (20 for FP16 × FP16). -/
  mantissaBits : ℤ
  deriving Repr, DecidableEq

def DenormalizedProduct.value (x : DenormalizedProduct) : ℚ :=
  (x.significand : ℚ) * pow2 (x.exponent - x.mantissaBits)

def denormalizedMul (a b : Decoded) : DenormalizedProduct :=
  ⟨a.significand * b.significand, a.exponent + b.exponent,
    a.mantissaBits + b.mantissaBits⟩

theorem denormalizedProduct_value (a b : Decoded) :
    (denormalizedMul a b).value = a.value * b.value := by
  simp only [denormalizedMul, DenormalizedProduct.value, Decoded.value, Rat.intCast_mul]
  have h : a.exponent + b.exponent - (a.mantissaBits + b.mantissaBits) =
      (a.exponent - a.mantissaBits) + (b.exponent - b.mantissaBits) := by omega
  rw [h, pow2_add]
  grind

/-- A common bound for c (significand below two) and denormalized products (below four). -/
def DenormalizedProduct.Bounded (t : DenormalizedProduct) : Prop := absQ t.value < 4 * pow2 t.exponent

theorem denormalizedMul_bounded (a b : Decoded) (ha : a.Bounded) (hb : b.Bounded) :
    (denormalizedMul a b).Bounded := by
  have hpa := pow2_pos a.exponent
  have hpb := pow2_pos b.exponent
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
  change absQ (denormalizedMul a b).value < 4 * pow2 (a.exponent + b.exponent)
  rw [denormalizedProduct_value, hm, pow2_add]
  unfold Decoded.Bounded at ha hb
  have h1 := Rat.mul_le_mul_of_nonneg_right (Rat.le_of_lt ha) hnb
  have h2 := Rat.mul_lt_mul_of_pos_left hb (show 0 < 2 * pow2 a.exponent by grind)
  grind

theorem c_term_bounded (c : Decoded) (hc : c.Bounded) :
    (DenormalizedProduct.mk c.significand c.exponent c.mantissaBits).Bounded := by
  have hp := pow2_pos c.exponent
  change absQ c.value < 4 * pow2 c.exponent
  unfold Decoded.Bounded at hc
  grind

end TensorCore
