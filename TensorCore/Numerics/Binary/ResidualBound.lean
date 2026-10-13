import TensorCore.Numerics.Binary.ScalarSum

/-! Residual coefficient budgets for exact scalar consolidation. -/

namespace TensorCore

/-- Residual magnitudes below `2^b` on grid `2^ℓ` imply the coefficient budget. -/
theorem extraction_coefficient_bound (zs : List ℤ) (b ℓ : ℤ) (P : ℕ)
    (hgrid : ℓ ≤ b)
    (hterm : ∀ z ∈ zs, absQ ((z : ℚ) * pow2 ℓ) < pow2 b)
    (hbound : zs.length * (2 ^ (b - ℓ).toNat - 1) < 2 ^ P) :
    magnitudeSum zs < 2 ^ P := by
  have he : ((b - ℓ).toNat : ℤ) + ℓ = b := by omega
  have hcoeff : ∀ z ∈ zs, z.natAbs ≤ 2 ^ (b - ℓ).toNat - 1 := by
    intro z hz
    have h := hterm z hz
    rw [absQ_mul_pos _ _ (pow2_pos _), absQ_intCast, Rat.intCast_natCast,
      ← he, pow2_add, pow2_natCast] at h
    have hc := Rat.natCast_lt_natCast.mp
      (Rat.lt_of_mul_lt_mul_right h (Rat.le_of_lt (pow2_pos ℓ)))
    omega
  exact Nat.lt_of_le_of_lt (magnitudeSum_le_length_mul zs _ hcoeff) hbound

/-- Exact scalar consolidation under coefficient-budget, minimum-grid, and finite-range conditions. -/
theorem naiveSumBinary_exact_of_extraction_bound (f : Format) (hf : f.WellFormed)
    (b ℓ : ℤ) (hmin : f.emin - f.mantissaBits ≤ ℓ) (hgrid : ℓ ≤ b)
    (zs : List ℤ) (hterm : ∀ z ∈ zs, absQ ((z : ℚ) * pow2 ℓ) < pow2 b)
    (hbound : zs.length * (2 ^ (b - ℓ).toNat - 1) < 2 ^ (f.mantissaBits + 1))
    (hrange : (magnitudeSum zs : ℚ) * pow2 ℓ ≤ f.maxFinite) :
    naiveSumBinary f (zs.map fun (z : ℤ) => (z : ℚ) * pow2 ℓ) =
      some ((sumZ zs : ℚ) * pow2 ℓ) :=
  naiveSumBinary_exact f hf ℓ hmin zs
    (extraction_coefficient_bound zs b ℓ _ hgrid hterm hbound) hrange

end TensorCore
