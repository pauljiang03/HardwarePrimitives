import TensorCore.Numerics.Binary.CorrectRounding

/-! Directed rounding on finite binary formats. -/

namespace TensorCore

/-- Greatest finite value at or below the exact input. -/
def TowardNegative (f : Format) (x : ℚ) (bits : BitVec f.width) : Prop :=
  ∃ d : ℚ, binaryValue f bits = some d ∧ d ≤ x ∧
    ∀ y : ℚ, f.FiniteValue y → y ≤ x → y ≤ d

/-- Least finite value at or above the exact input. -/
def TowardPositive (f : Format) (x : ℚ) (bits : BitVec f.width) : Prop :=
  ∃ d : ℚ, binaryValue f bits = some d ∧ x ≤ d ∧
    ∀ y : ℚ, f.FiniteValue y → x ≤ y → d ≤ y

theorem binary_ceil_magnitude_spec (f : Format) (hf : f.WellFormed) (m : ℚ)
    (hm : 0 < m) (hr : m ≤ f.maxFinite) :
    m ≤ binaryMagnitudeRounded f .towardPositive false m ∧
    ∀ y : ℚ, f.FiniteValue y → m ≤ y →
      binaryMagnitudeRounded f .towardPositive false m ≤ y := by
  have hq := pow2_pos (binaryNormExp f m - f.mantissaBits)
  constructor
  · have h := Rat.mul_le_mul_of_nonneg_right
      (Rat.le_ceil (x := m / pow2 (binaryNormExp f m - f.mantissaBits))) (Rat.le_of_lt hq)
    rwa [Rat.div_mul_cancel (Rat.ne_of_gt hq)] at h
  · intro y hy hmy
    obtain ⟨j, fe, hfe, _, hj, rfl⟩ := hy
    by_cases he : binaryNormExp f m ≤ fe
    · obtain ⟨z, hz⟩ := f.finite_on_grid j fe (binaryNormExp f m) he
      rw [hz] at hmy ⊢
      change (((m / pow2 (binaryNormExp f m - f.mantissaBits)).ceil : ℤ) : ℚ) *
        pow2 (binaryNormExp f m - f.mantissaBits) ≤ _
      apply Rat.mul_le_mul_of_nonneg_right _ (Rat.le_of_lt hq)
      apply Rat.intCast_le_intCast.mpr
      apply Rat.ceil_le_iff.mpr
      apply Rat.le_of_mul_le_mul_right (c := pow2 (binaryNormExp f m - f.mantissaBits)) _ hq
      rwa [Rat.div_mul_cancel (Rat.ne_of_gt hq)]
    · obtain ⟨_, _, _, hl⟩ := binaryNormExp_bounds f hf m hm hr
      have hl' : pow2 (binaryNormExp f m) ≤ m := by
        rcases hl with h | h
        · exact h
        · exfalso; omega
      have hsmall := f.finite_below_binade j fe (binaryNormExp f m) hj (by omega)
      have hsmall' := (absQ_le_iff _ _).mp hsmall
      have := pow2_pos (binaryNormExp f m - f.mantissaBits - 1)
      grind

theorem binarySignedRounded_towardNegative (f : Format) (hf : f.WellFormed) (x : ℚ)
    (hx : x ≠ 0) (hr : absQ x ≤ f.maxFinite) :
    binarySignedRounded f .towardNegative x ≤ x ∧
    ∀ y : ℚ, f.FiniteValue y → y ≤ x → y ≤ binarySignedRounded f .towardNegative x := by
  have hm := absQ_pos_of_ne_zero x hx
  unfold binarySignedRounded
  by_cases hn : x < 0
  · rw [if_pos hn]
    have hc := binary_ceil_magnitude_spec f hf (absQ x) hm hr
    have ha := absQ_of_neg hn
    have he : binaryMagnitudeRounded f .towardNegative true (absQ x) =
        binaryMagnitudeRounded f .towardPositive false (absQ x) := rfl
    rw [he]
    refine ⟨by grind, ?_⟩
    intro y hy hyx
    have h := hc.2 (-y) (f.finiteValue_neg hy) (by grind)
    grind
  · rw [if_neg hn]
    have hc := binary_trunc_magnitude_spec f hf false (absQ x) hm hr
    have ha := absQ_of_nonneg (show 0 ≤ x by grind)
    change binaryMagnitudeRounded f .truncate false (absQ x) ≤ x ∧ _
    refine ⟨by grind, ?_⟩
    intro y hy hyx
    exact hc.2.2 y hy (by grind)

theorem binarySignedRounded_towardPositive (f : Format) (hf : f.WellFormed) (x : ℚ)
    (hx : x ≠ 0) (hr : absQ x ≤ f.maxFinite) :
    x ≤ binarySignedRounded f .towardPositive x ∧
    ∀ y : ℚ, f.FiniteValue y → x ≤ y → binarySignedRounded f .towardPositive x ≤ y := by
  have hm := absQ_pos_of_ne_zero x hx
  unfold binarySignedRounded
  by_cases hn : x < 0
  · rw [if_pos hn]
    have hc := binary_trunc_magnitude_spec f hf true (absQ x) hm hr
    have ha := absQ_of_neg hn
    change x ≤ -binaryMagnitudeRounded f .truncate true (absQ x) ∧ _
    refine ⟨by grind, ?_⟩
    intro y hy hxy
    have h := hc.2.2 (-y) (f.finiteValue_neg hy) (by grind)
    change -binaryMagnitudeRounded f .truncate true (absQ x) ≤ y
    grind
  · rw [if_neg hn]
    have hc := binary_ceil_magnitude_spec f hf (absQ x) hm hr
    have ha := absQ_of_nonneg (show 0 ≤ x by grind)
    refine ⟨by grind, ?_⟩
    intro y hy hxy
    exact hc.2 y hy (by grind)

theorem roundBinary_towardNegative_correct (f : Format) (hf : f.WellFormed) (x : ℚ)
    (hr : absQ x ≤ f.maxFinite) :
    ∃ bits, roundBinary f .towardNegative x = some bits ∧ TowardNegative f x bits := by
  by_cases hx : x = 0
  · subst x
    refine ⟨0, ?_, 0, binaryValue_zero f hf, Rat.le_refl, fun _ _ h => h⟩
    simp only [roundBinary, hf, not_true_eq_false, ↓reduceIte]
    rw [if_neg (by grind)]
  · obtain ⟨bits, hb, hv, _⟩ := roundBinary_nonzero_spec f hf .towardNegative x hx hr
    exact ⟨bits, hb, _, hv, binarySignedRounded_towardNegative f hf x hx hr⟩

theorem roundBinary_towardPositive_correct (f : Format) (hf : f.WellFormed) (x : ℚ)
    (hr : absQ x ≤ f.maxFinite) :
    ∃ bits, roundBinary f .towardPositive x = some bits ∧ TowardPositive f x bits := by
  by_cases hx : x = 0
  · subst x
    refine ⟨0, ?_, 0, binaryValue_zero f hf, Rat.le_refl, fun _ _ h => h⟩
    simp only [roundBinary, hf, not_true_eq_false, ↓reduceIte]
    rw [if_neg (by grind)]
  · obtain ⟨bits, hb, hv, _⟩ := roundBinary_nonzero_spec f hf .towardPositive x hx hr
    exact ⟨bits, hb, _, hv, binarySignedRounded_towardPositive f hf x hx hr⟩

end TensorCore
