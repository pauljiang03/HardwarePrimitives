import TensorCore.Numerics.CorrectRounding

/-! Error bounds for finite FP32 rounding. -/

namespace TensorCore

/-- The magnitude truncation loss is strictly smaller than the conversion grid. -/
theorem trunc_magnitude_residual (m : ℚ) :
    absQ (m - magnitudeRounded .truncate m) < pow2 (normExp m - 23) := by
  let q := pow2 (normExp m - 23)
  have hq : 0 < q := pow2_pos _
  have hf := floor_frac_bounds (m / q)
  have he : m - magnitudeRounded .truncate m = (m / q - (m / q).floor) * q := by
    have h := Rat.div_mul_cancel (a := m) (Rat.ne_of_gt hq)
    unfold magnitudeRounded roundedSignificand roundSignificand
    change m - ((m / q).floor : ℚ) * q = _
    grind
  rw [he, absQ_mul_pos _ q hq, absQ_of_nonneg hf.1]
  have h := Rat.mul_lt_mul_of_pos_right hf.2 hq
  simpa using h

theorem trunc_signed_residual (x : ℚ) :
    absQ (x - signedRounded .truncate x) < pow2 (normExp (absQ x) - 23) := by
  have h := trunc_magnitude_residual (absQ x)
  unfold signedRounded
  by_cases hn : x < 0
  · simp only [hn, ↓reduceIte, absQ_of_neg hn] at h ⊢
    have he : x - -magnitudeRounded .truncate (-x) =
      -(-x - magnitudeRounded .truncate (-x)) := by grind
    rw [he, absQ_neg]; exact h
  · have hn' : 0 ≤ x := by grind
    simpa [hn, absQ_of_nonneg hn'] using h

/-- Truncation to FP32 loses less than one ulp of the output. -/
theorem output_residual_bound (x : ℚ) (b : F32) (d : ℚ)
    (hr : absQ x ≤ maxFinite32) (hb : round32 .truncate x = some b)
    (hd : value32 b = some d) :
    absQ (x - d) < pow2 (outputUlpExponent b) := by
  by_cases hx : x = 0
  · subst x
    have hz : round32 .truncate 0 = some 0 := by decide +kernel
    rw [hz] at hb
    cases Option.some.inj hb
    have hv : value32 0 = some 0 := by decide +kernel
    rw [hv] at hd
    cases Option.some.inj hd
    have ha : absQ (0 - 0) = 0 := by decide +kernel
    rw [ha]; exact pow2_pos _
  · obtain ⟨b', hb', hd', _, he⟩ := round32_nonzero_spec .truncate x hx hr
    rw [hb] at hb'
    cases Option.some.inj hb'
    rw [hd] at hd'
    have hvalue := Option.some.inj hd'
    rw [hvalue]
    have hl := trunc_signed_residual x
    have hq := pow2_le_of_le he
    grind

/-- Truncation loses less than the conversion grid of the input magnitude. -/
theorem trunc_residual_lt (x : ℚ) (b : F32) (d : ℚ) (hr : absQ x ≤ maxFinite32)
    (hb : round32 .truncate x = some b) (hd : value32 b = some d) :
    absQ (x - d) < pow2 (normExp (absQ x) - 23) := by
  by_cases hx : x = 0
  · subst x
    have hz : round32 .truncate 0 = some 0 := by decide +kernel
    rw [hz] at hb
    cases Option.some.inj hb
    have hv : value32 0 = some 0 := by decide +kernel
    rw [hv] at hd
    cases Option.some.inj hd
    have ha : absQ (0 - 0) = 0 := by decide +kernel
    rw [ha]; exact pow2_pos _
  · obtain ⟨b', hb', hd', _, _⟩ := round32_nonzero_spec .truncate x hx hr
    rw [hb] at hb'
    cases Option.some.inj hb'
    rw [hd] at hd'
    rw [Option.some.inj hd']
    exact trunc_signed_residual x

end TensorCore
