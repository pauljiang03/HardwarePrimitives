import OzakiMC.Exactness

/-! # Binary32 rounding in the recombination

`round32Value` is `MatrixCore`'s binary32 round to nearest even (`rne32`) as a rounding of values,
and `fp32Add` the correctly rounded addition it induces. Both satisfy the standard model with a
subnormal term: `|fl(q) − q| ≤ 2^-24 |q| + 2^-150` (`round32Value_within`). -/

open MatrixCore

namespace Ozaki.MC

/-- Binary32 round to nearest even, as a value; `none` on overflow. -/
def round32Value (q : ℚ) : Option ℚ := (rne32 q).bind value32

/-- Correctly rounded binary32 addition. -/
def fp32Add (a b : ℚ) : Option ℚ := round32Value (a + b)

theorem fp32Add_eq_addOfRound : fp32Add = addOfRound round32Value := rfl

/-- Rounding a positive magnitude to nearest even loses at most `2^-24 a + 2^-150`. -/
theorem rneMagnitude_error {a : ℚ} (ha : 0 < a) :
    Rat.abs (rneMagnitude a - a) ≤ 2 ^ (-24 : ℤ) * a + 2 ^ (-150 : ℤ) := by
  obtain ⟨_, hlow, he1⟩ := normExp_bounds ha
  generalize hE : normExp a = e at *
  have hg := pow2_pos (e - 23)
  have hdist := rneInt_dist (a / pow2 (e - 23))
  rw [absQ_eq] at hdist
  have heq : rneMagnitude a - a =
      ((rneInt (a / pow2 (e - 23)) : ℚ) - a / pow2 (e - 23)) * pow2 (e - 23) := by
    unfold rneMagnitude
    rw [hE]
    have : a / pow2 (e - 23) * pow2 (e - 23) = a := Rat.div_mul_cancel (Rat.ne_of_gt hg)
    grind
  rw [heq, abs_mul, abs_of_nonneg (Rat.le_of_lt hg), abs_sub_comm]
  have hhalf : Rat.abs (a / pow2 (e - 23) - rneInt (a / pow2 (e - 23))) * pow2 (e - 23) ≤
      pow2 (e - 24) := by
    have h2 : pow2 (e - 23) = 2 * pow2 (e - 24) := by
      rw [show e - 23 = (e - 24) + 1 by omega, pow2_succ]; grind
    have := Rat.mul_le_mul_of_nonneg_right hdist (Rat.le_of_lt (pow2_pos (e - 24)))
    generalize Rat.abs (a / pow2 (e - 23) - rneInt (a / pow2 (e - 23))) = A at this ⊢
    rw [h2]; grind
  refine Rat.le_trans hhalf ?_
  have ha0 : (0 : ℚ) ≤ 2 ^ (-24 : ℤ) * a :=
    Rat.mul_nonneg (Rat.le_of_lt (two_pow_pos _)) (Rat.le_of_lt ha)
  have h150 : (0 : ℚ) ≤ 2 ^ (-150 : ℤ) := Rat.le_of_lt (two_pow_pos _)
  by_cases hsub : e = -126
  · subst hsub
    have : pow2 (-126 - 24) = 2 ^ (-150 : ℤ) := rfl
    rw [this]
    grind
  · have hlo := hlow hsub
    have : pow2 (e - 24) ≤ 2 ^ (-24 : ℤ) * a := by
      rw [show e - 24 = -24 + e by omega, pow2_add]
      exact Rat.mul_le_mul_of_nonneg_left hlo (Rat.le_of_lt (pow2_pos _))
    grind

/-- **Binary32 rounding error.** `|fl(q) − q| ≤ 2^-24 |q| + 2^-150` whenever `fl(q)` is finite. -/
theorem round32Value_within : RoundWithin round32Value (2 ^ (-24 : ℤ)) (2 ^ (-150 : ℤ)) := by
  intro q v h
  unfold round32Value at h
  cases hw : rne32 q with
  | none => simp [hw] at h
  | some w =>
    simp only [hw, Option.bind_some] at h
    rw [rne32_value hw] at h
    cases Option.some.inj h
    by_cases hq : q = 0
    · subst hq
      rw [rneValue_zero, show (0 : ℚ) - 0 = 0 by grind, abs_zero]
      have := two_pow_pos (-150 : ℤ); have := abs_nonneg (0 : ℚ)
      grind
    · have hpos := absQ_pos hq
      have herr := rneMagnitude_error hpos
      rw [← absQ_eq q] at *
      unfold rneValue
      split
      · rename_i hneg
        rw [absQ_of_neg hneg] at herr ⊢
        have : -rneMagnitude (-q) - q = -(rneMagnitude (-q) - -q) := by grind
        rw [this, abs_neg]; exact herr
      · rename_i hnn
        rw [absQ_of_nonneg (by grind)] at herr ⊢
        exact herr

theorem fp32Add_within : AddWithin fp32Add (2 ^ (-24 : ℤ)) (2 ^ (-150 : ℤ)) :=
  addOfRound_within round32Value_within

end Ozaki.MC
