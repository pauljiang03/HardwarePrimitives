import OzakiTC.Exactness
import Ozaki.Binary

/-! # Binary32 rounding in the recombination

Ozaki-I adds its scaled slice products, and Ozaki-II rounds its reconstructed product, in binary32
with round to nearest even. `round32Value` is IEEE's binary32 round to nearest even
(`Ozaki.rne32Q`), and `add32` the correctly rounded addition it induces. Both satisfy the standard
model with a subnormal term: `|fl(q) − q| ≤ 2^-24 |q| + 2^-150` (`round32Value_within`).

TensorCore's binary32 converter (`round32ValueTC`, and `TensorCore`'s addition `fp32Add`) computes the
same value on every input of magnitude at most the largest finite value
(`round32ValueTC_eq`): it is the same formula (`signedRounded_eq_rneU`). It differs only in
overflow, returning no result above the largest finite value where IEEE rounds values below half an
ulp above it down to it. The σ-trick of `OzakiTC.Split32` is stated with `fp32Add`; every result it
returns is also IEEE's (`add32_of_fp32Add`). -/

open TensorCore

namespace Ozaki.TC

/-- TensorCore's binary32 round to nearest even, as a value; `none` above the largest finite value. -/
def round32ValueTC (q : ℚ) : Option ℚ := (round32 .nearestEven q).bind value32

/-- **Binary32 round to nearest even**, IEEE's: `Ozaki.rne32Q`; `none` exactly when the rounded
magnitude exceeds the largest finite value. -/
def round32Value (q : ℚ) : Option ℚ := rne32Q q

/-- IEEE binary32 addition: the exact sum rounded to nearest even. -/
def add32 (a b : ℚ) : Option ℚ := round32Value (a + b)

theorem add32_eq_addOfRound : add32 = addOfRound round32Value := rfl

theorem fp32Add_eq_addOfRound : fp32Add = addOfRound round32ValueTC := by
  funext x y; rfl

/-- Rounding a positive magnitude to nearest even loses at most `2^-24 m + 2^-150`. -/
theorem magnitudeRounded_error {m : ℚ} (hm : 0 < m) (hr : m ≤ maxFinite32) :
    Rat.abs (magnitudeRounded .nearestEven m - m) ≤ 2 ^ (-24 : ℤ) * m + 2 ^ (-150 : ℤ) := by
  obtain ⟨he1, _, _, hlow⟩ := normExp_bounds m hm hr
  generalize hE : normExp m = e at *
  have hg := pow2_pos (e - 23)
  have hdist := rneInt_dist_le_half (m / pow2 (e - 23))
  rw [absQ_eq] at hdist
  have heq : magnitudeRounded .nearestEven m - m =
      ((rneInt (m / pow2 (e - 23)) : ℚ) - m / pow2 (e - 23)) * pow2 (e - 23) := by
    unfold magnitudeRounded roundedSignificand roundSignificand
    rw [hE]
    have : m / pow2 (e - 23) * pow2 (e - 23) = m := Rat.div_mul_cancel (Rat.ne_of_gt hg)
    grind
  rw [heq, abs_mul, abs_of_nonneg (Rat.le_of_lt hg), abs_sub_comm]
  have hhalf : Rat.abs (m / pow2 (e - 23) - rneInt (m / pow2 (e - 23))) * pow2 (e - 23) ≤
      pow2 (e - 24) := by
    have h2 : pow2 (e - 23) = 2 * pow2 (e - 24) := by
      rw [show e - 23 = (e - 24) + 1 by omega, pow2_succ]; grind
    have := Rat.mul_le_mul_of_nonneg_right hdist (Rat.le_of_lt (pow2_pos (e - 24)))
    generalize Rat.abs (m / pow2 (e - 23) - rneInt (m / pow2 (e - 23))) = A at this ⊢
    rw [h2]; grind
  refine Rat.le_trans hhalf ?_
  have hm0 : (0 : ℚ) ≤ 2 ^ (-24 : ℤ) * m :=
    Rat.mul_nonneg (Rat.le_of_lt (two_pow_pos _)) (Rat.le_of_lt hm)
  have h150 : (0 : ℚ) ≤ 2 ^ (-150 : ℤ) := Rat.le_of_lt (two_pow_pos _)
  rcases hlow with hlow | hlow
  · have : pow2 (e - 24) ≤ 2 ^ (-24 : ℤ) * m := by
      rw [show e - 24 = -24 + e by omega, pow2_add]
      exact Rat.mul_le_mul_of_nonneg_left hlow (Rat.le_of_lt (pow2_pos _))
    grind
  · subst hlow
    have : pow2 (-126 - 24) = 2 ^ (-150 : ℤ) := rfl
    rw [this]
    grind

/-- TensorCore's binary32 rounding error: `|fl(q) − q| ≤ 2^-24 |q| + 2^-150`. -/
theorem round32ValueTC_within : RoundWithin round32ValueTC (2 ^ (-24 : ℤ)) (2 ^ (-150 : ℤ)) := by
  intro q v h
  unfold round32ValueTC at h
  cases hw : round32 .nearestEven q with
  | none => simp [hw] at h
  | some w =>
    simp only [hw, Option.bind_some] at h
    by_cases hq : q = 0
    · subst hq
      have h0 : round32 .nearestEven 0 = some 0 := by decide +kernel
      rw [h0] at hw; cases Option.some.inj hw
      have : value32 0 = some 0 := by decide +kernel
      rw [this] at h; cases Option.some.inj h
      rw [show (0 : ℚ) - 0 = 0 by grind, abs_zero]
      have := two_pow_pos (-150 : ℤ); have := abs_nonneg (0 : ℚ)
      grind
    · have hr := round32_range hw
      obtain ⟨b, hb, hv, _⟩ := round32_nonzero_spec .nearestEven q hq hr
      rw [hw] at hb; cases Option.some.inj hb
      rw [hv] at h; cases Option.some.inj h
      have hpos : 0 < absQ q := by rw [absQ_eq]; exact Rat.abs_pos_iff.mpr hq
      have herr := magnitudeRounded_error hpos hr
      rw [← absQ_eq q] at *
      unfold signedRounded
      split
      · rename_i hneg
        rw [absQ_of_neg hneg] at herr ⊢
        have : -magnitudeRounded .nearestEven (-q) - q =
            -(magnitudeRounded .nearestEven (-q) - -q) := by grind
        rw [this, abs_neg]; exact herr
      · rename_i hnn
        rw [absQ_of_nonneg (by grind)] at herr ⊢
        exact herr

theorem fp32Add_within : AddWithin fp32Add (2 ^ (-24 : ℤ)) (2 ^ (-150 : ℤ)) := by
  rw [fp32Add_eq_addOfRound]; exact addOfRound_within round32ValueTC_within

/-- **Binary32 rounding error.** `|fl(q) − q| ≤ 2^-24 |q| + 2^-150` whenever `fl(q)` is finite. -/
theorem round32Value_within : RoundWithin round32Value (2 ^ (-24 : ℤ)) (2 ^ (-150 : ℤ)) :=
  rne32Q_within

theorem add32_within : AddWithin add32 (2 ^ (-24 : ℤ)) (2 ^ (-150 : ℤ)) :=
  addOfRound_within round32Value_within

/-! ## TensorCore's round to nearest is IEEE's in range -/

theorem magnitudeRounded_eq_rneMag (m : ℚ) :
    magnitudeRounded .nearestEven m = rneMag 24 (-126) m := rfl

/-- TensorCore's rounded value is IEEE's, before the overflow check. -/
theorem signedRounded_eq_rneU (q : ℚ) : signedRounded .nearestEven q = rneU 24 (-126) q := by
  unfold signedRounded rneU
  by_cases h : q < 0
  · have : absQ q = -q := by unfold absQ; simp [h]
    rw [if_pos h, if_pos h, this, magnitudeRounded_eq_rneMag]
  · have : absQ q = q := by unfold absQ; simp [h]
    rw [if_neg h, if_neg h, this, magnitudeRounded_eq_rneMag]

theorem maxFinite32_eq_maxFormat : maxFinite32 = maxFormat 24 127 := by decide +kernel

/-- **TensorCore's binary32 round to nearest is IEEE's** on every input of magnitude at most the
largest finite value. -/
theorem round32ValueTC_eq {q : ℚ} (hq : absQ q ≤ maxFinite32) : round32ValueTC q = round32Value q := by
  by_cases h0 : q = 0
  · subst h0; decide +kernel
  · obtain ⟨b, hb, hv, _⟩ := round32_nonzero_spec .nearestEven q h0 hq
    have hfin := value32_finite b _ hv
    have habs := finiteValue32_abs_le hfin
    rw [signedRounded_eq_rneU, absQ_eq] at habs
    unfold round32ValueTC round32Value rne32Q roundRNE
    rw [hb, Option.bind_some, hv, signedRounded_eq_rneU, ← maxFinite32_eq_maxFormat,
      if_pos habs]

/-- A result TensorCore's rounding returns is IEEE's. -/
theorem round32Value_of_TC {q v : ℚ} (h : round32ValueTC q = some v) : round32Value q = some v := by
  have hr : absQ q ≤ maxFinite32 := by
    unfold round32ValueTC at h
    cases hw : round32 .nearestEven q with
    | none => simp [hw] at h
    | some w => exact round32_range hw
  rw [← round32ValueTC_eq hr]; exact h

/-- A sum `TensorCore`'s binary32 addition returns is IEEE's. -/
theorem add32_of_fp32Add {a b v : ℚ} (h : fp32Add a b = some v) : add32 a b = some v := by
  rw [fp32Add_eq_addOfRound] at h
  exact round32Value_of_TC h

/-- IEEE binary32 addition is exact when the sum is a binary32 value. -/
theorem add32_exact (x y : ℚ) (h : FiniteValue32 (x + y)) : add32 x y = some (x + y) :=
  add32_of_fp32Add (fp32Add_exact x y h)

/-- TensorCore's binary32 values are the binary32 values of `Ozaki.Binary`. -/
theorem finiteValue32_binary32 {v : ℚ} (h : FiniteValue32 v) : Binary32Value v := by
  obtain ⟨k, e, h1, h2, h3, rfl⟩ := h
  exact ⟨k, e, h1, h2, h3, by rw [pow2_eq]; congr 2⟩

end Ozaki.TC
