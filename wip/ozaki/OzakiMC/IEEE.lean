import OzakiMC.Correct
import Ozaki.Binary

/-! # MatrixCore's round to nearest is IEEE's

MatrixCore's binary32 round to nearest even (`rne32`) computes the same value as the
hardware-independent IEEE round to nearest even of `Ozaki.Binary` (`rne32Q`)
(`rneValue_eq_rneU`), and both overflow exactly when the rounded magnitude exceeds the largest
finite value. So the two are the same function (`round32Value_eq_rne32Q`), and so is TensorCore's
on every input of magnitude at most the largest finite value (`Ozaki.TC.round32Value_eq_rne32Q`):
on that range the NVIDIA and AMD schemes round with literally the same function. -/

open MatrixCore

namespace Ozaki.MC

theorem rneMagnitude_eq_rneMag (a : ℚ) : rneMagnitude a = rneMag 24 (-126) a := rfl

theorem rneValue_eq_rneU (q : ℚ) : rneValue q = rneU 24 (-126) q := by
  unfold rneValue rneU
  by_cases h : q < 0
  · have : absQ q = -q := by unfold absQ; simp [h]
    rw [if_pos h, if_pos h, this, rneMagnitude_eq_rneMag]
  · have : absQ q = q := by unfold absQ; simp [h]
    rw [if_neg h, if_neg h, this, rneMagnitude_eq_rneMag]

theorem maxFinite32_eq_maxFormat : maxFinite32 = maxFormat 24 127 := by decide +kernel

/-- The overflow threshold rounds up to `2^128`, past the largest finite value. -/
theorem rneU_threshold : rneU 24 (-126) overflowThreshold32 = 2 ^ (128 : ℤ) := by decide +kernel

theorem rneU_neg_threshold : rneU 24 (-126) (-overflowThreshold32) = -2 ^ (128 : ℤ) := by
  decide +kernel

theorem maxFormat_lt_two_pow : maxFormat 24 127 < 2 ^ (128 : ℤ) := by decide +kernel

/-- **MatrixCore's binary32 round to nearest is IEEE's**, on every input. -/
theorem round32Value_eq_rne32Q (q : ℚ) : round32Value q = rne32Q q := by
  unfold round32Value
  cases hw : rne32 q with
  | some w =>
    have hv := rne32_value hw
    have habs := finiteValue32_abs_le (value32_finiteValue hv)
    rw [rneValue_eq_rneU, maxFinite32_eq_maxFormat] at habs
    rw [Option.bind_some, hv, rneValue_eq_rneU]
    unfold rne32Q roundRNE
    rw [if_pos habs]
  | none =>
    have hn : ¬ absQ q < overflowThreshold32 := by
      intro h; have := (rne32_isSome_iff q).mpr h; simp [hw] at this
    rw [absQ_eq, abs_lt_iff] at hn
    have hbig : maxFormat 24 127 < Rat.abs (rneU 24 (-126) q) := by
      have hm := maxFormat_lt_two_pow
      rcases (show overflowThreshold32 ≤ q ∨ q ≤ -overflowThreshold32 by grind) with hq | hq
      · have := rneU_monotone (p := 24) (emin := -126) (by decide) hq
        rw [rneU_threshold] at this
        have hpos : 0 ≤ rneU 24 (-126) q := Rat.le_trans (Rat.le_of_lt (two_pow_pos _)) this
        rw [abs_of_nonneg hpos]; grind
      · have := rneU_monotone (p := 24) (emin := -126) (by decide) hq
        rw [rneU_neg_threshold] at this
        have hneg : rneU 24 (-126) q < 0 := by have := two_pow_pos (128 : ℤ); grind
        rw [abs_of_neg hneg]; grind
    unfold rne32Q roundRNE
    rw [if_neg (by grind)]
    rfl

end Ozaki.MC
