import TensorCore.Kernels.EFT.Word
import TensorCore.TC.Monotonicity

/-! Values of the bounded split and rounding on dyadic words. -/

namespace TensorCore.EFMachine

theorem floor_nat_div (m d : ℕ) (hd : 0 < d) :
    ((m : ℚ) / (d : ℚ)).floor = (m / d : ℕ) := by
  have hdp : (0 : ℚ) < (d : ℚ) := Rat.natCast_pos.mpr hd
  have hlo : ((m / d : ℕ) : ℚ) * (d : ℚ) ≤ (m : ℚ) := by
    rw [← Rat.natCast_mul]
    exact Rat.natCast_le_natCast.mpr (Nat.div_mul_le_self m d)
  have hhi : (m : ℚ) < ((m / d : ℕ) + 1 : ℚ) * (d : ℚ) := by
    have hn : m < (m / d + 1) * d := by
      have := Nat.mod_lt m hd
      have hh := Nat.mod_add_div m d
      rw [Nat.mul_comm] at hh
      rw [Nat.add_mul, Nat.one_mul]
      omega
    exact_mod_cast hn
  have hl : ((m / d : ℕ) : ℤ) ≤ ((m : ℚ) / (d : ℚ)).floor := by
    apply Rat.le_floor_iff.mpr
    have h := Rat.div_lt_iff (a := (m : ℚ)) (c := ((m / d : ℕ) : ℚ)) hdp
    simp only [Rat.intCast_natCast]
    grind
  have hh : ((m : ℚ) / (d : ℚ)).floor < ((m / d : ℕ) : ℤ) + 1 := by
    apply Rat.floor_lt_iff.mpr
    simpa only [Rat.intCast_add, Rat.intCast_natCast, Rat.intCast_one] using
      (Rat.div_lt_iff hdp).mpr hhi
  omega

theorem dyadic_div (m : ℕ) (scale : ℤ) (gap : ℕ) :
    (m : ℚ) * pow2 scale / pow2 (scale + gap) = (m : ℚ) / (2 ^ gap : ℕ) := by
  have hp := pow2_pos scale
  have hd : (0 : ℚ) < ((2 ^ gap : ℕ) : ℚ) := Rat.natCast_pos.mpr (Nat.two_pow_pos _)
  rw [pow2_add, pow2_natCast, Rat.div_def, Rat.inv_mul_rev]
  have hc := Rat.mul_inv_cancel (pow2 scale) (Rat.ne_of_gt hp)
  rw [Rat.div_def]
  grind

/-- The coarse part of the split is truncation to the grid, for either sign. -/
theorem Word.split_coarse_value (x : Word) (g : Grid) :
    (x.split g).coarse.value = truncGrid x.value ((g.toNat : ℤ) - 272) := by
  have hs := x.split_sign g
  have hn : (0 : ℚ) ≤ (x.magnitude.toNat : ℚ) * pow2 (-272) :=
    Rat.mul_nonneg Rat.natCast_nonneg (Rat.le_of_lt (pow2_pos _))
  have hpos : ((x.split g).coarse.magnitude.toNat : ℚ) * pow2 (-272) =
      truncGrid ((x.magnitude.toNat : ℚ) * pow2 (-272)) ((g.toNat : ℤ) - 272) := by
    rw [show (g.toNat : ℤ) - 272 = -272 + g.toNat by omega]
    rw [alignment_value, truncBits_nonneg_eq _ _ hn, dyadic_div,
      floor_nat_div _ _ (Nat.two_pow_pos _), x.split_coarse, Rat.natCast_mul,
      pow2_add, pow2_natCast]
    simp only [Rat.intCast_natCast]
    grind
  cases hx : x.negative
  · simpa only [Word.value, Word.coefficient, hs.1, hx, Bool.false_eq_true,
      if_false, Rat.intCast_natCast] using hpos
  · simpa only [Word.value, Word.coefficient, hs.1, hx, if_true, Rat.intCast_neg,
      Rat.intCast_natCast, Rat.neg_mul, truncGrid_neg] using congrArg Neg.neg hpos

theorem Word.split_low_value (x : Word) (g : Grid) :
    (x.split g).low.value = x.value - truncGrid x.value ((g.toNat : ℤ) - 272) := by
  have h := x.split_reconstruct g
  rw [x.split_coarse_value] at h
  grind

theorem Word.split_low_bound (x : Word) (g : Grid) :
    absQ (x.split g).low.value < pow2 ((g.toNat : ℤ) - 272) := by
  rw [x.split_low_value]
  exact (alignment_residual _ _).2

theorem rneInt_nat_div (m d : ℕ) (hd : 0 < d) :
    rneInt ((m : ℚ) / (d : ℚ)) =
      if d < 2 * (m % d) ∨ (2 * (m % d) = d ∧ m / d % 2 = 1)
      then ((m / d + 1 : ℕ) : ℤ) else ((m / d : ℕ) : ℤ) := by
  have hp : (0 : ℚ) < (d : ℚ) := Rat.natCast_pos.mpr hd
  have hn : ((m % d : ℕ) : ℚ) + (d : ℚ) * ((m / d : ℕ) : ℚ) = m := by
    exact_mod_cast Nat.mod_add_div m d
  have hrem : (m : ℚ) / (d : ℚ) - ((m / d : ℕ) : ℚ) = (m % d : ℕ) / (d : ℚ) := by
    have hc := Rat.div_mul_cancel (a := (m : ℚ)) (Rat.ne_of_gt hp)
    have hr := Rat.div_mul_cancel (a := ((m % d : ℕ) : ℚ)) (Rat.ne_of_gt hp)
    grind
  have he : (1 : ℚ) < 2 * ((m % d : ℕ) / (d : ℚ)) ↔ d < 2 * (m % d) := by
    have hc := Rat.div_mul_cancel (a := ((m % d : ℕ) : ℚ)) (Rat.ne_of_gt hp)
    have hi := Rat.mul_lt_mul_right (a := (1 : ℚ)) (b := 2 * ((m % d : ℕ) / (d : ℚ))) hp
    have hc' : (2 : ℚ) * ((m % d : ℕ) / (d : ℚ)) * d = ((2 * (m % d) : ℕ) : ℚ) := by
      simp only [Rat.natCast_mul]; grind
    rw [Rat.one_mul, hc'] at hi
    exact hi.symm.trans Rat.natCast_lt_natCast
  have ht : 2 * ((m % d : ℕ) / (d : ℚ)) = (1 : ℚ) ↔ 2 * (m % d) = d := by
    have hc := Rat.div_mul_cancel (a := ((m % d : ℕ) : ℚ)) (Rat.ne_of_gt hp)
    have hdne := Rat.ne_of_gt hp
    constructor
    · intro h
      have h' : ((2 * (m % d) : ℕ) : ℚ) = (d : ℚ) := by
        simp only [Rat.natCast_mul]; grind
      exact Rat.natCast_inj.mp h'
    · intro h
      have h' : (2 : ℚ) * ((m % d : ℕ) : ℚ) = (d : ℚ) := by exact_mod_cast h
      grind
  unfold rneInt
  rw [floor_nat_div _ _ hd]
  simp only [Rat.intCast_natCast, hrem, he, ht]
  have hp2 : ((m / d : ℕ) : ℤ) % 2 = 1 ↔ m / d % 2 = 1 := by omega
  simp only [hp2, Int.natCast_add, Int.natCast_one]

end TensorCore.EFMachine
