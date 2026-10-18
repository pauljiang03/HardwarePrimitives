import TensorCore.Kernels.EFT.SplitDefs
import TensorCore.EFT.Extraction

/-! Correctness of the bounded high/low split. -/

namespace TensorCore.EFMachine

theorem multiplySignificands_exact (a b : BitVec 11) :
    (multiplySignificands a b).toNat = a.toNat * b.toNat := by
  have ha := a.isLt
  have hb := b.isLt
  have hprod : a.toNat * b.toNat < 2 ^ 24 := by
    have h := Nat.mul_le_mul (show a.toNat ≤ 2047 by omega) (show b.toNat ≤ 2047 by omega)
    omega
  simp [multiplySignificands, BitVec.toNat_mul,
    Nat.mod_eq_of_lt (show a.toNat < 2 ^ 24 by omega),
    Nat.mod_eq_of_lt (show b.toNat < 2 ^ 24 by omega), Nat.mod_eq_of_lt hprod]

theorem splitMagnitude_coarse (m : BitVec 24) (gap : BitVec 8) :
    (splitMagnitude m gap).coarse.toNat = m.toNat / 2 ^ gap.toNat * 2 ^ gap.toNat := by
  have hm := m.isLt
  have hle := Nat.div_mul_le_self m.toNat (2 ^ gap.toNat)
  unfold splitMagnitude
  split
  · rename_i h
    have hg : 24 ≤ gap.toNat := by simpa [BitVec.le_def] using h
    have hp : 2 ^ 24 ≤ 2 ^ gap.toNat := Nat.pow_le_pow_right (by decide) hg
    have hz : m.toNat / 2 ^ gap.toNat = 0 := Nat.div_eq_of_lt (by omega)
    simp [hz]
  · change (((m >>> gap.toNat) <<< gap.toNat) : BitVec 24).toNat = _
    rw [BitVec.toNat_shiftLeft, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow,
      Nat.shiftLeft_eq, Nat.mod_eq_of_lt (by omega)]

theorem splitMagnitude_low (m : BitVec 24) (gap : BitVec 8) :
    (splitMagnitude m gap).low.toNat = m.toNat % 2 ^ gap.toNat := by
  have hc := splitMagnitude_coarse m gap
  have hle := Nat.div_mul_le_self m.toNat (2 ^ gap.toNat)
  have hmod := Nat.mod_add_div m.toNat (2 ^ gap.toNat)
  rw [Nat.mul_comm] at hmod
  by_cases hg : gap ≥ 24
  · simp only [splitMagnitude, if_pos hg] at hc ⊢
    have hz : m.toNat / 2 ^ gap.toNat * 2 ^ gap.toNat = 0 := by simpa using hc.symm
    omega
  · simp only [splitMagnitude, if_neg hg] at hc ⊢
    rw [BitVec.toNat_sub_of_le (by rw [BitVec.le_def]; rw [hc]; exact hle)]
    rw [hc]
    omega

theorem splitMagnitude_reconstruct (m : BitVec 24) (gap : BitVec 8) :
    (splitMagnitude m gap).coarse.toNat + (splitMagnitude m gap).low.toNat = m.toNat := by
  rw [splitMagnitude_coarse, splitMagnitude_low]
  have h := Nat.mod_add_div m.toNat (2 ^ gap.toNat)
  rw [Nat.mul_comm] at h
  omega

theorem splitMagnitude_low_lt (m : BitVec 24) (gap : BitVec 8) :
    (splitMagnitude m gap).low.toNat < 2 ^ gap.toNat := by
  rw [splitMagnitude_low]
  exact Nat.mod_lt _ (Nat.two_pow_pos _)

theorem splitMagnitude_shift_bound (gap : BitVec 8) (h : ¬ gap ≥ 24) : gap.toNat < 24 := by
  simpa [BitVec.le_def] using h

private theorem floor_nat_div (m d : ℕ) (hd : 0 < d) :
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

/-- Specification-side interpretation only; the machine stores a separate sign bit. -/
def signedDyadic (negative : Bool) (m : ℕ) (scale : ℤ) : ℚ :=
  if negative then -((m : ℚ) * pow2 scale) else (m : ℚ) * pow2 scale

/-- The machine coarse component equals exact truncation at any binary scale and for either sign. -/
theorem splitMagnitude_coarse_truncGrid (negative : Bool) (m : BitVec 24)
    (gap : BitVec 8) (scale : ℤ) :
    signedDyadic negative (splitMagnitude m gap).coarse.toNat scale =
      truncGrid (signedDyadic negative m.toNat scale) (scale + gap.toNat) := by
  have hp := pow2_pos scale
  have hd : 0 < (2 ^ gap.toNat : ℕ) := Nat.two_pow_pos _
  have hdp : (0 : ℚ) < ((2 ^ gap.toNat : ℕ) : ℚ) := Rat.natCast_pos.mpr hd
  have he : pow2 (scale + gap.toNat) = pow2 scale * ((2 ^ gap.toNat : ℕ) : ℚ) := by
    rw [pow2_add, pow2_natCast]
  have hdiv : (m.toNat : ℚ) * pow2 scale / pow2 (scale + gap.toNat) =
      (m.toNat : ℚ) / ((2 ^ gap.toNat : ℕ) : ℚ) := by
    rw [he]
    have hne := Rat.ne_of_gt hp
    have hdne := Rat.ne_of_gt hdp
    rw [Rat.div_def, Rat.inv_mul_rev]
    have hcancel := Rat.mul_inv_cancel (pow2 scale) hne
    rw [Rat.div_def]
    grind
  have hnonneg : (0 : ℚ) ≤ (m.toNat : ℚ) * pow2 scale :=
    Rat.mul_nonneg Rat.natCast_nonneg (Rat.le_of_lt hp)
  have hpos : ((splitMagnitude m gap).coarse.toNat : ℚ) * pow2 scale =
      truncGrid ((m.toNat : ℚ) * pow2 scale) (scale + gap.toNat) := by
    rw [alignment_value, truncBits_nonneg_eq _ _ hnonneg, hdiv,
      floor_nat_div _ _ hd, splitMagnitude_coarse, Rat.natCast_mul, he]
    simp only [Rat.intCast_natCast]
    grind
  cases negative
  · exact hpos
  · simpa only [signedDyadic, Bool.false_eq_true, if_false, if_true, truncGrid_neg] using congrArg Neg.neg hpos

/-- The low component refines the independently specified exact residual. -/
theorem splitMagnitude_low_residual (negative : Bool) (m : BitVec 24)
    (gap : BitVec 8) (scale : ℤ) :
    signedDyadic negative (splitMagnitude m gap).low.toNat scale =
      signedDyadic negative m.toNat scale -
        truncGrid (signedDyadic negative m.toNat scale) (scale + gap.toNat) := by
  rw [← splitMagnitude_coarse_truncGrid]
  have h := splitMagnitude_reconstruct m gap
  have hq := congrArg (fun n : ℕ => (n : ℚ)) h
  rw [Rat.natCast_add] at hq
  cases negative <;> simp only [signedDyadic, Bool.false_eq_true, if_false, if_true] <;> grind

end TensorCore.EFMachine
