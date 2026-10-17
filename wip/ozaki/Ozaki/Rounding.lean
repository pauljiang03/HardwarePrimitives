import Ozaki.Basic

/-! # Exponents and integer rounding

* `ceilLog2 m`: the smallest `E` with `m ≤ 2^E`, for `m > 0`. The Ozaki schemes scale each row
  of `A` (column of `B`) by this exponent of its largest magnitude.
* `roundNearestEven t`: the integer nearest to `t`, ties to even. It is the coefficient that
  binary32 round-to-nearest-even selects on a fixed grid; the σ-trick of Ozaki-I computes it.
  Its body is the same as `TensorCore.rneInt` and `MatrixCore.rneInt`.
* `truncInt t`: `t` rounded toward zero, the integer part kept by Ozaki-II's scaling. -/

local notation "ℕ" => Nat
local notation "ℤ" => Int
local notation "ℚ" => Rat

namespace Ozaki

/-! ## Binary exponents -/

/-- `⌊log₂ m⌋` for `m > 0`, from the bit lengths of the numerator and denominator. -/
def floorLog2 (m : ℚ) : ℤ :=
  let e : ℤ := (m.num.natAbs.log2 : ℤ) - (m.den.log2 : ℤ)
  if m < 2 ^ e then e - 1 else e

theorem floorLog2_spec {m : ℚ} (hm : 0 < m) :
    (2 : ℚ) ^ floorLog2 m ≤ m ∧ m < 2 ^ (floorLog2 m + 1) := by
  have hden : (0 : ℚ) < m.den := Rat.natCast_pos.mpr m.den_pos
  have hnum0 : m.num ≠ 0 := fun h => by
    have := Rat.num_eq_zero.mp h; subst this; exact Rat.lt_irrefl hm
  have hnumnn : 0 ≤ m.num := Rat.num_nonneg.mpr (Rat.le_of_lt hm)
  have hmd : m * m.den = m.num := by
    have h := Rat.num_divInt_den m
    rw [Rat.divInt_eq_div, Rat.intCast_natCast] at h
    calc m * m.den = (m.num / (m.den : ℚ)) * m.den := by rw [h]
      _ = m.num := Rat.div_mul_cancel (Rat.ne_of_gt hden)
  have hnR : ((m.num.natAbs : ℕ) : ℚ) = (m.num : ℚ) := by
    rw [← Rat.intCast_natCast, Int.natAbs_of_nonneg hnumnn]
  have hn0 : m.num.natAbs ≠ 0 := fun h => hnum0 (Int.natAbs_eq_zero.mp h)
  have hd0 : m.den ≠ 0 := Nat.pos_iff_ne_zero.mp m.den_pos
  have h1 : ((2 ^ m.num.natAbs.log2 : ℕ) : ℚ) ≤ m.num.natAbs :=
    Rat.natCast_le_natCast.mpr (Nat.log2_self_le hn0)
  have h2 : (m.num.natAbs : ℚ) < ((2 ^ (m.num.natAbs.log2 + 1) : ℕ) : ℚ) :=
    Rat.natCast_lt_natCast.mpr Nat.lt_log2_self
  have h3 : ((2 ^ m.den.log2 : ℕ) : ℚ) ≤ m.den :=
    Rat.natCast_le_natCast.mpr (Nat.log2_self_le hd0)
  have h4 : (m.den : ℚ) < ((2 ^ (m.den.log2 + 1) : ℕ) : ℚ) :=
    Rat.natCast_lt_natCast.mpr Nat.lt_log2_self
  rw [← two_pow_natCast] at h1 h2 h3 h4
  rw [hnR] at h1 h2
  generalize hA : (m.num.natAbs.log2 : ℤ) = a at *
  generalize hB : (m.den.log2 : ℤ) = b at *
  have hc1 : ((m.num.natAbs.log2 + 1 : ℕ) : ℤ) = a + 1 := by omega
  have hc2 : ((m.den.log2 + 1 : ℕ) : ℤ) = b + 1 := by omega
  rw [hc1] at h2; rw [hc2] at h4
  have lo : (2 : ℚ) ^ (a - b - 1) < m := by
    have hq := two_pow_pos (a - b - 1)
    have e1 : (2 : ℚ) ^ (a - b - 1) * 2 ^ (b + 1) = 2 ^ a := by
      rw [← two_pow_add]; congr 1; omega
    have e2 : (2 : ℚ) ^ (a - b - 1) * m.den < 2 ^ (a - b - 1) * 2 ^ (b + 1) :=
      (Rat.mul_lt_mul_left hq).mpr h4
    rw [e1] at e2
    have e3 : (2 : ℚ) ^ (a - b - 1) * m.den < m * m.den := by rw [hmd]; grind
    exact Rat.lt_of_mul_lt_mul_right e3 (Rat.le_of_lt hden)
  have hi : m < (2 : ℚ) ^ (a - b + 1) := by
    have hq := two_pow_pos (a - b + 1)
    have e1 : (2 : ℚ) ^ (a - b + 1) * 2 ^ b = 2 ^ (a + 1) := by
      rw [← two_pow_add]; congr 1; omega
    have e2 : (2 : ℚ) ^ (a - b + 1) * 2 ^ b ≤ 2 ^ (a - b + 1) * m.den :=
      Rat.mul_le_mul_of_nonneg_left h3 (Rat.le_of_lt hq)
    rw [e1] at e2
    have e3 : m * m.den < 2 ^ (a - b + 1) * m.den := by rw [hmd]; grind
    exact Rat.lt_of_mul_lt_mul_right e3 (Rat.le_of_lt hden)
  have hdef : floorLog2 m = if m < (2 : ℚ) ^ (a - b) then a - b - 1 else a - b := by
    unfold floorLog2; rw [hA, hB]
  rw [hdef]
  split
  · have : a - b - 1 + 1 = a - b := by omega
    rw [this]; exact ⟨Rat.le_of_lt lo, by assumption⟩
  · exact ⟨by grind, hi⟩

/-- `⌈log₂ m⌉` for `m > 0`: the smallest `E` with `m ≤ 2^E`. -/
def ceilLog2 (m : ℚ) : ℤ := if m = 2 ^ floorLog2 m then floorLog2 m else floorLog2 m + 1

theorem ceilLog2_spec {m : ℚ} (hm : 0 < m) :
    (2 : ℚ) ^ (ceilLog2 m - 1) < m ∧ m ≤ 2 ^ ceilLog2 m := by
  obtain ⟨h1, h2⟩ := floorLog2_spec hm
  unfold ceilLog2
  split
  · rename_i h
    refine ⟨?_, by grind⟩
    have := two_pow_lt (show floorLog2 m - 1 < floorLog2 m by omega)
    grind
  · rename_i h
    refine ⟨?_, Rat.le_of_lt h2⟩
    have : floorLog2 m + 1 - 1 = floorLog2 m := by omega
    rw [this]
    grind

/-- `ceilLog2 m` is the least exponent whose power of two bounds `m`. -/
theorem ceilLog2_le_iff {m : ℚ} (hm : 0 < m) (e : ℤ) : ceilLog2 m ≤ e ↔ m ≤ 2 ^ e := by
  obtain ⟨h1, h2⟩ := ceilLog2_spec hm
  constructor
  · intro h; exact Rat.le_trans h2 (two_pow_le h)
  · intro h
    apply Classical.byContradiction
    intro hn
    have := two_pow_le (show e ≤ ceilLog2 m - 1 by omega)
    grind

/-! ## Round to nearest, ties to even -/

/-- The integer nearest to `t`, ties to even: floor, then a doubled-remainder comparison. -/
def roundNearestEven (t : ℚ) : ℤ :=
  if 1 < 2 * (t - t.floor) ∨ (2 * (t - t.floor) = 1 ∧ t.floor % 2 = 1) then t.floor + 1
  else t.floor

theorem floor_frac (t : ℚ) : (t.floor : ℚ) ≤ t ∧ t < (t.floor : ℚ) + 1 := by
  have h1 := Rat.floor_le t
  have h2 := Rat.lt_floor_add_one t
  simp only [Rat.intCast_add, Rat.intCast_one] at h2
  exact ⟨h1, h2⟩

/-- `|t − roundNearestEven t| ≤ 1/2`. -/
theorem roundNearestEven_error (t : ℚ) : 2 * Rat.abs (t - roundNearestEven t) ≤ 1 := by
  have ⟨h1, h2⟩ := floor_frac t
  unfold roundNearestEven
  split
  · rename_i h
    simp only [Rat.intCast_add, Rat.intCast_one]
    rw [abs_def]; split <;> grind
  · rename_i h
    rw [abs_def]; split <;> grind

theorem roundNearestEven_intCast (k : ℤ) : roundNearestEven (k : ℚ) = k := by
  unfold roundNearestEven
  rw [Rat.floor_intCast]
  have h : (k : ℚ) - (k : ℚ) = 0 := by grind
  rw [h, if_neg]
  intro hc
  rcases hc with hc | ⟨hc, _⟩ <;> grind

/-- Rounding never leaves an interval with integer endpoints. -/
theorem roundNearestEven_le {t : ℚ} {n : ℤ} (h : t ≤ n) : roundNearestEven t ≤ n := by
  have ⟨h1, h2⟩ := floor_frac t
  have hf : t.floor ≤ n := by
    have := Rat.floor_monotone h; rwa [Rat.floor_intCast] at this
  unfold roundNearestEven
  split
  · rename_i hc
    by_cases he : t.floor = n
    · exfalso
      have hcast : (t.floor : ℚ) = n := by rw [he]
      grind
    · omega
  · exact hf

theorem le_roundNearestEven {t : ℚ} {n : ℤ} (h : (n : ℚ) ≤ t) : n ≤ roundNearestEven t := by
  have hf : n ≤ t.floor := Rat.le_floor_iff.mpr h
  unfold roundNearestEven
  split <;> omega

/-- `|t| ≤ n` with `n` an integer bounds the rounded value by `n`. -/
theorem natAbs_roundNearestEven_le {t : ℚ} {n : ℕ} (h : Rat.abs t ≤ n) :
    (roundNearestEven t).natAbs ≤ n := by
  have ⟨h1, h2⟩ := (abs_le_iff t n).mp h
  have u := roundNearestEven_le (n := (n : ℤ)) (by rw [Rat.intCast_natCast]; exact h2)
  have l := le_roundNearestEven (n := -(n : ℤ)) (by
    rw [Rat.intCast_neg, Rat.intCast_natCast]; exact h1)
  omega

/-- Adding an even integer commutes with rounding. -/
theorem roundNearestEven_add_even (t : ℚ) (k : ℤ) :
    roundNearestEven (t + (2 * k : ℤ)) = roundNearestEven t + 2 * k := by
  unfold roundNearestEven
  have hf : (t + ((2 * k : ℤ) : ℚ)).floor = t.floor + 2 * k := Rat.floor_add_intCast
  rw [hf]
  have hfr : t + ((2 * k : ℤ) : ℚ) - ((t.floor + 2 * k : ℤ) : ℚ) = t - (t.floor : ℚ) := by
    rw [Rat.intCast_add]; grind
  rw [hfr]
  have hpar : (t.floor + 2 * k) % 2 = t.floor % 2 := by omega
  rw [hpar]
  split <;> omega

/-! ## Truncation toward zero -/

/-- `t` rounded toward zero. -/
def truncInt (t : ℚ) : ℤ := if t < 0 then -((-t).floor) else t.floor

/-- Truncation loses less than one and never increases the magnitude. -/
theorem truncInt_spec (t : ℚ) :
    Rat.abs (t - truncInt t) < 1 ∧ Rat.abs (truncInt t : ℚ) ≤ Rat.abs t := by
  unfold truncInt
  split
  · rename_i ht
    have ⟨h1, h2⟩ := floor_frac (-t)
    have hf : (0 : ℤ) ≤ (-t).floor := Rat.le_floor_iff.mpr (by simp; grind)
    have hf' : (0 : ℚ) ≤ ((-t).floor : ℚ) := Rat.intCast_nonneg.mpr hf
    rw [Rat.intCast_neg, abs_neg, abs_of_nonneg hf', abs_of_neg ht]
    refine ⟨?_, by grind⟩
    rw [abs_lt_iff]; grind
  · rename_i ht
    have ⟨h1, h2⟩ := floor_frac t
    have hf : (0 : ℤ) ≤ t.floor := Rat.le_floor_iff.mpr (by simp; grind)
    have hf' : (0 : ℚ) ≤ (t.floor : ℚ) := Rat.intCast_nonneg.mpr hf
    rw [abs_of_nonneg hf', abs_of_nonneg (by grind : (0 : ℚ) ≤ t)]
    refine ⟨?_, h1⟩
    rw [abs_lt_iff]; grind

theorem natAbs_truncInt_le {t : ℚ} {n : ℕ} (h : Rat.abs t ≤ n) : (truncInt t).natAbs ≤ n := by
  have h1 := (truncInt_spec t).2
  rw [abs_intCast] at h1
  exact Rat.natCast_le_natCast.mp (Rat.le_trans h1 h)

end Ozaki
