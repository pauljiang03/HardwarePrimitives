import TensorCore.Numerics.Exact

/-! Truncation onto a binary grid and its residuals. -/

namespace TensorCore

theorem alignment_value (x : ℚ) (e : ℤ) :
    truncGrid x e = (truncBits x e : ℚ) * pow2 e := rfl

/-- Strict signed bounds, valid for every positive binary grid and either input sign. -/
theorem alignment_residual_bounds (x : ℚ) (e : ℤ) :
    -pow2 e < x - truncGrid x e ∧ x - truncGrid x e < pow2 e := by
  have hq := pow2_pos e
  have hq0 : 0 ≤ pow2 e := by grind
  have hqn : pow2 e ≠ 0 := by grind
  unfold truncGrid truncBits
  split
  · have lo := Rat.mul_le_mul_of_nonneg_right (Rat.floor_le (-x / pow2 e)) hq0
    rw [Rat.div_mul_cancel hqn] at lo
    have hi := (Rat.div_lt_iff hq).mp (Rat.lt_floor_add_one (-x / pow2 e))
    simp only [Rat.intCast_neg, Rat.intCast_add] at *
    grind
  · have lo := Rat.mul_le_mul_of_nonneg_right (Rat.floor_le (x / pow2 e)) hq0
    rw [Rat.div_mul_cancel hqn] at lo
    have hi := (Rat.div_lt_iff hq).mp (Rat.lt_floor_add_one (x / pow2 e))
    simp only [Rat.intCast_add] at *
    grind

theorem alignment_residual (x : ℚ) (e : ℤ) :
    x = truncGrid x e + (x - truncGrid x e) ∧
    absQ (x - truncGrid x e) < pow2 e := by
  have h := alignment_residual_bounds x e
  unfold absQ
  split <;> grind

theorem floor_sub_intCast (t : ℚ) (k : ℤ) : (t - k).floor = t.floor - k := by
  have h := Rat.floor_add_intCast (x := t) (y := -k)
  rw [Rat.intCast_neg] at h
  have : t - (k : ℚ) = t + -(k : ℚ) := by grind
  rw [this, h]
  omega

theorem floor_grid_split (m : ℚ) (N : ℕ) :
    m.floor = (N : ℤ) * (m / (N : ℚ)).floor + (m - (N : ℚ) * (m / (N : ℚ)).floor).floor := by
  have hq : (N : ℚ) * ((m / (N : ℚ)).floor : ℚ) = (((N : ℤ) * (m / (N : ℚ)).floor : ℤ) : ℚ) := by
    rw [Rat.intCast_mul, Rat.intCast_natCast]
  rw [hq, floor_sub_intCast]
  omega

theorem truncBits_nonneg_eq (x : ℚ) (e : ℤ) (hx : 0 ≤ x) :
    truncBits x e = (x / pow2 e).floor := by
  unfold truncBits
  rw [if_neg (by grind)]

theorem truncGrid_le_self (x : ℚ) (e : ℤ) (hx : 0 ≤ x) : truncGrid x e ≤ x := by
  have hq := pow2_pos e
  unfold truncGrid
  rw [truncBits_nonneg_eq x e hx]
  have := Rat.mul_le_mul_of_nonneg_right (Rat.floor_le (x / pow2 e)) (Rat.le_of_lt hq)
  rwa [Rat.div_mul_cancel (Rat.ne_of_gt hq)] at this

theorem truncGrid_zero (e : ℤ) : truncGrid 0 e = 0 := by
  unfold truncGrid truncBits
  rw [if_neg (by decide +kernel), Rat.div_def, Rat.zero_mul, ← Rat.intCast_zero,
    Rat.floor_intCast]
  simp

theorem truncGrid_neg (z : ℚ) (e : ℤ) : truncGrid (-z) e = -truncGrid z e := by
  by_cases hz0 : z = 0
  · subst hz0
    rw [Rat.neg_zero, truncGrid_zero]
    simp
  · unfold truncGrid truncBits
    by_cases hz : z < 0
    · rw [if_pos hz, if_neg (by grind)]
      rw [Rat.intCast_neg]
      grind
    · rw [if_neg hz, if_pos (by grind)]
      rw [Rat.intCast_neg]
      grind

/-- `trunc_qA(x) = trunc_qE(x) + trunc_qA(x − trunc_qE(x))` for `qE = 2^τ · qA`. -/
theorem truncGrid_split (x : ℚ) (a : ℤ) (τ : ℕ) :
    truncGrid x a = truncGrid x (a + τ) + truncGrid (x - truncGrid x (a + τ)) a := by
  have hqa := pow2_pos a
  have hne := Rat.ne_of_gt hqa
  have hN : pow2 (a + τ) = pow2 a * ((2 ^ τ : ℕ) : ℚ) := by
    rw [pow2_add, pow2_natCast]
  have hNpos : (0 : ℚ) < ((2 ^ τ : ℕ) : ℚ) := Rat.natCast_pos.mpr (Nat.two_pow_pos τ)
  have hNne : ((2 ^ τ : ℕ) : ℚ) ≠ 0 := Rat.ne_of_gt hNpos
  have hqEne : pow2 a * ((2 ^ τ : ℕ) : ℚ) ≠ 0 := Rat.ne_of_gt (Rat.mul_pos hqa hNpos)
  have key : ∀ y : ℚ, 0 ≤ y →
      truncGrid y a = truncGrid y (a + τ) + truncGrid (y - truncGrid y (a + τ)) a := by
    intro y hy
    have hyq : y / pow2 a * pow2 a = y := Rat.div_mul_cancel hne
    have hmq : 0 ≤ y / pow2 a := by
      have := Rat.div_lt_iff (a := y) (c := 0) hqa
      grind
    generalize y / pow2 a = m at hyq hmq
    subst hyq
    have hfloorN : ((m / ((2 ^ τ : ℕ) : ℚ)).floor : ℚ) ≤ m / ((2 ^ τ : ℕ) : ℚ) :=
      Rat.floor_le _
    have hdivN : m / ((2 ^ τ : ℕ) : ℚ) * ((2 ^ τ : ℕ) : ℚ) = m := Rat.div_mul_cancel hNne
    have h1 : truncGrid (m * pow2 a) a = ((m.floor : ℤ) : ℚ) * pow2 a := by
      rw [alignment_value, truncBits_nonneg_eq _ _ hy, Rat.mul_div_cancel hne]
    have hcoarse : m * pow2 a / pow2 (a + τ) = m / ((2 ^ τ : ℕ) : ℚ) := by
      rw [hN]
      have : m * pow2 a = m / ((2 ^ τ : ℕ) : ℚ) * (pow2 a * ((2 ^ τ : ℕ) : ℚ)) := by grind
      rw [this, Rat.mul_div_cancel hqEne]
    have h2 : truncGrid (m * pow2 a) (a + τ) =
        (((m / ((2 ^ τ : ℕ) : ℚ)).floor : ℤ) : ℚ) * (pow2 a * ((2 ^ τ : ℕ) : ℚ)) := by
      rw [alignment_value, truncBits_nonneg_eq _ _ hy, hcoarse, hN]
    have hrem_eq : m * pow2 a - truncGrid (m * pow2 a) (a + τ) =
        (m - ((2 ^ τ : ℕ) : ℚ) * (((m / ((2 ^ τ : ℕ) : ℚ)).floor : ℤ) : ℚ)) * pow2 a := by
      rw [h2]; grind
    have hrem_nonneg :
        0 ≤ m - ((2 ^ τ : ℕ) : ℚ) * (((m / ((2 ^ τ : ℕ) : ℚ)).floor : ℤ) : ℚ) := by
      have := Rat.mul_le_mul_of_nonneg_right hfloorN (Rat.le_of_lt hNpos)
      rw [hdivN] at this
      grind
    have h3 : truncGrid (m * pow2 a - truncGrid (m * pow2 a) (a + τ)) a =
        (((m - ((2 ^ τ : ℕ) : ℚ) * (((m / ((2 ^ τ : ℕ) : ℚ)).floor : ℤ) : ℚ)).floor : ℤ) : ℚ) *
          pow2 a := by
      rw [hrem_eq, alignment_value,
        truncBits_nonneg_eq _ _ (Rat.mul_nonneg hrem_nonneg (Rat.le_of_lt hqa)),
        Rat.mul_div_cancel hne]
    rw [h3, h1, h2, floor_grid_split m (2 ^ τ), Rat.intCast_add, Rat.intCast_mul,
      Rat.intCast_natCast]
    grind
  by_cases hx : 0 ≤ x
  · exact key x hx
  · have h := key (-x) (by grind)
    rw [truncGrid_neg, truncGrid_neg] at h
    have h2 : -x - -truncGrid x (a + τ) = -(x - truncGrid x (a + τ)) := by grind
    rw [h2, truncGrid_neg] at h
    grind

/-- A term already on the grid keeps its coefficient. -/
theorem truncBits_of_grid (k e : ℤ) : truncBits ((k : ℚ) * pow2 e) e = k := by
  have hne := Rat.ne_of_gt (pow2_pos e)
  unfold truncBits
  split
  · rw [show -((k : ℚ) * pow2 e) = ((-k : ℤ) : ℚ) * pow2 e by
        rw [Rat.intCast_neg]; grind,
      Rat.mul_div_cancel hne, Rat.floor_intCast]
    omega
  · rw [Rat.mul_div_cancel hne, Rat.floor_intCast]

/-- Truncation never increases the magnitude of a scaled value. -/
theorem truncBits_abs_le (x : ℚ) (e : ℤ) :
    ((truncBits x e).natAbs : ℚ) ≤ absQ x / pow2 e := by
  have hp := pow2_pos e
  unfold truncBits
  split
  · rename_i hx
    have hn : 0 ≤ -x / pow2 e := by
      have := Rat.div_lt_iff (a := -x) (c := 0) hp
      grind
    have hf : 0 ≤ (-x / pow2 e).floor := Rat.le_floor_iff.mpr hn
    rw [Int.natAbs_neg, ← Rat.intCast_natCast, Int.natAbs_of_nonneg hf, absQ_of_neg hx]
    exact Rat.floor_le _
  · rename_i hx
    have hn : 0 ≤ x / pow2 e := by
      have := Rat.div_lt_iff (a := x) (c := 0) hp
      grind
    have hf : 0 ≤ (x / pow2 e).floor := Rat.le_floor_iff.mpr hn
    rw [← Rat.intCast_natCast, Int.natAbs_of_nonneg hf, absQ_of_nonneg (by grind)]
    exact Rat.floor_le _

/-- Two integer magnitude bits plus F mantissa bits suffice for each aligned term. -/

theorem truncGrid_abs_le (x : ℚ) (e : ℤ) : absQ (truncGrid x e) ≤ absQ x := by
  have hq := pow2_pos e
  have h := truncBits_abs_le x e
  unfold truncGrid
  rw [absQ_mul_pos _ _ hq, absQ_intCast]
  have := Rat.mul_le_mul_of_nonneg_right h (Rat.le_of_lt hq)
  rwa [Rat.div_mul_cancel (Rat.ne_of_gt hq)] at this

theorem truncGrid_fixed (k e : ℤ) : truncGrid ((k : ℚ) * pow2 e) e = (k : ℚ) * pow2 e := by
  have hn : pow2 e ≠ 0 := Rat.ne_of_gt (pow2_pos e)
  unfold truncGrid truncBits
  split
  · have he : -((k : ℚ) * pow2 e) / pow2 e = ((-k : ℤ) : ℚ) := by
      rw [← Rat.neg_mul, Rat.mul_div_cancel hn, Rat.intCast_neg]
    rw [he, Rat.floor_intCast]
    simp
  · rw [Rat.mul_div_cancel hn, Rat.floor_intCast]

theorem truncGrid_exact_of_grid (k scale grid : ℤ) (h : grid ≤ scale) :
    truncGrid ((k : ℚ) * pow2 scale) grid = (k : ℚ) * pow2 scale := by
  obtain ⟨j, hj⟩ := finite_on_grid k (scale + 23) (grid + 23) (by omega)
  have hs : scale + 23 - 23 = scale := by omega
  have hg : grid + 23 - 23 = grid := by omega
  rw [hs, hg] at hj
  rw [hj, truncGrid_fixed]

end TensorCore
