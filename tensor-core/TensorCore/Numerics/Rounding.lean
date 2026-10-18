import TensorCore.Numerics.EncodingProperties

/-! Integer rounding and binary exponents. -/

namespace TensorCore

theorem floor_frac_bounds (t : ℚ) : 0 ≤ t - t.floor ∧ t - t.floor < 1 := by
  have h1 := Rat.floor_le t
  have h2 := Rat.lt_floor_add_one t
  simp only [Rat.intCast_add, Rat.intCast_one] at h2
  grind

theorem rneInt_cases (t : ℚ) :
    (rneInt t = t.floor + 1 ∧
      (1 < 2 * (t - t.floor) ∨ (2 * (t - t.floor) = 1 ∧ t.floor % 2 = 1))) ∨
    (rneInt t = t.floor ∧
      ¬(1 < 2 * (t - t.floor) ∨ (2 * (t - t.floor) = 1 ∧ t.floor % 2 = 1))) := by
  unfold rneInt; split <;> simp [*]

theorem intCast_le_or_succ_le (j k : ℤ) : (j : ℚ) ≤ k ∨ (k : ℚ) + 1 ≤ j := by
  by_cases h : j ≤ k
  · exact Or.inl (Rat.intCast_le_intCast.mpr h)
  · right
    have : k + 1 ≤ j := by omega
    have h' := Rat.intCast_le_intCast.mpr this
    simpa [Rat.intCast_add, Rat.intCast_one] using h'

theorem rneInt_dist_le_half (t : ℚ) : 2 * absQ (t - rneInt t) ≤ 1 := by
  have h := floor_frac_bounds t
  rcases rneInt_cases t with ⟨hk, hc⟩ | ⟨hk, hc⟩ <;> rw [hk] <;>
    (try simp only [Rat.intCast_add, Rat.intCast_one]) <;> unfold absQ <;> split <;> grind

/-- The selected integer is at least as close as every integer. -/
theorem rneInt_nearest (t : ℚ) (j : ℤ) : absQ (t - rneInt t) ≤ absQ (t - j) := by
  have h := floor_frac_bounds t
  have hj := intCast_le_or_succ_le j t.floor
  rcases rneInt_cases t with ⟨hk, hc⟩ | ⟨hk, hc⟩ <;> rw [hk] <;>
    (try simp only [Rat.intCast_add, Rat.intCast_one]) <;> unfold absQ <;> split <;> split <;>
    grind

/-- An equally close different integer forces a tie, and the selection is then even. -/
theorem rneInt_tie_even (t : ℚ) (j : ℤ) (htie : absQ (t - j) = absQ (t - rneInt t))
    (hne : j ≠ rneInt t) : rneInt t % 2 = 0 := by
  have h := floor_frac_bounds t
  have hj := intCast_le_or_succ_le j t.floor
  have hj2 := intCast_le_or_succ_le (t.floor + 1) j
  simp only [Rat.intCast_add, Rat.intCast_one] at hj2
  rcases rneInt_cases t with ⟨hk, hc⟩ | ⟨hk, hc⟩ <;> rw [hk] at htie hne ⊢
  · have hne' : (j : ℚ) ≠ (t.floor : ℚ) + 1 := by
      intro he
      apply hne
      have : (j : ℚ) = ((t.floor + 1 : ℤ) : ℚ) := by
        simpa [Rat.intCast_add, Rat.intCast_one] using he
      exact Rat.intCast_inj.mp this
    simp only [Rat.intCast_add, Rat.intCast_one] at htie
    have hf : 2 * (t - t.floor) = 1 := by
      unfold absQ at htie; split at htie <;> split at htie <;> grind
    rcases hc with hc | ⟨_, hodd⟩
    · exfalso; rw [hf] at hc; exact Rat.lt_irrefl hc
    · omega
  · have hne' : (j : ℚ) ≠ (t.floor : ℚ) := fun he => hne (Rat.intCast_inj.mp he)
    have hf : 2 * (t - t.floor) = 1 := by
      unfold absQ at htie; split at htie <;> split at htie <;> grind
    have : ¬ (t.floor % 2 = 1) := fun hodd => hc (Or.inr ⟨hf, hodd⟩)
    omega

theorem floor_nonneg_of_nonneg (t : ℚ) (h : 0 ≤ t) : 0 ≤ t.floor := by
  have := Rat.lt_floor_add_one t
  simp only [Rat.intCast_add, Rat.intCast_one] at this
  have h2 : (-1 : ℚ) < t.floor := by grind
  have h3 : (-1 : ℤ) < t.floor := by
    have := Rat.intCast_lt_intCast (a := -1) (b := t.floor)
    simp only [Rat.intCast_neg, Rat.intCast_one] at this
    exact this.mp h2
  omega

theorem rneInt_nonneg (t : ℚ) (h : 0 ≤ t) : 0 ≤ rneInt t := by
  have := floor_nonneg_of_nonneg t h
  rcases rneInt_cases t with ⟨hk, _⟩ | ⟨hk, _⟩ <;> omega

/-- For positive x, `magnitudeExponent x` is the binary exponent: `2^e ≤ x < 2^(e+1)`. -/
theorem magnitudeExponent_spec (x : ℚ) (hx : 0 < x) :
    pow2 (magnitudeExponent x) ≤ x ∧ x < pow2 (magnitudeExponent x + 1) := by
  have hden : (0 : ℚ) < x.den := Rat.natCast_pos.mpr x.den_pos
  have hnum0 : x.num ≠ 0 := fun h => by
    have := Rat.num_eq_zero.mp h; subst this; exact Rat.lt_irrefl hx
  have hnumnn : 0 ≤ x.num := Rat.num_nonneg.mpr (Rat.le_of_lt hx)
  have hxd : x * x.den = x.num := by
    have h := Rat.num_divInt_den x
    rw [Rat.divInt_eq_div, Rat.intCast_natCast] at h
    calc x * x.den = (x.num / (x.den : ℚ)) * x.den := by rw [h]
      _ = x.num := Rat.div_mul_cancel (Rat.ne_of_gt hden)
  have hnR : ((x.num.natAbs : ℕ) : ℚ) = (x.num : ℚ) := by
    rw [← Rat.intCast_natCast, Int.natAbs_of_nonneg hnumnn]
  have hn0 : x.num.natAbs ≠ 0 := fun h => hnum0 (Int.natAbs_eq_zero.mp h)
  have hd0 : x.den ≠ 0 := Nat.pos_iff_ne_zero.mp x.den_pos
  have h1 : ((2 ^ x.num.natAbs.log2 : ℕ) : ℚ) ≤ x.num.natAbs :=
    Rat.natCast_le_natCast.mpr (Nat.log2_self_le hn0)
  have h2 : (x.num.natAbs : ℚ) < ((2 ^ (x.num.natAbs.log2 + 1) : ℕ) : ℚ) :=
    Rat.natCast_lt_natCast.mpr Nat.lt_log2_self
  have h3 : ((2 ^ x.den.log2 : ℕ) : ℚ) ≤ x.den :=
    Rat.natCast_le_natCast.mpr (Nat.log2_self_le hd0)
  have h4 : (x.den : ℚ) < ((2 ^ (x.den.log2 + 1) : ℕ) : ℚ) :=
    Rat.natCast_lt_natCast.mpr Nat.lt_log2_self
  rw [← pow2_natCast] at h1 h2 h3 h4
  rw [hnR] at h1 h2
  generalize hA : (x.num.natAbs.log2 : ℤ) = a at *
  generalize hB : (x.den.log2 : ℤ) = b at *
  have hcast1 : ((x.num.natAbs.log2 + 1 : ℕ) : ℤ) = a + 1 := by omega
  have hcast2 : ((x.den.log2 + 1 : ℕ) : ℤ) = b + 1 := by omega
  rw [hcast1] at h2; rw [hcast2] at h4
  have lo : pow2 (a - b - 1) < x := by
    have hq := pow2_pos (a - b - 1)
    have e1 : pow2 (a - b - 1) * pow2 (b + 1) = pow2 a := by
      rw [← pow2_add]; congr 1; omega
    have e2 : pow2 (a - b - 1) * x.den < pow2 (a - b - 1) * pow2 (b + 1) :=
      (Rat.mul_lt_mul_left hq).mpr h4
    rw [e1] at e2
    have e3 : pow2 (a - b - 1) * x.den < x * x.den := by rw [hxd]; grind
    exact Rat.lt_of_mul_lt_mul_right e3 (Rat.le_of_lt hden)
  have hi : x < pow2 (a - b + 1) := by
    have hq := pow2_pos (a - b + 1)
    have e1 : pow2 (a - b + 1) * pow2 b = pow2 (a + 1) := by
      rw [← pow2_add]; congr 1; omega
    have e2 : pow2 (a - b + 1) * pow2 b ≤ pow2 (a - b + 1) * x.den :=
      Rat.mul_le_mul_of_nonneg_left h3 (Rat.le_of_lt hq)
    rw [e1] at e2
    have e3 : x * x.den < pow2 (a - b + 1) * x.den := by rw [hxd]; grind
    exact Rat.lt_of_mul_lt_mul_right e3 (Rat.le_of_lt hden)
  have hdef : magnitudeExponent x = if x < pow2 (a - b) then a - b - 1 else a - b := by
    unfold magnitudeExponent; rw [hA, hB]
  rw [hdef]
  split
  · have : a - b - 1 + 1 = a - b := by omega
    rw [this]; exact ⟨Rat.le_of_lt lo, by assumption⟩
  · exact ⟨by grind, hi⟩

/-! ## Grid geometry -/

theorem dist_scale (m : ℚ) (q : ℚ) (hq : 0 < q) (j : ℤ) :
    absQ (m - j * q) = absQ (m / q - j) * q := by
  rw [← absQ_mul_pos _ q hq]
  have := Rat.div_mul_cancel (a := m) (Rat.ne_of_gt hq)
  congr 1
  grind

theorem magnitudeExponent_eq_of_bounds (x : ℚ) (e : ℤ) (h1 : pow2 e ≤ x)
    (h2 : x < pow2 (e + 1)) : magnitudeExponent x = e := by
  have hx : 0 < x := by have := pow2_pos e; grind
  obtain ⟨hlo, hhi⟩ := magnitudeExponent_spec x hx
  apply Classical.byContradiction
  intro hne
  rcases Int.lt_or_gt_of_ne hne with hlt | hgt
  · have := pow2_le_of_le (show magnitudeExponent x + 1 ≤ e by omega)
    grind
  · have := pow2_le_of_le (show e + 1 ≤ magnitudeExponent x by omega)
    grind

theorem magnitudeExponent_le_of_lt (x : ℚ) (hx : 0 < x) (e : ℤ) (h : x < pow2 (e + 1)) :
    magnitudeExponent x ≤ e := by
  obtain ⟨hlo, _⟩ := magnitudeExponent_spec x hx
  apply Classical.byContradiction
  intro hne
  have hle : e + 1 ≤ magnitudeExponent x := by omega
  have := pow2_le_of_le hle
  grind

theorem normExp_le_of_lt (x : ℚ) (hx : 0 < x) (e : ℤ) (h : x < pow2 (e + 1)) :
    normExp x ≤ max e (-126) := by
  unfold normExp emin32
  have := magnitudeExponent_le_of_lt x hx e h
  omega

end TensorCore
