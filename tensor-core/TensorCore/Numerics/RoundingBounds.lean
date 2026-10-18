import TensorCore.Numerics.Rounding

/-! Exponent and significand bounds for FP32 rounding. -/

namespace TensorCore

theorem binade_grid (e : ℤ) : pow2 e = 8388608 * pow2 (e - 23) := by
  have h : e = 23 + (e - 23) := by omega
  rw [h, pow2_add]
  have hc : pow2 23 = 8388608 := by decide
  rw [hc]
  congr 2 <;> omega

theorem next_binade_grid (e : ℤ) : pow2 (e + 1) = 16777216 * pow2 (e - 23) := by
  rw [pow2_succ, binade_grid]
  grind

theorem maxFinite32_lt_pow128 : maxFinite32 < pow2 128 := by decide +kernel

theorem normExp_bounds (m : ℚ) (hm : 0 < m) (hr : m ≤ maxFinite32) :
    -126 ≤ normExp m ∧ normExp m ≤ 127 ∧
    m < pow2 (normExp m + 1) ∧ (pow2 (normExp m) ≤ m ∨ normExp m = -126) := by
  have hs := magnitudeExponent_spec m hm
  have htop : magnitudeExponent m ≤ 127 := by
    apply Classical.byContradiction
    intro h
    have hg := pow2_le_of_le (e := 128) (f := magnitudeExponent m) (by omega)
    have := maxFinite32_lt_pow128
    grind
  have hmax : magnitudeExponent m ≤ normExp m := by unfold normExp; omega
  have he1 : -126 ≤ normExp m := by unfold normExp emin32; omega
  have he2 : normExp m ≤ 127 := by unfold normExp emin32; omega
  have hupper := pow2_le_of_le (e := magnitudeExponent m + 1)
    (f := normExp m + 1) (by omega)
  refine ⟨he1, he2, by grind, ?_⟩
  by_cases h : -126 ≤ magnitudeExponent m
  · left
    have : normExp m = magnitudeExponent m := by unfold normExp emin32; omega
    rw [this]; exact hs.1
  · right; unfold normExp emin32; omega

theorem roundSignificand_bounds (mode : RoundingMode) (t : ℚ)
    (ht : 0 ≤ t) (htop : t < 16777216) :
    0 ≤ roundSignificand mode t ∧ roundSignificand mode t ≤ 16777216 ∧
    t.floor ≤ roundSignificand mode t := by
  have hlo := floor_nonneg_of_nonneg t ht
  have hhi : t.floor < 16777216 := Rat.floor_lt_iff.mpr htop
  cases mode with
  | truncate => simp only [roundSignificand]; omega
  | nearestEven =>
    simp only [roundSignificand]
    rcases rneInt_cases t with ⟨h, _⟩ | ⟨h, _⟩ <;> omega

theorem roundSignificand_le_integer (mode : RoundingMode) (t : ℚ) (n : ℤ)
    (h : t ≤ n) : roundSignificand mode t ≤ n := by
  have hf := Rat.floor_monotone h
  rw [Rat.floor_intCast] at hf
  cases mode with
  | truncate => exact hf
  | nearestEven =>
    change rneInt t ≤ n
    rcases rneInt_cases t with ⟨hk, hc⟩ | ⟨hk, hc⟩
    · by_cases he : t.floor = n
      · rw [he] at hc
        exfalso; grind
      · omega
    · omega

theorem roundedSignificand_bounds (mode : RoundingMode) (m : ℚ)
    (hm : 0 < m) (hr : m ≤ maxFinite32) :
    0 ≤ roundedSignificand mode m ∧ roundedSignificand mode m ≤ 16777216 ∧
    (8388608 ≤ roundedSignificand mode m ∨ normExp m = -126) ∧
    (normExp m = 127 → roundedSignificand mode m ≤ 16777215) := by
  obtain ⟨he1, he2, hupper, hlower⟩ := normExp_bounds m hm hr
  have hq := pow2_pos (normExp m - 23)
  have ht : 0 < m / pow2 (normExp m - 23) := by
    apply (Rat.lt_div_iff hq).mpr
    simpa using hm
  have htop : m / pow2 (normExp m - 23) < 16777216 := by
    apply (Rat.div_lt_iff hq).mpr
    rwa [next_binade_grid] at hupper
  have hb := roundSignificand_bounds mode _ (Rat.le_of_lt ht) htop
  change 0 ≤ roundedSignificand mode m ∧ roundedSignificand mode m ≤ 16777216 ∧
    (m / pow2 (normExp m - 23)).floor ≤ roundedSignificand mode m at hb
  refine ⟨hb.1, hb.2.1, ?_, ?_⟩
  · rcases hlower with hl | he
    · left
      have hs : (8388608 : ℚ) ≤ m / pow2 (normExp m - 23) := by
        apply Classical.byContradiction
        intro h
        have h' : m / pow2 (normExp m - 23) < 8388608 := by grind
        have h'' := (Rat.div_lt_iff hq).mp h'
        rw [binade_grid] at hl
        grind
      have hf : 8388608 ≤ (m / pow2 (normExp m - 23)).floor := Rat.le_floor_iff.mpr hs
      omega
    · exact Or.inr he
  · intro he
    unfold roundedSignificand
    apply roundSignificand_le_integer
    have hscale : m / pow2 (normExp m - 23) ≤ (16777215 : ℚ) := by
      rw [he]
      apply Classical.byContradiction
      intro h
      have h' : (16777215 : ℚ) < m / pow2 (127 - 23) := by grind
      have h'' := (Rat.lt_div_iff (pow2_pos (127 - 23))).mp h'
      change (16777215 : ℚ) * pow2 104 < m at h''
      change m ≤ (16777215 : ℚ) * pow2 104 at hr
      grind
    exact hscale

theorem carry_spec (e k : ℤ) (he1 : -126 ≤ e) (he2 : e ≤ 127)
    (hk0 : 0 ≤ k) (hk1 : k ≤ 16777216)
    (hsub : 8388608 ≤ k ∨ e = -126) (htop : e = 127 → k ≤ 16777215) :
    -126 ≤ (carry e k).1 ∧ (carry e k).1 ≤ 127 ∧
    0 ≤ (carry e k).2 ∧ (carry e k).2 < 16777216 ∧
    (8388608 ≤ (carry e k).2 ∨ (carry e k).1 = -126) ∧
    ((carry e k).2 : ℚ) * pow2 ((carry e k).1 - 23) = (k : ℚ) * pow2 (e - 23) ∧
    e ≤ (carry e k).1 ∧ (k % 2 = 0 → (carry e k).2 % 2 = 0) := by
  unfold carry
  split
  · rename_i hk
    have hk' : k = 16777216 := hk
    subst k
    change -126 ≤ e + 1 ∧ e + 1 ≤ 127 ∧
      0 ≤ (8388608 : ℤ) ∧ (8388608 : ℤ) < 16777216 ∧
      ((8388608 : ℤ) ≤ 8388608 ∨ e + 1 = -126) ∧
      (8388608 : ℚ) * pow2 (e + 1 - 23) = 16777216 * pow2 (e - 23) ∧
      e ≤ e + 1 ∧ ((16777216 : ℤ) % 2 = 0 → (8388608 : ℤ) % 2 = 0)
    have hpow : pow2 (e + 1 - 23) = 2 * pow2 (e - 23) := by
      have : e + 1 - 23 = (e - 23) + 1 := by omega
      rw [this, pow2_succ]; grind
    rw [hpow]
    have he : e < 127 := by omega
    constructor
    · omega
    constructor
    · omega
    constructor
    · decide
    constructor
    · decide
    constructor
    · exact Or.inl (by decide)
    constructor
    · grind
    constructor
    · omega
    · simp
  · exact ⟨he1, he2, hk0, by omega, hsub, rfl, by omega, fun h => h⟩

end TensorCore
