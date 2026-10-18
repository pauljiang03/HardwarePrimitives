import TensorCore.Numerics.Binary.Encoding
import TensorCore.Numerics.RoundingBounds

/-! Exponent and significand bounds for binary rounding. -/

namespace TensorCore

theorem Format.binade_grid (f : Format) (e : ℤ) :
    pow2 e = ((2 ^ f.mantissaBits : ℕ) : ℚ) * pow2 (e - f.mantissaBits) := by
  rw [← pow2_natCast, ← pow2_add]
  congr 1
  omega

theorem Format.next_binade_grid (f : Format) (e : ℤ) :
    pow2 (e + 1) = ((2 ^ (f.mantissaBits + 1) : ℕ) : ℚ) * pow2 (e - f.mantissaBits) := by
  rw [← pow2_natCast, ← pow2_add]
  congr 1
  omega

theorem Format.maxFinite_lt (f : Format) : f.maxFinite < pow2 (f.emax + 1) := by
  unfold Format.maxFinite
  rw [f.next_binade_grid f.emax]
  have hq := pow2_pos (f.emax - f.mantissaBits)
  have h : ((2 ^ (f.mantissaBits + 1) - 1 : ℕ) : ℚ) < ((2 ^ (f.mantissaBits + 1) : ℕ) : ℚ) :=
    Rat.natCast_lt_natCast.mpr (by have := Nat.two_pow_pos (f.mantissaBits + 1); omega)
  exact Rat.mul_lt_mul_of_pos_right h hq

theorem binaryNormExp_bounds (f : Format) (hf : f.WellFormed) (m : ℚ) (hm : 0 < m)
    (hr : m ≤ f.maxFinite) :
    f.emin ≤ binaryNormExp f m ∧ binaryNormExp f m ≤ f.emax ∧
    m < pow2 (binaryNormExp f m + 1) ∧
    (pow2 (binaryNormExp f m) ≤ m ∨ binaryNormExp f m = f.emin) := by
  have hs := magnitudeExponent_spec m hm
  have hemin := f.emin_le_emax hf
  have htop : magnitudeExponent m ≤ f.emax := by
    apply Classical.byContradiction
    intro h
    have hg := pow2_le_of_le (e := f.emax + 1) (f := magnitudeExponent m) (by omega)
    have := f.maxFinite_lt
    grind
  have hmax : magnitudeExponent m ≤ binaryNormExp f m := by unfold binaryNormExp; omega
  have he1 : f.emin ≤ binaryNormExp f m := by unfold binaryNormExp; omega
  have he2 : binaryNormExp f m ≤ f.emax := by unfold binaryNormExp; omega
  have hupper := pow2_le_of_le (e := magnitudeExponent m + 1)
    (f := binaryNormExp f m + 1) (by omega)
  refine ⟨he1, he2, by grind, ?_⟩
  by_cases h : f.emin ≤ magnitudeExponent m
  · left
    have : binaryNormExp f m = magnitudeExponent m := by unfold binaryNormExp; omega
    rw [this]
    exact hs.1
  · right
    unfold binaryNormExp
    omega

theorem floor_le_ceil (t : ℚ) : t.floor ≤ t.ceil := by
  have h1 := Rat.floor_le t
  have h2 := Rat.le_ceil (x := t)
  exact Rat.intCast_le_intCast.mp (Rat.le_trans h1 h2)

theorem binaryCoefficient_bounds (mode : BinaryRoundingMode) (negative : Bool) (t : ℚ)
    (N : ℕ) (ht : 0 ≤ t) (htop : t < (N : ℚ)) :
    0 ≤ binaryCoefficient mode negative t ∧ binaryCoefficient mode negative t ≤ N ∧
    t.floor ≤ binaryCoefficient mode negative t ∧ binaryCoefficient mode negative t ≤ t.ceil := by
  have hlo := floor_nonneg_of_nonneg t ht
  have hhi : t.floor < N := Rat.floor_lt_iff.mpr (by rw [Rat.intCast_natCast]; exact htop)
  have hceil : t.ceil ≤ N := Rat.ceil_le_iff.mpr (by rw [Rat.intCast_natCast]; exact Rat.le_of_lt htop)
  have hfc := floor_le_ceil t
  have hceil' : t.ceil ≤ t.floor + 1 := by
    have h := Rat.ceil_lt (x := t)
    have h2 := Rat.lt_floor_add_one t
    have h3 : (t.ceil : ℚ) < (t.floor : ℚ) + 2 := by grind
    have h4 : t.ceil < t.floor + 2 := by
      have := Rat.intCast_lt_intCast (a := t.ceil) (b := t.floor + 2)
      simp only [Rat.intCast_add, Rat.intCast_ofNat] at this
      exact this.mp h3
    omega
  cases mode with
  | truncate => simp only [binaryCoefficient]; omega
  | nearestEven =>
    simp only [binaryCoefficient]
    have hr : rneInt t ≤ t.ceil := by
      rcases rneInt_cases t with ⟨h, hc⟩ | ⟨h, _⟩
      · rw [h]
        by_cases hint : t = t.floor
        · exfalso
          have h0 : t - t.floor = 0 := by rw [← hint]; exact Rat.sub_self
          rw [h0] at hc
          grind
        · have hlt : (t.floor : ℚ) < t := by
            have := Rat.floor_le t
            grind
          have : t.floor + 1 ≤ t.ceil := by
            apply Int.lt_iff_add_one_le.mp
            have := Rat.intCast_lt_intCast (a := t.floor) (b := t.ceil)
            apply this.mp
            have hc' := Rat.le_ceil (x := t)
            grind
          omega
      · omega
    rcases rneInt_cases t with ⟨h, _⟩ | ⟨h, _⟩ <;> omega
  | towardNegative => simp only [binaryCoefficient]; split <;> omega
  | towardPositive => simp only [binaryCoefficient]; split <;> omega

theorem binaryCoefficient_le_integer (mode : BinaryRoundingMode) (negative : Bool) (t : ℚ)
    (n : ℤ) (h : t ≤ n) : binaryCoefficient mode negative t ≤ n := by
  have hf := Rat.floor_monotone h
  rw [Rat.floor_intCast] at hf
  have hc : t.ceil ≤ n := Rat.ceil_le_iff.mpr h
  cases mode with
  | truncate => exact hf
  | nearestEven =>
    change rneInt t ≤ n
    rcases rneInt_cases t with ⟨hk, hcond⟩ | ⟨hk, _⟩
    · by_cases he : t.floor = n
      · have : (n : ℚ) ≤ t := by rw [← he]; exact Rat.floor_le t
        have ht : t = n := Rat.le_antisymm h this
        have h0 : t - t.floor = 0 := by rw [he, ht]; exact Rat.sub_self
        rw [h0] at hcond
        grind
      · omega
    · omega
  | towardNegative => simp only [binaryCoefficient]; split <;> omega
  | towardPositive => simp only [binaryCoefficient]; split <;> omega

theorem binaryRoundedCoeff_bounds (f : Format) (hf : f.WellFormed) (mode : BinaryRoundingMode)
    (negative : Bool) (m : ℚ) (hm : 0 < m) (hr : m ≤ f.maxFinite) :
    let e := binaryNormExp f m
    let k := binaryCoefficient mode negative (m / pow2 (e - f.mantissaBits))
    0 ≤ k ∧ k ≤ ((2 ^ (f.mantissaBits + 1) : ℕ) : ℤ) ∧
    (((2 ^ f.mantissaBits : ℕ) : ℤ) ≤ k ∨ e = f.emin) ∧
    (e = f.emax → k ≤ ((2 ^ (f.mantissaBits + 1) - 1 : ℕ) : ℤ)) := by
  intro e k
  obtain ⟨he1, he2, hupper, hlower⟩ := binaryNormExp_bounds f hf m hm hr
  have hq := pow2_pos (e - f.mantissaBits)
  have ht : 0 < m / pow2 (e - f.mantissaBits) := by
    apply (Rat.lt_div_iff hq).mpr
    simpa using hm
  have htop : m / pow2 (e - f.mantissaBits) < ((2 ^ (f.mantissaBits + 1) : ℕ) : ℚ) := by
    apply (Rat.div_lt_iff hq).mpr
    rwa [f.next_binade_grid] at hupper
  have hb := binaryCoefficient_bounds mode negative _ _ (Rat.le_of_lt ht) htop
  refine ⟨hb.1, hb.2.1, ?_, ?_⟩
  · rcases hlower with hl | he
    · left
      have hs : (((2 ^ f.mantissaBits : ℕ) : ℤ) : ℚ) ≤ m / pow2 (e - f.mantissaBits) := by
        apply Classical.byContradiction
        intro h
        have h' : m / pow2 (e - f.mantissaBits) < ((2 ^ f.mantissaBits : ℕ) : ℚ) := by
          rw [Rat.intCast_natCast] at h
          grind
        have h'' := (Rat.div_lt_iff hq).mp h'
        rw [f.binade_grid] at hl
        grind
      have hfl : ((2 ^ f.mantissaBits : ℕ) : ℤ) ≤ (m / pow2 (e - f.mantissaBits)).floor :=
        Rat.le_floor_iff.mpr hs
      have := hb.2.2.1
      omega
    · exact Or.inr he
  · intro he
    apply binaryCoefficient_le_integer
    have hscale : m / pow2 (e - f.mantissaBits) ≤ (((2 ^ (f.mantissaBits + 1) - 1 : ℕ) : ℤ) : ℚ) := by
      rw [he, Rat.intCast_natCast]
      apply Classical.byContradiction
      intro h
      have h' : ((2 ^ (f.mantissaBits + 1) - 1 : ℕ) : ℚ) < m / pow2 (f.emax - f.mantissaBits) := by
        grind
      have h'' := (Rat.lt_div_iff (pow2_pos (f.emax - f.mantissaBits))).mp h'
      unfold Format.maxFinite at hr
      grind
    exact hscale

theorem binaryCarry_spec (f : Format) (hf : f.WellFormed) (e k : ℤ) (he1 : f.emin ≤ e)
    (he2 : e ≤ f.emax) (hk0 : 0 ≤ k) (hk1 : k ≤ ((2 ^ (f.mantissaBits + 1) : ℕ) : ℤ))
    (hsub : ((2 ^ f.mantissaBits : ℕ) : ℤ) ≤ k ∨ e = f.emin)
    (htop : e = f.emax → k ≤ ((2 ^ (f.mantissaBits + 1) - 1 : ℕ) : ℤ)) :
    f.emin ≤ (binaryCarry f e k).1 ∧ (binaryCarry f e k).1 ≤ f.emax ∧
    0 ≤ (binaryCarry f e k).2 ∧ (binaryCarry f e k).2 < ((2 ^ (f.mantissaBits + 1) : ℕ) : ℤ) ∧
    (((2 ^ f.mantissaBits : ℕ) : ℤ) ≤ (binaryCarry f e k).2 ∨ (binaryCarry f e k).1 = f.emin) ∧
    ((binaryCarry f e k).2 : ℚ) * pow2 ((binaryCarry f e k).1 - f.mantissaBits) =
      (k : ℚ) * pow2 (e - f.mantissaBits) ∧
    e ≤ (binaryCarry f e k).1 ∧ (k % 2 = 0 → (binaryCarry f e k).2 % 2 = 0) := by
  have hpow : 2 ^ (f.mantissaBits + 1) = 2 ^ f.mantissaBits * 2 := Nat.pow_succ 2 _
  have hP := Nat.two_pow_pos f.mantissaBits
  unfold binaryCarry
  split
  · rename_i hk
    have hlt : e < f.emax := by
      apply Classical.byContradiction
      intro h
      have he : e = f.emax := by omega
      have := htop he
      rw [hk] at this
      have h2 := Nat.two_pow_pos (f.mantissaBits + 1)
      omega
    have hhalf : k / 2 = ((2 ^ f.mantissaBits : ℕ) : ℤ) := by
      rw [hk, hpow]
      omega
    have hval : ((k / 2 : ℤ) : ℚ) * pow2 (e + 1 - f.mantissaBits) = (k : ℚ) * pow2 (e - f.mantissaBits) := by
      rw [hhalf, hk]
      have : e + 1 - f.mantissaBits = (e - f.mantissaBits) + 1 := by omega
      rw [this, pow2_succ, hpow]
      simp only [Rat.intCast_natCast, Rat.natCast_mul]
      grind
    refine ⟨by omega, by omega, by omega, by omega, Or.inl (by omega), hval, by omega, ?_⟩
    intro _
    rw [hhalf]
    have : (2 ^ f.mantissaBits) % 2 = 0 := by
      obtain ⟨m, hm⟩ : ∃ m, f.mantissaBits = m + 1 := ⟨f.mantissaBits - 1, by have := hf.1; omega⟩
      rw [hm, Nat.pow_succ]
      simp
    omega
  · exact ⟨he1, he2, hk0, by omega, hsub, rfl, Int.le_refl _, fun h => h⟩

end TensorCore
