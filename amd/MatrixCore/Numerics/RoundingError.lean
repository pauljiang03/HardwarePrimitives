import MatrixCore.Numerics.RoundingContract

/-! # Error of FP32 RNE

`fl{x}` is within half an ulp of `x`, hence `|x − fl{x}| ≤ 2^-24 |x| + 2^-150`. -/

namespace MatrixCore

/-- Value of an FP32 word, `0` for an infinity or NaN. -/
def wordValue (w : F32) : ℚ := (value32 w).getD 0

/-- Half an FP32 ulp of `x`; `2^-150` below the normal range. -/
def halfUlp32 (x : ℚ) : ℚ := if x = 0 then 0 else pow2 (normExp (absQ x) - 24)

theorem halfUlp32_nonneg (x : ℚ) : 0 ≤ halfUlp32 x := by
  unfold halfUlp32; split
  · exact Rat.le_refl
  · exact Rat.le_of_lt (pow2_pos _)

theorem rneMagnitude_error {a : ℚ} : absQ (a - rneMagnitude a) ≤ pow2 (normExp a - 24) := by
  unfold rneMagnitude
  have hp := pow2_pos (normExp a - 24)
  rw [dist_scale a _ (pow2_pos _)]
  have hd := rneInt_dist (a / pow2 (normExp a - 23))
  have hq : pow2 (normExp a - 23) = pow2 (normExp a - 24) * 2 := by
    rw [show normExp a - 23 = (normExp a - 24) + 1 by omega, pow2_succ]
  rw [hq]
  have := Rat.mul_le_mul_of_nonneg_right hd (Rat.le_of_lt hp)
  grind

/-- `fl{x}` is within half an ulp of `x`. -/
theorem rneValue_error (x : ℚ) : absQ (x - rneValue x) ≤ halfUlp32 x := by
  by_cases hx : x = 0
  · subst hx
    rw [rneValue_zero, show absQ ((0 : ℚ) - 0) = 0 by decide +kernel]
    exact halfUlp32_nonneg 0
  · unfold halfUlp32
    rw [if_neg hx]
    unfold rneValue
    split
    · rename_i hneg
      have hx' : x - -rneMagnitude (absQ x) = -(absQ x - rneMagnitude (absQ x)) := by
        rw [absQ_of_neg hneg]; grind
      rw [hx', absQ_neg]
      exact rneMagnitude_error
    · rename_i hnn
      have ha : absQ x = x := absQ_of_nonneg (by grind)
      have := rneMagnitude_error (a := absQ x)
      rw [ha] at this ⊢
      exact this

/-- Half an ulp is at most `2^-24 |x| + 2^-150`. -/
theorem halfUlp32_le (x : ℚ) : halfUlp32 x ≤ pow2 (-24) * absQ x + pow2 (-150) := by
  have h24 := pow2_pos (-24)
  have h150 := pow2_pos (-150)
  have hab := absQ_nonneg x
  have hm : 0 ≤ pow2 (-24) * absQ x := Rat.mul_nonneg (Rat.le_of_lt h24) hab
  unfold halfUlp32
  split
  · grind
  · rename_i hx
    obtain ⟨_, hlo, hge⟩ := normExp_bounds (absQ_pos hx)
    by_cases hn : normExp (absQ x) = -126
    · rw [hn]; grind
    · have h := hlo hn
      have : pow2 (normExp (absQ x) - 24) = pow2 (-24) * pow2 (normExp (absQ x)) := by
        rw [← pow2_add]; congr 1; omega
      rw [this]
      have := Rat.mul_le_mul_of_nonneg_left h (Rat.le_of_lt h24)
      grind

/-! ## Monotonicity of RNE -/

theorem floor_mono {t s : ℚ} (h : t ≤ s) : t.floor ≤ s.floor :=
  Rat.le_floor_iff.mpr (Rat.le_trans (floor_bounds t).1 h)

theorem rneInt_mono {t s : ℚ} (h : t ≤ s) : rneInt t ≤ rneInt s := by
  have hf := floor_mono h
  rcases Int.lt_or_eq_of_le hf with hlt | heq
  · rcases rneInt_cases t with ⟨h1, _⟩ | ⟨h1, _⟩ <;>
      rcases rneInt_cases s with ⟨h2, _⟩ | ⟨h2, _⟩ <;> omega
  · rcases rneInt_cases t with ⟨h1, c1⟩ | ⟨h1, c1⟩ <;>
      rcases rneInt_cases s with ⟨h2, c2⟩ | ⟨h2, c2⟩
    · omega
    · exfalso
      rw [heq] at c1
      apply c2
      rcases c1 with c1 | ⟨c1, odd⟩
      · left; grind
      · by_cases hst : 2 * (s - s.floor) = 1
        · exact Or.inr ⟨hst, odd⟩
        · left; grind
    · omega
    · omega

theorem normExp_mono {a b : ℚ} (ha : 0 < a) (hab : a ≤ b) : normExp a ≤ normExp b := by
  have hb : 0 < b := by grind
  obtain ⟨hb1, _, hb3⟩ := normExp_bounds hb
  obtain ⟨_, ha2, _⟩ := normExp_bounds ha
  by_cases hle : normExp a ≤ normExp b
  · exact hle
  · exfalso
    have hlt : normExp b + 1 ≤ normExp a := by omega
    have h1 := pow2_le_of_le hlt
    have h2 := ha2 (by omega)
    grind

theorem rneMagnitude_nonneg {a : ℚ} (ha : 0 ≤ a) : 0 ≤ rneMagnitude a := by
  unfold rneMagnitude
  have hq := pow2_pos (normExp a - 23)
  have : 0 ≤ a / pow2 (normExp a - 23) := by
    rw [Rat.div_def]; exact Rat.mul_nonneg ha (Rat.le_of_lt (Rat.inv_pos.mpr hq))
  have h0 : (0 : ℚ) ≤ (rneInt (a / pow2 (normExp a - 23)) : ℚ) := by
    exact_mod_cast rneInt_nonneg this
  exact Rat.mul_nonneg h0 (Rat.le_of_lt hq)

theorem rneMagnitude_bounds {a : ℚ} (ha : 0 < a) :
    rneMagnitude a ≤ pow2 (normExp a + 1) ∧
      (normExp a ≠ -126 → pow2 (normExp a) ≤ rneMagnitude a) := by
  obtain ⟨hlt, hnorm, _⟩ := scaled_bounds ha
  have hq := pow2_pos (normExp a - 23)
  have e1 : pow2 (normExp a + 1) = ((16777216 : ℤ) : ℚ) * pow2 (normExp a - 23) := by
    rw [pow2_split _ 24, show normExp a + 1 - ((24 : ℕ) : ℤ) = normExp a - 23 by omega]; rfl
  have e2 : pow2 (normExp a) = ((8388608 : ℤ) : ℚ) * pow2 (normExp a - 23) := by
    rw [pow2_split _ 23, show normExp a - ((23 : ℕ) : ℤ) = normExp a - 23 by omega]; rfl
  unfold rneMagnitude
  constructor
  · have hk : rneInt (a / pow2 (normExp a - 23)) ≤ 16777216 :=
      rneInt_le_of_lt (by rw [Rat.intCast_ofNat]; exact hlt)
    have hk' : ((rneInt (a / pow2 (normExp a - 23)) : ℤ) : ℚ) ≤ ((16777216 : ℤ) : ℚ) :=
      Rat.intCast_le_intCast.mpr hk
    rw [e1]; exact Rat.mul_le_mul_of_nonneg_right hk' (Rat.le_of_lt hq)
  · intro hne
    have hk : 8388608 ≤ rneInt (a / pow2 (normExp a - 23)) :=
      le_rneInt_of_le (by rw [Rat.intCast_ofNat]; exact hnorm hne)
    have hk' : ((8388608 : ℤ) : ℚ) ≤ ((rneInt (a / pow2 (normExp a - 23)) : ℤ) : ℚ) :=
      Rat.intCast_le_intCast.mpr hk
    rw [e2]; exact Rat.mul_le_mul_of_nonneg_right hk' (Rat.le_of_lt hq)

theorem rneMagnitude_mono {a b : ℚ} (ha : 0 < a) (hab : a ≤ b) : rneMagnitude a ≤ rneMagnitude b := by
  have hb : 0 < b := by grind
  have hn := normExp_mono ha hab
  rcases Int.lt_or_eq_of_le hn with hlt | heq
  · have h1 := (rneMagnitude_bounds ha).1
    have h2 := (rneMagnitude_bounds hb).2 (by have := (normExp_bounds ha).2.2; omega)
    have h3 := pow2_le_of_le (show normExp a + 1 ≤ normExp b by omega)
    grind
  · unfold rneMagnitude
    rw [heq]
    have hq := pow2_pos (normExp b - 23)
    apply Rat.mul_le_mul_of_nonneg_right _ (Rat.le_of_lt hq)
    have : a / pow2 (normExp b - 23) ≤ b / pow2 (normExp b - 23) := by
      rw [Rat.div_def, Rat.div_def]
      exact Rat.mul_le_mul_of_nonneg_right hab (Rat.le_of_lt (Rat.inv_pos.mpr hq))
    exact Rat.intCast_le_intCast.mpr (rneInt_mono this)

/-- RNE is monotone. -/
theorem rneValue_mono {x y : ℚ} (h : x ≤ y) : rneValue x ≤ rneValue y := by
  unfold rneValue
  by_cases hx : x < 0 <;> by_cases hy : y < 0 <;> simp only [hx, hy, ↓reduceIte]
  · have hax : absQ x = -x := absQ_of_neg hx
    have hay : absQ y = -y := absQ_of_neg hy
    have := rneMagnitude_mono (a := absQ y) (b := absQ x) (by rw [hay]; grind) (by rw [hax, hay]; grind)
    grind
  · have h1 := rneMagnitude_nonneg (absQ_nonneg x)
    have h2 := rneMagnitude_nonneg (absQ_nonneg y)
    grind
  · exfalso; grind
  · have hax : absQ x = x := absQ_of_nonneg (by grind)
    have hay : absQ y = y := absQ_of_nonneg (by grind)
    rw [hax, hay]
    by_cases hx0 : x = 0
    · subst hx0
      have h0 : rneMagnitude 0 = 0 := by
        have := rneValue_zero; unfold rneValue at this; simpa [show absQ (0 : ℚ) = 0 from rfl] using this
      rw [h0]; exact rneMagnitude_nonneg (by grind)
    · exact rneMagnitude_mono (by grind) h

/-- Flushing a value below the normal range to zero. -/
def flushValue (v : ℚ) : ℚ := if absQ v < pow2 (-126) then 0 else v

theorem flushValue_mono {x y : ℚ} (h : x ≤ y) : flushValue x ≤ flushValue y := by
  unfold flushValue
  have hp := pow2_pos (-126)
  have hx := (absQ_lt_iff x (pow2 (-126)))
  have hy := (absQ_lt_iff y (pow2 (-126)))
  split <;> split <;> grind

end MatrixCore
