import TensorCore.Numerics.RoundingBounds

/-! FP32 nearest-even rounding is correct. -/

namespace TensorCore

theorem rne_grid_nearest (m : ℚ) (e : ℤ) (j : ℤ) :
    absQ (m - (rneInt (m / pow2 (e - 23)) : ℚ) * pow2 (e - 23)) ≤
      absQ (m - (j : ℚ) * pow2 (e - 23)) := by
  rw [dist_scale _ _ (pow2_pos _) _, dist_scale _ _ (pow2_pos _) _]
  exact Rat.mul_le_mul_of_nonneg_right (rneInt_nearest _ j) (Rat.le_of_lt (pow2_pos _))

theorem rne_lower_binade_strict (m : ℚ) (hm : 0 < m) (hr : m ≤ maxFinite32)
    (j f : ℤ) (hf : -126 ≤ f) (hj : j.natAbs < 2 ^ 24) (he : f < normExp m) :
    absQ (m - magnitudeRounded .nearestEven m) <
      absQ (m - (j : ℚ) * pow2 (f - 23)) := by
  obtain ⟨_, _, _, hl⟩ := normExp_bounds m hm hr
  have hl' : pow2 (normExp m) ≤ m := by rcases hl with h | h <;> first | exact h | omega
  have hb := rne_grid_nearest m (normExp m) 8388608
  change absQ (m - magnitudeRounded .nearestEven m) ≤
    absQ (m - 8388608 * pow2 (normExp m - 23)) at hb
  rw [← binade_grid] at hb
  have hsmall := finite_below_binade j f (normExp m) hj he
  have hsmall' := (absQ_le_iff _ _).mp hsmall
  have hq := pow2_pos (normExp m - 24)
  have h1 : 0 ≤ m - pow2 (normExp m) := by grind
  have h2 : 0 ≤ m - (j : ℚ) * pow2 (f - 23) := by grind
  rw [absQ_of_nonneg h1] at hb
  rw [absQ_of_nonneg h2]
  grind

theorem rne_magnitude_nearest (m y : ℚ) (hm : 0 < m) (hr : m ≤ maxFinite32)
    (hy : FiniteValue32 y) :
    absQ (m - magnitudeRounded .nearestEven m) ≤ absQ (m - y) := by
  obtain ⟨j, f, hf, _, hj, rfl⟩ := hy
  by_cases he : normExp m ≤ f
  · obtain ⟨z, hz⟩ := finite_on_grid j f (normExp m) he
    rw [hz]
    exact rne_grid_nearest m (normExp m) z
  · exact Rat.le_of_lt (rne_lower_binade_strict m hm hr j f hf hj (by omega))

theorem rne_magnitude_tie_even (m y : ℚ) (hm : 0 < m) (hr : m ≤ maxFinite32)
    (hy : FiniteValue32 y) (hne : y ≠ magnitudeRounded .nearestEven m)
    (ht : absQ (m - y) = absQ (m - magnitudeRounded .nearestEven m)) :
    roundedSignificand .nearestEven m % 2 = 0 := by
  obtain ⟨j, f, hf, _, hj, rfl⟩ := hy
  by_cases he : normExp m ≤ f
  · obtain ⟨z, hz⟩ := finite_on_grid j f (normExp m) he
    rw [hz] at hne ht
    have hz' : z ≠ rneInt (m / pow2 (normExp m - 23)) := by
      intro h
      apply hne
      rw [h]; rfl
    unfold magnitudeRounded roundedSignificand roundSignificand at ht
    rw [dist_scale _ _ (pow2_pos _) _, dist_scale _ _ (pow2_pos _) _] at ht
    have hcancel := congrArg (fun a : ℚ => a / pow2 (normExp m - 23)) ht
    simp only [Rat.mul_div_cancel (Rat.ne_of_gt (pow2_pos _))] at hcancel
    exact rneInt_tie_even _ z hcancel hz'
  · have h := rne_lower_binade_strict m hm hr j f hf hj (by omega)
    rw [ht] at h
    exact False.elim (Rat.lt_irrefl h)

theorem finiteValue32_neg {y : ℚ} (h : FiniteValue32 y) : FiniteValue32 (-y) := by
  obtain ⟨k, e, he1, he2, hk, rfl⟩ := h
  refine ⟨-k, e, he1, he2, ?_, ?_⟩
  · simpa using hk
  · simp [Rat.intCast_neg, Rat.neg_mul]

theorem absQ_pos_of_ne_zero (x : ℚ) (hx : x ≠ 0) : 0 < absQ x := by
  unfold absQ; split <;> grind

theorem signedRounded_nearest (x y : ℚ) (hx : x ≠ 0) (hr : absQ x ≤ maxFinite32)
    (hy : FiniteValue32 y) :
    absQ (x - signedRounded .nearestEven x) ≤ absQ (x - y) := by
  have hm := absQ_pos_of_ne_zero x hx
  unfold signedRounded
  split
  · rename_i hn
    have h := rne_magnitude_nearest (absQ x) (-y) hm hr (finiteValue32_neg hy)
    rw [absQ_of_neg hn] at h
    have h1 : -x - magnitudeRounded .nearestEven (-x) =
      -(x - -magnitudeRounded .nearestEven (-x)) := by grind
    have h2 : -x - -y = -(x - y) := by grind
    rw [h1, h2, absQ_neg, absQ_neg] at h
    simpa [absQ_of_neg hn] using h
  · have h := rne_magnitude_nearest (absQ x) y hm hr hy
    have hn : 0 ≤ x := by grind
    simpa [absQ_of_nonneg hn] using h

theorem signedRounded_tie_even (x y : ℚ) (hx : x ≠ 0) (hr : absQ x ≤ maxFinite32)
    (hy : FiniteValue32 y) (hne : y ≠ signedRounded .nearestEven x)
    (ht : absQ (x - y) = absQ (x - signedRounded .nearestEven x)) :
    roundedSignificand .nearestEven (absQ x) % 2 = 0 := by
  have hm := absQ_pos_of_ne_zero x hx
  unfold signedRounded at hne ht
  split at hne
  · rename_i hn
    simp only [hn, ↓reduceIte, absQ_of_neg hn] at ht hne ⊢
    have h1 : -x - -y = -(x - y) := by grind
    have h2 : -x - magnitudeRounded .nearestEven (-x) =
      -(x - -magnitudeRounded .nearestEven (-x)) := by grind
    apply rne_magnitude_tie_even (-x) (-y)
      (by simpa [absQ_of_neg hn] using hm) (by simpa [absQ_of_neg hn] using hr)
      (finiteValue32_neg hy)
    · intro h; apply hne; grind
    · rw [h1, h2, absQ_neg, absQ_neg]; exact ht
  · have hn : 0 ≤ x := by grind
    simp only [show ¬x < 0 by grind, ↓reduceIte, absQ_of_nonneg hn] at ht hne ⊢
    apply rne_magnitude_tie_even x y (by simpa [absQ_of_nonneg hn] using hm)
      (by simpa [absQ_of_nonneg hn] using hr) hy hne ht

theorem round32_nonzero_spec (mode : RoundingMode) (x : ℚ)
    (hx : x ≠ 0) (hr : absQ x ≤ maxFinite32) :
    ∃ b : F32, round32 mode x = some b ∧ value32 b = some (signedRounded mode x) ∧
      (roundedSignificand mode (absQ x) % 2 = 0 → b.toNat % 2 = 0) ∧
      normExp (absQ x) - 23 ≤ outputUlpExponent b := by
  have hm := absQ_pos_of_ne_zero x hx
  obtain ⟨he1, he2, _, _⟩ := normExp_bounds (absQ x) hm hr
  obtain ⟨hk0, hk1, hsub, htop⟩ := roundedSignificand_bounds mode (absQ x) hm hr
  have hs := carry_spec _ _ he1 he2 hk0 hk1 hsub htop
  let e := (carry (normExp (absQ x)) (roundedSignificand mode (absQ x))).1
  let k := (carry (normExp (absQ x)) (roundedSignificand mode (absQ x))).2
  let b := encode32 (decide (x < 0)) e k
  refine ⟨b, ?_, ?_, ?_, ?_⟩
  · unfold round32 round32Core
    have hn : ¬absQ x > maxFinite32 := by grind
    simp only [hn, hx, ↓reduceIte]
    have hh : ¬e > 127 := by exact Int.not_lt.mpr hs.2.1
    change (if e > 127 then none else some b) = some b
    rw [if_neg hh]
  · have he := (encode32_value (decide (x < 0)) e k hs.1 hs.2.1 hs.2.2.1
      hs.2.2.2.1 hs.2.2.2.2.1).1
    change value32 b = _ at he
    rw [he]
    unfold signedRounded magnitudeRounded
    have hv := hs.2.2.2.2.2.1
    change (k : ℚ) * pow2 (e - 23) = _ at hv
    by_cases hn : x < 0 <;> simp [hn] <;> grind
  · intro h
    have he := (encode32_value (decide (x < 0)) e k hs.1 hs.2.1 hs.2.2.1
      hs.2.2.2.1 hs.2.2.2.2.1).2
    change b.toNat % 2 = k.toNat % 2 at he
    have hk : k % 2 = 0 := hs.2.2.2.2.2.2.2 h
    have hk0 : 0 ≤ k := hs.2.2.1
    omega
  · have he := encode32_ulpExponent (decide (x < 0)) e k hs.1 hs.2.1 hs.2.2.1
      hs.2.2.2.1 hs.2.2.2.2.1
    change outputUlpExponent b = e - 23 at he
    have hh : normExp (absQ x) ≤ e := hs.2.2.2.2.2.2.1
    omega

/-- Total correctness on the declared finite range, for all rational inputs. -/
theorem round32_nearestEven_correct (x : ℚ) (hr : absQ x ≤ maxFinite32) :
    ∃ b : F32, round32 .nearestEven x = some b ∧ NearestEven32 x b := by
  by_cases hx : x = 0
  · subst x
    refine ⟨0, by decide +kernel, 0, by decide +kernel, ?_, ?_⟩
    · intro y _
      have h := absQ_nonneg (0 - y)
      have hz : absQ (0 - 0) = 0 := by decide +kernel
      rw [hz]; exact h
    · intros; decide
  · obtain ⟨b, hb, hv, hp, _⟩ := round32_nonzero_spec .nearestEven x hx hr
    refine ⟨b, hb, signedRounded .nearestEven x, hv, ?_, ?_⟩
    · intro y hy; exact signedRounded_nearest x y hx hr hy
    · intro y hy hne ht
      exact hp (signedRounded_tie_even x y hx hr hy hne ht)

theorem finalRound_correct (x : ℚ) (b : F32) (hr : absQ x ≤ maxFinite32)
    (h : round32 .nearestEven x = some b) : NearestEven32 x b := by
  obtain ⟨b', hb', hc⟩ := round32_nearestEven_correct x hr
  rw [h] at hb'
  cases Option.some.inj hb'
  exact hc

end TensorCore
