import TensorCore.Numerics.Binary.RoundingBounds
import TensorCore.Numerics.CorrectRounding

/-! Correctness of `roundBinary` for every well-formed `Format` (TC-EFT Definition II.2). -/

namespace TensorCore

def binaryMagnitudeRounded (f : Format) (mode : BinaryRoundingMode) (negative : Bool)
    (m : ℚ) : ℚ :=
  (binaryCoefficient mode negative (m / pow2 (binaryNormExp f m - f.mantissaBits)) : ℚ) *
    pow2 (binaryNormExp f m - f.mantissaBits)

def binarySignedRounded (f : Format) (mode : BinaryRoundingMode) (x : ℚ) : ℚ :=
  if x < 0 then -binaryMagnitudeRounded f mode true (absQ x)
  else binaryMagnitudeRounded f mode false (absQ x)

/-! ## Grid geometry -/

theorem rne_grid_nearest_q (m q : ℚ) (hq : 0 < q) (j : ℤ) :
    absQ (m - (rneInt (m / q) : ℚ) * q) ≤ absQ (m - (j : ℚ) * q) := by
  rw [dist_scale _ _ hq _, dist_scale _ _ hq _]
  exact Rat.mul_le_mul_of_nonneg_right (rneInt_nearest _ j) (Rat.le_of_lt hq)

theorem Format.finite_on_grid (f : Format) (k e2 e : ℤ) (h : e ≤ e2) :
    ∃ j : ℤ, (k : ℚ) * pow2 (e2 - f.mantissaBits) = j * pow2 (e - f.mantissaBits) := by
  refine ⟨k * 2 ^ (e2 - e).toNat, ?_⟩
  have : pow2 (e2 - f.mantissaBits) = pow2 (e - f.mantissaBits) * pow2 ((e2 - e).toNat : ℤ) := by
    rw [← pow2_add]; congr 1; omega
  rw [this, pow2_natCast, Rat.intCast_mul, Rat.intCast_pow]
  simp only [Rat.intCast_ofNat, Rat.natCast_pow, Rat.natCast_ofNat]
  grind

/-- A finite value with exponent below `e` is at most `2^e − 2^(e−p−1)` in magnitude. -/
theorem Format.finite_below_binade (f : Format) (k e2 e : ℤ)
    (hk : k.natAbs < 2 ^ (f.mantissaBits + 1)) (h : e2 < e) :
    absQ ((k : ℚ) * pow2 (e2 - f.mantissaBits)) ≤ pow2 e - pow2 (e - f.mantissaBits - 1) := by
  have hq := pow2_pos (e2 - f.mantissaBits)
  rw [absQ_mul_pos _ _ hq, absQ_intCast]
  have hk' : ((k.natAbs : ℤ) : ℚ) ≤ ((2 ^ (f.mantissaBits + 1) - 1 : ℕ) : ℚ) := by
    have h1 : (k.natAbs : ℤ) ≤ ((2 ^ (f.mantissaBits + 1) - 1 : ℕ) : ℤ) := by omega
    have h2 := Rat.intCast_le_intCast.mpr h1
    simpa [Rat.intCast_natCast] using h2
  have hgrid : pow2 (e2 - f.mantissaBits) ≤ pow2 (e - f.mantissaBits - 1) :=
    pow2_le_of_le (by omega)
  have hnn : (0 : ℚ) ≤ ((k.natAbs : ℤ) : ℚ) := Rat.intCast_nonneg.mpr (by omega)
  have step1 : ((k.natAbs : ℤ) : ℚ) * pow2 (e2 - f.mantissaBits) ≤
      ((2 ^ (f.mantissaBits + 1) - 1 : ℕ) : ℚ) * pow2 (e - f.mantissaBits - 1) :=
    calc ((k.natAbs : ℤ) : ℚ) * pow2 (e2 - f.mantissaBits)
        ≤ ((k.natAbs : ℤ) : ℚ) * pow2 (e - f.mantissaBits - 1) :=
          Rat.mul_le_mul_of_nonneg_left hgrid hnn
      _ ≤ ((2 ^ (f.mantissaBits + 1) - 1 : ℕ) : ℚ) * pow2 (e - f.mantissaBits - 1) :=
          Rat.mul_le_mul_of_nonneg_right hk' (Rat.le_of_lt (pow2_pos _))
  have step2 : ((2 ^ (f.mantissaBits + 1) - 1 : ℕ) : ℚ) * pow2 (e - f.mantissaBits - 1) =
      pow2 e - pow2 (e - f.mantissaBits - 1) := by
    have hp1 : pow2 e = ((2 ^ (f.mantissaBits + 1) : ℕ) : ℚ) * pow2 (e - f.mantissaBits - 1) := by
      rw [← pow2_natCast, ← pow2_add]; congr 1; omega
    have hsub : ((2 ^ (f.mantissaBits + 1) - 1 : ℕ) : ℚ) + 1 =
        ((2 ^ (f.mantissaBits + 1) : ℕ) : ℚ) := by
      rw [show (1 : ℚ) = ((1 : ℕ) : ℚ) from rfl, ← Rat.natCast_add,
        Nat.sub_add_cancel (Nat.two_pow_pos _)]
    rw [hp1]
    grind
  rw [← step2]
  exact step1

theorem binaryCoefficient_nearestEven (negative : Bool) (t : ℚ) :
    binaryCoefficient .nearestEven negative t = rneInt t := rfl

theorem binaryMagnitudeRounded_lower (f : Format) (hf : f.WellFormed) (mode : BinaryRoundingMode)
    (negative : Bool) (m : ℚ) (hm : 0 < m) (hr : m ≤ f.maxFinite)
    (he : f.emin < binaryNormExp f m) :
    pow2 (binaryNormExp f m) ≤ binaryMagnitudeRounded f mode negative m := by
  obtain ⟨_, _, _, hl⟩ := binaryNormExp_bounds f hf m hm hr
  have hl' : pow2 (binaryNormExp f m) ≤ m := by
    rcases hl with h | h
    · exact h
    · exfalso; omega
  have hq := pow2_pos (binaryNormExp f m - f.mantissaBits)
  have hs : (((2 ^ f.mantissaBits : ℕ) : ℤ) : ℚ) ≤
      m / pow2 (binaryNormExp f m - f.mantissaBits) := by
    apply le_div_of_mul_le _ _ _ hq
    rw [Rat.intCast_natCast, ← f.binade_grid]
    exact hl'
  have hfl : ((2 ^ f.mantissaBits : ℕ) : ℤ) ≤
      (m / pow2 (binaryNormExp f m - f.mantissaBits)).floor := Rat.le_floor_iff.mpr hs
  have hb := binaryCoefficient_bounds mode negative (m / pow2 (binaryNormExp f m - f.mantissaBits))
    (2 ^ (f.mantissaBits + 1)) (Rat.le_of_lt ((Rat.lt_div_iff hq).mpr (by simpa using hm)))
    (by
      apply (Rat.div_lt_iff hq).mpr
      obtain ⟨_, _, hupper, _⟩ := binaryNormExp_bounds f hf m hm hr
      rwa [f.next_binade_grid] at hupper)
  have hk : ((2 ^ f.mantissaBits : ℕ) : ℤ) ≤
      binaryCoefficient mode negative (m / pow2 (binaryNormExp f m - f.mantissaBits)) := by
    have := hb.2.2.1
    omega
  unfold binaryMagnitudeRounded
  rw [f.binade_grid (binaryNormExp f m), ← Rat.intCast_natCast]
  exact Rat.mul_le_mul_of_nonneg_right (Rat.intCast_le_intCast.mpr hk) (Rat.le_of_lt hq)

theorem binary_rne_lower_binade_strict (f : Format) (hf : f.WellFormed) (negative : Bool) (m : ℚ)
    (hm : 0 < m) (hr : m ≤ f.maxFinite) (j fe : ℤ) (hfe : f.emin ≤ fe)
    (hj : j.natAbs < 2 ^ (f.mantissaBits + 1)) (he : fe < binaryNormExp f m) :
    absQ (m - binaryMagnitudeRounded f .nearestEven negative m) <
      absQ (m - (j : ℚ) * pow2 (fe - f.mantissaBits)) := by
  obtain ⟨_, _, _, hl⟩ := binaryNormExp_bounds f hf m hm hr
  have hl' : pow2 (binaryNormExp f m) ≤ m := by
    rcases hl with h | h
    · exact h
    · exfalso; omega
  have hq := pow2_pos (binaryNormExp f m - f.mantissaBits)
  have hb := rne_grid_nearest_q m _ hq ((2 ^ f.mantissaBits : ℕ) : ℤ)
  change absQ (m - binaryMagnitudeRounded f .nearestEven negative m) ≤
    absQ (m - (((2 ^ f.mantissaBits : ℕ) : ℤ) : ℚ) * pow2 (binaryNormExp f m - f.mantissaBits)) at hb
  rw [Rat.intCast_natCast, ← f.binade_grid] at hb
  have hsmall := f.finite_below_binade j fe (binaryNormExp f m) hj he
  have hsmall' := (absQ_le_iff _ _).mp hsmall
  have hq' := pow2_pos (binaryNormExp f m - f.mantissaBits - 1)
  have h1 : 0 ≤ m - pow2 (binaryNormExp f m) := by grind
  have h2 : 0 ≤ m - (j : ℚ) * pow2 (fe - f.mantissaBits) := by grind
  rw [absQ_of_nonneg h1] at hb
  rw [absQ_of_nonneg h2]
  grind

theorem binary_rne_magnitude_nearest (f : Format) (hf : f.WellFormed) (negative : Bool) (m y : ℚ)
    (hm : 0 < m) (hr : m ≤ f.maxFinite) (hy : f.FiniteValue y) :
    absQ (m - binaryMagnitudeRounded f .nearestEven negative m) ≤ absQ (m - y) := by
  obtain ⟨j, fe, hfe, _, hj, rfl⟩ := hy
  by_cases he : binaryNormExp f m ≤ fe
  · obtain ⟨z, hz⟩ := f.finite_on_grid j fe (binaryNormExp f m) he
    rw [hz]
    exact rne_grid_nearest_q m _ (pow2_pos _) z
  · exact Rat.le_of_lt (binary_rne_lower_binade_strict f hf negative m hm hr j fe hfe hj (by omega))

theorem binary_rne_magnitude_tie_even (f : Format) (hf : f.WellFormed) (negative : Bool) (m y : ℚ)
    (hm : 0 < m) (hr : m ≤ f.maxFinite) (hy : f.FiniteValue y)
    (hne : y ≠ binaryMagnitudeRounded f .nearestEven negative m)
    (ht : absQ (m - y) = absQ (m - binaryMagnitudeRounded f .nearestEven negative m)) :
    binaryCoefficient .nearestEven negative (m / pow2 (binaryNormExp f m - f.mantissaBits)) % 2 = 0 := by
  obtain ⟨j, fe, hfe, _, hj, rfl⟩ := hy
  by_cases he : binaryNormExp f m ≤ fe
  · obtain ⟨z, hz⟩ := f.finite_on_grid j fe (binaryNormExp f m) he
    rw [hz] at hne ht
    have hz' : z ≠ rneInt (m / pow2 (binaryNormExp f m - f.mantissaBits)) := by
      intro h
      apply hne
      rw [h]; rfl
    unfold binaryMagnitudeRounded at ht
    rw [binaryCoefficient_nearestEven] at ht ⊢
    rw [dist_scale _ _ (pow2_pos _) _, dist_scale _ _ (pow2_pos _) _] at ht
    have hcancel := congrArg (fun a : ℚ => a / pow2 (binaryNormExp f m - f.mantissaBits)) ht
    simp only [Rat.mul_div_cancel (Rat.ne_of_gt (pow2_pos _))] at hcancel
    exact rneInt_tie_even _ z hcancel hz'
  · have h := binary_rne_lower_binade_strict f hf negative m hm hr j fe hfe hj (by omega)
    rw [ht] at h
    exact False.elim (Rat.lt_irrefl h)

theorem Format.finiteValue_neg (f : Format) {y : ℚ} (h : f.FiniteValue y) :
    f.FiniteValue (-y) := by
  obtain ⟨k, e, he1, he2, hk, rfl⟩ := h
  refine ⟨-k, e, he1, he2, ?_, ?_⟩
  · simpa using hk
  · simp [Rat.intCast_neg, Rat.neg_mul]

theorem binarySignedRounded_nearest (f : Format) (hf : f.WellFormed) (x y : ℚ) (hx : x ≠ 0)
    (hr : absQ x ≤ f.maxFinite) (hy : f.FiniteValue y) :
    absQ (x - binarySignedRounded f .nearestEven x) ≤ absQ (x - y) := by
  have hm := absQ_pos_of_ne_zero x hx
  unfold binarySignedRounded
  split
  · rename_i hn
    have h := binary_rne_magnitude_nearest f hf true (absQ x) (-y) hm hr (f.finiteValue_neg hy)
    rw [absQ_of_neg hn] at h
    have h1 : -x - binaryMagnitudeRounded f .nearestEven true (-x) =
      -(x - -binaryMagnitudeRounded f .nearestEven true (-x)) := by grind
    have h2 : -x - -y = -(x - y) := by grind
    rw [h1, h2, absQ_neg, absQ_neg] at h
    simpa [absQ_of_neg hn] using h
  · have h := binary_rne_magnitude_nearest f hf false (absQ x) y hm hr hy
    have hn : 0 ≤ x := by grind
    simpa [absQ_of_nonneg hn] using h

theorem binarySignedRounded_tie_even (f : Format) (hf : f.WellFormed) (x y : ℚ) (hx : x ≠ 0)
    (hr : absQ x ≤ f.maxFinite) (hy : f.FiniteValue y)
    (hne : y ≠ binarySignedRounded f .nearestEven x)
    (ht : absQ (x - y) = absQ (x - binarySignedRounded f .nearestEven x)) :
    binaryCoefficient .nearestEven (decide (x < 0))
      (absQ x / pow2 (binaryNormExp f (absQ x) - f.mantissaBits)) % 2 = 0 := by
  have hm := absQ_pos_of_ne_zero x hx
  unfold binarySignedRounded at hne ht
  split at hne
  · rename_i hn
    simp only [hn, ↓reduceIte, absQ_of_neg hn, decide_true] at ht hne ⊢
    have h1 : -x - -y = -(x - y) := by grind
    have h2 : -x - binaryMagnitudeRounded f .nearestEven true (-x) =
      -(x - -binaryMagnitudeRounded f .nearestEven true (-x)) := by grind
    apply binary_rne_magnitude_tie_even f hf true (-x) (-y)
      (by simpa [absQ_of_neg hn] using hm) (by simpa [absQ_of_neg hn] using hr)
      (f.finiteValue_neg hy)
    · intro h; apply hne; grind
    · rw [h1, h2, absQ_neg, absQ_neg]; exact ht
  · have hn : 0 ≤ x := by grind
    simp only [show ¬x < 0 by grind, ↓reduceIte, absQ_of_nonneg hn, decide_false] at ht hne ⊢
    apply binary_rne_magnitude_tie_even f hf false x y (by simpa [absQ_of_nonneg hn] using hm)
      (by simpa [absQ_of_nonneg hn] using hr) hy hne ht

theorem roundBinary_nonzero_spec (f : Format) (hf : f.WellFormed) (mode : BinaryRoundingMode)
    (x : ℚ) (hx : x ≠ 0) (hr : absQ x ≤ f.maxFinite) :
    ∃ bits : BitVec f.width, roundBinary f mode x = some bits ∧
      binaryValue f bits = some (binarySignedRounded f mode x) ∧
      (binaryCoefficient mode (decide (x < 0))
        (absQ x / pow2 (binaryNormExp f (absQ x) - f.mantissaBits)) % 2 = 0 →
        bits.toNat % 2 = 0) := by
  have hm := absQ_pos_of_ne_zero x hx
  obtain ⟨he1, he2, _, _⟩ := binaryNormExp_bounds f hf (absQ x) hm hr
  obtain ⟨hk0, hk1, hsub, htop⟩ := binaryRoundedCoeff_bounds f hf mode (decide (x < 0)) (absQ x) hm hr
  have hs := binaryCarry_spec f hf _ _ he1 he2 hk0 hk1 hsub htop
  let e := (binaryCarry f (binaryNormExp f (absQ x)) (binaryCoefficient mode (decide (x < 0))
    (absQ x / pow2 (binaryNormExp f (absQ x) - f.mantissaBits)))).1
  let k := (binaryCarry f (binaryNormExp f (absQ x)) (binaryCoefficient mode (decide (x < 0))
    (absQ x / pow2 (binaryNormExp f (absQ x) - f.mantissaBits)))).2
  let bits := encodeBinary f (decide (x < 0)) e k
  refine ⟨bits, ?_, ?_, ?_⟩
  · unfold roundBinary
    have hn : ¬absQ x > f.maxFinite := by grind
    rw [if_neg (by intro h; exact h hf), if_neg hn, if_neg hx]
    have hh : ¬e > f.emax := Int.not_lt.mpr hs.2.1
    change (if e > f.emax then none else some bits) = some bits
    rw [if_neg hh]
  · have he := encodeBinary_value f hf (decide (x < 0)) e k hs.1 hs.2.1 hs.2.2.1
      hs.2.2.2.1 hs.2.2.2.2.1
    change binaryValue f bits = _ at he
    rw [he]
    unfold binarySignedRounded binaryMagnitudeRounded
    have hv := hs.2.2.2.2.2.1
    change (k : ℚ) * pow2 (e - f.mantissaBits) = _ at hv
    by_cases hn : x < 0 <;> simp [hn] <;> grind
  · intro h
    have he := encodeBinary_parity f hf (decide (x < 0)) e k hs.2.2.1 hs.2.2.2.1 hs.1 hs.2.1
    change bits.toNat % 2 = k.toNat % 2 at he
    have hk : k % 2 = 0 := hs.2.2.2.2.2.2.2 h
    have hk0 : 0 ≤ k := hs.2.2.1
    omega

theorem binaryValue_zero (f : Format) (hf : f.WellFormed) : binaryValue f 0 = some 0 := by
  obtain ⟨_, hE⟩ := hf
  have hW : 4 ≤ 2 ^ f.exponentBits := by
    have := Nat.pow_le_pow_right (show 0 < 2 by decide) hE
    simpa using this
  have h0 : (0 : BitVec f.width).toNat = 0 := by simp
  unfold binaryValue classify classifyNat
  dsimp only
  rw [h0, Nat.zero_mod, Nat.zero_div, Nat.zero_mod, Nat.zero_div]
  rw [if_neg (by omega), if_pos rfl, if_pos rfl]
  simp [Classification.finite, Decoded.value]

/-- Nearest finite value of the format, ties to an even low bit. -/
def NearestEven (f : Format) (x : ℚ) (bits : BitVec f.width) : Prop :=
  ∃ d : ℚ, binaryValue f bits = some d ∧
    (∀ y : ℚ, f.FiniteValue y → absQ (x - d) ≤ absQ (x - y)) ∧
    (∀ y : ℚ, f.FiniteValue y → y ≠ d → absQ (x - y) = absQ (x - d) → bits.toNat % 2 = 0)

theorem fp32_nearestEven (x : ℚ) (bits : F32) : NearestEven fp32 x bits ↔ NearestEven32 x bits :=
  Iff.rfl

/-- Total correctness of nearest-even conversion on the finite range of any format. -/
theorem roundBinary_nearestEven_correct (f : Format) (hf : f.WellFormed) (x : ℚ)
    (hr : absQ x ≤ f.maxFinite) :
    ∃ bits : BitVec f.width, roundBinary f .nearestEven x = some bits ∧ NearestEven f x bits := by
  by_cases hx : x = 0
  · subst x
    have hz : roundBinary f .nearestEven 0 = some 0 := by
      unfold roundBinary
      rw [if_neg (by intro h; exact h hf), if_neg (by have := absQ_nonneg (0 : ℚ); grind),
        if_pos rfl]
    refine ⟨0, hz, 0, binaryValue_zero f hf, ?_, ?_⟩
    · intro y _
      have h := absQ_nonneg (0 - y)
      have hz0 : absQ (0 - 0) = 0 := by decide +kernel
      rw [hz0]; exact h
    · intros; simp
  · obtain ⟨bits, hb, hv, hp⟩ := roundBinary_nonzero_spec f hf .nearestEven x hx hr
    refine ⟨bits, hb, binarySignedRounded f .nearestEven x, hv, ?_, ?_⟩
    · intro y hy; exact binarySignedRounded_nearest f hf x y hx hr hy
    · intro y hy hne ht
      exact hp (binarySignedRounded_tie_even f hf x y hx hr hy hne ht)

/-! ## Truncation -/

/-- `y` lies between zero and `x`, inclusive. -/
def Between0 (x y : ℚ) : Prop := (0 ≤ x ∧ 0 ≤ y ∧ y ≤ x) ∨ (x ≤ 0 ∧ x ≤ y ∧ y ≤ 0)

theorem binary_trunc_magnitude_spec (f : Format) (hf : f.WellFormed) (negative : Bool) (m : ℚ)
    (hm : 0 < m) (hr : m ≤ f.maxFinite) :
    0 ≤ binaryMagnitudeRounded f .truncate negative m ∧
    binaryMagnitudeRounded f .truncate negative m ≤ m ∧
    (∀ y : ℚ, f.FiniteValue y → y ≤ m → y ≤ binaryMagnitudeRounded f .truncate negative m) := by
  have hq := pow2_pos (binaryNormExp f m - f.mantissaBits)
  have hfl : (0 : ℤ) ≤ (m / pow2 (binaryNormExp f m - f.mantissaBits)).floor := by
    apply Rat.le_floor_iff.mpr
    have := div_nonneg_of_pos _ _ (Rat.le_of_lt hm) hq
    simpa using this
  refine ⟨?_, ?_, ?_⟩
  · unfold binaryMagnitudeRounded
    have : (0 : ℚ) ≤ (((m / pow2 (binaryNormExp f m - f.mantissaBits)).floor : ℤ) : ℚ) := by
      have := Rat.intCast_le_intCast.mpr hfl
      simpa using this
    exact Rat.mul_nonneg this (Rat.le_of_lt hq)
  · unfold binaryMagnitudeRounded
    change (((m / pow2 (binaryNormExp f m - f.mantissaBits)).floor : ℤ) : ℚ) *
      pow2 (binaryNormExp f m - f.mantissaBits) ≤ m
    have := Rat.mul_le_mul_of_nonneg_right (Rat.floor_le (m / pow2 (binaryNormExp f m - f.mantissaBits)))
      (Rat.le_of_lt hq)
    rwa [Rat.div_mul_cancel (Rat.ne_of_gt hq)] at this
  · intro y hy hym
    obtain ⟨j, fe, hfe, _, hj, rfl⟩ := hy
    by_cases he : binaryNormExp f m ≤ fe
    · obtain ⟨z, hz⟩ := f.finite_on_grid j fe (binaryNormExp f m) he
      rw [hz] at hym ⊢
      unfold binaryMagnitudeRounded
      change (z : ℚ) * pow2 (binaryNormExp f m - f.mantissaBits) ≤
        (((m / pow2 (binaryNormExp f m - f.mantissaBits)).floor : ℤ) : ℚ) *
          pow2 (binaryNormExp f m - f.mantissaBits)
      apply Rat.mul_le_mul_of_nonneg_right _ (Rat.le_of_lt hq)
      apply Rat.intCast_le_intCast.mpr
      apply Rat.le_floor_iff.mpr
      exact le_div_of_mul_le _ _ _ hq hym
    · have hlow := binaryMagnitudeRounded_lower f hf .truncate negative m hm hr (by omega)
      have hsmall := f.finite_below_binade j fe (binaryNormExp f m) hj (by omega)
      have hsmall' := (absQ_le_iff _ _).mp hsmall
      have := pow2_pos (binaryNormExp f m - f.mantissaBits - 1)
      grind

/-- Truncated result: between zero and `x`, of largest magnitude among the finite values there. -/
def Truncated (f : Format) (x : ℚ) (bits : BitVec f.width) : Prop :=
  ∃ d : ℚ, binaryValue f bits = some d ∧ Between0 x d ∧
    ∀ y : ℚ, f.FiniteValue y → Between0 x y → absQ y ≤ absQ d

theorem roundBinary_truncate_correct (f : Format) (hf : f.WellFormed) (x : ℚ)
    (hr : absQ x ≤ f.maxFinite) :
    ∃ bits : BitVec f.width, roundBinary f .truncate x = some bits ∧ Truncated f x bits := by
  by_cases hx : x = 0
  · subst x
    have hz : roundBinary f .truncate 0 = some 0 := by
      unfold roundBinary
      rw [if_neg (by intro h; exact h hf), if_neg (by have := absQ_nonneg (0 : ℚ); grind),
        if_pos rfl]
    refine ⟨0, hz, 0, binaryValue_zero f hf, Or.inl ⟨Rat.le_refl, Rat.le_refl, Rat.le_refl⟩, ?_⟩
    intro y _ hy
    have : y = 0 := by unfold Between0 at hy; grind
    rw [this]
    exact Rat.le_refl
  · obtain ⟨bits, hb, hv, _⟩ := roundBinary_nonzero_spec f hf .truncate x hx hr
    refine ⟨bits, hb, binarySignedRounded f .truncate x, hv, ?_, ?_⟩
    · unfold binarySignedRounded
      split
      · rename_i hn
        have hm := absQ_pos_of_ne_zero x hx
        obtain ⟨h0, hle, _⟩ := binary_trunc_magnitude_spec f hf true (absQ x) hm hr
        have hax := absQ_of_neg hn
        right
        exact ⟨Rat.le_of_lt hn, by grind, by grind⟩
      · rename_i hn
        have hm := absQ_pos_of_ne_zero x hx
        obtain ⟨h0, hle, _⟩ := binary_trunc_magnitude_spec f hf false (absQ x) hm hr
        have hn' : 0 ≤ x := by grind
        have hax := absQ_of_nonneg hn'
        left
        exact ⟨hn', h0, by grind⟩
    · intro y hy hb0
      have hm := absQ_pos_of_ne_zero x hx
      unfold binarySignedRounded
      split
      · rename_i hn
        obtain ⟨h0, _, hmax⟩ := binary_trunc_magnitude_spec f hf true (absQ x) hm hr
        have hyx : -y ≤ absQ x := by
          rw [absQ_of_neg hn]
          unfold Between0 at hb0
          grind
        have hle := hmax (-y) (f.finiteValue_neg hy) hyx
        have hy0 : y ≤ 0 := by unfold Between0 at hb0; grind
        rw [absQ_neg, absQ_of_nonneg h0]
        apply (absQ_le_iff _ _).mpr
        constructor <;> grind
      · rename_i hn
        obtain ⟨h0, _, hmax⟩ := binary_trunc_magnitude_spec f hf false (absQ x) hm hr
        have hn' : 0 ≤ x := by grind
        have hyx : y ≤ absQ x := by
          rw [absQ_of_nonneg hn']
          unfold Between0 at hb0
          grind
        have hle := hmax y hy hyx
        have hy0 : 0 ≤ y := by unfold Between0 at hb0; grind
        rw [absQ_of_nonneg h0]
        apply (absQ_le_iff _ _).mpr
        constructor <;> grind

end TensorCore
