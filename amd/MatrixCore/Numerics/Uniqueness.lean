import MatrixCore.Numerics.RoundingContract

/-! # Uniqueness of the binary32 RNE word

A word that is nearest to `x` among all finite binary32 words, has an even last bit on ties, and
carries the sign of `x`, is the word returned by `rne32`. -/

namespace MatrixCore

/-- Sign bit of a binary32 word. -/
def sign32 (w : F32) : Bool := w.toNat / 2147483648 % 2 == 1

/-- Correctly rounded binary32 result: nearest value, even on ties, sign of the input. -/
def RoundsNearestEven32 (x : ℚ) (w : F32) : Prop := NearestEven32 x w ∧ sign32 w = decide (x < 0)

theorem sign32_encode32 (negative : Bool) (e : ℤ) (m : ℕ) (hm : m < 16777216) (he1 : -126 ≤ e)
    (he2 : e ≤ 127) : sign32 (encode32 negative e m) = negative := by
  simp only [sign32, encode32, BitVec.toNat_ofNat]
  by_cases hs : m < 8388608 <;> cases negative <;> simp [hs] <;> omega

theorem rne32_sign {x : ℚ} {w : F32} (h : rne32 x = some w) : sign32 w = decide (x < 0) := by
  by_cases hx : x = 0
  · subst hx; unfold rne32 at h; simp at h; subst h; decide
  · obtain ⟨hle, rfl⟩ := rne32_some hx h
    obtain ⟨h1, h2, _⟩ := rneFields_spec (absQ_pos hx)
    exact sign32_encode32 _ _ _ h2 h1 hle

theorem rne32_rounds {x : ℚ} {w : F32} (h : rne32 x = some w) : RoundsNearestEven32 x w :=
  ⟨rne32_nearestEven h, rne32_sign h⟩

/-! ## Words are determined by sign and value -/

/-- Fields of a binary32 word. -/
theorem decode32_eq (w : F32) :
    fp32.decode w =
      let M := w.toNat % 8388608
      let E := w.toNat / 8388608 % 256
      let neg := w.toNat / 2147483648 % 2 == 1
      if E = 255 then (if M = 0 then .infinity neg else .nan)
      else .finite (if E = 0 then ⟨neg, M, -126, 23⟩ else ⟨neg, 8388608 + M, (E : ℤ) - 127, 23⟩) := by
  rfl

/-- Significand and exponent of a finite binary32 word from its fields. -/
def fields32 (E M : ℕ) : ℕ × ℤ := if E = 0 then (M, -126) else (8388608 + M, (E : ℤ) - 127)

theorem fields32_spec {E M : ℕ} (hE : E < 255) (hM : M < 8388608) :
    (fields32 E M).1 < 16777216 ∧ -126 ≤ (fields32 E M).2 ∧
      (8388608 ≤ (fields32 E M).1 ∨ (fields32 E M).2 = -126) ∧
      E = (if (fields32 E M).1 < 8388608 then 0 else ((fields32 E M).2 + 127).toNat) ∧
      M = (fields32 E M).1 % 8388608 := by
  unfold fields32
  by_cases h0 : E = 0
  · subst h0
    simp only [↓reduceIte, hM]
    exact ⟨by omega, by omega, Or.inr trivial, trivial, (Nat.mod_eq_of_lt hM).symm⟩
  · simp only [h0, ↓reduceIte]
    have : ¬ (8388608 + M < 8388608) := by omega
    simp only [this, ↓reduceIte]
    omega

theorem value32_abs {w : F32} {y : ℚ} (h : value32 w = some y) :
    w.toNat / 8388608 % 256 < 255 ∧
      absQ y = ((fields32 (w.toNat / 8388608 % 256) (w.toNat % 8388608)).1 : ℚ) *
        pow2 ((fields32 (w.toNat / 8388608 % 256) (w.toNat % 8388608)).2 - 23) := by
  unfold value32 at h
  rw [decode32_eq] at h
  simp only at h
  have hE : w.toNat / 8388608 % 256 < 256 := Nat.mod_lt _ (by decide)
  split at h
  · split at h <;> simp [Datum.toFinite] at h
  · rename_i hne
    simp only [Datum.toFinite, Option.map_some, Option.some.injEq] at h
    refine ⟨by omega, ?_⟩
    rw [← h]
    unfold fields32
    split <;> (rw [Unpacked.absQ_value]; rfl)

theorem decode32_fields_eq (w : F32) :
    w.toNat = (w.toNat / 2147483648 % 2) * 2147483648 + (w.toNat / 8388608 % 256) * 8388608 +
      w.toNat % 8388608 := by
  have := w.isLt
  have : w.toNat < 4294967296 := this
  omega

/-- Normalized binary32 significands and exponents are unique. -/
theorem normalized_unique {m₁ m₂ : ℕ} {e₁ e₂ : ℤ}
    (hm₁ : m₁ < 16777216) (hm₂ : m₂ < 16777216) (he₁ : -126 ≤ e₁) (he₂ : -126 ≤ e₂)
    (hn₁ : 8388608 ≤ m₁ ∨ e₁ = -126) (hn₂ : 8388608 ≤ m₂ ∨ e₂ = -126)
    (h : (m₁ : ℚ) * pow2 (e₁ - 23) = (m₂ : ℚ) * pow2 (e₂ - 23)) (hz : m₁ ≠ 0) :
    m₁ = m₂ ∧ e₁ = e₂ := by
  have key : ∀ {a b : ℕ} {f g : ℤ}, a < 16777216 → -126 ≤ f → (8388608 ≤ b ∨ g = -126) →
      f < g → (a : ℚ) * pow2 (f - 23) = (b : ℚ) * pow2 (g - 23) → b = 0 := by
    intro a b f g ha hf hb hfg hab
    have hsplit : pow2 (g - 23) = ((2 ^ (g - f).toNat : ℕ) : ℚ) * pow2 (f - 23) := by
      rw [← pow2_natCast, ← pow2_add]; congr 1; omega
    rw [hsplit, ← Rat.mul_assoc] at hab
    have hab' := mul_right_cancel_pos (pow2_ne_zero _) hab
    have hnat : a = b * 2 ^ (g - f).toNat := by exact_mod_cast hab'
    rcases hb with hb | hb
    · have : 2 ≤ 2 ^ (g - f).toNat := by
        have := Nat.pow_le_pow_right (show 0 < 2 by decide) (show 1 ≤ (g - f).toNat by omega)
        simpa using this
      have := Nat.mul_le_mul hb this
      omega
    · omega
  rcases Int.lt_trichotomy e₁ e₂ with hlt | heq | hgt
  · have := key hm₁ he₁ hn₂ hlt h
    subst this
    simp at h
    exact absurd (by exact_mod_cast (Rat.mul_eq_zero.mp h).resolve_right (pow2_ne_zero _)) hz
  · subst heq
    refine ⟨?_, rfl⟩
    have := mul_right_cancel_pos (pow2_ne_zero _) h
    exact_mod_cast this
  · exact absurd (key hm₂ he₂ hn₁ hgt h.symm) hz

/-- Two finite words with the same sign bit and the same value are equal. -/
theorem value32_injective {w₁ w₂ : F32} {y : ℚ} (h₁ : value32 w₁ = some y)
    (h₂ : value32 w₂ = some y) (hs : sign32 w₁ = sign32 w₂) : w₁ = w₂ := by
  obtain ⟨hE₁, ha₁⟩ := value32_abs h₁
  obtain ⟨hE₂, ha₂⟩ := value32_abs h₂
  have hM₁ : w₁.toNat % 8388608 < 8388608 := Nat.mod_lt _ (by decide)
  have hM₂ : w₂.toNat % 8388608 < 8388608 := Nat.mod_lt _ (by decide)
  obtain ⟨b₁, c₁, n₁, rE₁, rM₁⟩ := fields32_spec hE₁ hM₁
  obtain ⟨b₂, c₂, n₂, rE₂, rM₂⟩ := fields32_spec hE₂ hM₂
  have hsame : fields32 (w₁.toNat / 8388608 % 256) (w₁.toNat % 8388608) =
      fields32 (w₂.toNat / 8388608 % 256) (w₂.toNat % 8388608) := by
    generalize fields32 (w₁.toNat / 8388608 % 256) (w₁.toNat % 8388608) = f₁ at *
    generalize fields32 (w₂.toNat / 8388608 % 256) (w₂.toNat % 8388608) = f₂ at *
    obtain ⟨m₁, e₁⟩ := f₁
    obtain ⟨m₂, e₂⟩ := f₂
    simp only at *
    have hv : (m₁ : ℚ) * pow2 (e₁ - 23) = (m₂ : ℚ) * pow2 (e₂ - 23) := by rw [← ha₁, ← ha₂]
    by_cases hz : m₁ = 0
    · subst hz
      have : (m₂ : ℚ) * pow2 (e₂ - 23) = 0 := by rw [← hv]; simp
      have hm₂ : m₂ = 0 := by
        rcases Rat.mul_eq_zero.mp this with h | h
        · exact_mod_cast h
        · exact absurd h (pow2_ne_zero _)
      subst hm₂
      have e₁eq : e₁ = -126 := by omega
      have e₂eq : e₂ = -126 := by omega
      rw [e₁eq, e₂eq]
    · obtain ⟨rfl, rfl⟩ := normalized_unique b₁ b₂ c₁ c₂ n₁ n₂ hv hz
      rfl
  rw [hsame] at rE₁ rM₁
  have hsign : w₁.toNat / 2147483648 % 2 = w₂.toNat / 2147483648 % 2 := by
    have ha : w₁.toNat / 2147483648 % 2 < 2 := Nat.mod_lt _ (by decide)
    have hb : w₂.toNat / 2147483648 % 2 < 2 := Nat.mod_lt _ (by decide)
    unfold sign32 at hs
    rcases (by omega : w₁.toNat / 2147483648 % 2 = 0 ∨ w₁.toNat / 2147483648 % 2 = 1) with h1 | h1 <;>
      rcases (by omega : w₂.toNat / 2147483648 % 2 = 0 ∨ w₂.toNat / 2147483648 % 2 = 1) with h2 | h2 <;>
      rw [h1, h2] at hs ⊢ <;> simp_all
  apply BitVec.eq_of_toNat_eq
  have e1 := decode32_fields_eq w₁
  have e2 := decode32_fields_eq w₂
  have hE : w₁.toNat / 8388608 % 256 = w₂.toNat / 8388608 % 256 := rE₁.trans rE₂.symm
  have hM : w₁.toNat % 8388608 = w₂.toNat % 8388608 := rM₁.trans rM₂.symm
  omega

/-! ## Ties -/

/-- A finite value as close to `a` as the RNE value, but different from it, is the mirror image
`(2t − k)·q` of the RNE grid point `k·q` about `a = t·q`. -/
theorem grid_tie {a : ℚ} (e : ℤ) (hbinade : e ≠ -126 → pow2 e ≤ a)
    {y : ℚ} (hy : FiniteValue32 y)
    (htie : absQ (a - y) = absQ (a - rneInt (a / pow2 (e - 23)) * pow2 (e - 23)))
    (hne : y ≠ rneInt (a / pow2 (e - 23)) * pow2 (e - 23)) :
    ∃ J : ℤ, y = J * pow2 (e - 23) ∧
      (J : ℚ) = 2 * (a / pow2 (e - 23)) - rneInt (a / pow2 (e - 23)) := by
  obtain ⟨j, ey, hey1, hey2, hj, rfl⟩ := hy
  have hq := pow2_pos (e - 23)
  by_cases hge : e ≤ ey
  · refine ⟨j * 2 ^ (ey - e).toNat, ?_, ?_⟩
    · have : pow2 (ey - 23) = pow2 ((ey - e).toNat : ℤ) * pow2 (e - 23) := by
        rw [← pow2_add]; congr 1; omega
      rw [this, ← Rat.mul_assoc, intCast_mul_pow2_nat]
    · have hgrid : (j : ℚ) * pow2 (ey - 23) = ((j * 2 ^ (ey - e).toNat : ℤ) : ℚ) * pow2 (e - 23) := by
        have : pow2 (ey - 23) = pow2 ((ey - e).toNat : ℤ) * pow2 (e - 23) := by
          rw [← pow2_add]; congr 1; omega
        rw [this, ← Rat.mul_assoc, intCast_mul_pow2_nat]
      rw [hgrid] at htie hne
      rw [dist_scale _ _ hq, dist_scale _ _ hq] at htie
      have ht := mul_right_cancel_pos (Rat.ne_of_gt hq) htie
      generalize (j * 2 ^ (ey - e).toNat : ℤ) = J at ht hne ⊢
      generalize rneInt (a / pow2 (e - 23)) = k at ht hne ⊢
      have hJk : (J : ℚ) ≠ k := fun h => hne (by rw [h])
      unfold absQ at ht
      split at ht <;> split at ht <;> grind
  · exfalso
    have hlt : ey < e := by omega
    have hae : pow2 e ≤ a := hbinade (by omega)
    have hn := (grid_nearest e hbinade ⟨j, ey, hey1, hey2, hj, rfl⟩).1
    -- the off-grid value is strictly farther than `2^e`, which is no closer than the RNE point
    have hysmall : (j : ℚ) * pow2 (ey - 23) < pow2 e := by
      have hjle : (j : ℚ) ≤ 16777215 := by
        have : j ≤ 16777215 := by omega
        have h' := Rat.intCast_le_intCast.mpr this
        rwa [show ((16777215 : ℤ) : ℚ) = 16777215 by rw [Rat.intCast_ofNat]] at h'
      have h1 := Rat.mul_le_mul_of_nonneg_right hjle (Rat.le_of_lt (pow2_pos (ey - 23)))
      have h2 : (16777215 : ℚ) * pow2 (ey - 23) < pow2 (ey + 1) := by
        rw [pow2_split (ey + 1) 24, show ey + 1 - ((24 : ℕ) : ℤ) = ey - 23 by omega]
        have := pow2_pos (ey - 23)
        have : ((2 ^ 24 : ℕ) : ℚ) = 16777216 := by simp
        grind
      have h3 := pow2_le_of_le (show ey + 1 ≤ e by omega)
      grind
    have h2e : pow2 e = ((8388608 : ℤ) : ℚ) * pow2 (e - 23) := by
      rw [pow2_split _ 23, show e - ((23 : ℕ) : ℤ) = e - 23 by omega]; rfl
    have hnear := rneInt_nearest (a / pow2 (e - 23)) 8388608
    have hfar : absQ (a - rneInt (a / pow2 (e - 23)) * pow2 (e - 23)) ≤ a - pow2 e := by
      rw [dist_scale _ _ hq]
      have hpe := dist_scale a _ hq 8388608
      rw [← h2e] at hpe
      have : absQ (a - pow2 e) = a - pow2 e := absQ_of_nonneg (by grind)
      rw [← this, hpe]
      exact Rat.mul_le_mul_of_nonneg_right hnear (Rat.le_of_lt hq)
    have : absQ (a - j * pow2 (ey - 23)) = a - j * pow2 (ey - 23) := absQ_of_nonneg (by grind)
    grind

theorem value32_parity (w : F32) :
    w.toNat % 2 = (fields32 (w.toNat / 8388608 % 256) (w.toNat % 8388608)).1 % 2 := by
  unfold fields32
  by_cases h0 : w.toNat / 8388608 % 256 = 0
  · rw [if_pos h0]; dsimp only; omega
  · rw [if_neg h0]; dsimp only; omega

/-- `m·2^(f−23) = n·2^(g−23)` with `f < g` gives `m = n·2^(g−f)`. -/
theorem scale_nat {m n : ℕ} {f g : ℤ} (hfg : f < g)
    (h : (m : ℚ) * pow2 (f - 23) = (n : ℚ) * pow2 (g - 23)) : m = n * 2 ^ (g - f).toNat := by
  have hsplit : pow2 (g - 23) = ((2 ^ (g - f).toNat : ℕ) : ℚ) * pow2 (f - 23) := by
    rw [← pow2_natCast, ← pow2_add]; congr 1; omega
  rw [hsplit, ← Rat.mul_assoc] at h
  have h' := mul_right_cancel_pos (pow2_ne_zero _) h
  exact_mod_cast h'

/-- Every correctly rounded word has the value `rne32` produces. -/
theorem nearestEven32_value {x : ℚ} {w w₀ : F32} (h₀ : rne32 x = some w₀)
    (h : NearestEven32 x w) : value32 w = some (rneValue x) := by
  obtain ⟨d, hd, hnear, htie⟩ := h
  have hr := rne32_value h₀
  obtain ⟨r, hr', hrnear, _⟩ := rne32_nearestEven h₀
  rw [hr] at hr'
  cases hr'
  have hdist : absQ (x - d) = absQ (x - rneValue x) :=
    Rat.le_antisymm (hnear w₀ _ hr) (hrnear w d hd)
  rw [hd]
  by_cases hdr : d = rneValue x
  · rw [hdr]
  exfalso
  have heven := htie w₀ (rneValue x) hr (Ne.symm hdr) hdist.symm
  -- `x ≠ 0`: at zero the only nearest value is zero
  have hx : x ≠ 0 := by
    intro hx0; subst hx0
    rw [rneValue_zero] at hdist hdr
    have : absQ (0 - d) = 0 := by rw [hdist]; decide +kernel
    have : 0 - d = 0 := absQ_eq_zero.mp this
    exact hdr (by grind)
  have ha := absQ_pos hx
  -- move to the magnitude `a = |x|`
  have hfin := value32_finiteValue hd
  let y' := if x < 0 then -d else d
  have hy' : FiniteValue32 y' := by
    show FiniteValue32 (if x < 0 then -d else d)
    split
    · exact hfin.neg
    · exact hfin
  have hmag : absQ (absQ x - y') = absQ (absQ x - rneMagnitude (absQ x)) := by
    show absQ (absQ x - (if x < 0 then -d else d)) = _
    unfold rneValue at hdist
    by_cases hn : x < 0
    · rw [if_pos hn] at hdist ⊢; rw [absQ_of_neg hn]
      have e1 : absQ (-x - -d) = absQ (x - d) := by rw [← absQ_neg]; congr 1; grind
      have e2 : absQ (-x - rneMagnitude (-x)) = absQ (x - -rneMagnitude (-x)) := by
        rw [← absQ_neg]; congr 1; grind
      rw [e1, e2, hdist, absQ_of_neg hn]
    · rw [if_neg hn] at hdist ⊢; rw [absQ_of_nonneg (show (0 : ℚ) ≤ x by grind)] at hdist ⊢
      exact hdist
  have hne' : y' ≠ rneMagnitude (absQ x) := by
    show (if x < 0 then -d else d) ≠ _
    unfold rneValue at hdr
    split
    · rename_i hn; rw [if_pos hn] at hdr; intro h; apply hdr; rw [← h]; grind
    · rename_i hn; rw [if_neg hn] at hdr; exact hdr
  obtain ⟨hbin, hnorm, hemin⟩ := normExp_bounds ha
  obtain ⟨J, hyJ, hJ⟩ := grid_tie (normExp (absQ x)) hnorm hy' hmag hne'
  generalize hT : absQ x / pow2 (normExp (absQ x) - 23) = t at hJ
  have hk := rneInt_dist (absQ x / pow2 (normExp (absQ x) - 23))
  have hk0 := rneInt_nonneg (scaled_bounds ha).2.2
  have hnormal := (scaled_bounds ha).2.1
  rw [hT] at hk hk0 hnormal
  generalize hK : rneInt t = k at hJ hk hk0
  have hkeven : k % 2 = 0 := by
    have := (rneMagnitude_nearest ha hy').2 hmag hne'
    rw [hT, hK] at this; exact this
  -- `J = 2t − k` with `|t − k| ≤ 1/2`, so `J = k ± 1`: odd and positive
  have hJk : J = k + 1 ∨ J = k - 1 := by
    have hJne : J ≠ k := by
      intro hJ'; subst hJ'
      apply hne'; rw [hyJ]; unfold rneMagnitude; rw [hT, hK]
    have h1 : (J : ℚ) - k ≤ 1 ∧ -1 ≤ (J : ℚ) - k := by
      rw [hJ]; unfold absQ at hk; split at hk <;> constructor <;> grind
    have h2 : J - k ≤ 1 := by
      have := h1.1; have : ((J - k : ℤ) : ℚ) ≤ ((1 : ℤ) : ℚ) := by push_cast; exact this
      exact Rat.intCast_le_intCast.mp this
    have h3 : -1 ≤ J - k := by
      have := h1.2; have : ((-1 : ℤ) : ℚ) ≤ ((J - k : ℤ) : ℚ) := by push_cast; exact this
      exact Rat.intCast_le_intCast.mp this
    omega
  have hJodd : J % 2 = 1 := by omega
  have hJk0 : 0 ≤ J + k := by
    have ht0 : 0 ≤ t := by rw [← hT]; exact (scaled_bounds ha).2.2
    have : (0 : ℚ) ≤ ((J + k : ℤ) : ℚ) := by push_cast; rw [hJ]; grind
    exact Rat.intCast_le_intCast.mp (by simpa using this)
  have hJpos : 1 ≤ J := by omega
  -- the word's significand equals `J` up to a power of two; normalization forces equality
  obtain ⟨hE, habs⟩ := value32_abs hd
  have hM : w.toNat % 8388608 < 8388608 := Nat.mod_lt _ (by decide)
  obtain ⟨b, c, n, _, _⟩ := fields32_spec hE hM
  have hpar := value32_parity w
  generalize hf : fields32 (w.toNat / 8388608 % 256) (w.toNat % 8388608) = f at b c n habs hpar
  obtain ⟨m, ew⟩ := f
  simp only at b c n habs hpar
  have habsy : absQ d = absQ y' := by
    show absQ d = absQ (if x < 0 then -d else d)
    split
    · rw [absQ_neg]
    · rfl
  rw [habsy, hyJ, absQ_mul_pos _ _ (pow2_pos _), absQ_intCast] at habs
  have hJnat : ((J.natAbs : ℕ) : ℚ) * pow2 (normExp (absQ x) - 23) = (m : ℚ) * pow2 (ew - 23) := habs
  have hJabs : (J.natAbs : ℤ) = J := by omega
  have hmodd : m % 2 = 1 := by
    rcases Int.lt_trichotomy ew (normExp (absQ x)) with hlt | heq | hgt
    · -- the word's exponent is smaller: impossible for a normal-range tie
      have hm := scale_nat hlt hJnat.symm
      have hnorm' : normExp (absQ x) ≠ -126 := by omega
      have hJbig : (8388608 : ℤ) ≤ J := by
        have := hnormal hnorm'
        have h' : (8388608 : ℚ) - 1 / 2 ≤ J := by
          rw [hJ]; unfold absQ at hk; split at hk <;> grind
        have : ((8388607 : ℤ) : ℚ) < ((J : ℤ) : ℚ) := by
          rw [Rat.intCast_ofNat]; grind
        have := Rat.intCast_lt_intCast.mp this
        omega
      have : 2 ≤ 2 ^ (normExp (absQ x) - ew).toNat := by
        have := Nat.pow_le_pow_right (show 0 < 2 by decide) (show 1 ≤ (normExp (absQ x) - ew).toNat by omega)
        simpa using this
      have := Nat.mul_le_mul (show 8388608 ≤ J.natAbs by omega) this
      omega
    · subst heq
      have := mul_right_cancel_pos (pow2_ne_zero _) hJnat
      have : J.natAbs = m := by exact_mod_cast this
      omega
    · have hm := scale_nat hgt hJnat
      obtain ⟨u, hu⟩ : ∃ u, (ew - normExp (absQ x)).toNat = u + 1 :=
        ⟨_, (Nat.succ_pred_eq_of_pos (by omega)).symm⟩
      have : J.natAbs % 2 = 0 := by
        rw [hm, hu, Nat.pow_succ, ← Nat.mul_assoc]; exact Nat.mul_mod_left _ _
      omega
  omega

/-- A correctly rounded word is the word `rne32` returns. -/
theorem roundsNearestEven32_unique {x : ℚ} {w w₀ : F32} (h₀ : rne32 x = some w₀)
    (h : RoundsNearestEven32 x w) : w = w₀ :=
  value32_injective (nearestEven32_value h₀ h.1) (rne32_value h₀) (by rw [h.2, rne32_sign h₀])

/-- Inside the finite range, `rne32` is characterized by correct rounding: nearest finite value,
even last bit on ties, and the sign of the input. -/
theorem rne32_iff {x : ℚ} {w : F32} (hx : absQ x < overflowThreshold32) :
    rne32 x = some w ↔ RoundsNearestEven32 x w := by
  constructor
  · exact rne32_rounds
  · intro h
    obtain ⟨w₀, h₀⟩ := Option.isSome_iff_exists.mp ((rne32_isSome_iff x).mpr hx)
    rw [h₀, roundsNearestEven32_unique h₀ h]

end MatrixCore
