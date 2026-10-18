import MatrixCore.Numerics.Round32

/-! # Correctness of binary32 RNE

`rne32` returns the binary32 word whose value is nearest to the exact input among *all finite
binary32 words*, with an even last bit on ties, and it overflows exactly at
`2^128 − 2^103`. -/

namespace MatrixCore

/-! ## Encoding and decoding binary32 -/

/-- Decoding a constructed word returns its sign, significand, and exponent. -/
theorem decode_encode32 (negative : Bool) (e : ℤ) (m : ℕ) (he1 : -126 ≤ e) (he2 : e ≤ 127)
    (hm : m < 16777216) (hn : 8388608 ≤ m ∨ e = -126) :
    fp32.decode (encode32 negative e m) = .finite ⟨negative, m, e, 23⟩ := by
  show fp32.decodeNat (BitVec.ofNat 32 _).toNat = _
  rw [BitVec.toNat_ofNat]
  unfold Format.decodeNat
  simp only [fp32, Format.unpackFields, Format.emin, show (2 : ℕ) ^ 23 = 8388608 from rfl,
    show (2 : ℕ) ^ 8 = 256 from rfl, show (2 : ℕ) ^ (23 + 8) = 2147483648 from rfl,
    show (2 : ℕ) ^ 32 = 4294967296 from rfl]
  generalize hN : ((if negative then 2147483648 else 0) +
    (if m < 8388608 then m else (e + 127).toNat * 8388608 + (m - 8388608))) % 4294967296 = N
  by_cases hs : m < 8388608
  · have he : e = -126 := by omega
    subst he
    have hN' : N = (if negative then 2147483648 else 0) + m := by
      rw [← hN, if_pos hs]; cases negative <;> simp <;> omega
    have hM : N % 8388608 = m := by rw [hN']; cases negative <;> simp <;> omega
    have hE : N / 8388608 % 256 = 0 := by rw [hN']; cases negative <;> simp <;> omega
    have hS : (N / 2147483648 % 2 == 1) = negative := by
      rw [hN']; cases negative <;> simp <;> omega
    simp only [hM, hE, hS]
    simp
  · have hN' : N = (if negative then 2147483648 else 0) +
        ((e + 127).toNat * 8388608 + (m - 8388608)) := by
      rw [← hN, if_neg hs]; cases negative <;> simp <;> omega
    have hM : N % 8388608 = m - 8388608 := by rw [hN']; cases negative <;> simp <;> omega
    have hE : N / 8388608 % 256 = (e + 127).toNat := by
      rw [hN']; cases negative <;> simp <;> omega
    have hS : (N / 2147483648 % 2 == 1) = negative := by
      rw [hN']; cases negative <;> simp <;> omega
    simp only [hM, hE, hS]
    have h1 : (e + 127).toNat ≠ 256 - 1 := by omega
    have h2 : (e + 127).toNat ≠ 0 := by omega
    simp only [h1, h2, ↓reduceIte, Datum.finite.injEq, Unpacked.mk.injEq, true_and]
    exact ⟨by omega, by omega, trivial⟩

/-- Every finite binary32 word decodes to `±m · 2^(e−23)` with `m < 2^24` and `−126 ≤ e ≤ 127`. -/
theorem decode32_finite_fields {w : F32} {x : Unpacked} (h : fp32.decode w = .finite x) :
    x.t = 23 ∧ x.m < 16777216 ∧ -126 ≤ x.e ∧ x.e ≤ 127 ∧ (8388608 ≤ x.m ∨ x.e = -126) := by
  unfold Format.decode Format.decodeNat at h
  simp only [fp32, Format.unpackFields, Format.emin] at h
  have hw := w.isLt
  generalize w.toNat = n at h hw
  simp only [show (2 : ℕ) ^ 23 = 8388608 from rfl, show (2 : ℕ) ^ 8 = 256 from rfl,
    show (2 : ℕ) ^ (23 + 8) = 2147483648 from rfl] at h
  have hM : n % 8388608 < 8388608 := Nat.mod_lt _ (by decide)
  have hE : n / 8388608 % 256 < 256 := Nat.mod_lt _ (by decide)
  split at h
  · split at h <;> simp at h
  · split at h
    · simp only [Datum.finite.injEq] at h
      subst h
      exact ⟨rfl, by simp only; omega, by simp only; omega, by simp only; omega, Or.inr rfl⟩
    · rename_i htop hz
      simp only [Datum.finite.injEq] at h
      subst h
      exact ⟨rfl, by simp only; omega, by simp only; omega, by simp only; omega,
        Or.inl (by simp only; omega)⟩

/-- Arithmetic form of every finite binary32 value. -/
def FiniteValue32 (y : ℚ) : Prop :=
  ∃ k e : ℤ, -126 ≤ e ∧ e ≤ 127 ∧ k.natAbs < 16777216 ∧ y = (k : ℚ) * pow2 (e - 23)

theorem value32_finiteValue {w : F32} {y : ℚ} (h : value32 w = some y) : FiniteValue32 y := by
  unfold value32 at h
  cases hd : fp32.decode w with
  | finite x =>
    rw [hd] at h
    simp only [Datum.toFinite, Option.map_some, Option.some.injEq] at h
    obtain ⟨ht, hm, he1, he2, _⟩ := decode32_finite_fields hd
    refine ⟨if x.negative then -(x.m : ℤ) else x.m, x.e, he1, he2, ?_, ?_⟩
    · split <;> simp <;> omega
    · rw [← h]; unfold Unpacked.value; rw [ht]
      split <;> simp [Rat.intCast_neg, Rat.intCast_natCast]
  | infinity _ => rw [hd] at h; simp [Datum.toFinite] at h
  | nan => rw [hd] at h; simp [Datum.toFinite] at h

theorem FiniteValue32.neg {y : ℚ} (h : FiniteValue32 y) : FiniteValue32 (-y) := by
  obtain ⟨k, e, h1, h2, hk, rfl⟩ := h
  exact ⟨-k, e, h1, h2, by omega, by rw [Rat.intCast_neg, Rat.neg_mul]⟩

/-! ## The rounded magnitude -/

theorem mul_right_cancel_pos {a b q : ℚ} (hq : q ≠ 0) (h : a * q = b * q) : a = b := by
  have ha := Rat.mul_div_cancel (a := a) hq
  have hb := Rat.mul_div_cancel (a := b) hq
  rw [← ha, ← hb, h]

theorem pow2_split (e : ℤ) (n : ℕ) : pow2 e = ((2 ^ n : ℕ) : ℚ) * pow2 (e - n) := by
  rw [← pow2_natCast, ← pow2_add]; congr 1; omega

theorem le_div_of_mul_le {x a q : ℚ} (hq : 0 < q) (h : x * q ≤ a) : x ≤ a / q :=
  Rat.not_lt.mp fun h' => by have := (Rat.div_lt_iff hq).mp h'; grind

/-- Magnitude bounds of the rounding binade: `a < 2^(e+1)`, and `2^e ≤ a` above the subnormal range. -/
theorem normExp_bounds {a : ℚ} (ha : 0 < a) :
    a < pow2 (normExp a + 1) ∧ (normExp a ≠ -126 → pow2 (normExp a) ≤ a) ∧ -126 ≤ normExp a := by
  obtain ⟨hlo, hhi⟩ := log2Floor_spec ha
  unfold normExp
  refine ⟨?_, ?_, by omega⟩
  · have := pow2_le_of_le (show log2Floor a + 1 ≤ max (log2Floor a) (-126) + 1 by omega)
    grind
  · intro hne
    have : max (log2Floor a) (-126) = log2Floor a := by omega
    rw [this]; exact hlo

theorem pow2_shift (e : ℤ) (n : ℕ) : pow2 (e + n) = ((2 ^ n : ℕ) : ℚ) * pow2 e := by
  rw [pow2_add, pow2_natCast, Rat.mul_comm]

/-- Scaled magnitude `a / 2^(e−23)` lies below `2^24`, and at least `2^23` in the normal range. -/
theorem scaled_bounds {a : ℚ} (ha : 0 < a) :
    a / pow2 (normExp a - 23) < 16777216 ∧
      (normExp a ≠ -126 → (8388608 : ℚ) ≤ a / pow2 (normExp a - 23)) ∧
      0 ≤ a / pow2 (normExp a - 23) := by
  obtain ⟨h1, h2, _⟩ := normExp_bounds ha
  have hq := pow2_pos (normExp a - 23)
  have e1 : pow2 (normExp a + 1) = 16777216 * pow2 (normExp a - 23) := by
    rw [pow2_split _ 24, show normExp a + 1 - ((24 : ℕ) : ℤ) = normExp a - 23 by omega]; rfl
  have e2 : pow2 (normExp a) = 8388608 * pow2 (normExp a - 23) := by
    rw [pow2_split _ 23, show normExp a - ((23 : ℕ) : ℤ) = normExp a - 23 by omega]; rfl
  refine ⟨?_, ?_, ?_⟩
  · rw [Rat.div_lt_iff hq]; rw [e1] at h1; exact h1
  · intro hne
    apply le_div_of_mul_le hq; rw [e2] at h2; exact h2 hne
  · rw [Rat.div_def]; exact Rat.mul_nonneg (Rat.le_of_lt ha) (Rat.le_of_lt (Rat.inv_pos.mpr hq))

/-- The rounded magnitude `rneInt(a / 2^(e−23)) · 2^(e−23)` with `e = normExp a`. -/
def rneMagnitude (a : ℚ) : ℚ :=
  (rneInt (a / pow2 (normExp a - 23)) : ℚ) * pow2 (normExp a - 23)

/-- The rounded signed value. -/
def rneValue (x : ℚ) : ℚ := if x < 0 then -rneMagnitude (absQ x) else rneMagnitude (absQ x)

theorem dist_scale (a q : ℚ) (hq : 0 < q) (j : ℤ) :
    absQ (a - j * q) = absQ (a / q - j) * q := by
  rw [← absQ_mul_pos _ q hq]
  have := Rat.div_mul_cancel (a := a) (Rat.ne_of_gt hq)
  congr 1
  grind

/-- Nearest property on the grid `2^(e−23)` against every finite value, strict off the grid. -/
theorem grid_nearest {a : ℚ} (e : ℤ) (hbinade : e ≠ -126 → pow2 e ≤ a)
    {y : ℚ} (hy : FiniteValue32 y) :
    absQ (a - rneInt (a / pow2 (e - 23)) * pow2 (e - 23)) ≤ absQ (a - y) ∧
      (absQ (a - y) = absQ (a - rneInt (a / pow2 (e - 23)) * pow2 (e - 23)) →
        y ≠ rneInt (a / pow2 (e - 23)) * pow2 (e - 23) →
        rneInt (a / pow2 (e - 23)) % 2 = 0) := by
  obtain ⟨j, ey, hey1, hey2, hj, rfl⟩ := hy
  have hq := pow2_pos (e - 23)
  have hscale : ∀ i : ℤ, absQ (a - i * pow2 (e - 23)) = absQ (a / pow2 (e - 23) - i) * pow2 (e - 23) :=
    fun i => dist_scale a _ hq i
  have hn := rneInt_nearest (a / pow2 (e - 23))
  have htie := rneInt_tie_even (a / pow2 (e - 23))
  generalize rneInt (a / pow2 (e - 23)) = k at hn htie ⊢
  by_cases hge : e ≤ ey
  · -- `y` lies on the rounding grid.
    have hgrid : (j : ℚ) * pow2 (ey - 23) = ((j * 2 ^ (ey - e).toNat : ℤ) : ℚ) * pow2 (e - 23) := by
      have : pow2 (ey - 23) = pow2 ((ey - e).toNat : ℤ) * pow2 (e - 23) := by
        rw [← pow2_add]; congr 1; omega
      rw [this, ← Rat.mul_assoc, intCast_mul_pow2_nat]
    rw [hgrid, hscale, hscale]
    refine ⟨Rat.mul_le_mul_of_nonneg_right (hn _) (Rat.le_of_lt hq), ?_⟩
    intro hti hne
    have hti' := mul_right_cancel_pos (Rat.ne_of_gt hq) hti
    exact htie _ hti' (fun h => hne (by rw [h]))
  · -- `y` is below the binade `[2^e, 2^(e+1))`, which `a` occupies.
    have hae : pow2 e ≤ a := hbinade (by omega)
    have hysmall : (j : ℚ) * pow2 (ey - 23) < pow2 e := by
      have hjle : (j : ℚ) ≤ 16777215 := by
        have : j ≤ 16777215 := by omega
        have h' := Rat.intCast_le_intCast.mpr this
        have hc : ((16777215 : ℤ) : ℚ) = 16777215 := by simp only [Rat.intCast_ofNat]
        rwa [hc] at h'
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
    have hnear : absQ (a - k * pow2 (e - 23)) ≤ a - pow2 e := by
      rw [hscale]
      have hpe := hscale 8388608
      rw [← h2e] at hpe
      have : absQ (a - pow2 e) = a - pow2 e := absQ_of_nonneg (by grind)
      rw [← this, hpe]
      exact Rat.mul_le_mul_of_nonneg_right (hn _) (Rat.le_of_lt hq)
    have hfar : a - pow2 e < absQ (a - j * pow2 (ey - 23)) := by
      have : absQ (a - j * pow2 (ey - 23)) = a - j * pow2 (ey - 23) := absQ_of_nonneg (by grind)
      rw [this]; grind
    refine ⟨by grind, ?_⟩
    intro hti _
    grind

theorem rneMagnitude_nearest {a : ℚ} (ha : 0 < a) {y : ℚ} (hy : FiniteValue32 y) :
    absQ (a - rneMagnitude a) ≤ absQ (a - y) ∧
      (absQ (a - y) = absQ (a - rneMagnitude a) → y ≠ rneMagnitude a →
        rneInt (a / pow2 (normExp a - 23)) % 2 = 0) :=
  grid_nearest (normExp a) (normExp_bounds ha).2.1 hy

/-! ## Fields of the result -/

theorem rneFields_spec {a : ℚ} (ha : 0 < a) :
    -126 ≤ (rneFields a).1 ∧ (rneFields a).2 < 16777216 ∧
      (8388608 ≤ (rneFields a).2 ∨ (rneFields a).1 = -126) ∧
      ((rneFields a).2 : ℚ) * pow2 ((rneFields a).1 - 23) = rneMagnitude a ∧
      (rneFields a).2 % 2 = (rneInt (a / pow2 (normExp a - 23))).toNat % 2 ∧
      ((rneFields a).1 = normExp a ∨
        ((rneFields a).1 = normExp a + 1 ∧ rneInt (a / pow2 (normExp a - 23)) = 16777216)) := by
  obtain ⟨hlt, hnorm, hge⟩ := scaled_bounds ha
  obtain ⟨_, _, hemin⟩ := normExp_bounds ha
  have hk0 := rneInt_nonneg hge
  have hk1 : rneInt (a / pow2 (normExp a - 23)) ≤ 16777216 := by
    apply rneInt_le_of_lt
    rw [Rat.intCast_ofNat]; exact hlt
  unfold rneFields rneMagnitude
  simp only
  split
  · rename_i hk
    refine ⟨by simp; omega, by simp, Or.inl (by simp), ?_, ?_, Or.inr ⟨rfl, hk⟩⟩
    · simp only
      rw [hk, show normExp a + 1 - 23 = (normExp a - 23) + 1 by omega, pow2_succ]
      rw [Rat.mul_comm (pow2 _) 2, ← Rat.mul_assoc]
      have h2 : ((8388608 : ℕ) : ℚ) * 2 = ((16777216 : ℤ) : ℚ) := by
        rw [Rat.natCast_ofNat, Rat.intCast_ofNat]; decide +kernel
      rw [h2]
    · rw [hk]
      show (8388608 : ℕ) % 2 = (16777216 : ℤ).toNat % 2
      decide +kernel
  · rename_i hk
    have hk2 : rneInt (a / pow2 (normExp a - 23)) < 16777216 := by omega
    refine ⟨hemin, by omega, ?_, ?_, rfl, Or.inl rfl⟩
    · by_cases hn : normExp a = -126
      · exact Or.inr hn
      · left
        have := le_rneInt_of_le (n := 8388608) (by rw [Rat.intCast_ofNat]; exact hnorm hn)
        omega
    · congr 1
      rw [← Rat.intCast_natCast, Int.toNat_of_nonneg hk0]

/-! ## Correctness -/

/-- Nearest finite binary32 value to `x`, ties to an even last bit, compared against every
finite binary32 word. -/
def NearestEven32 (x : ℚ) (w : F32) : Prop :=
  ∃ d, value32 w = some d ∧
    (∀ v y, value32 v = some y → absQ (x - d) ≤ absQ (x - y)) ∧
    (∀ v y, value32 v = some y → y ≠ d → absQ (x - y) = absQ (x - d) → w.toNat % 2 = 0)

theorem encode32_parity (negative : Bool) (e : ℤ) (m : ℕ) (hm : m < 16777216) :
    (encode32 negative e m).toNat % 2 = m % 2 := by
  show (BitVec.ofNat 32 _).toNat % 2 = _
  rw [BitVec.toNat_ofNat]
  by_cases hs : m < 8388608 <;> cases negative <;> simp [hs] <;> omega

theorem value32_encode32 (negative : Bool) (e : ℤ) (m : ℕ) (he1 : -126 ≤ e) (he2 : e ≤ 127)
    (hm : m < 16777216) (hn : 8388608 ≤ m ∨ e = -126) :
    value32 (encode32 negative e m) =
      some ((if negative then -(m : ℚ) else (m : ℚ)) * pow2 (e - 23)) := by
  unfold value32
  rw [decode_encode32 negative e m he1 he2 hm hn]
  rfl

theorem rneValue_zero : rneValue 0 = 0 := by
  unfold rneValue rneMagnitude
  have h0 : absQ 0 = 0 := rfl
  have h1 : (0 : ℚ) / pow2 (normExp 0 - 23) = ((0 : ℤ) : ℚ) := by
    rw [Rat.div_def, Rat.zero_mul]; rfl
  simp only [h0, h1, rneInt_intCast]
  simp

theorem value32_zero : value32 0 = some 0 := by
  have : (0 : F32) = encode32 false (-126) 0 := by decide
  rw [this, value32_encode32 false (-126) 0 (by decide) (by decide) (by decide) (Or.inr rfl)]
  simp

/-- Successful conversion of a nonzero input: the encoded fields. -/
theorem rne32_some {x : ℚ} {w : F32} (hx : x ≠ 0) (h : rne32 x = some w) :
    (rneFields (absQ x)).1 ≤ 127 ∧ w = encode32 (decide (x < 0)) (rneFields (absQ x)).1 (rneFields (absQ x)).2 := by
  unfold rne32 at h
  rw [if_neg hx] at h
  simp only at h
  split at h
  · simp at h
  · rename_i hle
    simp only [Option.some.injEq] at h
    exact ⟨by omega, h.symm⟩

/-- The value of a successful conversion is the rounded value. -/
theorem rne32_value {x : ℚ} {w : F32} (h : rne32 x = some w) : value32 w = some (rneValue x) := by
  by_cases hx : x = 0
  · subst hx
    unfold rne32 at h; simp at h; subst h
    rw [rneValue_zero]; exact value32_zero
  · obtain ⟨hle, rfl⟩ := rne32_some hx h
    have ha := absQ_pos hx
    obtain ⟨h1, h2, h3, h4, _, _⟩ := rneFields_spec ha
    rw [value32_encode32 _ _ _ h1 hle h2 h3]
    congr 1
    unfold rneValue
    by_cases hn : x < 0
    · simp only [hn, decide_true, ↓reduceIte, Rat.neg_mul]; rw [h4]
    · simp only [hn, decide_false, Bool.false_eq_true, ↓reduceIte]; rw [h4]

/-- Correct rounding: a successful `fl{x}` is the nearest finite binary32 value, ties to even. -/
theorem rne32_nearestEven {x : ℚ} {w : F32} (h : rne32 x = some w) : NearestEven32 x w := by
  refine ⟨rneValue x, rne32_value h, ?_, ?_⟩
  · intro v y hv
    have hy := value32_finiteValue hv
    by_cases hx : x = 0
    · subst hx; rw [rneValue_zero]
      have : absQ (0 - 0 : ℚ) = 0 := by decide +kernel
      rw [this]; exact absQ_nonneg _
    · have ha := absQ_pos hx
      by_cases hn : x < 0
      · have hnear := (rneMagnitude_nearest ha hy.neg).1
        unfold rneValue; rw [if_pos hn]
        rw [absQ_of_neg hn] at hnear ⊢
        have e1 : absQ (x - -rneMagnitude (-x)) = absQ (-x - rneMagnitude (-x)) := by
          rw [← absQ_neg]; congr 1; grind
        have e2 : absQ (x - y) = absQ (-x - -y) := by rw [← absQ_neg]; congr 1; grind
        rw [e1, e2]; exact hnear
      · have hnear := (rneMagnitude_nearest ha hy).1
        unfold rneValue; rw [if_neg hn]
        rw [absQ_of_nonneg (show (0 : ℚ) ≤ x by grind)] at hnear ⊢
        exact hnear
  · intro v y hv hne hti
    have hy := value32_finiteValue hv
    by_cases hx : x = 0
    · subst hx
      unfold rne32 at h; simp at h; subst h; decide
    · have ha := absQ_pos hx
      obtain ⟨hle, rfl⟩ := rne32_some hx h
      obtain ⟨_, h2, _, _, h5, _⟩ := rneFields_spec ha
      rw [encode32_parity _ _ _ h2, h5]
      have heven : rneInt (absQ x / pow2 (normExp (absQ x) - 23)) % 2 = 0 := by
        by_cases hn : x < 0
        · have hk := (rneMagnitude_nearest ha hy.neg).2
          unfold rneValue at hne hti; rw [if_pos hn] at hne hti
          rw [absQ_of_neg hn] at hk ⊢
          apply hk
          · have e1 : absQ (x - -rneMagnitude (-x)) = absQ (-x - rneMagnitude (-x)) := by
              rw [← absQ_neg]; congr 1; grind
            have e2 : absQ (x - y) = absQ (-x - -y) := by rw [← absQ_neg]; congr 1; grind
            rw [← e1, ← e2]; rw [absQ_of_neg hn] at hti; exact hti
          · intro he; apply hne; rw [absQ_of_neg hn]; grind
        · have hk := (rneMagnitude_nearest ha hy).2
          unfold rneValue at hne hti; rw [if_neg hn] at hne hti
          rw [absQ_of_nonneg (show (0 : ℚ) ≤ x by grind)] at hk hne hti ⊢
          exact hk hti hne
      have hk0 := rneInt_nonneg (scaled_bounds ha).2.2
      omega

/-! ## Overflow threshold -/

/-- Values from `2^24 − 1/2` up to `2^24` round to `2^24` (the odd neighbour `2^24 − 1` loses ties). -/
theorem rneInt_top {t : ℚ} (h1 : 16777216 - 1 / 2 ≤ t) (h2 : t < 16777216) :
    rneInt t = 16777216 := by
  have hf1 : (16777215 : ℤ) ≤ t.floor := Rat.le_floor_iff.mpr (by
    have : ((16777215 : ℤ) : ℚ) = 16777215 := by rw [Rat.intCast_ofNat]
    rw [this]; grind)
  have hf2 : t.floor < 16777216 := Rat.floor_lt_iff.mpr (by
    have : ((16777216 : ℤ) : ℚ) = 16777216 := by rw [Rat.intCast_ofNat]
    rw [this]; exact h2)
  have hf : t.floor = 16777215 := by omega
  unfold rneInt
  rw [hf]
  have : (1 < 2 * (t - ((16777215 : ℤ) : ℚ)) ∨ (2 * (t - ((16777215 : ℤ) : ℚ)) = 1 ∧ (16777215 : ℤ) % 2 = 1)) := by
    have hc : ((16777215 : ℤ) : ℚ) = 16777215 := by rw [Rat.intCast_ofNat]
    rw [hc]
    by_cases hs : 1 < 2 * (t - 16777215)
    · exact Or.inl hs
    · right; exact ⟨by grind, by decide⟩
  rw [if_pos this]; rfl

theorem rne32_zero : rne32 0 = some 0 := by unfold rne32; simp

theorem rneFields_fst (a : ℚ) : (rneFields a).1 =
    if rneInt (a / pow2 (normExp a - 23)) = 16777216 then normExp a + 1 else normExp a := by
  unfold rneFields; simp only
  split <;> simp [*]

/-- `fl{x}` is finite exactly below the IEEE overflow threshold `2^128 − 2^103`. -/
theorem rne32_isSome_iff (x : ℚ) : (rne32 x).isSome ↔ absQ x < overflowThreshold32 := by
  by_cases hx : x = 0
  · subst hx; rw [rne32_zero]; simp only [Option.isSome_some, true_iff]; decide +kernel
  have ha := absQ_pos hx
  obtain ⟨hlt, _, hge⟩ := scaled_bounds ha
  obtain ⟨hbin, hnorm, hemin⟩ := normExp_bounds ha
  have hk := rneInt_dist (absQ x / pow2 (normExp (absQ x) - 23))
  have hq := pow2_pos (normExp (absQ x) - 23)
  have hsplit : absQ x = absQ x / pow2 (normExp (absQ x) - 23) * pow2 (normExp (absQ x) - 23) :=
    (div_mul_pow2 _ _).symm
  have hthr : overflowThreshold32 = (16777216 - 1 / 2) * pow2 104 := by
    unfold overflowThreshold32; decide +kernel
  have h127 : pow2 127 < (16777216 - 1 / 2) * pow2 104 := by decide +kernel
  have h128 : (16777216 - 1 / 2) * pow2 104 < pow2 128 := by decide +kernel
  have hsome : (rne32 x).isSome ↔ (rneFields (absQ x)).1 ≤ 127 := by
    unfold rne32; rw [if_neg hx]; simp only
    split <;> simp <;> omega
  rw [hsome, rneFields_fst, hthr]
  generalize hT : absQ x / pow2 (normExp (absQ x) - 23) = T at *
  generalize hK : rneInt T = K at *
  generalize hE : normExp (absQ x) = E at *
  have hT' : T < 16777216 := hlt
  have hEle : E ≤ 127 → pow2 (E - 23) ≤ pow2 104 := fun h => pow2_le_of_le (by omega)
  constructor
  · intro hle
    split at hle
    · rename_i hK2
      have h1 := pow2_le_of_le (show E + 1 ≤ 127 by omega)
      grind
    · rename_i hK2
      have hTlt : T < 16777216 - 1 / 2 := by
        apply Classical.byContradiction
        intro hc
        have := rneInt_top (Rat.not_lt.mp hc) hT'
        rw [hK] at this; exact hK2 this
      have h1 := Rat.mul_lt_mul_of_pos_right hTlt hq
      have h2 := Rat.mul_le_mul_of_nonneg_left (hEle hle) (show (0 : ℚ) ≤ 16777216 - 1 / 2 by decide +kernel)
      grind
  · intro hlt'
    have hE127 : E ≤ 127 := by
      apply Classical.byContradiction
      intro hc
      have h1 := hnorm (by omega)
      have h2 := pow2_le_of_le (show (128 : ℤ) ≤ E by omega)
      grind
    split
    · rename_i hK2
      by_cases h127' : E = 127
      · exfalso
        subst h127'
        rw [hK2] at hk
        have hTge : 16777216 - 1 / 2 ≤ T := by
          have := (absQ_le_iff _ _).mp (show absQ (T - ((16777216 : ℤ) : ℚ)) ≤ 1 / 2 by grind)
          rw [Rat.intCast_ofNat] at this; grind
        have := Rat.mul_le_mul_of_nonneg_right hTge (Rat.le_of_lt hq)
        have h104 : (127 : ℤ) - 23 = 104 := by decide
        rw [h104] at this
        grind
      · omega
    · exact hE127

end MatrixCore
