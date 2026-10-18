import TensorCore.Numerics.ScalarSum

/-! Decoder/encoder round trip for nonzero finite FP32 encodings. -/

namespace TensorCore

set_option maxRecDepth 4096

theorem decode32_fields (b : F32) (d : Decoded) (h : decode32 b = some d) :
    (b.toNat / 8388608 % 256 = 0 ∧ b.toNat % 8388608 = 0 ∧ d = ⟨0, 0, 0⟩) ∨
    (b.toNat / 8388608 % 256 = 0 ∧ b.toNat % 8388608 ≠ 0 ∧
      d = ⟨if (b.toNat / 2147483648 != 0) then -((b.toNat % 8388608 : ℕ) : ℤ)
           else ((b.toNat % 8388608 : ℕ) : ℤ), -126, 23⟩) ∨
    (1 ≤ b.toNat / 8388608 % 256 ∧ b.toNat / 8388608 % 256 ≤ 254 ∧
      d = ⟨if (b.toNat / 2147483648 != 0) then -((8388608 + b.toNat % 8388608 : ℕ) : ℤ)
           else ((8388608 + b.toNat % 8388608 : ℕ) : ℤ),
           ((b.toNat / 8388608 % 256 : ℕ) : ℤ) - 127, 23⟩) := by
  rw [decode32_eq, classifyNat_fp32] at h
  by_cases h1 : b.toNat / 8388608 % 256 = 255
  · by_cases h3 : b.toNat % 8388608 = 0 <;> simp [h1, h3, Classification.finite] at h
  · by_cases h2 : b.toNat / 8388608 % 256 = 0
    · by_cases h3 : b.toNat % 8388608 = 0
      · rw [if_neg h1, if_pos h2, if_pos h3] at h
        simp only [Classification.finite, Option.some.injEq] at h
        subst h
        exact Or.inl ⟨h2, h3, rfl⟩
      · rw [if_neg h1, if_pos h2, if_neg h3] at h
        simp only [Classification.finite, Option.some.injEq] at h
        subst h
        exact Or.inr (Or.inl ⟨h2, h3, rfl⟩)
    · rw [if_neg h1, if_neg h2] at h
      simp only [Classification.finite, Option.some.injEq] at h
      subst h
      exact Or.inr (Or.inr ⟨by omega, by omega, rfl⟩)

theorem roundSignificand_intCast (mode : RoundingMode) (k : ℤ) :
    roundSignificand mode (k : ℚ) = k := by
  cases mode with
  | truncate => exact Rat.floor_intCast k
  | nearestEven =>
    show rneInt (k : ℚ) = k
    unfold rneInt
    rw [Rat.floor_intCast]
    have h : (k : ℚ) - (k : ℚ) = 0 := by grind
    rw [h]
    have h' : ¬ ((1 : ℚ) < 2 * 0 ∨ (2 * (0 : ℚ) = 1 ∧ k % 2 = 1)) := by
      intro hc
      rcases hc with hc | ⟨hc, _⟩ <;> exact absurd hc (by decide +kernel)
    rw [if_neg h']

/-- The converter returns the canonical encoding of any nonzero representable value. -/
theorem round32_canonical (mode : RoundingMode) (negative : Bool) (e k : ℤ)
    (he1 : -126 ≤ e) (he2 : e ≤ 127) (hk0 : 0 < k) (hk1 : k < 2 ^ 24)
    (hsub : 2 ^ 23 ≤ k ∨ e = -126) :
    round32 mode ((if negative then -(k : ℚ) else (k : ℚ)) * pow2 (e - 23)) =
      some (encode32 negative e k) := by
  have hq := pow2_pos (e - 23)
  have hkR : (0 : ℚ) < (k : ℚ) := Rat.intCast_pos.mpr hk0
  have hmag : absQ ((if negative then -(k : ℚ) else (k : ℚ)) * pow2 (e - 23)) =
      (k : ℚ) * pow2 (e - 23) := by
    cases negative <;> simp only [Bool.false_eq_true, ↓reduceIte]
    · rw [absQ_of_nonneg (Rat.le_of_lt (Rat.mul_pos hkR hq))]
    · rw [Rat.neg_mul, absQ_neg, absQ_of_nonneg (Rat.le_of_lt (Rat.mul_pos hkR hq))]
  have hfin : FiniteValue32 ((if negative then -(k : ℚ) else (k : ℚ)) * pow2 (e - 23)) := by
    refine ⟨if negative then -k else k, e, he1, he2, ?_, ?_⟩
    · cases negative <;> simp <;> omega
    · cases negative <;> simp
  have hrange := finiteValue32_abs_le hfin
  have hpos : 0 < (k : ℚ) * pow2 (e - 23) := Rat.mul_pos hkR hq
  have hne : (if negative then -(k : ℚ) else (k : ℚ)) * pow2 (e - 23) ≠ 0 := by
    intro h0
    rw [h0] at hmag
    simp [absQ] at hmag
    grind
  have hexp : normExp ((k : ℚ) * pow2 (e - 23)) = e := by
    unfold normExp emin32
    by_cases hk : 2 ^ 23 ≤ k
    · have hlo : pow2 e ≤ (k : ℚ) * pow2 (e - 23) := by
        rw [binade_grid]
        apply Rat.mul_le_mul_of_nonneg_right _ (Rat.le_of_lt hq)
        have := Rat.intCast_le_intCast.mpr hk
        simpa using this
      have hhi : (k : ℚ) * pow2 (e - 23) < pow2 (e + 1) := by
        rw [next_binade_grid]
        apply Rat.mul_lt_mul_of_pos_right _ hq
        have := Rat.intCast_lt_intCast.mpr hk1
        simpa using this
      rw [magnitudeExponent_eq_of_bounds _ e hlo hhi]
      omega
    · have he : e = -126 := by rcases hsub with h | h <;> omega
      subst he
      have hsmall : (k : ℚ) * pow2 (-126 - 23) < pow2 (-126) := by
        rw [binade_grid (-126)]
        apply Rat.mul_lt_mul_of_pos_right _ (pow2_pos _)
        have hk23 : k < 8388608 := by omega
        have := Rat.intCast_lt_intCast.mpr hk23
        simpa using this
      have hme : magnitudeExponent ((k : ℚ) * pow2 (-126 - 23)) < -126 := by
        apply Classical.byContradiction
        intro hn
        have hge : -126 ≤ magnitudeExponent ((k : ℚ) * pow2 (-126 - 23)) := by omega
        have h1 := (magnitudeExponent_spec _ hpos).1
        have h2 := pow2_le_of_le hge
        grind
      omega
  have hcoef : roundedSignificand mode ((k : ℚ) * pow2 (e - 23)) = k := by
    unfold roundedSignificand
    rw [hexp, Rat.mul_div_cancel (Rat.ne_of_gt hq)]
    exact roundSignificand_intCast mode k
  have hcarry : carry e k = (e, k) := by
    unfold carry
    rw [if_neg (by omega)]
  have hsign : decide ((if negative then -(k : ℚ) else (k : ℚ)) * pow2 (e - 23) < 0) =
      negative := by
    cases negative <;> simp only [Bool.false_eq_true, ↓reduceIte, decide_eq_true_eq,
      decide_eq_false_iff_not]
    · exact Rat.not_lt.mpr (Rat.le_of_lt hpos)
    · rw [Rat.neg_mul]; grind
  unfold round32 round32Core
  rw [if_neg (by rw [hmag]; rw [hmag] at hrange; exact Rat.not_lt.mpr hrange), if_neg hne,
    hmag, hexp, hcoef, hcarry, hsign]
  try dsimp only
  rw [if_neg (show ¬ (e > 127) by omega)]

/-- Converting the value of a nonzero finite encoding returns the same bits. -/
theorem value32_round32 (mode : RoundingMode) (b : F32) (v : ℚ)
    (h : value32 b = some v) (hnz : v ≠ 0) : round32 mode v = some b := by
  unfold value32 at h
  cases hd : decode32 b with
  | none => simp [hd] at h
  | some d =>
    simp only [hd, Option.map_some, Option.some.injEq] at h
    subst h
    have hlt := b.isLt
    have hquot : b.toNat / 2147483648 = 0 ∨ b.toNat / 2147483648 = 1 := by omega
    rcases decode32_fields b d hd with ⟨_, _, rfl⟩ | ⟨hE, hm, rfl⟩ | ⟨hE1, hE2, rfl⟩
    · exact absurd (by decide +kernel : (Decoded.mk 0 0 0).value = 0) hnz
    · -- Subnormal.
      have hval : (Decoded.mk (if (b.toNat / 2147483648 != 0) then
            -((b.toNat % 8388608 : ℕ) : ℤ) else ((b.toNat % 8388608 : ℕ) : ℤ)) (-126) 23).value =
          (if (b.toNat / 2147483648 != 0) then -(((b.toNat % 8388608 : ℕ) : ℤ) : ℚ)
            else (((b.toNat % 8388608 : ℕ) : ℤ) : ℚ)) * pow2 (-126 - 23) := by
        unfold Decoded.value
        cases hs : (b.toNat / 2147483648 != 0) <;> simp
      rw [hval]
      rw [round32_canonical mode _ (-126) _ (by omega) (by omega) (by omega) (by omega)
        (Or.inr rfl)]
      refine congrArg some ?_
      apply BitVec.eq_of_toNat_eq
      rw [encode32_toNat _ _ _ (by omega) (by omega) (by omega) (by omega)]
      cases hs : (b.toNat / 2147483648 != 0)
      · have : b.toNat / 2147483648 = 0 := by simpa using hs
        simp only [Bool.false_eq_true, ↓reduceIte, Nat.reducePow, Int.reducePow]
        rw [if_pos (by omega)]
        omega
      · have : b.toNat / 2147483648 ≠ 0 := by simpa using hs
        simp only [↓reduceIte, Nat.reducePow, Int.reducePow]
        rw [if_pos (by omega)]
        omega
    · -- Normal.
      have hval : (Decoded.mk (if (b.toNat / 2147483648 != 0) then
            -((8388608 + b.toNat % 8388608 : ℕ) : ℤ) else ((8388608 + b.toNat % 8388608 : ℕ) : ℤ))
            (((b.toNat / 8388608 % 256 : ℕ) : ℤ) - 127) 23).value =
          (if (b.toNat / 2147483648 != 0) then -(((8388608 + b.toNat % 8388608 : ℕ) : ℤ) : ℚ)
            else (((8388608 + b.toNat % 8388608 : ℕ) : ℤ) : ℚ)) *
            pow2 (((b.toNat / 8388608 % 256 : ℕ) : ℤ) - 127 - 23) := by
        unfold Decoded.value
        cases hs : (b.toNat / 2147483648 != 0) <;> simp
      rw [hval]
      rw [round32_canonical mode _ _ _ (by omega) (by omega) (by omega) (by omega)
        (Or.inl (by omega))]
      refine congrArg some ?_
      apply BitVec.eq_of_toNat_eq
      rw [encode32_toNat _ _ _ (by omega) (by omega) (by omega) (by omega)]
      cases hs : (b.toNat / 2147483648 != 0)
      · have : b.toNat / 2147483648 = 0 := by simpa using hs
        simp only [Bool.false_eq_true, ↓reduceIte, Nat.reducePow, Int.reducePow]
        rw [if_neg (by omega)]
        omega
      · have : b.toNat / 2147483648 ≠ 0 := by simpa using hs
        simp only [↓reduceIte, Nat.reducePow, Int.reducePow]
        rw [if_neg (by omega)]
        omega

/-- Nonzero finite values have unique encodings. -/
theorem value32_injective (b₁ b₂ : F32) (v : ℚ) (h₁ : value32 b₁ = some v)
    (h₂ : value32 b₂ = some v) (hnz : v ≠ 0) : b₁ = b₂ := by
  have r₁ := value32_round32 .truncate b₁ v h₁ hnz
  have r₂ := value32_round32 .truncate b₂ v h₂ hnz
  rw [r₁] at r₂
  exact Option.some.inj r₂

end TensorCore
