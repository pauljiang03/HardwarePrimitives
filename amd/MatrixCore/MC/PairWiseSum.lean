import MatrixCore.MC.AcceptedDomain

/-! # `pair_wise_sum`: CDNA 2

Closed forms of the pairwise sum for groups of two and four, and flush to zero in `fl{·}`. -/

namespace MatrixCore

theorem pairwiseGroupSum_two (ftz : Bool) (n : ℕ) (q₁ q₂ : ℚ) :
    pairwiseGroupSum ftz (n + 1) [q₁, q₂] = flValue ftz (q₁ + q₂) := by
  simp [pairwiseGroupSum]

theorem pairwiseGroupSum_four (ftz : Bool) (n : ℕ) (q₁ q₂ q₃ q₄ : ℚ) :
    pairwiseGroupSum ftz (n + 2) [q₁, q₂, q₃, q₄] =
      (flValue ftz (q₁ + q₂)).bind fun u =>
        (flValue ftz (q₃ + q₄)).bind fun v => flValue ftz (u + v) := by
  simp only [pairwiseGroupSum, List.length_cons, List.length_nil]
  simp [pairwiseGroupSum_two]

/-- A group of four: `S_acc = c + fl{fl{p₁ + p₂} + fl{p₃ + p₄}}` with `p_ℓ = fl{a_ℓ b_ℓ}`. -/
theorem pairwiseSum_four (P : Model) (x : Prepared) (p₁ p₂ p₃ p₄ : Unpacked)
    (hp : (if P.subnormals then x else x.flushed).p = [p₁, p₂, p₃, p₄]) :
    pairwiseSum P x = do
      let q₁ ← flValue (!P.subnormals) p₁.value
      let q₂ ← flValue (!P.subnormals) p₂.value
      let q₃ ← flValue (!P.subnormals) p₃.value
      let q₄ ← flValue (!P.subnormals) p₄.value
      let u ← flValue (!P.subnormals) (q₁ + q₂)
      let v ← flValue (!P.subnormals) (q₃ + q₄)
      let t ← flValue (!P.subnormals) (u + v)
      return (if P.subnormals then x else x.flushed).c.value + t := by
  unfold pairwiseSum
  simp only [hp, List.mapM_cons, List.mapM_nil]
  cases flValue (!P.subnormals) p₁.value <;> cases flValue (!P.subnormals) p₂.value <;>
    cases flValue (!P.subnormals) p₃.value <;> cases flValue (!P.subnormals) p₄.value <;>
    simp [pairwiseGroupSum_four, Option.bind_assoc]

/-- A group of two: `S_acc = c + fl{p₁ + p₂}`. -/
theorem pairwiseSum_two (P : Model) (x : Prepared) (p₁ p₂ : Unpacked)
    (hp : (if P.subnormals then x else x.flushed).p = [p₁, p₂]) :
    pairwiseSum P x = do
      let q₁ ← flValue (!P.subnormals) p₁.value
      let q₂ ← flValue (!P.subnormals) p₂.value
      let t ← flValue (!P.subnormals) (q₁ + q₂)
      return (if P.subnormals then x else x.flushed).c.value + t := by
  unfold pairwiseSum
  simp only [hp, List.mapM_cons, List.mapM_nil]
  cases flValue (!P.subnormals) p₁.value <;> cases flValue (!P.subnormals) p₂.value <;>
    simp [pairwiseGroupSum_two]

/-! ## Flush to zero -/

theorem value32_subnormal {w : F32} {y : ℚ} (h : value32 w = some y) :
    (isSubnormal32 w = true → y ≠ 0 ∧ absQ y < pow2 (-126)) ∧
      (isSubnormal32 w = false → y = 0 ∨ pow2 (-126) ≤ absQ y) := by
  unfold value32 at h
  rw [decode32_eq] at h
  simp only at h
  have hM : w.toNat % 8388608 < 8388608 := Nat.mod_lt _ (by decide)
  unfold isSubnormal32
  generalize w.toNat % 8388608 = M at h hM ⊢
  generalize w.toNat / 8388608 % 256 = E at h ⊢
  generalize (w.toNat / 2147483648 % 2 == 1) = neg at h ⊢
  split at h
  · split at h <;> simp [Datum.toFinite] at h
  · rename_i hE
    simp only [Datum.toFinite, Option.map_some, Option.some.injEq] at h
    subst h
    split
    · rename_i hE0
      subst hE0
      have hval : absQ (Unpacked.value ⟨neg, M, -126, 23⟩) = (M : ℚ) * pow2 (-149) := by
        rw [Unpacked.absQ_value]; rfl
      constructor
      · intro hs
        simp at hs
        refine ⟨fun h0 => hs ((Unpacked.value_eq_zero_iff _).mp h0), ?_⟩
        rw [hval]
        have : (M : ℚ) < 8388608 := by exact_mod_cast hM
        have h1 := Rat.mul_lt_mul_of_pos_right this (pow2_pos (-149))
        have : (8388608 : ℚ) * pow2 (-149) = pow2 (-126) := by decide +kernel
        grind
      · intro hs
        simp at hs
        left; exact (Unpacked.value_eq_zero_iff _).mpr hs
    · rename_i hE0
      constructor
      · intro hs; simp [hE0] at hs
      · intro _
        right
        rw [Unpacked.absQ_value]
        simp only
        have hE1 : 1 ≤ E := by omega
        have h1 : (8388608 : ℚ) ≤ ((8388608 + M : ℕ) : ℚ) := by exact_mod_cast Nat.le_add_right _ _
        have h2 : pow2 (1 - 127 - 23) ≤ pow2 ((E : ℤ) - 127 - ((23 : ℕ) : ℤ)) :=
          pow2_le_of_le (by omega)
        have h3a := Rat.mul_le_mul_of_nonneg_right h1 (Rat.le_of_lt (pow2_pos (1 - 127 - 23)))
        have h3b := Rat.mul_le_mul_of_nonneg_left h2
          (show (0 : ℚ) ≤ ((8388608 + M : ℕ) : ℚ) by exact_mod_cast Nat.zero_le _)
        have : (8388608 : ℚ) * pow2 (1 - 127 - 23) = pow2 (-126) := by decide +kernel
        grind

theorem value32_signedZero32 (w : F32) : value32 (signedZero32 w) = some 0 := by
  unfold value32 signedZero32
  rw [decode32_eq]
  have hs : w.toNat / 2147483648 % 2 < 2 := Nat.mod_lt _ (by decide)
  generalize w.toNat / 2147483648 % 2 = s at hs
  rcases (by omega : s = 0 ∨ s = 1) with rfl | rfl <;> decide +kernel

/-- With flush to zero, `fl{·}` is the RNE value if that is zero or normal, and zero otherwise. -/
theorem flValue_true {x v : ℚ} (h : flValue true x = some v) :
    (v = rneValue x ∧ (v = 0 ∨ pow2 (-126) ≤ absQ v)) ∨
      (v = 0 ∧ rneValue x ≠ 0 ∧ absQ (rneValue x) < pow2 (-126)) := by
  unfold flValue fl32 at h
  cases hr : rne32 x with
  | none => rw [hr] at h; simp at h
  | some w =>
    rw [hr] at h
    have hv := rne32_value hr
    simp only [Bool.true_and, Option.bind_some] at h
    split at h
    · rename_i hs
      rw [value32_signedZero32] at h
      obtain ⟨h1, h2⟩ := (value32_subnormal hv).1 hs
      right; exact ⟨(Option.some.inj h).symm, h1, h2⟩
    · rename_i hs
      rw [hv] at h
      have := (value32_subnormal hv).2 (by simpa using hs)
      left; rw [← Option.some.inj h]; exact ⟨rfl, this⟩

/-- Without flushing, `fl{·}` is the RNE value. -/
theorem flValue_false {x v : ℚ} (h : flValue false x = some v) : v = rneValue x := by
  unfold flValue at h
  rw [fl32_false] at h
  cases hr : rne32 x with
  | none => rw [hr] at h; simp at h
  | some w =>
    rw [hr] at h
    simp only [Option.bind_some] at h
    rw [rne32_value hr] at h
    exact (Option.some.inj h).symm

end MatrixCore
