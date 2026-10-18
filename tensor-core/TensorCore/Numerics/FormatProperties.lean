import TensorCore.Numerics.Format

/-! Bounds on decoded values. -/

namespace TensorCore

theorem decoded_signed_bounded (negative : Bool) (m : ℕ) (e : ℤ) (f : ℕ)
    (hm : m < 2 ^ (f + 1)) :
    (Decoded.mk (if negative then -(m : ℤ) else m) e f).Bounded := by
  have hq := pow2_pos (e - f)
  have hm' := Rat.natCast_lt_natCast.mpr hm
  have hs : ((2 ^ (f + 1) : ℕ) : ℚ) * pow2 (e - f) = 2 * pow2 e := by
    rw [← pow2_natCast, ← pow2_add]
    have he : ((f + 1 : ℕ) : ℤ) + (e - f) = e + 1 := by omega
    rw [he, pow2_succ, Rat.mul_comm]
  have hb := Rat.mul_lt_mul_of_pos_right hm' hq
  rw [hs] at hb
  unfold Decoded.Bounded Decoded.value
  cases negative <;> simp only [Bool.false_eq_true, ↓reduceIte, Rat.intCast_neg,
    Rat.intCast_natCast, Rat.neg_mul]
  · rw [absQ_mul_pos _ _ hq, absQ_of_nonneg Rat.natCast_nonneg]
    exact hb
  · rw [absQ_neg, absQ_mul_pos _ _ hq, absQ_of_nonneg Rat.natCast_nonneg]
    exact hb

theorem decoded_zero_bounded : (Decoded.mk 0 0 0).Bounded := by
  simp [Decoded.Bounded, Decoded.value, absQ, pow2]
  decide

theorem classifyNat_bounded (f : Format) (n : ℕ) (d : Decoded)
    (h : (classifyNat f n).finite = some d) : d.Bounded := by
  have hmant := Nat.mod_lt n (Nat.two_pow_pos f.mantissaBits)
  have hpow : 2 ^ (f.mantissaBits + 1) = 2 ^ f.mantissaBits * 2 := by rw [Nat.pow_succ]
  unfold classifyNat at h
  dsimp only at h
  split at h
  · split at h <;> simp [Classification.finite] at h
  · split at h
    · split at h
      · simp only [Classification.finite, Option.some.injEq] at h
        subst d; exact decoded_zero_bounded
      · simp only [Classification.finite, Option.some.injEq] at h
        subst d; apply decoded_signed_bounded; omega
    · simp only [Classification.finite, Option.some.injEq] at h
      subst d; apply decoded_signed_bounded; omega

theorem valueFormat_decode_bounded (f : ValueFormat) (n : ℕ) (d : Decoded)
    (h : (f.classifyNat n).finite = some d) : d.Bounded := by
  cases hs : f.special with
  | ieee => exact classifyNat_bounded f.layout n d (by simpa [ValueFormat.classifyNat, hs] using h)
  | finiteTopNaN =>
    simp only [ValueFormat.classifyNat, hs] at h
    split at h
    · split at h
      · simp [Classification.finite] at h
      · simp only [Classification.finite, Option.some.injEq] at h
        subst d
        apply decoded_signed_bounded
        have := Nat.mod_lt n (Nat.two_pow_pos f.layout.mantissaBits)
        rw [Nat.pow_succ]
        omega
    · exact classifyNat_bounded f.layout n d h

theorem operand_decode_bounded {s : OperandEncoding} {bits : s.Word} {d : Decoded}
    (h : s.decode bits = some d) : d.Bounded :=
  valueFormat_decode_bounded _ _ _ (padded_decode_value h)

theorem classifyNat_scale_lower (f : Format) (n : ℕ) (d : Decoded)
    (h : (classifyNat f n).finite = some d) (hnz : d.significand ≠ 0) :
    1 - f.bias ≤ d.exponent := by
  unfold classifyNat at h
  dsimp only at h
  split at h
  · split at h <;> simp [Classification.finite] at h
  · split at h
    · split at h
      · simp only [Classification.finite, Option.some.injEq] at h
        subst d
        simp at hnz
      · simp only [Classification.finite, Option.some.injEq] at h
        subst d
        exact Int.le_refl _
    · simp only [Classification.finite, Option.some.injEq] at h
      subst d
      change 1 - f.bias ≤ ((n / 2 ^ f.mantissaBits % 2 ^ f.exponentBits : ℕ) : ℤ) - f.bias
      omega

theorem classifyNat_metadata (f : Format) (he : 2 ≤ f.exponentBits) (n : ℕ) (d : Decoded)
    (h : (classifyNat f n).finite = some d) (hnz : d.significand ≠ 0) :
    d.mantissaBits = f.mantissaBits ∧ 1 - f.bias ≤ d.exponent ∧
      d.exponent ≤ ((2 ^ f.exponentBits - 2 : ℕ) : ℤ) - f.bias := by
  have hp : (2 : ℕ) ^ 2 ≤ 2 ^ f.exponentBits := Nat.pow_le_pow_right (by decide) he
  have hm := Nat.mod_lt (n / 2 ^ f.mantissaBits) (Nat.two_pow_pos f.exponentBits)
  unfold classifyNat at h
  dsimp only at h
  split at h
  · split at h <;> simp [Classification.finite] at h
  · split at h
    · split at h
      · simp only [Classification.finite, Option.some.injEq] at h
        subst d
        simp at hnz
      · simp only [Classification.finite, Option.some.injEq] at h
        subst d
        refine ⟨rfl, Int.le_refl _, ?_⟩
        change 1 - f.bias ≤ ((2 ^ f.exponentBits - 2 : ℕ) : ℤ) - f.bias
        omega
    · simp only [Classification.finite, Option.some.injEq] at h
      subst d
      refine ⟨rfl, ?_, ?_⟩
      · change 1 - f.bias ≤ ((n / 2 ^ f.mantissaBits % 2 ^ f.exponentBits : ℕ) : ℤ) - f.bias
        omega
      · change ((n / 2 ^ f.mantissaBits % 2 ^ f.exponentBits : ℕ) : ℤ) - f.bias ≤
          ((2 ^ f.exponentBits - 2 : ℕ) : ℤ) - f.bias
        omega

end TensorCore
