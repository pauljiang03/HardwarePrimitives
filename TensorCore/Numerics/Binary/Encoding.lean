import TensorCore.Numerics.Binary.Defs
import TensorCore.Numerics.Binary.RoundOp
import TensorCore.Numerics.FormatProperties
import TensorCore.Numerics.Rounding

/-! Finite values and constructed encodings of an arbitrary well-formed IEEE-style `Format` (TC-EFT Definition II.1 for FP16, BF16, tf19, FP32, and FP64). -/

namespace TensorCore

theorem fp32_finiteValue (z : ℚ) : fp32.FiniteValue z ↔ FiniteValue32 z := Iff.rfl

theorem Format.emin_le_emax (f : Format) (hf : f.WellFormed) : f.emin ≤ f.emax := by
  obtain ⟨_, hE⟩ := hf
  have h4 : 4 ≤ 2 ^ f.exponentBits := by
    have := Nat.pow_le_pow_right (show 0 < 2 by decide) hE
    simpa using this
  unfold Format.emin Format.emax
  omega

/-- Every finite decoded value of a well-formed format has the arithmetic form. -/
theorem classifyNat_finiteValue (f : Format) (hf : f.WellFormed) (n : ℕ) (d : Decoded)
    (h : (classifyNat f n).finite = some d) : f.FiniteValue d.value := by
  have hemin := f.emin_le_emax hf
  have hmant := Nat.mod_lt n (Nat.two_pow_pos f.mantissaBits)
  have hexp := Nat.mod_lt (n / 2 ^ f.mantissaBits) (Nat.two_pow_pos f.exponentBits)
  have hpow : 2 ^ (f.mantissaBits + 1) = 2 ^ f.mantissaBits * 2 := Nat.pow_succ 2 _
  unfold classifyNat at h
  dsimp only at h
  unfold Format.FiniteValue
  generalize hP : 2 ^ f.mantissaBits = P at *
  generalize hP1 : 2 ^ (f.mantissaBits + 1) = P1 at *
  generalize hW : 2 ^ f.exponentBits = W at *
  split at h
  · split at h <;> simp [Classification.finite] at h
  · split at h
    · split at h
      · simp only [Classification.finite, Option.some.injEq] at h
        subst d
        refine ⟨0, f.emin, Int.le_refl _, hemin, by simp; omega, ?_⟩
        simp [Decoded.value]
      · simp only [Classification.finite, Option.some.injEq] at h
        subst d
        refine ⟨if (n / 2 ^ (f.mantissaBits + f.exponentBits) != 0) then
          -((n % P : ℕ) : ℤ) else ((n % P : ℕ) : ℤ),
          1 - f.bias, Int.le_refl _, hemin, ?_, ?_⟩
        · split
          · rw [Int.natAbs_neg, Int.natAbs_natCast]; omega
          · rw [Int.natAbs_natCast]; omega
        · simp [Decoded.value]
    · simp only [Classification.finite, Option.some.injEq] at h
      subst d
      rename_i htop hzero
      refine ⟨if (n / 2 ^ (f.mantissaBits + f.exponentBits) != 0) then
        -((P + n % P : ℕ) : ℤ) else ((P + n % P : ℕ) : ℤ),
        ((n / P % W : ℕ) : ℤ) - f.bias, ?_, ?_, ?_, ?_⟩
      · unfold Format.emin
        omega
      · unfold Format.emax
        rw [hW]
        omega
      · split
        · rw [Int.natAbs_neg, Int.natAbs_natCast]; omega
        · rw [Int.natAbs_natCast]; omega
      · simp [Decoded.value]

/-- The constructed encoding fits the word and has the stated fields. -/
theorem encodeBinary_toNat (f : Format) (hf : f.WellFormed) (negative : Bool) (e k : ℤ)
    (hk0 : 0 ≤ k) (hk1 : k < ((2 ^ (f.mantissaBits + 1) : ℕ) : ℤ)) (_he1 : f.emin ≤ e)
    (he2 : e ≤ f.emax) :
    (encodeBinary f negative e k).toNat =
      (if negative then 2 ^ (f.mantissaBits + f.exponentBits) else 0) +
        (if k < (2 ^ f.mantissaBits : ℕ) then k.toNat
         else (e + f.bias).toNat * 2 ^ f.mantissaBits + (k - (2 ^ f.mantissaBits : ℕ)).toNat) := by
  obtain ⟨hp, hE⟩ := hf
  unfold encodeBinary
  rw [BitVec.toNat_ofNat]
  apply Nat.mod_eq_of_lt
  have hwidth : 2 ^ f.width = 2 * 2 ^ (f.mantissaBits + f.exponentBits) := by
    unfold Format.width
    rw [show 1 + f.exponentBits + f.mantissaBits = (f.mantissaBits + f.exponentBits) + 1 by omega,
      Nat.pow_succ]
    omega
  have hPW : 2 ^ (f.mantissaBits + f.exponentBits) = 2 ^ f.mantissaBits * 2 ^ f.exponentBits :=
    Nat.pow_add 2 _ _
  have hpow : 2 ^ (f.mantissaBits + 1) = 2 ^ f.mantissaBits * 2 := Nat.pow_succ 2 _
  have hP := Nat.two_pow_pos f.mantissaBits
  have hW : 4 ≤ 2 ^ f.exponentBits := by
    have := Nat.pow_le_pow_right (show 0 < 2 by decide) hE
    simpa using this
  have hemax : e + f.bias ≤ ((2 ^ f.exponentBits - 2 : ℕ) : ℤ) := by
    unfold Format.emax at he2
    omega
  rw [hwidth, hPW]
  generalize hPv : 2 ^ f.mantissaBits = P at *
  generalize hWv : 2 ^ f.exponentBits = W at *
  generalize hP1 : 2 ^ (f.mantissaBits + 1) = P1 at *
  have hpay : (if k < (P : ℕ) then k.toNat
      else (e + f.bias).toNat * P + (k - (P : ℕ)).toNat) < P * W := by
    split
    · rename_i hk
      have h1 : P ≤ P * W := Nat.le_mul_of_pos_right _ (by omega)
      omega
    · rename_i hk
      have hle : (e + f.bias).toNat ≤ W - 2 := by omega
      have hmul : (e + f.bias).toNat * P ≤ (W - 2) * P := Nat.mul_le_mul_right _ hle
      have hr : (k - (P : ℕ)).toNat < P := by
        omega
      have hsplit : (W - 2) * P + 2 * P = W * P := by
        rw [← Nat.add_mul, Nat.sub_add_cancel (by omega)]
      rw [Nat.mul_comm P W]
      omega
  generalize hpayv : (if k < (P : ℕ) then k.toNat
      else (e + f.bias).toNat * P + (k - (P : ℕ)).toNat) = pay at *
  cases negative <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> omega

theorem encodeBinary_parity (f : Format) (hf : f.WellFormed) (negative : Bool) (e k : ℤ)
    (hk0 : 0 ≤ k) (hk1 : k < ((2 ^ (f.mantissaBits + 1) : ℕ) : ℤ)) (he1 : f.emin ≤ e)
    (he2 : e ≤ f.emax) :
    (encodeBinary f negative e k).toNat % 2 = k.toNat % 2 := by
  rw [encodeBinary_toNat f hf negative e k hk0 hk1 he1 he2]
  obtain ⟨hp, _⟩ := hf
  have hPeven : 2 ^ f.mantissaBits % 2 = 0 := by
    obtain ⟨m, hm⟩ : ∃ m, f.mantissaBits = m + 1 := ⟨f.mantissaBits - 1, by omega⟩
    rw [hm, Nat.pow_succ]
    simp
  have hPW : 2 ^ (f.mantissaBits + f.exponentBits) % 2 = 0 := by
    rw [Nat.pow_add, Nat.mul_mod, hPeven]
    simp
  have hmul : (e + f.bias).toNat * 2 ^ f.mantissaBits % 2 = 0 := by
    rw [Nat.mul_mod, hPeven]
    simp
  generalize hPv : 2 ^ f.mantissaBits = P at *
  generalize hPWv : 2 ^ (f.mantissaBits + f.exponentBits) = PW at *
  generalize hP1 : 2 ^ (f.mantissaBits + 1) = P1 at *
  generalize hmv : (e + f.bias).toNat * P = M at *
  cases negative <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> split <;> omega

/-- The payload of a constructed encoding is below `2^(p+E)`. -/
theorem encodeBinary_payload_lt (f : Format) (hf : f.WellFormed) (e k : ℤ)
    (_hk0 : 0 ≤ k) (hk1 : k < ((2 ^ (f.mantissaBits + 1) : ℕ) : ℤ)) (_he1 : f.emin ≤ e)
    (he2 : e ≤ f.emax) :
    (if k < (2 ^ f.mantissaBits : ℕ) then k.toNat
      else (e + f.bias).toNat * 2 ^ f.mantissaBits + (k - (2 ^ f.mantissaBits : ℕ)).toNat) <
      2 ^ f.mantissaBits * 2 ^ f.exponentBits := by
  obtain ⟨hp, hE⟩ := hf
  have hpow : 2 ^ (f.mantissaBits + 1) = 2 ^ f.mantissaBits * 2 := Nat.pow_succ 2 _
  have hP := Nat.two_pow_pos f.mantissaBits
  have hW : 4 ≤ 2 ^ f.exponentBits := by
    have := Nat.pow_le_pow_right (show 0 < 2 by decide) hE
    simpa using this
  have hemax : e + f.bias ≤ ((2 ^ f.exponentBits - 2 : ℕ) : ℤ) := by
    unfold Format.emax at he2
    omega
  generalize hPv : 2 ^ f.mantissaBits = P at *
  generalize hWv : 2 ^ f.exponentBits = W at *
  generalize hP1 : 2 ^ (f.mantissaBits + 1) = P1 at *
  split
  · rename_i hk
    have h1 : P ≤ P * W := Nat.le_mul_of_pos_right _ (by omega)
    omega
  · rename_i hk
    have hle : (e + f.bias).toNat ≤ W - 2 := by omega
    have hmul : (e + f.bias).toNat * P ≤ (W - 2) * P := Nat.mul_le_mul_right _ hle
    have hr : (k - (P : ℕ)).toNat < P := by omega
    have hsplit : (W - 2) * P + 2 * P = W * P := by
      rw [← Nat.add_mul, Nat.sub_add_cancel (by omega)]
    rw [Nat.mul_comm P W]
    omega

/-- The constructed encoding decodes to the value it was built from. -/
theorem encodeBinary_value (f : Format) (hf : f.WellFormed) (negative : Bool) (e k : ℤ)
    (he1 : f.emin ≤ e) (he2 : e ≤ f.emax) (hk0 : 0 ≤ k)
    (hk1 : k < ((2 ^ (f.mantissaBits + 1) : ℕ) : ℤ))
    (hsub : ((2 ^ f.mantissaBits : ℕ) : ℤ) ≤ k ∨ e = f.emin) :
    binaryValue f (encodeBinary f negative e k) =
      some ((if negative then -(k : ℚ) else (k : ℚ)) * pow2 (e - f.mantissaBits)) := by
  have hpaylt := encodeBinary_payload_lt f hf e k hk0 hk1 he1 he2
  obtain ⟨hp, hE⟩ := hf
  have hPW : 2 ^ (f.mantissaBits + f.exponentBits) = 2 ^ f.mantissaBits * 2 ^ f.exponentBits :=
    Nat.pow_add 2 _ _
  have hpow : 2 ^ (f.mantissaBits + 1) = 2 ^ f.mantissaBits * 2 := Nat.pow_succ 2 _
  have hP := Nat.two_pow_pos f.mantissaBits
  have hW : 4 ≤ 2 ^ f.exponentBits := by
    have := Nat.pow_le_pow_right (show 0 < 2 by decide) hE
    simpa using this
  have hemax : e + f.bias ≤ ((2 ^ f.exponentBits - 2 : ℕ) : ℤ) := by
    unfold Format.emax at he2
    omega
  have hemin : 1 - f.bias ≤ e := he1
  unfold binaryValue classify
  rw [encodeBinary_toNat f ⟨hp, hE⟩ negative e k hk0 hk1 he1 he2]
  unfold classifyNat
  dsimp only
  rw [hPW]
  generalize hPv : 2 ^ f.mantissaBits = P at *
  generalize hWv : 2 ^ f.exponentBits = W at *
  generalize hP1 : 2 ^ (f.mantissaBits + 1) = P1 at *
  have hPWpos : 0 < P * W := Nat.mul_pos hP (by omega)
  -- The three fields of the word, for either sign.
  have hsgn : ∀ pay, pay < P * W →
      ((if negative then P * W else 0) + pay) % P = pay % P ∧
      ((if negative then P * W else 0) + pay) / P % W = pay / P % W ∧
      (((if negative then P * W else 0) + pay) / (P * W) != 0) = negative := by
    intro pay hlt
    cases negative
    · show (0 + pay) % P = pay % P ∧ (0 + pay) / P % W = pay / P % W ∧
        ((0 + pay) / (P * W) != 0) = false
      rw [Nat.zero_add, Nat.div_eq_of_lt hlt]
      exact ⟨rfl, rfl, rfl⟩
    · show (P * W + pay) % P = pay % P ∧ (P * W + pay) / P % W = pay / P % W ∧
        ((P * W + pay) / (P * W) != 0) = true
      have h1 : (P * W + pay) / (P * W) = 1 := by
        rw [show P * W + pay = P * W * 1 + pay by omega, Nat.mul_add_div hPWpos,
          Nat.div_eq_of_lt hlt]
      rw [Nat.mul_add_mod, Nat.mul_add_div hP, Nat.add_mod_left, h1]
      exact ⟨rfl, rfl, rfl⟩
  by_cases hk : k < (P : ℤ)
  · rw [if_pos hk] at hpaylt ⊢
    obtain ⟨hmant, hexpf, hneg⟩ := hsgn k.toNat hpaylt
    have hkP : k.toNat < P := by omega
    rw [hmant, hexpf, hneg, Nat.mod_eq_of_lt hkP, Nat.div_eq_of_lt hkP, Nat.zero_mod]
    have he : e = f.emin := by
      rcases hsub with h | h
      · exfalso; omega
      · exact h
    subst he
    simp only [show (0 : ℕ) ≠ W - 1 by omega, ↓reduceIte]
    by_cases hz : k.toNat = 0
    · have hk0' : k = 0 := by omega
      subst hk0'
      simp [hz, Classification.finite, Decoded.value] <;> cases negative <;> simp
    · have hk' : ((k.toNat : ℕ) : ℤ) = k := Int.toNat_of_nonneg hk0
      simp only [hz, ↓reduceIte, Classification.finite, hk']
      unfold Format.emin
      cases negative <;> simp [Decoded.value]
  · rw [if_neg hk] at hpaylt ⊢
    have hP' : (P : ℤ) ≤ k := by omega
    obtain ⟨hmant, hexpf, hneg⟩ := hsgn _ hpaylt
    have hr : (k - (P : ℕ)).toNat < P := by omega
    have hfield : (e + f.bias).toNat < W := by omega
    have hfield1 : (e + f.bias).toNat ≠ 0 := by omega
    have hfieldtop : (e + f.bias).toNat ≠ W - 1 := by omega
    rw [hmant, hexpf, hneg, Nat.mul_comm _ P, Nat.mul_add_mod, Nat.mul_add_div hP,
      Nat.div_eq_of_lt hr, Nat.add_zero, Nat.mod_eq_of_lt hr, Nat.mod_eq_of_lt hfield]
    have hsig : ((P + (k - (P : ℕ)).toNat : ℕ) : ℤ) = k := by omega
    have hexp : (((e + f.bias).toNat : ℕ) : ℤ) - f.bias = e := by omega
    simp only [hfieldtop, hfield1, ↓reduceIte, Classification.finite, hsig, hexp]
    cases negative <;> simp [Decoded.value]

def binarySign (f : Format) (bits : BitVec f.width) : Bool :=
  bits.toNat / 2 ^ (f.mantissaBits + f.exponentBits) != 0

def binaryExponentField (f : Format) (bits : BitVec f.width) : ℕ :=
  bits.toNat / 2 ^ f.mantissaBits % 2 ^ f.exponentBits

end TensorCore
