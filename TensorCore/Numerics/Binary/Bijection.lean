import TensorCore.Numerics.Binary.ScalarSum
import TensorCore.Numerics.RoundingStage

/-! Finite IEEE encodings and canonical signed representations. -/

namespace TensorCore

def BinaryRep.encode {f : Format} (r : BinaryRep f) : BitVec f.width :=
  encodeBinary f r.negative r.exponent r.significand

theorem BinaryRep.encode_value {f : Format} (hf : f.WellFormed) (r : BinaryRep f) :
    binaryValue f r.encode = some r.value := by
  exact encodeBinary_value f hf r.negative r.exponent r.significand
    r.exponent_min r.exponent_max (by omega) (by have := r.significand_lt; omega)
    (by have := r.normalized; omega)

theorem finiteBinaryWord_exponent {f : Format} (b : FiniteBinaryWord f) :
    binaryExponentField f b.val ≠ 2 ^ f.exponentBits - 1 := by
  obtain ⟨d, hd⟩ := b.property
  intro he
  unfold classify classifyNat at hd
  change b.val.toNat / 2 ^ f.mantissaBits % 2 ^ f.exponentBits = _ at he
  simp only [he, ↓reduceIte] at hd
  split at hd <;> simp [Classification.finite] at hd

def decodeBinaryRep (f : Format) (hf : f.WellFormed) (b : FiniteBinaryWord f) : BinaryRep f :=
  { negative := binarySign f b.val
    exponent := if binaryExponentField f b.val = 0 then f.emin
      else (binaryExponentField f b.val : ℤ) - f.bias
    significand := if binaryExponentField f b.val = 0 then b.val.toNat % 2 ^ f.mantissaBits
      else 2 ^ f.mantissaBits + b.val.toNat % 2 ^ f.mantissaBits
    exponent_min := by split <;> unfold Format.emin <;> omega
    exponent_max := by
      have ht := finiteBinaryWord_exponent b
      have hb := Nat.mod_lt (b.val.toNat / 2 ^ f.mantissaBits) (Nat.two_pow_pos f.exponentBits)
      change binaryExponentField f b.val < 2 ^ f.exponentBits at hb
      split
      · exact f.emin_le_emax hf
      · unfold Format.emax; omega
    significand_lt := by
      have hm := Nat.mod_lt b.val.toNat (Nat.two_pow_pos f.mantissaBits)
      rw [Nat.pow_succ]
      split <;> omega
    normalized := by split <;> simp_all }

def encodeBinaryRep (f : Format) (hf : f.WellFormed) (r : BinaryRep f) : FiniteBinaryWord f :=
  ⟨r.encode, by
    have h := r.encode_value hf
    unfold binaryValue at h
    cases hd : (classify f r.encode).finite with
    | none => simp [hd] at h
    | some d => exact ⟨d, rfl⟩⟩

/-- Recover the sign, exponent, and mantissa fields of the generic binary encoder. -/
theorem encodeBinary_fields (f : Format) (hf : f.WellFormed) (r : BinaryRep f) :
    binarySign f r.encode = r.negative ∧
    binaryExponentField f r.encode =
      (if r.significand < 2 ^ f.mantissaBits then 0 else (r.exponent + f.bias).toNat) ∧
    r.encode.toNat % 2 ^ f.mantissaBits =
      (if r.significand < 2 ^ f.mantissaBits then r.significand
       else r.significand - 2 ^ f.mantissaBits) := by
  have hpay := encodeBinary_payload_lt f hf r.exponent r.significand
    (by omega) (by have := r.significand_lt; omega) r.exponent_min r.exponent_max
  have hnat := encodeBinary_toNat f hf r.negative r.exponent r.significand
    (by omega) (by have := r.significand_lt; omega) r.exponent_min r.exponent_max
  have hP := Nat.two_pow_pos f.mantissaBits
  have hW := Nat.two_pow_pos f.exponentBits
  have hk := r.significand_lt
  rw [Nat.pow_succ] at hk
  have hE : (r.exponent + f.bias).toNat < 2 ^ f.exponentBits := by
    have := r.exponent_max
    unfold Format.emax at this
    omega
  unfold binarySign binaryExponentField
  rw [show r.encode.toNat = _ from hnat, Nat.pow_add]
  generalize hPv : 2 ^ f.mantissaBits = P at *
  generalize hWv : 2 ^ f.exponentBits = W at *
  have hsgn : ∀ pay, pay < P * W →
      ((if r.negative then P * W else 0) + pay) % P = pay % P ∧
      ((if r.negative then P * W else 0) + pay) / P % W = pay / P % W ∧
      (((if r.negative then P * W else 0) + pay) / (P * W) != 0) = r.negative := by
    intro pay hlt
    have hPW := Nat.mul_pos hP hW
    cases r.negative
    · simp [Nat.div_eq_of_lt hlt]
    · have h1 : (P * W + pay) / (P * W) = 1 := by
        rw [show P * W + pay = P * W * 1 + pay by omega,
          Nat.mul_add_div hPW, Nat.div_eq_of_lt hlt]
      simp only [↓reduceIte, Nat.mul_add_mod, Nat.mul_add_div hP, Nat.add_mod_left, h1]
      simp
  by_cases hsub : r.significand < P
  · rw [if_pos (show (r.significand : ℤ) < (P : ℕ) by omega)] at hpay ⊢
    simp only [Int.toNat_natCast]
    obtain ⟨hmant, hexp, hsign⟩ := hsgn r.significand hpay
    rw [hsign, hexp, hmant, if_pos hsub, Nat.mod_eq_of_lt hsub, Nat.div_eq_of_lt hsub]
    simp [hsub]
  · rw [if_neg (show ¬(r.significand : ℤ) < (P : ℕ) by omega)] at hpay ⊢
    have hcast : ((r.significand : ℤ) - (P : ℕ)).toNat = r.significand - P := by omega
    rw [hcast] at hpay ⊢
    obtain ⟨hmant, hexp, hsign⟩ := hsgn _ hpay
    rw [hsign, hexp, hmant, if_neg hsub, Nat.mul_comm _ P,
      Nat.mul_add_mod, Nat.mul_add_div hP,
      Nat.mod_eq_of_lt (show r.significand - P < P by omega),
      Nat.div_eq_of_lt (show r.significand - P < P by omega), Nat.add_zero,
      Nat.mod_eq_of_lt hE]
    simp [hsub]

theorem decode_encodeBinaryRep (f : Format) (hf : f.WellFormed) (r : BinaryRep f) :
    decodeBinaryRep f hf (encodeBinaryRep f hf r) = r := by
  obtain ⟨hs, he, hk⟩ := encodeBinary_fields f hf r
  have hemin := r.exponent_min
  have hn := r.normalized
  have hP := Nat.two_pow_pos f.mantissaBits
  have hE : (r.exponent + f.bias).toNat ≠ 0 := by unfold Format.emin at hemin; omega
  cases r with
  | mk s e k h1 h2 h3 h4 =>
    simp only [decodeBinaryRep, encodeBinaryRep, hs, he, hk]
    congr 1 <;> split <;> simp_all <;> omega

/-- Reassembling sign, exponent and mantissa reproduces the original finite word. -/
theorem encode_decodeBinaryRep (f : Format) (hf : f.WellFormed) (b : FiniteBinaryWord f) :
    encodeBinaryRep f hf (decodeBinaryRep f hf b) = b := by
  apply Subtype.ext
  change (decodeBinaryRep f hf b).encode = b.val
  apply BitVec.eq_of_toNat_eq
  let hr := decodeBinaryRep f hf b
  rw [show (decodeBinaryRep f hf b).encode.toNat = _ from
    encodeBinary_toNat f hf hr.negative hr.exponent hr.significand
      (by omega) (by have := hr.significand_lt; omega) hr.exponent_min hr.exponent_max]
  simp only [hr, decodeBinaryRep, binarySign, binaryExponentField, Nat.pow_add]
  dsimp +instances only [hr, decodeBinaryRep, binarySign, binaryExponentField]
  have hn := b.val.isLt
  have hwidth : 2 ^ f.width = 2 ^ (f.mantissaBits + f.exponentBits) * 2 := by
    rw [show f.width = f.mantissaBits + f.exponentBits + 1 by unfold Format.width; omega,
      Nat.pow_succ]
  rw [hwidth, Nat.pow_add] at hn
  have hP := Nat.two_pow_pos f.mantissaBits
  have hW := Nat.two_pow_pos f.exponentBits
  generalize hPv : 2 ^ f.mantissaBits = P at *
  generalize hWv : 2 ^ f.exponentBits = W at *
  generalize hnv : b.val.toNat = n at *
  have hPW := Nat.mul_pos hP hW
  have hq : n / (P * W) < 2 := (Nat.div_lt_iff_lt_mul hPW).mpr (by omega)
  have hdecomp : n = (n / (P * W)) * (P * W) + (n / P % W) * P + n % P := by
    have h1 := Nat.div_add_mod n P
    have h2 := Nat.div_add_mod (n / P) W
    have h3 := congrArg (fun z => z * P) h2
    rw [Nat.div_div_eq_div_mul] at h3
    grind
  have hmant := Nat.mod_lt n hP
  have hsign : (if (n / (P * W) != 0) then P * W else 0) = (n / (P * W) : ℕ) * (P * W) := by
    by_cases hz : n / (P * W) = 0
    · simp [hz]
    · have ho : n / (P * W) = 1 := by
        generalize n / (P * W) = q at *
        omega
      simp [ho]
  rw [hsign]
  by_cases he : n / P % W = 0
  · simp only [he, ↓reduceIte]
    rw [if_pos (show ((n % P : ℕ) : ℤ) < (P : ℕ) by omega)]
    simp only [Int.toNat_natCast]
    simp only [he, Nat.zero_mul, Nat.add_zero] at hdecomp
    omega
  · simp only [he, ↓reduceIte]
    rw [if_neg (show ¬ ((P + n % P : ℕ) : ℤ) < (P : ℕ) by omega)]
    have hE : (((n / P % W : ℕ) : ℤ) - f.bias + f.bias).toNat = n / P % W := by omega
    have hK : (((P + n % P : ℕ) : ℤ) - (P : ℕ)).toNat = n % P := by omega
    rw [hE, hK]
    omega

def finiteBinaryBijection (f : Format) (hf : f.WellFormed) :
    BinaryBijection (BinaryRep f) (FiniteBinaryWord f) :=
  ⟨encodeBinaryRep f hf, decodeBinaryRep f hf,
    decode_encodeBinaryRep f hf, encode_decodeBinaryRep f hf⟩

theorem decodeBinaryRep_value (f : Format) (hf : f.WellFormed) (b : FiniteBinaryWord f) :
    binaryValue f b.val = some (decodeBinaryRep f hf b).value := by
  have h := (decodeBinaryRep f hf b).encode_value hf
  have hb := congrArg Subtype.val (encode_decodeBinaryRep f hf b)
  change (decodeBinaryRep f hf b).encode = b.val at hb
  rwa [hb] at h

end TensorCore
