import TensorCore.Numerics.Binary.RoundTrip

/-! Numerical finite bijection: a representable rational together with a sign bit. -/

namespace TensorCore

theorem BinaryRep.sign_of_nonzero {f : Format} (r : BinaryRep f) (hn : r.value ≠ 0) :
    r.negative = decide (r.value < 0) := by
  have hk : r.significand ≠ 0 := by intro h; exact hn (r.value_eq_zero_iff.mpr h)
  have hp := Rat.mul_pos (Rat.natCast_pos.mpr (show 0 < r.significand by omega))
    (pow2_pos (r.exponent - f.mantissaBits))
  symm
  unfold BinaryRep.value
  cases r.negative <;> simp only [Bool.false_eq_true, ↓reduceIte,
    decide_eq_true_eq, decide_eq_false_iff_not]
  · exact Rat.not_lt.mpr (Rat.le_of_lt hp)
  · rw [Rat.neg_mul]; grind

theorem binaryValue_sign (f : Format) (hf : f.WellFormed) (b : FiniteBinaryWord f)
    (v : ℚ) (hv : binaryValue f b.val = some v) (hn : v ≠ 0) :
    binarySign f b.val = decide (v < 0) := by
  have he : (decodeBinaryRep f hf b).value = v :=
    Option.some.inj ((decodeBinaryRep_value f hf b).symm.trans hv)
  have hs := (decodeBinaryRep f hf b).sign_of_nonzero (by rwa [he])
  rwa [he] at hs

/-- Equal rational values and equal sign bits identify finite words, including zero. -/
theorem binaryValue_sign_injective (f : Format) (hf : f.WellFormed)
    (b₁ b₂ : FiniteBinaryWord f) (v : ℚ) (h₁ : binaryValue f b₁.val = some v)
    (h₂ : binaryValue f b₂.val = some v) (hs : binarySign f b₁.val = binarySign f b₂.val) :
    b₁ = b₂ := by
  by_cases hn : v = 0
  · have hv₁ : (decodeBinaryRep f hf b₁).value = 0 :=
      (Option.some.inj ((decodeBinaryRep_value f hf b₁).symm.trans h₁)).trans hn
    have hv₂ : (decodeBinaryRep f hf b₂).value = 0 :=
      (Option.some.inj ((decodeBinaryRep_value f hf b₂).symm.trans h₂)).trans hn
    have hk₁ := (decodeBinaryRep f hf b₁).value_eq_zero_iff.mp hv₁
    have hk₂ := (decodeBinaryRep f hf b₂).value_eq_zero_iff.mp hv₂
    have heq : decodeBinaryRep f hf b₁ = decodeBinaryRep f hf b₂ := by
      have he₁ := (decodeBinaryRep f hf b₁).normalized
      have he₂ := (decodeBinaryRep f hf b₂).normalized
      have hp := Nat.two_pow_pos f.mantissaBits
      have he : (decodeBinaryRep f hf b₁).exponent = (decodeBinaryRep f hf b₂).exponent := by omega
      have hs' : (decodeBinaryRep f hf b₁).negative = (decodeBinaryRep f hf b₂).negative := hs
      exact BinaryRep.ext hs' he (hk₁.trans hk₂.symm)
    rw [← encode_decodeBinaryRep f hf b₁, heq, encode_decodeBinaryRep]
  · apply Subtype.ext
    exact binaryValue_injective_nonzero f hf b₁.val b₂.val v h₁ h₂ hn

def decodeSignedBinary (f : Format) (hf : f.WellFormed) (b : FiniteBinaryWord f) :
    SignedFiniteValue f :=
  ⟨(decodeBinaryRep f hf b).value, binarySign f b.val,
    (decodeBinaryRep f hf b).finiteValue, (decodeBinaryRep f hf b).sign_of_nonzero⟩

/-- Exact encoding of a representable finite value using the binary converter. -/
def exactFiniteWord (f : Format) (hf : f.WellFormed) (v : ℚ) (hv : f.FiniteValue v) :
    FiniteBinaryWord f :=
  match h : roundBinary f .nearestEven v with
  | none => by
    exfalso
    obtain ⟨b, hb, _⟩ := roundBinary_exact_of_finite f hf hv
    simp [h] at hb
  | some bits => ⟨bits, by
    obtain ⟨b, hb, hbv⟩ := roundBinary_exact_of_finite f hf hv
    rw [h] at hb
    cases Option.some.inj hb
    unfold binaryValue at hbv
    cases hd : (classify f bits).finite with
    | none => simp [hd] at hbv
    | some d => exact ⟨d, rfl⟩⟩

theorem exactFiniteWord_value (f : Format) (hf : f.WellFormed) (v : ℚ) (hv : f.FiniteValue v) :
    binaryValue f (exactFiniteWord f hf v hv).val = some v := by
  obtain ⟨b, hb, hbv⟩ := roundBinary_exact_of_finite f hf hv
  unfold exactFiniteWord
  split
  · rename_i h
    rw [h] at hb
    contradiction
  · rename_i bits h
    rw [h] at hb
    cases Option.some.inj hb
    exact hbv

def BinaryRep.zero (f : Format) (hf : f.WellFormed) (negative : Bool) : BinaryRep f :=
  ⟨negative, f.emin, 0, Int.le_refl _, f.emin_le_emax hf, Nat.two_pow_pos _, Or.inr rfl⟩

/-- Encoding a signed value preserves its zero sign, separately from arithmetic rounding. -/
def encodeSignedBinary (f : Format) (hf : f.WellFormed) (v : SignedFiniteValue f) :
    FiniteBinaryWord f :=
  if v.value = 0 then encodeBinaryRep f hf (BinaryRep.zero f hf v.negative)
  else exactFiniteWord f hf v.value v.finite

theorem encodeSignedBinary_value (f : Format) (hf : f.WellFormed) (v : SignedFiniteValue f) :
    binaryValue f (encodeSignedBinary f hf v).val = some v.value := by
  unfold encodeSignedBinary
  split
  · rename_i hz
    have h := (BinaryRep.zero f hf v.negative).encode_value hf
    have hzero := (BinaryRep.zero f hf v.negative).value_eq_zero_iff.mpr rfl
    change binaryValue f (BinaryRep.zero f hf v.negative).encode = some v.value
    rw [h, hzero, hz]
  · exact exactFiniteWord_value f hf v.value v.finite

theorem encodeSignedBinary_sign (f : Format) (hf : f.WellFormed) (v : SignedFiniteValue f) :
    binarySign f (encodeSignedBinary f hf v).val = v.negative := by
  by_cases hz : v.value = 0
  · simp only [encodeSignedBinary, hz, ↓reduceIte, encodeBinaryRep]
    exact (encodeBinary_fields f hf (BinaryRep.zero f hf v.negative)).1
  · rw [binaryValue_sign f hf _ v.value (encodeSignedBinary_value f hf v) hz]
    exact (v.sign_nonzero hz).symm

theorem decode_encodeSignedBinary (f : Format) (hf : f.WellFormed) (v : SignedFiniteValue f) :
    decodeSignedBinary f hf (encodeSignedBinary f hf v) = v := by
  have hv := Option.some.inj ((decodeBinaryRep_value f hf (encodeSignedBinary f hf v)).symm.trans
    (encodeSignedBinary_value f hf v))
  have hs := encodeSignedBinary_sign f hf v
  cases v
  simp only [decodeSignedBinary]
  congr

theorem encode_decodeSignedBinary (f : Format) (hf : f.WellFormed) (b : FiniteBinaryWord f) :
    encodeSignedBinary f hf (decodeSignedBinary f hf b) = b := by
  apply binaryValue_sign_injective f hf _ _ (decodeSignedBinary f hf b).value
  · exact encodeSignedBinary_value f hf _
  · exact decodeBinaryRep_value f hf b
  · exact encodeSignedBinary_sign f hf _

/-- Finite IEEE words correspond bijectively to representable rationals with two zeros. -/
def signedFiniteBinaryBijection (f : Format) (hf : f.WellFormed) :
    BinaryBijection (SignedFiniteValue f) (FiniteBinaryWord f) :=
  ⟨encodeSignedBinary f hf, decodeSignedBinary f hf,
    decode_encodeSignedBinary f hf, encode_decodeSignedBinary f hf⟩

end TensorCore
