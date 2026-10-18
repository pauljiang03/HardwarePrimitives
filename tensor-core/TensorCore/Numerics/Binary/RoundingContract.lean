import TensorCore.Numerics.Binary.SignedBijection
import TensorCore.Numerics.Binary.DirectedRounding

/-! Rounding contracts for four modes, finite-domain totality, and explicit zero/sign conventions. -/

namespace TensorCore

def BinaryRoundSpec (f : Format) (mode : BinaryRoundingMode) (x : ℚ)
    (bits : BitVec f.width) : Prop :=
  match mode with
  | .nearestEven => NearestEven f x bits
  | .truncate => Truncated f x bits
  | .towardNegative => TowardNegative f x bits
  | .towardPositive => TowardPositive f x bits

/-- Rounding to a well-formed binary format is correct in every mode, within the finite range. -/
theorem roundBinary_correct (f : Format) (hf : f.WellFormed) (mode : BinaryRoundingMode)
    (x : ℚ) (hr : absQ x ≤ f.maxFinite) :
    ∃ bits, roundBinary f mode x = some bits ∧ BinaryRoundSpec f mode x bits := by
  cases mode
  · exact roundBinary_truncate_correct f hf x hr
  · exact roundBinary_nearestEven_correct f hf x hr
  · exact roundBinary_towardNegative_correct f hf x hr
  · exact roundBinary_towardPositive_correct f hf x hr

theorem BinaryRoundSpec.finite {f : Format} {mode : BinaryRoundingMode} {x : ℚ}
    {bits : BitVec f.width} (h : BinaryRoundSpec f mode x bits) :
    ∃ d, (classify f bits).finite = some d := by
  have hv : ∃ v, binaryValue f bits = some v := by
    cases mode <;> obtain ⟨v, hv, _⟩ := h <;> exact ⟨v, hv⟩
  obtain ⟨v, hv⟩ := hv
  unfold binaryValue at hv
  cases hd : (classify f bits).finite with
  | none => simp [hd] at hv
  | some d => exact ⟨d, rfl⟩

/-- Rounding succeeds exactly within the format's finite range. -/
theorem roundBinary_isSome_iff (f : Format) (mode : BinaryRoundingMode) (x : ℚ) :
    (roundBinary f mode x).isSome = true ↔ f.WellFormed ∧ absQ x ≤ f.maxFinite := by
  constructor
  · intro h
    cases hb : roundBinary f mode x with
    | none => simp [hb] at h
    | some b => exact roundBinary_range hb
  · rintro ⟨hf, hr⟩
    obtain ⟨b, hb, _⟩ := roundBinary_correct f hf mode x hr
    simp [hb]

theorem roundBinary_zero (f : Format) (hf : f.WellFormed) (mode : BinaryRoundingMode) :
    roundBinary f mode 0 = some 0 := by
  have hr : 0 ≤ f.maxFinite := Rat.mul_nonneg Rat.natCast_nonneg (Rat.le_of_lt (pow2_pos _))
  simp only [roundBinary, hf, not_true_eq_false, ↓reduceIte]
  rw [if_neg (by simpa [absQ] using Rat.not_lt.mpr hr)]

/-- The output sign is the input's strict negativity, even when it underflows to zero. -/
theorem roundBinary_sign (f : Format) (mode : BinaryRoundingMode) (x : ℚ)
    (bits : BitVec f.width) (h : roundBinary f mode x = some bits) :
    binarySign f bits = decide (x < 0) := by
  obtain ⟨hf, hr⟩ := roundBinary_range h
  by_cases hx : x = 0
  · subst x
    rw [roundBinary_zero f hf mode] at h
    cases Option.some.inj h
    simp [binarySign]
  · have hm := absQ_pos_of_ne_zero x hx
    obtain ⟨he1, he2, _, _⟩ := binaryNormExp_bounds f hf (absQ x) hm hr
    obtain ⟨hk0, hk1, hsub, htop⟩ := binaryRoundedCoeff_bounds f hf mode (decide (x < 0)) (absQ x) hm hr
    have hs := binaryCarry_spec f hf _ _ he1 he2 hk0 hk1 hsub htop
    let e := (binaryCarry f (binaryNormExp f (absQ x)) (binaryCoefficient mode (decide (x < 0))
      (absQ x / pow2 (binaryNormExp f (absQ x) - f.mantissaBits)))).1
    let k := (binaryCarry f (binaryNormExp f (absQ x)) (binaryCoefficient mode (decide (x < 0))
      (absQ x / pow2 (binaryNormExp f (absQ x) - f.mantissaBits)))).2
    have hk : 0 ≤ k := hs.2.2.1
    let r : BinaryRep f := ⟨decide (x < 0), e, k.toNat, hs.1, hs.2.1,
      by have := hs.2.2.2.1; change k < _ at this; omega,
      by have := hs.2.2.2.2.1; change _ ≤ k ∨ e = _ at this; omega⟩
    have heq : encodeBinary f (decide (x < 0)) e k = bits := by
      unfold roundBinary at h
      rw [if_neg (fun hn => hn hf), if_neg (Rat.not_lt.mpr hr), if_neg hx] at h
      change (if e > f.emax then none else some (encodeBinary f (decide (x < 0)) e k)) = some bits at h
      rw [if_neg (Int.not_lt.mpr hs.2.1)] at h
      exact Option.some.inj h
    have hsign := (encodeBinary_fields f hf r).1
    simpa only [r, BinaryRep.encode, Int.toNat_of_nonneg hk, heq] using hsign

end TensorCore
