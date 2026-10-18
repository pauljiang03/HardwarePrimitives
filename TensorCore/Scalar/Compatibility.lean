import TensorCore.Scalar.Specification

/-! Compatibility of IEEE scalar operations with exact rounding. -/

namespace TensorCore.IEEE

/-- Same-format conversion fixes every finite encoding, both zeros included, and raises no flags. -/
theorem convert_self_finite (f : BinaryFormat) (cfg : Context) (a : Word f)
    (s : Bool) (x : ℚ) (hd : decode f a = .finite s x) :
    convert f f cfg a = ⟨a, {}⟩ := by
  obtain ⟨hv, hs⟩ := (decode_finite_iff f a s x).mp hd
  by_cases hx : x = 0
  · have ha : ∃ d, (classify f.layout a).finite = some d := by
      unfold binaryValue at hv
      cases hc : (classify f.layout a).finite with
      | none => simp [hc] at hv
      | some d => exact ⟨d, rfl⟩
    let za := encodeBinaryRep f.layout f.valid (BinaryRep.zero f.layout f.valid s)
    have he := binaryValue_sign_injective f.layout f.valid za ⟨a, ha⟩ 0
      (zero_value f s) (by simpa [hx] using hv) (by
        change sign f (zero f s) = sign f a
        rw [zero_sign]; exact hs.symm)
    have heq : zero f s = a := congrArg Subtype.val he
    simp [convert, convertDatum, hd, round, hx, heq]
  · have hrb := binaryValue_roundBinary f.layout f.valid cfg.mode a x hv hx
    have hr := (roundBinary_range hrb).2
    have he : finiteBits f cfg.mode x hr = a :=
      Option.some.inj ((finiteBits_eq f cfg.mode x hr).symm.trans hrb)
    simp [convert, convertDatum, hd, round, hx, hr, he, hv]

theorem convertPayload_bounded (source target : BinaryFormat) (p : ℕ)
    (hp : p < quietBit source) : convertPayload source target p < quietBit target := by
  cases source <;> cases target <;>
    simp [convertPayload, quietBit, BinaryFormat.layout, fp16, fp32, fp64] at hp ⊢ <;> omega

theorem convertPayload_roundtrip (source target : BinaryFormat) (p : ℕ)
    (hw : source.layout.mantissaBits ≤ target.layout.mantissaBits) :
    convertPayload target source (convertPayload source target p) = p := by
  cases source <;> cases target <;>
    simp [convertPayload, BinaryFormat.layout, fp16, fp32, fp64] at hw ⊢ <;> omega

/-- Widening then narrowing a quiet NaN preserves sign and payload. -/
theorem convert_quietNaN_roundtrip (source target : BinaryFormat) (cfg : Context)
    (s : Bool) (p : ℕ) (hp : p < quietBit source)
    (hw : source.layout.mantissaBits ≤ target.layout.mantissaBits) :
    convert target source cfg (convert source target cfg (nan source s p)).bits =
      ⟨nan source s p, {}⟩ := by
  have hpt := convertPayload_bounded source target p hp
  simp [convert, convertDatum, decode_nan, Nat.mod_eq_of_lt hp, Nat.mod_eq_of_lt hpt,
    convertPayload_roundtrip source target p hw]

/-- Finite FMA needs only its exact result in range, not its product. -/
theorem fma_finite_contract (f : BinaryFormat) (cfg : Context) (a b c : Word f)
    (sa sb sc : Bool) (x y z : ℚ)
    (ha : decode f a = .finite sa x) (hb : decode f b = .finite sb y)
    (hc : decode f c = .finite sc z) :
    RoundSpec f cfg (sumZeroSign cfg.mode (xor sa sb) sc) (x * y + z) (fma f cfg a b c) := by
  have h := fma_correct f cfg a b c
  simpa [FmaSpec, ha, hb, hc, Datum.isNaN] using h

end TensorCore.IEEE
