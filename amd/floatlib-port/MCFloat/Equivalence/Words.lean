import MCFloat.Equivalence.Decode

/-! # Observed FP32 words

`observe` reads a FloatLib FP32 word as a `MatrixCore` `Outcome`; `fl{·}` words observe as
`roundOutcome`. -/

set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false

namespace MCFloat.Equivalence
open FloatLib.Floats.Formats.BinaryInterchange

def observe (w : MCFloat.F32) : MatrixCore.Outcome :=
  match MCFloat.classifyModel w with
  | .finite _ => .finite (BitVec.ofNat 32 (MCFloat.bits w))
  | .inf s => .infinity s
  | .nan => .nan

def WordX (w : MCFloat.F32) : MatrixCore.XVal → Prop
  | .fin q => ∃ t, MCFloat.classifyModel w = .finite t ∧ t.value = q
  | .inf s => MCFloat.classifyModel w = .inf s
  | .nan => MCFloat.classifyModel w = .nan

theorem ofNat_bits_self (w : MCFloat.F32) : MCFloat.ofNat .binary32 (MCFloat.bits w) = w := by
  unfold MCFloat.ofNat MCFloat.bits
  rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]
  rfl

theorem classify_word (w : MCFloat.F32) :
    Agree (MCFloat.classifyModel w) (MatrixCore.fp32.decodeNat (MCFloat.bits w)) := by
  have h := fp32_agree (MCFloat.bits w) (bits_lt w)
  rwa [MCFloat.classify, ofNat_bits_self] at h

theorem decode_signedZero (w : MatrixCore.F32) :
    ∃ u, MatrixCore.fp32.decode (MatrixCore.signedZero32 w) = .finite u := by
  have h : w.toNat / 2147483648 % 2 = 0 ∨ w.toNat / 2147483648 % 2 = 1 := by omega
  unfold MatrixCore.signedZero32
  rcases h with h | h <;> rw [h] <;> exact ⟨_, rfl⟩

theorem decode_rne32 {x : ℚ} {w : MatrixCore.F32} (h : MatrixCore.rne32 x = some w) :
    ∃ u, MatrixCore.fp32.decode w = .finite u := by
  have hv := MatrixCore.rne32_value h
  unfold MatrixCore.value32 at hv
  cases hd : MatrixCore.fp32.decode w <;> simp [hd, MatrixCore.Datum.toFinite] at hv
  exact ⟨_, rfl⟩

theorem decode_fl32 {ftz : Bool} {x : ℚ} {d : MatrixCore.F32} (h : MatrixCore.fl32 ftz x = some d) :
    ∃ u, MatrixCore.fp32.decode d = .finite u := by
  unfold MatrixCore.fl32 at h
  cases hr : MatrixCore.rne32 x with
  | none => simp [hr] at h
  | some w =>
    simp only [hr, Option.some.injEq] at h
    subst h
    split
    · exact decode_signedZero w
    · exact decode_rne32 hr

theorem decode_infinity (s : Bool) :
    MatrixCore.fp32.decodeNat (MatrixCore.infinity32 s).toNat = .infinity s := by
  cases s <;> decide

theorem observe_fl (ftz : Bool) (x : ℚ) :
    observe (MCFloat.fl ftz x) = MatrixCore.roundOutcome ftz x := by
  have hc := classify_word (MCFloat.fl ftz x)
  rw [fl_bits] at hc
  unfold observe MatrixCore.roundOutcome
  rw [fl_bits]
  unfold refWord at hc ⊢
  cases h : MatrixCore.fl32 ftz x with
  | some d =>
    obtain ⟨u, hu⟩ := decode_fl32 h
    rw [h] at hc
    change Agree _ (MatrixCore.fp32.decode d) at hc
    rw [hu] at hc
    simp only
    cases hm : MCFloat.classifyModel (MCFloat.fl ftz x) <;> rw [hm] at hc <;> simp [Agree] at hc
    simp
  | none =>
    rw [h, decode_infinity] at hc
    simp only
    cases hm : MCFloat.classifyModel (MCFloat.fl ftz x) <;> rw [hm] at hc <;> simp [Agree] at hc
    simp [hc]

theorem wordX_fl (ftz : Bool) (x : ℚ) :
    WordX (MCFloat.fl ftz x) (MatrixCore.XVal.fl ftz (.fin x)) := by
  have hc := classify_word (MCFloat.fl ftz x)
  rw [fl_bits] at hc
  unfold refWord at hc
  unfold MatrixCore.XVal.fl MatrixCore.flValue
  cases h : MatrixCore.fl32 ftz x with
  | some d =>
    obtain ⟨u, hu⟩ := decode_fl32 h
    rw [h] at hc
    change Agree _ (MatrixCore.fp32.decode d) at hc
    rw [hu] at hc
    have hv : MatrixCore.value32 d = some u.value := by
      simp [MatrixCore.value32, hu, MatrixCore.Datum.toFinite]
    simp only [h, Option.bind_some, hv, WordX]
    cases hm : MCFloat.classifyModel (MCFloat.fl ftz x) <;> rw [hm] at hc <;> simp [Agree] at hc
    exact ⟨_, rfl, hc.value⟩
  | none =>
    rw [h, decode_infinity] at hc
    simp only [h, Option.bind_none, WordX]
    cases hm : MCFloat.classifyModel (MCFloat.fl ftz x) <;> rw [hm] at hc <;> simp [Agree] at hc
    rw [hc]

end MCFloat.Equivalence
