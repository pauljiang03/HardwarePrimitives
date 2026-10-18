import TCFloat.Equivalence.Base
import FloatLib.Floats.Formats.BinaryInterchange.Model.Fields.Proof

namespace TCFloat.Equivalence
open FloatLib.Floats.Formats.BinaryInterchange

def format (f : FloatFormat) : TensorCore.Format := ⟨f.fracWidth,f.expWidth,f.exponentBias⟩

theorem expField_eq (f : FloatFormat) (n : Nat) (hn : n < 2^f.bitWidth) :
    Model.expField (ofNat f n) = n / 2^f.fracWidth % 2^f.expWidth := by
  rw [Model.expField_eq_expFieldImpl_apply]
  simp [Model.expFieldImpl,Model.toNatBits,ofNat,Model.ofBits,
    FloatFormat.expAllOnesNat,Nat.and_two_pow_sub_one_eq_mod,Nat.shiftRight_eq_div_pow,
    Nat.mod_eq_of_lt hn]

theorem fracField_eq (f : FloatFormat) (n : Nat) (hn : n < 2^f.bitWidth) :
    Model.fracField (ofNat f n) = n % 2^f.fracWidth := by
  rw [Model.fracField_eq_fracFieldImpl_apply]
  simp [Model.fracFieldImpl,Model.toNatBits,ofNat,Model.ofBits,
    FloatFormat.fracMaskNat,Nat.and_two_pow_sub_one_eq_mod,Nat.mod_eq_of_lt hn]

theorem signBit_eq (f : FloatFormat) (n : Nat) (hn : n < 2^f.bitWidth) :
    Model.signBit (ofNat f n) = (n / 2^(f.fracWidth+f.expWidth) != 0) := by
  apply Bool.eq_iff_iff.mpr
  rw [Model.signBit_eq_true_iff_signMaskNat_le]
  simp only [Model.toNatBits,ofNat,Model.ofBits,BitVec.toNat_ofNat,Nat.mod_eq_of_lt hn,
    bne_iff_ne]
  have hw : f.bitWidth-1 = f.fracWidth+f.expWidth := by unfold FloatFormat.bitWidth; omega
  simp only [FloatFormat.signMaskNat,FloatFormat.signBitIndex,hw]
  have hp : 0 < 2^(f.fracWidth+f.expWidth) := by positivity
  rw [← Nat.pos_iff_ne_zero, Nat.div_pos_iff]
  simp [hp]

/-- Decoder equivalence, including NaN and infinity rejection and all metadata. -/
theorem decode_project (f : FloatFormat) (hf : f.isIEEE = true)
    (n : Nat) (hn : n < 2^f.bitWidth) :
    (decode f n).map project = (TensorCore.classifyNat (format f) n).finite := by
  have hb := FloatFormat.exponentBias_eq_bias_of_isIEEE f hf
  have hp : 0 < 2^f.fracWidth := by positivity
  simp only [decode,not_le.mpr hn,ite_false,Model.toDyadic?,hf,ite_true]
  simp only [Model.ieeeToDyadic?,Model.IEEE.isNaN,Model.IEEE.isInf,
    expField_eq f n hn,fracField_eq f n hn,signBit_eq f n hn,
    TensorCore.classifyNat,format,FloatFormat.expAllOnesNat]
  by_cases hall : n / 2^f.fracWidth % 2^f.expWidth = 2^f.expWidth-1
  · by_cases hmant : n % 2^f.fracWidth = 0 <;>
      simp [hall,hmant,TensorCore.Classification.finite]
  · have hz : (0:Nat) ≠ 2^f.expWidth-1 := by
      intro h
      have hh : 1 < 2^f.expWidth := Nat.one_lt_two_pow_iff.mpr (by have := f.expWidth_ge_two; omega)
      omega
    by_cases he : n / 2^f.fracWidth % 2^f.expWidth = 0
    · by_cases hmant : n % 2^f.fracWidth = 0 <;>
        simp [he,hmant,hz,project,FloatLib.Numerics.Dyadic.signedSignificand,
          TensorCore.Classification.finite]
    · have hs : max (1:Int) ((n / 2^f.fracWidth % 2^f.expWidth : Nat) : Int) =
          (n / 2^f.fracWidth % 2^f.expWidth : Nat) := by omega
      simp [hall,he,project,Model.pow2_eq_two_pow,
        FloatLib.Numerics.Dyadic.signedSignificand,TensorCore.Classification.finite]
      exact_mod_cast (Nat.one_le_iff_ne_zero.mpr he)

theorem decode_value (f : FloatFormat) (hf : f.isIEEE = true)
    (n : Nat) (t : Term) (ht : decode f n = some t) :
    t.value = (project t).value := by
  have hb := FloatFormat.exponentBias_eq_bias_of_isIEEE f hf
  unfold decode at ht
  split at ht
  · simp at ht
  · simp only [Model.toDyadic?,hf,ite_true,Model.ieeeToDyadic?] at ht
    split at ht
    · simp at ht
    · split at ht
      · split at ht
        · simp at ht; subst t
          simp [Term.value,project,TensorCore.Decoded.value,FloatLib.Numerics.Dyadic.signedSignificand]
        · rename_i hmant
          dsimp only [Bind.bind, Pure.pure, Option.bind] at ht
          simp only [beq_iff_eq] at *
          simp only [ite_eq_right hmant,Option.some.injEq] at ht
          subst t
          simp only [Term.value,project,TensorCore.Decoded.value,FloatLib.Numerics.Dyadic.toRat,
            Rat.ofInt_eq_cast,pow2_eq,TCFloat.pow2]
          congr 2
          simp only [FloatFormat.ieeeMinSubnormalExponent,Int.ofNat_eq_natCast,hb]
          omega
      · have hp : Model.pow2 f.fracWidth + Model.fracField (ofNat f n) ≠ 0 := by
          rw [Model.pow2_eq_two_pow]; positivity
        dsimp only [Bind.bind, Pure.pure, Option.bind] at ht
        simp only [ite_eq_right hp,Option.some.injEq] at ht
        subst t
        simp only [Term.value,project,TensorCore.Decoded.value,FloatLib.Numerics.Dyadic.toRat,
          Rat.ofInt_eq_cast,pow2_eq,TCFloat.pow2]
        congr 2
        simp only [FloatFormat.ieeeNormalMantissaExpOffset,Int.ofNat_eq_natCast,Int.natCast_add,hb]
        rename_i he
        simp only [beq_iff_eq] at he
        omega

theorem decode_values (f : FloatFormat) (n : Nat) (hn : n < 2^f.bitWidth) :
    (decode f n).map Term.value = (ofNat f n).toRat? := by
  unfold decode Model.toRat?
  simp only [not_le.mpr hn,ite_false]
  cases hd : (ofNat f n).toDyadic? with
  | none => simp
  | some d =>
    by_cases hz : d.significand=0 <;> simp [hz,Term.value]

/-- FloatLib decodes every word of `f` as the reference does, with consistent metadata. -/
structure DecodesLikeReference (f : FloatFormat) : Prop where
  decode_eq : ∀ n, n < 2^f.bitWidth →
    (decode f n).map project = (TensorCore.classifyNat (format f) n).finite
  value_eq : ∀ n t, decode f n = some t → t.value = (project t).value

theorem DecodesLikeReference.of_isIEEE {f : FloatFormat} (hf : f.isIEEE = true) :
    DecodesLikeReference f :=
  ⟨decode_project f hf, decode_value f hf⟩

theorem decode_none_of_ge (f : FloatFormat) {n : Nat} (hn : 2^f.bitWidth ≤ n) : decode f n = none := by
  simp [decode, hn]

set_option maxRecDepth 100000 in
/-- The 9-bit E4M3 layout has bias 7, not IEEE's 15; its decoding is checked on all 512 words. -/
theorem e4m3x_decodesLikeReference : DecodesLikeReference e4m3x := by
  have hd : ∀ n, n < 512 →
      (decode e4m3x n).map project = (TensorCore.classifyNat (format e4m3x) n).finite := by
    decide +kernel
  have hv : ∀ n, n < 512 →
      (decode e4m3x n).all (fun t => decide (t.value = (project t).value)) = true := by
    decide +kernel
  refine ⟨fun n hn => hd n hn, fun n t ht => ?_⟩
  have hn : n < 512 := by
    by_contra h
    rw [decode_none_of_ge e4m3x (show 2^e4m3x.bitWidth ≤ n by
      change 2^9 ≤ n; omega)] at ht
    cases ht
  have h := hv n hn
  rw [ht] at h
  simpa using h

/-- FP32 decoder equality on every word, including special-value rejection. -/
theorem value32_eq (b : TensorCore.F32) : TCFloat.value32 b.toNat = TensorCore.value32 b := by
  have hn : b.toNat < 2^FloatFormat.binary32.bitWidth := b.isLt
  have hp := decode_project .binary32 (by decide) b.toNat hn
  have hv := decode_values .binary32 b.toNat hn
  have hm := congrArg (Option.map TensorCore.Decoded.value) hp
  change _ = TensorCore.value32 b at hm
  unfold TCFloat.value32
  rw [← hm,← hv]
  cases hd : decode .binary32 b.toNat with
  | none => rfl
  | some t =>
    simp only [Option.map_some]
    exact congrArg some (decode_value .binary32 (by decide) b.toNat t hd)

end TCFloat.Equivalence
