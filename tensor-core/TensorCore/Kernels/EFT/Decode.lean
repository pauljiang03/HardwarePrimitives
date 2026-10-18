import TensorCore.Kernels.EFT.DecodeDefs
import TensorCore.Kernels.EFT.Round
import TensorCore.Kernels.EFT.Split

/-! Correctness of bounded input decoding and products. -/

namespace TensorCore.EFMachine

set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
set_option exponentiation.threshold 1024

def Factor.decoded (x : Factor) : Decoded :=
  ⟨if x.negative then -(x.magnitude.toNat : ℤ) else x.magnitude.toNat,
    (x.biasedExp.toNat : ℤ) - 256, x.mantissaBits.toNat⟩

theorem field_toNat (bits : F32) (shift width outWidth : ℕ)
    (hw : width ≤ outWidth) (hw' : width < 32) :
    (((bits >>> shift) &&& (((1 : F32) <<< width) - 1)).setWidth outWidth).toNat =
      bits.toNat / 2 ^ shift % 2 ^ width := by
  have hp : (2 ^ width : ℕ) < 2 ^ 32 :=
    Nat.pow_lt_pow_right (by decide) (by omega)
  have hm : (((1 : F32) <<< width) - 1).toNat = 2 ^ width - 1 := by
    rw [BitVec.toNat_sub_of_le]
    · rw [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]
      change (1 * 2 ^ width) % 2 ^ 32 - 1 = _
      rw [Nat.one_mul, Nat.mod_eq_of_lt hp]
    · change 1 ≤ ((1 : F32) <<< width).toNat
      rw [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]
      change 1 ≤ (1 * 2 ^ width) % 2 ^ 32
      rw [Nat.one_mul, Nat.mod_eq_of_lt hp]
      exact Nat.one_le_two_pow
  rw [BitVec.toNat_setWidth, BitVec.toNat_and, hm, BitVec.toNat_ushiftRight,
    Nat.shiftRight_eq_div_pow, Nat.and_two_pow_sub_one_eq_mod]
  exact Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le (Nat.mod_lt _ (Nat.two_pow_pos _))
    (Nat.pow_le_pow_right (by decide) hw))

theorem mantissaBits_toNat (bits : F32) (width : ℕ) (hw : width ≤ 10) :
    ((bits &&& (((1 : F32) <<< width) - 1)).setWidth 11).toNat = bits.toNat % 2 ^ width := by
  simpa only [BitVec.ushiftRight_zero, Nat.pow_zero, Nat.div_one] using
    field_toNat bits 0 width 11 (by omega) (by omega)

theorem decodeFactor_asDecoded (kind : InputKind) (bits : F32) :
    (decodeFactor kind bits).map Factor.decoded = (classifyNat kind.format bits.toNat).finite := by
  have he5 := field_toNat bits 10 5 10 (by decide) (by decide)
  have he8 := field_toNat bits 7 8 10 (by decide) (by decide)
  have he8' := field_toNat bits 10 8 10 (by decide) (by decide)
  have hm10 := mantissaBits_toNat bits 10 (by decide)
  have hm7 := mantissaBits_toNat bits 7 (by decide)
  by_cases ht : bits.toNat / 2 ^ kind.format.mantissaBits % 2 ^ kind.format.exponentBits =
      2 ^ kind.format.exponentBits - 1 <;>
    by_cases he : bits.toNat / 2 ^ kind.format.mantissaBits % 2 ^ kind.format.exponentBits = 0 <;>
    by_cases hm : bits.toNat % 2 ^ kind.format.mantissaBits = 0 <;>
    by_cases hs : bits.toNat / 2 ^ (kind.format.mantissaBits + kind.format.exponentBits) = 0 <;>
    cases kind <;>
    dsimp +instances only [decodeFactor, InputKind.format, fp16, bf16, tf19,
      Option.map, Factor.decoded, classifyNat] at * <;>
    simp only [beq_iff_eq, BitVec.toNat_eq, he5, he8, he8', hm10, hm7] <;>
    simp_all [Classification.finite, BitVec.toNat_add, BitVec.toNat_ushiftRight,
      Nat.shiftRight_eq_div_pow,
      bne_iff_ne, BitVec.toNat_eq] <;> omega

theorem decodeFactor_bounds {kind : InputKind} {bits : F32} {a : Factor}
    (h : decodeFactor kind bits = some a) :
    130 ≤ a.biasedExp.toNat ∧ a.biasedExp.toNat ≤ 383 ∧ a.mantissaBits.toNat ≤ 10 := by
  have hd : (classifyNat kind.format bits.toNat).finite = some a.decoded := by
    rw [← decodeFactor_asDecoded, h]; rfl
  cases kind <;>
    dsimp +instances only [InputKind.format, fp16, bf16, tf19, classifyNat] at hd <;>
    repeat' (split at hd)
  all_goals
    simp only [Classification.finite, Option.some.injEq, Factor.decoded, Decoded.mk.injEq] at hd
    first | contradiction | omega

theorem shift_magnitude (m : Magnitude) (g : Grid)
    (hm : m.toNat < 2 ^ 24) (hg : g.toNat ≤ 550) :
    (m <<< g).toNat = m.toNat * 2 ^ g.toNat ∧ (m <<< g).toNat < 2 ^ 574 := by
  have hmul : m.toNat * 2 ^ g.toNat < 2 ^ (24 + g.toNat) := by
    rw [Nat.pow_add]
    exact Nat.mul_lt_mul_of_pos_right hm (Nat.two_pow_pos _)
  have hp : 2 ^ (24 + g.toNat) ≤ 2 ^ 574 := Nat.pow_le_pow_right (by decide) (by omega)
  have hwide : m.toNat * 2 ^ g.toNat < 2 ^ 576 := by omega
  change (m <<< g.toNat).toNat = _ ∧ (m <<< g.toNat).toNat < _
  rw [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, Nat.mod_eq_of_lt hwide]
  exact ⟨rfl, by omega⟩

theorem shiftedWord_value (negative : Bool) (m : Magnitude) (g : Grid)
    (hm : m.toNat < 2 ^ 24) (hg : g.toNat ≤ 550) :
    (Word.mk negative (m <<< g)).value =
      (if negative then -(m.toNat : ℚ) else (m.toNat : ℚ)) * pow2 ((g.toNat : ℤ) - 272) := by
  have h := (shift_magnitude m g hm hg).1
  cases negative <;>
    simp only [Word.value, Word.coefficient, h, Bool.false_eq_true, if_false, if_true,
      Rat.intCast_neg, Rat.intCast_natCast, Rat.natCast_mul, pow2_common] <;> grind

theorem product_grid {a b : Factor}
    (ha : 130 ≤ a.biasedExp.toNat ∧ a.biasedExp.toNat ≤ 383 ∧ a.mantissaBits.toNat ≤ 10)
    (hb : 130 ≤ b.biasedExp.toNat ∧ b.biasedExp.toNat ≤ 383 ∧ b.mantissaBits.toNat ≤ 10) :
    (product a b).biasedExp.toNat = a.biasedExp.toNat + b.biasedExp.toNat ∧
    ((product a b).support.toNat : ℤ) =
      (a.biasedExp.toNat : ℤ) + b.biasedExp.toNat - a.mantissaBits.toNat - b.mantissaBits.toNat - 240 ∧
    (product a b).support.toNat ≤ 526 := by
  have hr : (a.biasedExp + b.biasedExp).toNat = a.biasedExp.toNat + b.biasedExp.toNat := by
    rw [BitVec.toNat_add, Nat.mod_eq_of_lt (by omega)]
  have hf : (a.mantissaBits + b.mantissaBits).toNat = a.mantissaBits.toNat + b.mantissaBits.toNat := by
    rw [BitVec.toNat_add, Nat.mod_eq_of_lt (by omega)]
  have hsub : (a.biasedExp + b.biasedExp - (a.mantissaBits + b.mantissaBits)).toNat =
      a.biasedExp.toNat + b.biasedExp.toNat - (a.mantissaBits.toNat + b.mantissaBits.toNat) := by
    rw [BitVec.toNat_sub_of_le (by change (a.mantissaBits + b.mantissaBits).toNat ≤ _; rw [hf, hr]; omega), hr, hf]
  have hsub' : (a.biasedExp + b.biasedExp - (a.mantissaBits + b.mantissaBits) - 240).toNat =
      a.biasedExp.toNat + b.biasedExp.toNat - (a.mantissaBits.toNat + b.mantissaBits.toNat) - 240 := by
    rw [BitVec.toNat_sub_of_le (by
      change 240 ≤ (a.biasedExp + b.biasedExp - (a.mantissaBits + b.mantissaBits)).toNat
      rw [hsub]; omega), hsub]
    rfl
  simp only [product]
  exact ⟨hr, by rw [hsub']; omega, by rw [hsub']; omega⟩

theorem product_value {a b : Factor}
    (ha : 130 ≤ a.biasedExp.toNat ∧ a.biasedExp.toNat ≤ 383 ∧ a.mantissaBits.toNat ≤ 10)
    (hb : 130 ≤ b.biasedExp.toNat ∧ b.biasedExp.toNat ≤ 383 ∧ b.mantissaBits.toNat ≤ 10) :
    (product a b).word.value = (denormalizedMul a.decoded b.decoded).value := by
  have hg := product_grid ha hb
  have hm : ((multiplySignificands a.magnitude b.magnitude).zeroExtend 576).toNat =
      a.magnitude.toNat * b.magnitude.toNat := by
    rw [BitVec.toNat_setWidth_of_le (by decide), multiplySignificands_exact]
  have hmb : ((multiplySignificands a.magnitude b.magnitude).zeroExtend 576).toNat < 2 ^ 24 := by
    rw [BitVec.toNat_setWidth_of_le (by decide)]
    exact (multiplySignificands _ _).isLt
  change (Word.mk (a.negative != b.negative)
      (((multiplySignificands a.magnitude b.magnitude).zeroExtend 576) <<< (product a b).support)).value = _
  rw [shiftedWord_value _ _ _ hmb (by omega), hm]
  have he : ((product a b).support.toNat : ℤ) - 272 =
      ((a.biasedExp.toNat : ℤ) - 256 + ((b.biasedExp.toNat : ℤ) - 256)) -
        ((a.mantissaBits.toNat : ℤ) + b.mantissaBits.toNat) := by omega
  rw [he]
  cases ha' : a.negative <;> cases hb' : b.negative <;>
    simp only [DenormalizedProduct.value, denormalizedMul, Factor.decoded, ha', hb', Bool.false_eq_true,
      if_false, if_true, bne_self_eq_false, bne_iff_ne, Bool.false_eq_true,
      Rat.intCast_mul, Rat.intCast_neg, Rat.intCast_natCast, Rat.natCast_mul] <;> grind

theorem product_magnitude {a b : Factor}
    (ha : 130 ≤ a.biasedExp.toNat ∧ a.biasedExp.toNat ≤ 383 ∧ a.mantissaBits.toNat ≤ 10)
    (hb : 130 ≤ b.biasedExp.toNat ∧ b.biasedExp.toNat ≤ 383 ∧ b.mantissaBits.toNat ≤ 10) :
    (product a b).word.magnitude.toNat < 2 ^ 550 := by
  have hg := (product_grid ha hb).2.2
  have hm : ((multiplySignificands a.magnitude b.magnitude).zeroExtend 576).toNat < 2 ^ 24 := by
    rw [BitVec.toNat_setWidth_of_le (by decide)]
    exact (multiplySignificands _ _).isLt
  have hs := shift_magnitude _ (product a b).support hm (by omega)
  change (((multiplySignificands a.magnitude b.magnitude).zeroExtend 576) <<<
    (product a b).support).toNat < _
  rw [hs.1]
  have hmul := Nat.mul_lt_mul_of_pos_right hm (Nat.two_pow_pos (product a b).support.toNat)
  have hp : 2 ^ (24 + (product a b).support.toNat) ≤ 2 ^ 550 :=
    Nat.pow_le_pow_right (by decide) (by omega)
  rw [Nat.pow_add] at hp
  omega

theorem fp32_exponent_toNat (bits : F32) :
    (((bits >>> 23).setWidth 8).zeroExtend 10).toNat = bits.toNat / 8388608 % 256 := by
  rw [BitVec.toNat_setWidth_of_le (by decide), BitVec.toNat_setWidth,
    BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]

theorem fp32_mantissaBits_toNat (bits : F32) :
    ((bits &&& 0x007fffff).zeroExtend 576).toNat = bits.toNat % 8388608 := by
  rw [BitVec.toNat_setWidth_of_le (by decide), BitVec.toNat_and]
  change bits.toNat &&& (2 ^ 23 - 1) = _
  exact Nat.and_two_pow_sub_one_eq_mod _ _

theorem fp32_sign (bits : F32) : bits.msb = (bits.toNat / 2 ^ 31 != 0) := by
  rw [BitVec.msb_eq_decide]
  apply Bool.eq_iff_iff.mpr
  simp only [decide_eq_true_eq, bne_iff_ne]
  omega

theorem zeroWord_value (negative : Bool) : (Word.mk negative 0).value = 0 := by
  cases negative <;> simp [Word.value, Word.coefficient]

def Accumulator.decoded (x : Accumulator) : Decoded :=
  ⟨if x.negative then -(x.magnitude.toNat : ℤ) else x.magnitude.toNat,
    (x.biasedExp.toNat : ℤ) - 256, x.mantissaBits.toNat⟩

theorem fp32_mantissaBits24_toNat (bits : F32) :
    ((bits &&& 0x007fffff).setWidth 24).toNat = bits.toNat % 8388608 := by
  have h := field_toNat bits 0 23 24 (by decide) (by decide)
  simpa using h

theorem decode32Fields_asDecoded (bits : F32) :
    (decode32Fields bits).map Accumulator.decoded = decode32 bits := by
  have he := fp32_exponent_toNat bits
  have hm := fp32_mantissaBits24_toNat bits
  by_cases ht : bits.toNat / 8388608 % 256 = 255 <;>
    by_cases hz : bits.toNat / 8388608 % 256 = 0 <;>
    by_cases hzm : bits.toNat % 8388608 = 0 <;>
    by_cases hs : bits.toNat / 2147483648 = 0 <;>
    dsimp +instances only [decode32Fields, decode32, classify, fp32,
      Option.map, Accumulator.decoded, classifyNat] <;>
    simp only [beq_iff_eq, BitVec.toNat_eq, he, hm] <;>
    simp_all [Classification.finite, BitVec.toNat_add, fp32_sign,
      bne_iff_ne] <;> omega

theorem decode32Fields_bounds {bits : F32} {a : Accumulator}
    (h : decode32Fields bits = some a) :
    130 ≤ a.biasedExp.toNat ∧ a.biasedExp.toNat ≤ 383 ∧ a.mantissaBits.toNat ≤ 23 := by
  have hd : decode32 bits = some a.decoded := by
    rw [← decode32Fields_asDecoded, h]; rfl
  dsimp +instances only [decode32, classify, fp32, classifyNat] at hd
  repeat' (split at hd)
  all_goals
    simp only [Classification.finite, Option.some.injEq, Accumulator.decoded, Decoded.mk.injEq] at hd
    first | contradiction | omega

theorem Accumulator.term_grid {a : Accumulator}
    (ha : 130 ≤ a.biasedExp.toNat ∧ a.biasedExp.toNat ≤ 383 ∧ a.mantissaBits.toNat ≤ 23) :
    a.term.biasedExp.toNat = a.biasedExp.toNat + 256 ∧
    (a.term.support.toNat : ℤ) = (a.biasedExp.toNat : ℤ) + 16 - a.mantissaBits.toNat ∧
    123 ≤ a.term.support.toNat ∧ a.term.support.toNat ≤ 399 := by
  have hr : (a.biasedExp + 256).toNat = a.biasedExp.toNat + 256 := by
    rw [BitVec.toNat_add]
    change (a.biasedExp.toNat + 256) % 1024 = _
    exact Nat.mod_eq_of_lt (by omega)
  have hg : (a.biasedExp + 16).toNat = a.biasedExp.toNat + 16 := by
    rw [BitVec.toNat_add]
    change (a.biasedExp.toNat + 16) % 1024 = _
    exact Nat.mod_eq_of_lt (by omega)
  have hs : (a.biasedExp + 16 - a.mantissaBits).toNat = a.biasedExp.toNat + 16 - a.mantissaBits.toNat := by
    rw [BitVec.toNat_sub_of_le (by change a.mantissaBits.toNat ≤ _; rw [hg]; omega), hg]
  simp only [Accumulator.term]
  exact ⟨hr, by rw [hs]; omega, by rw [hs]; omega, by rw [hs]; omega⟩

theorem Accumulator.term_value {a : Accumulator}
    (ha : 130 ≤ a.biasedExp.toNat ∧ a.biasedExp.toNat ≤ 383 ∧ a.mantissaBits.toNat ≤ 23) :
    a.term.word.value = a.decoded.value := by
  have hg := a.term_grid ha
  have hm : (a.magnitude.zeroExtend 576).toNat = a.magnitude.toNat :=
    BitVec.toNat_setWidth_of_le (by decide)
  have hb : (a.magnitude.zeroExtend 576).toNat < 2 ^ 24 := by rw [hm]; exact a.magnitude.isLt
  change (Word.mk a.negative (a.magnitude.zeroExtend 576 <<< a.term.support)).value = _
  rw [shiftedWord_value _ _ _ hb (by omega), hm]
  have he : (a.term.support.toNat : ℤ) - 272 = (a.biasedExp.toNat : ℤ) - 256 - a.mantissaBits.toNat := by omega
  rw [he]
  cases hs : a.negative <;>
    simp [Accumulator.decoded, Decoded.value, hs, Rat.intCast_natCast]

theorem Accumulator.term_magnitude {a : Accumulator}
    (ha : 130 ≤ a.biasedExp.toNat ∧ a.biasedExp.toNat ≤ 383 ∧ a.mantissaBits.toNat ≤ 23) :
    a.term.word.magnitude.toNat < 2 ^ 424 := by
  have hg := a.term_grid ha
  have hm : (a.magnitude.zeroExtend 576).toNat < 2 ^ 24 := by
    rw [BitVec.toNat_setWidth_of_le (by decide)]; exact a.magnitude.isLt
  have hs := shift_magnitude _ a.term.support hm (by omega)
  change (a.magnitude.zeroExtend 576 <<< a.term.support).toNat < _
  rw [hs.1]
  have hmul := Nat.mul_lt_mul_of_pos_right hm (Nat.two_pow_pos a.term.support.toNat)
  have hp : 2 ^ (24 + a.term.support.toNat) ≤ 2 ^ 424 := Nat.pow_le_pow_right (by decide) (by omega)
  rw [Nat.pow_add] at hp
  omega

theorem decode32Word_value (bits : F32) :
    (decode32Word bits).map Word.value = TensorCore.value32 bits := by
  simp only [decode32Word, decode32Term, Option.map_map, TensorCore.value32,
    ← decode32Fields_asDecoded]
  cases hd : decode32Fields bits with
  | none => rfl
  | some a =>
    simp only [Option.map_some]
    exact congrArg some (a.term_value (decode32Fields_bounds hd))

theorem decode32Word_magnitude {bits : F32} {w : Word} (h : decode32Word bits = some w) :
    w.magnitude.toNat < 2 ^ 424 := by
  cases hd : decode32Fields bits with
  | none => simp [decode32Word, decode32Term, hd] at h
  | some a =>
    simp only [decode32Word, decode32Term, hd, Option.map_some, Option.some.injEq] at h
    rw [← h]
    exact a.term_magnitude (decode32Fields_bounds hd)

end TensorCore.EFMachine
