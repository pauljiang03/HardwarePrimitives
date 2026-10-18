import TensorCore.Kernels.Datapath.Align
import TensorCore.Kernels.EFT.Decode

/-! Bitvector decoding gives the model's decoded inputs. -/

namespace TensorCore.Datapath

open EFMachine

set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
set_option exponentiation.threshold 1024

theorem classifyNat_finite_bound (f : Format) (n : ℕ) (d : Decoded)
    (h : (classifyNat f n).finite = some d) :
    d.significand.natAbs < 2 ^ (d.mantissaBits.toNat + 1) := by
  have hm := Nat.mod_lt n (Nat.two_pow_pos f.mantissaBits)
  have hp : 2 ^ (f.mantissaBits + 1) = 2 * 2 ^ f.mantissaBits := by rw [Nat.pow_succ]; omega
  unfold classifyNat at h
  dsimp only at h
  by_cases ht : n / 2 ^ f.mantissaBits % 2 ^ f.exponentBits = 2 ^ f.exponentBits - 1
  · rw [if_pos ht] at h
    split at h <;> simp [Classification.finite] at h
  · rw [if_neg ht] at h
    by_cases hz : n / 2 ^ f.mantissaBits % 2 ^ f.exponentBits = 0
    · rw [if_pos hz] at h
      by_cases hm0 : n % 2 ^ f.mantissaBits = 0
      · rw [if_pos hm0] at h
        simp only [Classification.finite, Option.some.injEq] at h
        rw [← h]
        decide
      · rw [if_neg hm0] at h
        simp only [Classification.finite, Option.some.injEq] at h
        rw [← h]
        simp only [Int.toNat_natCast]
        split <;> simp only [Int.natAbs_neg, Int.natAbs_natCast] <;> omega
    · rw [if_neg hz] at h
      simp only [Classification.finite, Option.some.injEq] at h
      rw [← h]
      simp only [Int.toNat_natCast]
      split <;> simp only [Int.natAbs_neg, Int.natAbs_natCast] <;> omega

def Input.decoded (x : Input) : Decoded :=
  ⟨if x.negative then -(x.significand.toNat : ℤ) else x.significand.toNat,
    (x.biasedExp.toNat : ℤ) - 128, x.mantissaBits.toNat⟩

theorem decodeInput_asDecoded (kind : InputKind) (bits : F32) :
    (decodeInput kind bits).map Input.decoded = (classifyNat kind.format bits.toNat).finite := by
  have he5 := field_toNat bits 10 5 9 (by decide) (by decide)
  have he8 := field_toNat bits 7 8 9 (by decide) (by decide)
  have he8' := field_toNat bits 10 8 9 (by decide) (by decide)
  have hm10 := mantissaBits_toNat bits 10 (by decide)
  have hm7 := mantissaBits_toNat bits 7 (by decide)
  have he53 := field_toNat bits 3 5 9 (by decide) (by decide)
  have he52 := field_toNat bits 2 5 9 (by decide) (by decide)
  have hm3 := mantissaBits_toNat bits 3 (by decide)
  have hm2 := mantissaBits_toNat bits 2 (by decide)
  by_cases ht : bits.toNat / 2 ^ kind.format.mantissaBits % 2 ^ kind.format.exponentBits =
      2 ^ kind.format.exponentBits - 1 <;>
    by_cases he : bits.toNat / 2 ^ kind.format.mantissaBits % 2 ^ kind.format.exponentBits = 0 <;>
    by_cases hm : bits.toNat % 2 ^ kind.format.mantissaBits = 0 <;>
    by_cases hs : bits.toNat / 2 ^ (kind.format.mantissaBits + kind.format.exponentBits) = 0 <;>
    cases kind <;>
    dsimp +instances only [decodeInput, InputKind.format, fp16, bf16, tf19, e4m3x, e5m2,
      Option.map, Input.decoded, classifyNat] at * <;>
    simp only [beq_iff_eq, BitVec.toNat_eq, he5, he8, he8', hm10, hm7, he53, he52, hm3, hm2] <;>
    simp_all [Classification.finite, BitVec.toNat_add, BitVec.toNat_ushiftRight,
      Nat.shiftRight_eq_div_pow, bne_iff_ne, BitVec.toNat_eq] <;> omega

theorem decodeInput_model (variant : Variant) (word : variant.model.Word) :
    (decodeInput variant.kind (word.zeroExtend 32)).map Input.decoded = variant.model.decode word := by
  rw [decodeInput_asDecoded]
  cases variant <;> rw [BitVec.toNat_setWidth_of_le (by decide)] <;> rfl

theorem decodeInput_bounds {kind : InputKind} {bits : F32} {a : Input}
    (h : decodeInput kind bits = some a) :
    a.significand.toNat < 2 ^ (a.mantissaBits.toNat + 1) ∧ a.mantissaBits.toNat ≤ 10 ∧
      2 ≤ a.biasedExp.toNat ∧ a.biasedExp.toNat ≤ 255 := by
  have hd : (classifyNat kind.format bits.toNat).finite = some a.decoded := by
    rw [← decodeInput_asDecoded, h]; rfl
  have hb := classifyNat_finite_bound _ _ _ hd
  have hs : a.decoded.significand.natAbs = a.significand.toNat := by
    unfold Input.decoded; cases a.negative <;> simp
  have hmb : a.decoded.mantissaBits.toNat = a.mantissaBits.toNat := by simp [Input.decoded]
  rw [hs, hmb] at hb
  refine ⟨hb, ?_⟩
  cases kind <;>
    dsimp +instances only [InputKind.format, fp16, bf16, tf19, e4m3x, e5m2, classifyNat] at hd <;>
    repeat' (split at hd)
  all_goals
    simp only [Classification.finite, Option.some.injEq, Input.decoded, Decoded.mk.injEq] at hd
    first | contradiction | omega

theorem fp32_exponent9_toNat (bits : F32) :
    (((bits >>> 23).setWidth 8).zeroExtend 9).toNat = bits.toNat / 8388608 % 256 := by
  rw [BitVec.toNat_setWidth_of_le (by decide), BitVec.toNat_setWidth,
    BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]

theorem decodeC_spec (bits : F32) :
    (decodeC bits).map Term.denormalized =
      (decode32 bits).map fun d => ⟨d.significand, d.exponent, d.mantissaBits⟩ := by
  have he := fp32_exponent9_toNat bits
  have hm := fp32_mantissaBits24_toNat bits
  by_cases ht : bits.toNat / 8388608 % 256 = 255 <;>
    by_cases hz : bits.toNat / 8388608 % 256 = 0 <;>
    by_cases hzm : bits.toNat % 8388608 = 0 <;>
    by_cases hs : bits.toNat / 2147483648 = 0 <;>
    dsimp +instances only [decodeC, decode32, classify, fp32,
      Option.map, Term.denormalized, classifyNat] <;>
    simp only [beq_iff_eq, BitVec.toNat_eq, he, hm] <;>
    simp_all [Classification.finite, BitVec.toNat_add, fp32_sign,
      bne_iff_ne] <;> omega

end TensorCore.Datapath
