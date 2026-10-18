import TensorCore.Scalar.LeanRounding
import TensorCore.Scalar.Compatibility
import Init.Data.Float

/-! Bridge between FP32 words and Lean Float32. -/

namespace TensorCore.IEEE.LeanBridge

set_option maxRecDepth 4096

open Float.Model.UnpackedFloat

/-- Lean's representation permits every non-NaN encoding and one canonical NaN. -/
abbrev Native32Valid (bits : F32) : Prop := Float.Model.Format.binary32.Valid bits

/-- No arithmetic or rounding occurs in this adapter; the proof guards Lean's canonical-NaN representation invariant. -/
def toNative32 (bits : F32) (h : Native32Valid bits) : Float32 :=
  .ofModel ⟨UInt32.ofBitVec bits, h⟩

def fromNative32 (x : Float32) : F32 := x.toBits.toBitVec

theorem from_toNative32 (bits : F32) (h : Native32Valid bits) :
    fromNative32 (toNative32 bits h) = bits := rfl

theorem to_fromNative32 (x : Float32) :
    toNative32 (fromNative32 x) x.toModel.valid = x := rfl

def sign32 (a : F32) : Bool := a.toNat / 2147483648 != 0

def nativeSign (negative : Bool) : Sign := if negative then .negative else .positive

theorem unpackExponent32_toNat (a : F32) :
    (unpackExponent (spec := Float.Model.Format.binary32) a).toNat = a.toNat / 8388608 % 256 := by
  simp only [unpackExponent, BitVec.toNat_cast, BitVec.extractLsb, BitVec.extractLsb', BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow]

theorem unpackMantissa32_toNat (a : F32) :
    (unpackMantissa (spec := Float.Model.Format.binary32) a).toNat = a.toNat % 8388608 := by
  simp only [unpackMantissa, BitVec.toNat_cast, BitVec.extractLsb, BitVec.extractLsb', BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow]
  simp

theorem unpackSign32_eq (a : F32) :
    Sign.ofBitVec (unpackSign (spec := Float.Model.Format.binary32) a) = nativeSign (sign32 a) := by
  have hs : (unpackSign (spec := Float.Model.Format.binary32) a).toNat = a.toNat / 2147483648 := by
    simp only [unpackSign, BitVec.toNat_cast, BitVec.extractLsb, BitVec.extractLsb', BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow]
    have ha := a.isLt
    change a.toNat / 2147483648 % 2 = a.toNat / 2147483648
    omega
  have hz : unpackSign (spec := Float.Model.Format.binary32) a = 0 ↔ a.toNat / 2147483648 = 0 := by
    constructor
    · intro h
      have h' := congrArg BitVec.toNat h
      rw [hs] at h'
      exact h'
    · intro h
      apply BitVec.eq_of_toNat_eq
      rw [hs, h]
      rfl
  unfold Sign.ofBitVec nativeSign
  change (if _ = 0 then Sign.positive else Sign.negative) =
    (if (a.toNat / 2147483648 != 0) = true then Sign.negative else Sign.positive)
  by_cases h : a.toNat / 2147483648 = 0
  · rw [if_pos (hz.mpr h)]
    simp [h]
  · rw [if_neg (fun h' => h (hz.mp h'))]
    simp [h]

/-- Finite exponent fields satisfy Lean's representation invariant directly. -/
theorem native32Valid_finite (a : F32) (h : a.toNat / 8388608 % 256 < 255) : Native32Valid a := by
  constructor
  intro he _
  have hnat := congrArg BitVec.toNat he
  rw [unpackExponent32_toNat] at hnat
  change a.toNat / 8388608 % 256 = 255 at hnat
  omega

def mantissa32 (a : F32) : ℕ :=
  if a.toNat / 8388608 % 256 = 0 then a.toNat % 8388608 else 8388608 + a.toNat % 8388608

def exponent32 (a : F32) : ℤ :=
  if a.toNat / 8388608 % 256 = 0 then -149 else (a.toNat / 8388608 % 256 : ℤ) - 150

def NonzeroFinite32 (a : F32) : Prop := a.toNat / 8388608 % 256 < 255 ∧ 0 < mantissa32 a

instance (a : F32) : Decidable (NonzeroFinite32 a) := inferInstanceAs (Decidable (_ ∧ _))

theorem unpack32_nonzero (a : F32) (h : NonzeroFinite32 a) :
    unpack Float.Model.Format.binary32 a =
      .finite (nativeSign (sign32 a)) (mantissa32 a) (exponent32 a) h.2 := by
  have heMax : unpackExponent (spec := Float.Model.Format.binary32) a ≠ -1#8 := by
    intro he
    have hn := congrArg BitVec.toNat he
    rw [unpackExponent32_toNat] at hn
    change a.toNat / 8388608 % 256 = 255 at hn
    have := h.1
    omega
  have heZero : unpackExponent (spec := Float.Model.Format.binary32) a = 0#8 ↔
      a.toNat / 8388608 % 256 = 0 := by
    constructor
    · intro he
      have hn := congrArg BitVec.toNat he
      rw [unpackExponent32_toNat] at hn
      exact hn
    · intro he
      apply BitVec.eq_of_toNat_eq
      rw [unpackExponent32_toNat, he]
      rfl
  have hcat : (1#1 ++ unpackMantissa (spec := Float.Model.Format.binary32) a).toNat =
      8388608 + a.toNat % 8388608 := by
    rw [BitVec.toNat_append,
      ← Nat.shiftLeft_add_eq_or_of_lt (unpackMantissa (spec := Float.Model.Format.binary32) a).isLt,
      unpackMantissa32_toNat, Nat.shiftLeft_eq]
    rfl
  unfold unpack
  dsimp only
  rw [if_neg heMax]
  by_cases hz : a.toNat / 8388608 % 256 = 0
  · have hmZero : unpackMantissa (spec := Float.Model.Format.binary32) a ≠ 0#23 := by
      intro he
      have hn := congrArg BitVec.toNat he
      rw [unpackMantissa32_toNat] at hn
      have hm := h.2
      simp only [mantissa32, hz, ↓reduceIte] at hm
      change a.toNat % 8388608 = 0 at hn
      omega
    rw [if_pos (heZero.mpr hz), dif_neg hmZero]
    simp only [unpackSign32_eq, unpackMantissa32_toNat, unpackExponent32_toNat,
      mantissa32, exponent32, hz, ↓reduceIte]
    rfl
  · rw [if_neg (fun he => hz (heZero.mp he))]
    simp only [unpackSign32_eq, unpackExponent32_toNat, hcat,
      mantissa32, exponent32, hz, ↓reduceIte]
    rfl

theorem decode32_nonzero (a : F32) (h : NonzeroFinite32 a) :
    decode .fp32 a = .finite (sign32 a)
      ((nativeSign (sign32 a) |>.apply (mantissa32 a) : ℤ) * pow2 (exponent32 a)) := by
  have heMax : a.toNat / 8388608 % 256 ≠ 255 := by have := h.1; omega
  by_cases he : a.toNat / 8388608 % 256 = 0
  · have hm : a.toNat % 8388608 ≠ 0 := by
      have := h.2
      simp only [mantissa32, he, ↓reduceIte] at this
      omega
    simp [decode, classify, classifyNat, BinaryFormat.layout, fp32, he, hm,
      mantissa32, exponent32, sign, binarySign, sign32, nativeSign, Sign.apply, Decoded.value]
    split <;> rfl
  · simp [decode, classify, classifyNat, BinaryFormat.layout, fp32, heMax, he,
      mantissa32, exponent32, sign, binarySign, sign32, nativeSign, Sign.apply, Decoded.value]
    by_cases hs : 2147483648 ≤ a.toNat <;> simp only [hs, ↓reduceIte]
    all_goals congr 2 <;> omega

theorem packComponents32_eq (negative : Bool) (e : BitVec 8) (m : BitVec 23) :
    packComponents Float.Model.Format.binary32 (nativeSign negative) e m =
      BitVec.ofNat 32 ((if negative then 2 ^ 31 else 0) + e.toNat * 2 ^ 23 + m.toNat) := by
  have appendNat {n k : ℕ} (a : BitVec n) (b : BitVec k) :
      (a ++ b).toNat = a.toNat * 2 ^ k + b.toNat := by
    rw [BitVec.toNat_append, ← Nat.shiftLeft_add_eq_or_of_lt b.isLt, Nat.shiftLeft_eq]
  change (nativeSign negative).toBitVec ++ e ++ m = BitVec.ofNat 32 _
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ofNat]
  cases negative <;>
    simp only [nativeSign, Bool.false_eq_true, ↓reduceIte,
      Sign.toBitVec, appendNat, BitVec.toNat_ofNat]
  all_goals omega

theorem packZero32_eq (negative : Bool) :
    pack Float.Model.Format.binary32 (.zero (nativeSign negative)) = zero .fp32 negative := by
  rw [pack, packedZero, packComponents32_eq]
  cases negative <;> rfl

theorem encodeZero32_eq (negative : Bool) (e : ℤ) :
    encodeBinary fp32 negative e 0 = zero .fp32 negative := by
  change BitVec.ofNat 32 ((if negative then 2147483648 else 0) + 0) = _
  cases negative <;> rfl

/-- Once normalization has produced a bounded coefficient, the two output encoders agree bit for bit. -/
theorem packFinite32_eq (negative : Bool) (e : ℤ) (k : ℕ)
    (hk : 0 < k) (hu : k < 2 ^ 24) (he : -126 ≤ e) (he' : e ≤ 127) :
    pack Float.Model.Format.binary32 (.finite (nativeSign negative) k (e - 23) hk) =
      encodeBinary fp32 negative e (k : ℤ) := by
  have hb : e - 23 + 127 + 23 = e + 127 := by omega
  have hlo : (e + 127).toNat ≤ 254 := by omega
  have hn : k.log2 + 1 = 24 ↔ 2 ^ 23 ≤ k := by
    have hlog := Nat.log2_eq_iff (show k ≠ 0 by omega) (k := 23)
    omega
  change (if 256 ≤ (e - 23 + 127 + 23).toNat + 1 then
    packedInfinity Float.Model.Format.binary32 (nativeSign negative)
    else if k.log2 + 1 = 24 then
      packComponents Float.Model.Format.binary32 (nativeSign negative)
        (BitVec.ofNat 8 (e - 23 + 127 + 23).toNat) (BitVec.ofNat 23 k)
    else packComponents Float.Model.Format.binary32 (nativeSign negative)
        0 (BitVec.ofNat 23 k)) = _
  rw [hb]
  rw [if_neg (by omega)]
  by_cases hnormal : 2 ^ 23 ≤ k
  · rw [if_pos (hn.mpr hnormal), packComponents32_eq]
    change BitVec.ofNat 32 ((if negative then 2147483648 else 0) +
      ((e + 127).toNat % 256) * 8388608 + k % 8388608) =
      BitVec.ofNat 32 ((if negative then 2147483648 else 0) +
        (if (k : ℤ) < 8388608 then k else
          (e + 127).toNat * 8388608 + ((k : ℤ) - 8388608).toNat))
    rw [if_neg (show ¬ (k : ℤ) < 8388608 from by omega)]
    congr 1
    omega
  · rw [if_neg (fun h => hnormal (hn.mp h)), packComponents32_eq]
    change BitVec.ofNat 32 ((if negative then 2147483648 else 0) +
      0 * 8388608 + k % 8388608) =
      BitVec.ofNat 32 ((if negative then 2147483648 else 0) +
        (if (k : ℤ) < 8388608 then k else
          (e + 127).toNat * 8388608 + ((k : ℤ) - 8388608).toNat))
    rw [if_pos (show (k : ℤ) < 8388608 from by omega)]
    congr 1
    omega

/-- Complete agreement of normalization and packing on the finite reference domain. -/
theorem packRound32_eq (negative : Bool) (m : ℕ) (e : ℤ) (hm : 0 < m)
    (hr : (m : ℚ) * pow2 e ≤ fp32.maxFinite) :
    let x := (m : ℚ) * pow2 e
    let E := binaryNormExp fp32 x
    let K := rneInt (x / pow2 (E - 23))
    pack Float.Model.Format.binary32
      (Float.Model.UnpackedFloat.round Float.Model.Format.binary32 (nativeSign negative) m e) =
        encodeBinary fp32 negative (binaryCarry fp32 E K).1 (binaryCarry fp32 E K).2 := by
  intro x E K
  let q := Float.Model.Format.binary32.targetExponent (Float.Model.totalExponent m e)
  let d := decreaseExponent m e q
  let first := shiftToTargetExponent Float.Model.Format.binary32 d.1 d.2 .exact
  let k := first.1.roundedMantissa
  have hf : first.2 = q ∧ (k : ℤ) = rneInt (x / pow2 q) := firstPass32 m e hm
  have hq : q = E - 23 := targetExponent32_eq m e hm
  have hk : (k : ℤ) = K := by simpa only [hq] using hf.2
  have hx : 0 < x := Rat.mul_pos (Rat.natCast_pos.mpr hm) (pow2_pos e)
  have he := binaryNormExp_bounds fp32 (by decide) x hx hr
  have hb := binaryRoundedCoeff_bounds fp32 (by decide) .nearestEven negative x hx hr
  change 0 ≤ K ∧ K ≤ 16777216 ∧ (8388608 ≤ K ∨ E = -126) ∧
    (E = 127 → K ≤ 16777215) at hb
  have hEl : -126 ≤ E := he.1
  have hEu : E ≤ 127 := he.2.1
  have hku : k ≤ 2 ^ 24 := by omega
  have hql : -149 ≤ q := by omega
  change pack Float.Model.Format.binary32
    (if h : (shiftToTargetExponent Float.Model.Format.binary32 k first.2 .exact).1.mantissa = 0 then
      .zero (nativeSign negative)
    else .finite (nativeSign negative)
      (shiftToTargetExponent Float.Model.Format.binary32 k first.2 .exact).1.mantissa
      (shiftToTargetExponent Float.Model.Format.binary32 k first.2 .exact).2
      (Nat.pos_of_ne_zero h)) = _
  rw [hf.1, secondPass32 k q hku hql]
  by_cases hc : k = 2 ^ 24
  · have hK : K = 16777216 := by omega
    have hE : E + 1 ≤ 127 := by omega
    rw [if_pos hc]
    simp only [show (2 ^ 23 : ℕ) ≠ 0 from by decide, ↓reduceDIte]
    rw [show q + 1 = (E + 1) - 23 from by omega]
    rw [packFinite32_eq negative (E + 1) (2 ^ 23) (by decide) (by decide) (by omega) hE]
    simp only [binaryCarry, fp32, hK]
    rfl
  · rw [if_neg hc]
    have hK : K ≠ 16777216 := by omega
    have hcarry : binaryCarry fp32 E K = (E, K) := by
      change (if K = 16777216 then _ else _) = _
      rw [if_neg hK]
    rw [hcarry]
    by_cases hz : k = 0
    · rw [dif_pos hz, packZero32_eq]
      have hK0 : K = 0 := by omega
      rw [hK0]
      exact (encodeZero32_eq negative E).symm
    · rw [dif_neg hz, hq]
      rw [packFinite32_eq negative E k (by omega) (by omega) hEl hEu, hk]

theorem finiteBits32_encode (x : ℚ) (hx : x ≠ 0) (hr : absQ x ≤ fp32.maxFinite) :
    finiteBits .fp32 .nearestEven x hr =
      let E := binaryNormExp fp32 (absQ x)
      let K := rneInt (absQ x / pow2 (E - 23))
      encodeBinary fp32 (decide (x < 0)) (binaryCarry fp32 E K).1 (binaryCarry fp32 E K).2 := by
  have h := finiteBits_eq .fp32 .nearestEven x hr
  change roundBinary fp32 .nearestEven x = some _ at h
  unfold roundBinary at h
  rw [if_neg (by decide : ¬ ¬ fp32.WellFormed), if_neg (Rat.not_lt.mpr hr), if_neg hx] at h
  dsimp only at h ⊢
  simp only [binaryCoefficient, show fp32.mantissaBits = 23 from rfl] at h
  generalize hc : binaryCarry fp32 (binaryNormExp fp32 (absQ x))
    (rneInt (absQ x / pow2 (binaryNormExp fp32 (absQ x) - 23))) = c at h ⊢
  rcases c with ⟨E, K⟩
  change (if E > fp32.emax then none else some (encodeBinary fp32 (decide (x < 0)) E K)) = some _ at h
  split at h
  · contradiction
  · exact (Option.some.inj h).symm

theorem packRound32_reference (negative : Bool) (m : ℕ) (e : ℤ) (hm : 0 < m)
    (tinyMode : Tininess) (hr : (m : ℚ) * pow2 e ≤ fp32.maxFinite) :
    pack Float.Model.Format.binary32
      (Float.Model.UnpackedFloat.round Float.Model.Format.binary32 (nativeSign negative) m e) =
      (TensorCore.IEEE.round .fp32 ⟨.nearestEven, tinyMode⟩ negative
        (if negative then -((m : ℚ) * pow2 e) else (m : ℚ) * pow2 e)).bits := by
  have hx : 0 < (m : ℚ) * pow2 e := Rat.mul_pos (Rat.natCast_pos.mpr hm) (pow2_pos e)
  have habs : absQ ((m : ℚ) * pow2 e) = (m : ℚ) * pow2 e := absQ_of_nonneg (Rat.le_of_lt hx)
  have hnabs : absQ (-((m : ℚ) * pow2 e)) = (m : ℚ) * pow2 e := by rw [absQ_neg, habs]
  have hne : (m : ℚ) * pow2 e ≠ 0 := Rat.ne_of_gt hx
  have hnne : -((m : ℚ) * pow2 e) ≠ 0 := by grind
  have hneg : -((m : ℚ) * pow2 e) < 0 := by grind
  have hnneg : ¬ (m : ℚ) * pow2 e < 0 := by grind
  rw [packRound32_eq negative m e hm hr]
  cases negative <;>
    simp only [Bool.false_eq_true, ↓reduceIte, TensorCore.IEEE.round,
      BinaryFormat.layout, hne, hnne, habs, hnabs, hr, ↓reduceDIte] <;>
    rw [finiteBits32_encode _ (by assumption) (by simpa only [habs, hnabs] using hr)] <;>
    simp only [habs, hnabs, hneg, hnneg, decide_true, decide_false]

theorem packNormalize32_reference (m : ℤ) (e : ℤ) (tinyMode : Tininess)
    (hr : absQ ((m : ℚ) * pow2 e) ≤ fp32.maxFinite) :
    pack Float.Model.Format.binary32
      (normalize Float.Model.Format.binary32 m e .positive) =
      (TensorCore.IEEE.round .fp32 ⟨.nearestEven, tinyMode⟩ false
        ((m : ℚ) * pow2 e)).bits := by
  by_cases hz : m = 0
  · subst m
    rw [show (normalize Float.Model.Format.binary32 0 e .positive) = .zero .positive from rfl]
    simp only [Rat.intCast_zero, Rat.zero_mul, round_zero]
    exact packZero32_eq false
  by_cases hn : m < 0
  · have hm : 0 < (-m).toNat := by omega
    have hcast : (((-m).toNat : ℕ) : ℚ) = -(m : ℚ) := by
      rw [← Rat.intCast_natCast, Int.toNat_of_nonneg (by omega), Rat.intCast_neg]
    have hvalue : ((m : ℚ) * pow2 e) = -((((-m).toNat : ℕ) : ℚ) * pow2 e) := by
      rw [hcast]; grind
    have hp : 0 < (((-m).toNat : ℕ) : ℚ) * pow2 e :=
      Rat.mul_pos (Rat.natCast_pos.mpr hm) (pow2_pos e)
    have hrange : (((-m).toNat : ℕ) : ℚ) * pow2 e ≤ fp32.maxFinite := by
      simpa only [hvalue, absQ_neg, absQ_of_nonneg (Rat.le_of_lt hp)] using hr
    have h := packRound32_reference true (-m).toNat e hm tinyMode hrange
    simp only [nativeSign, ↓reduceIte] at h
    rw [normalize, Int.compare_eq_lt.mpr hn]
    rw [h]
    rw [hvalue]
    have hne : -((((-m).toNat : ℕ) : ℚ) * pow2 e) ≠ 0 := by grind
    simp only [TensorCore.IEEE.round, hne, ↓reduceIte]
    rfl
  · have hm : 0 < m.toNat := by omega
    have hcast : ((m.toNat : ℕ) : ℚ) = (m : ℚ) := by
      rw [← Rat.intCast_natCast, Int.toNat_of_nonneg (by omega)]
    have hp : 0 < (m : ℚ) * pow2 e := by
      rw [← hcast]
      exact Rat.mul_pos (Rat.natCast_pos.mpr hm) (pow2_pos e)
    have hrange : ((m.toNat : ℕ) : ℚ) * pow2 e ≤ fp32.maxFinite := by
      simpa only [hcast, absQ_of_nonneg (Rat.le_of_lt hp)] using hr
    have h := packRound32_reference false m.toNat e hm tinyMode hrange
    simp only [nativeSign, Bool.false_eq_true, ↓reduceIte, hcast] at h
    rw [normalize, Int.compare_eq_gt.mpr (by omega)]
    exact h

def finiteValue32 (a : F32) : ℚ :=
  (nativeSign (sign32 a) |>.apply (mantissa32 a) : ℤ) * pow2 (exponent32 a)

theorem aligned_add_value (sa sb : Sign) (ma mb : ℕ) (ea eb : ℤ) :
    let q := min ea eb
    let m := sa.apply (decreaseExponent ma ea q).1 + sb.apply (decreaseExponent mb eb q).1
    (m : ℚ) * pow2 q = (sa.apply ma : ℚ) * pow2 ea + (sb.apply mb : ℚ) * pow2 eb := by
  intro q m
  have hea : (decreaseExponent ma ea q).2 = q := by
    dsimp [decreaseExponent, q]
    omega
  have heb : (decreaseExponent mb eb q).2 = q := by
    dsimp [decreaseExponent, q]
    omega
  have ha := decreaseExponent_value ma ea q
  have hb := decreaseExponent_value mb eb q
  rw [hea] at ha
  rw [heb] at hb
  dsimp only [m]
  cases sa <;> cases sb <;>
    simp only [Sign.apply, Rat.intCast_add, Rat.intCast_neg, Rat.intCast_natCast] <;> grind

def nativeAdd32 (a b : F32) (ha : Native32Valid a) (hb : Native32Valid b) : F32 :=
  fromNative32 (toNative32 a ha + toNative32 b hb)

/-- Every nonzero finite pair with an in-range exact sum agrees bit for bit. -/
theorem nativeAdd32_reference (a b : F32) (ha : NonzeroFinite32 a) (hb : NonzeroFinite32 b)
    (tinyMode : Tininess) (hr : absQ (finiteValue32 a + finiteValue32 b) ≤ fp32.maxFinite) :
    nativeAdd32 a b (native32Valid_finite a ha.1) (native32Valid_finite b hb.1) =
      (TensorCore.IEEE.add .fp32 ⟨.nearestEven, tinyMode⟩ a b).bits := by
  change pack Float.Model.Format.binary32
    (Float.Model.UnpackedFloat.add Float.Model.Format.binary32
      (unpack Float.Model.Format.binary32 a) (unpack Float.Model.Format.binary32 b)) = _
  rw [unpack32_nonzero a ha, unpack32_nonzero b hb]
  simp only [Float.Model.UnpackedFloat.add]
  have hv := aligned_add_value (nativeSign (sign32 a)) (nativeSign (sign32 b))
    (mantissa32 a) (mantissa32 b) (exponent32 a) (exponent32 b)
  have hround := packNormalize32_reference
    ((nativeSign (sign32 a)).apply
      (decreaseExponent (mantissa32 a) (exponent32 a) (min (exponent32 a) (exponent32 b))).1 +
     (nativeSign (sign32 b)).apply
      (decreaseExponent (mantissa32 b) (exponent32 b) (min (exponent32 a) (exponent32 b))).1)
    (min (exponent32 a) (exponent32 b)) tinyMode (by simpa only [hv, finiteValue32] using hr)
  rw [hround, hv]
  change (TensorCore.IEEE.round .fp32 ⟨.nearestEven, tinyMode⟩ false
      (finiteValue32 a + finiteValue32 b)).bits =
    (addDatum .fp32 ⟨.nearestEven, tinyMode⟩ (decode .fp32 a) (decode .fp32 b)).bits
  rw [decode32_nonzero a ha, decode32_nonzero b hb]
  change (TensorCore.IEEE.round .fp32 ⟨.nearestEven, tinyMode⟩ false
    (finiteValue32 a + finiteValue32 b)).bits =
      (TensorCore.IEEE.round .fp32 ⟨.nearestEven, tinyMode⟩
        (sumZeroSign .nearestEven (sign32 a) (sign32 b))
        (finiteValue32 a + finiteValue32 b)).bits
  cases sa : sign32 a <;> cases sb : sign32 b
  all_goals try rfl
  have hpa : 0 < (mantissa32 a : ℚ) * pow2 (exponent32 a) :=
    Rat.mul_pos (Rat.natCast_pos.mpr ha.2) (pow2_pos _)
  have hpb : 0 < (mantissa32 b : ℚ) * pow2 (exponent32 b) :=
    Rat.mul_pos (Rat.natCast_pos.mpr hb.2) (pow2_pos _)
  have hne : finiteValue32 a + finiteValue32 b ≠ 0 := by
    simp only [finiteValue32, sa, sb, nativeSign, ↓reduceIte, Sign.apply,
      Rat.intCast_neg, Rat.intCast_natCast]
    grind
  simp only [TensorCore.IEEE.round, hne, ↓reduceIte]

theorem aligned_sub_value (sa sb : Sign) (ma mb : ℕ) (ea eb : ℤ) :
    let q := min ea eb
    let m := sa.apply (decreaseExponent ma ea q).1 - sb.apply (decreaseExponent mb eb q).1
    (m : ℚ) * pow2 q = (sa.apply ma : ℚ) * pow2 ea - (sb.apply mb : ℚ) * pow2 eb := by
  intro q m
  have hea : (decreaseExponent ma ea q).2 = q := by
    dsimp [decreaseExponent, q]
    omega
  have heb : (decreaseExponent mb eb q).2 = q := by
    dsimp [decreaseExponent, q]
    omega
  have ha := decreaseExponent_value ma ea q
  have hb := decreaseExponent_value mb eb q
  rw [hea] at ha
  rw [heb] at hb
  dsimp only [m]
  cases sa <;> cases sb <;>
    simp only [Sign.apply, Rat.intCast_sub, Rat.intCast_neg, Rat.intCast_natCast] <;> grind

def nativeSub32 (a b : F32) (ha : Native32Valid a) (hb : Native32Valid b) : F32 :=
  fromNative32 (toNative32 a ha - toNative32 b hb)

/-- Every nonzero finite pair with an in-range exact difference agrees bit for bit. -/
theorem nativeSub32_reference (a b : F32) (ha : NonzeroFinite32 a) (hb : NonzeroFinite32 b)
    (tinyMode : Tininess) (hr : absQ (finiteValue32 a - finiteValue32 b) ≤ fp32.maxFinite) :
    nativeSub32 a b (native32Valid_finite a ha.1) (native32Valid_finite b hb.1) =
      (TensorCore.IEEE.sub .fp32 ⟨.nearestEven, tinyMode⟩ a b).bits := by
  change pack Float.Model.Format.binary32
    (Float.Model.UnpackedFloat.sub Float.Model.Format.binary32
      (unpack Float.Model.Format.binary32 a) (unpack Float.Model.Format.binary32 b)) = _
  rw [unpack32_nonzero a ha, unpack32_nonzero b hb]
  simp only [Float.Model.UnpackedFloat.sub]
  have hv := aligned_sub_value (nativeSign (sign32 a)) (nativeSign (sign32 b))
    (mantissa32 a) (mantissa32 b) (exponent32 a) (exponent32 b)
  have hround := packNormalize32_reference
    ((nativeSign (sign32 a)).apply
      (decreaseExponent (mantissa32 a) (exponent32 a) (min (exponent32 a) (exponent32 b))).1 -
     (nativeSign (sign32 b)).apply
      (decreaseExponent (mantissa32 b) (exponent32 b) (min (exponent32 a) (exponent32 b))).1)
    (min (exponent32 a) (exponent32 b)) tinyMode (by simpa only [hv, finiteValue32] using hr)
  rw [hround, hv]
  change (TensorCore.IEEE.round .fp32 ⟨.nearestEven, tinyMode⟩ false
      (finiteValue32 a - finiteValue32 b)).bits =
    (addDatum .fp32 ⟨.nearestEven, tinyMode⟩ (decode .fp32 a) (decode .fp32 b).negate).bits
  rw [decode32_nonzero a ha, decode32_nonzero b hb]
  simp only [Datum.negate, addDatum, Datum.isNaN, Bool.false_or, Bool.false_eq_true, ↓reduceIte]
  rw [← Rat.sub_eq_add_neg]
  change (TensorCore.IEEE.round .fp32 ⟨.nearestEven, tinyMode⟩ false
    (finiteValue32 a - finiteValue32 b)).bits =
      (TensorCore.IEEE.round .fp32 ⟨.nearestEven, tinyMode⟩
        (sumZeroSign .nearestEven (sign32 a) (!(sign32 b)))
        (finiteValue32 a - finiteValue32 b)).bits
  cases sa : sign32 a <;> cases sb : sign32 b
  all_goals try rfl
  have hpa : 0 < (mantissa32 a : ℚ) * pow2 (exponent32 a) :=
    Rat.mul_pos (Rat.natCast_pos.mpr ha.2) (pow2_pos _)
  have hpb : 0 < (mantissa32 b : ℚ) * pow2 (exponent32 b) :=
    Rat.mul_pos (Rat.natCast_pos.mpr hb.2) (pow2_pos _)
  have hne : finiteValue32 a - finiteValue32 b ≠ 0 := by
    simp only [finiteValue32, sa, sb, nativeSign, Bool.false_eq_true, ↓reduceIte, Sign.apply,
      Rat.intCast_neg, Rat.intCast_natCast]
    grind
  simp only [TensorCore.IEEE.round, hne, ↓reduceIte]

theorem nativeSign_mul (a b : Bool) : nativeSign a * nativeSign b = nativeSign (xor a b) := by
  cases a <;> cases b <;> rfl

theorem mantissa32_normal_or_min (a : F32) :
    2 ^ 23 ≤ mantissa32 a ∨ exponent32 a = -149 := by
  by_cases h : a.toNat / 8388608 % 256 = 0
  · exact Or.inr (by simp [exponent32, h])
  · left
    simp only [mantissa32, h, ↓reduceIte]
    omega

theorem product32_no_leftshift (a b : F32) (ha : NonzeroFinite32 a) (hb : NonzeroFinite32 b) :
    exponent32 a + exponent32 b ≤ Float.Model.Format.binary32.targetExponent
      (Float.Model.totalExponent (mantissa32 a * mantissa32 b) (exponent32 a + exponent32 b)) := by
  have hp : 0 < mantissa32 a * mantissa32 b := Nat.mul_pos ha.2 hb.2
  have hma : mantissa32 a ≤ mantissa32 a * mantissa32 b := by
    have hh := Nat.mul_le_mul_left (mantissa32 a) (show 1 ≤ mantissa32 b by have := hb.2; omega)
    simpa using hh
  have hmb : mantissa32 b ≤ mantissa32 a * mantissa32 b := by
    have hh := Nat.mul_le_mul_right (mantissa32 b) (show 1 ≤ mantissa32 a by have := ha.2; omega)
    simpa using hh
  change exponent32 a + exponent32 b ≤
    max ((mantissa32 a * mantissa32 b).log2 + 1 + (exponent32 a + exponent32 b) - 24) (-149 : ℤ)
  rcases mantissa32_normal_or_min a with h | h
  · have hl := (Nat.le_log2 (show mantissa32 a * mantissa32 b ≠ 0 by omega)).mpr (Nat.le_trans h hma)
    omega
  · rcases mantissa32_normal_or_min b with h' | h'
    · have hl := (Nat.le_log2 (show mantissa32 a * mantissa32 b ≠ 0 by omega)).mpr (Nat.le_trans h' hmb)
      omega
    · omega

theorem roundWithAccuracy_eq_round32 (s : Sign) (m : ℕ) (e : ℤ)
    (h : e ≤ Float.Model.Format.binary32.targetExponent (Float.Model.totalExponent m e)) :
    roundWithAccuracy Float.Model.Format.binary32 s m e .exact =
      Float.Model.UnpackedFloat.round Float.Model.Format.binary32 s m e := by
  have hn : (e - Float.Model.Format.binary32.targetExponent (Float.Model.totalExponent m e)).toNat = 0 := by omega
  simp [Float.Model.UnpackedFloat.round, decreaseExponent, hn]

theorem finiteValue32_mul (a b : F32) :
    finiteValue32 a * finiteValue32 b =
      if xor (sign32 a) (sign32 b) then
        -(((mantissa32 a * mantissa32 b : ℕ) : ℚ) * pow2 (exponent32 a + exponent32 b))
      else ((mantissa32 a * mantissa32 b : ℕ) : ℚ) * pow2 (exponent32 a + exponent32 b) := by
  cases sa : sign32 a <;> cases sb : sign32 b <;>
    simp only [finiteValue32, sa, sb, nativeSign, Bool.false_eq_true, ↓reduceIte,
      Sign.apply, Rat.intCast_neg, Rat.intCast_natCast, Rat.natCast_mul, pow2_add,
      Bool.false_xor, Bool.true_xor, Bool.not_false, Bool.not_true] <;> grind

def nativeMul32 (a b : F32) (ha : Native32Valid a) (hb : Native32Valid b) : F32 :=
  fromNative32 (toNative32 a ha * toNative32 b hb)

theorem nativeMul32_reference (a b : F32) (ha : NonzeroFinite32 a) (hb : NonzeroFinite32 b)
    (tinyMode : Tininess) (hr : absQ (finiteValue32 a * finiteValue32 b) ≤ fp32.maxFinite) :
    nativeMul32 a b (native32Valid_finite a ha.1) (native32Valid_finite b hb.1) =
      (TensorCore.IEEE.mul .fp32 ⟨.nearestEven, tinyMode⟩ a b).bits := by
  have hm := Nat.mul_pos ha.2 hb.2
  have hp : 0 < ((mantissa32 a * mantissa32 b : ℕ) : ℚ) * pow2 (exponent32 a + exponent32 b) :=
    Rat.mul_pos (Rat.natCast_pos.mpr hm) (pow2_pos _)
  have hrange : ((mantissa32 a * mantissa32 b : ℕ) : ℚ) *
      pow2 (exponent32 a + exponent32 b) ≤ fp32.maxFinite := by
    rw [finiteValue32_mul] at hr
    split at hr <;> simpa only [absQ_neg, absQ_of_nonneg (Rat.le_of_lt hp)] using hr
  change pack Float.Model.Format.binary32
    (Float.Model.UnpackedFloat.mul Float.Model.Format.binary32
      (unpack Float.Model.Format.binary32 a) (unpack Float.Model.Format.binary32 b)) = _
  rw [unpack32_nonzero a ha, unpack32_nonzero b hb]
  simp only [Float.Model.UnpackedFloat.mul]
  rw [nativeSign_mul, roundWithAccuracy_eq_round32 _ _ _ (product32_no_leftshift a b ha hb),
    packRound32_reference _ _ _ hm tinyMode hrange, ← finiteValue32_mul]
  change (round .fp32 ⟨.nearestEven, tinyMode⟩ (xor (sign32 a) (sign32 b))
    (finiteValue32 a * finiteValue32 b)).bits =
      (mulDatum .fp32 ⟨.nearestEven, tinyMode⟩ (decode .fp32 a) (decode .fp32 b)).bits
  rw [decode32_nonzero a ha, decode32_nonzero b hb]
  rfl

end TensorCore.IEEE.LeanBridge
