import MCFloat.Equivalence.Base
import FloatLib.Floats.Formats.BinaryInterchange.DirectedSemantics.Rational.RoundingSemantics.Executable
import FloatLib.Floats.Formats.BinaryInterchange.DirectedSemantics.Rational.Scaling

/-! # `fl{·}`: FloatLib's FP32 rounding is `MatrixCore`'s `fl32`

FloatLib's round-to-nearest-even word is the `rne32` word, with `±∞` exactly where `rne32`
overflows. -/

set_option maxRecDepth 4096
set_option maxHeartbeats 1600000

namespace MCFloat.Equivalence
open FloatLib.Floats.Formats.BinaryInterchange
open FloatLib.Numerics

/-! ## Quotients -/

theorem rneInt_real (x : ℚ) :
    MatrixCore.rneInt x = FloatLib.Floats.Formats.Flocq.nearestEven (x : ℝ) := by
  have hf : (⌊(x : ℝ)⌋ : ℤ) = x.floor := Rat.floor_cast x
  have hc : ((x - (x.floor : ℚ) : ℚ) : ℝ) = (x : ℝ) - x.floor := by simp
  have hl : (x : ℝ) - x.floor < 1 / 2 ↔ 2 * (x - (x.floor : ℚ)) < 1 := by
    rw [← hc, ← Rat.cast_one, ← Rat.cast_ofNat (n := 2), ← Rat.cast_div, Rat.cast_lt]
    constructor <;> intro h <;> linarith
  have hg : (1 : ℝ) / 2 < (x : ℝ) - x.floor ↔ 1 < 2 * (x - (x.floor : ℚ)) := by
    rw [← hc, ← Rat.cast_one, ← Rat.cast_ofNat (n := 2), ← Rat.cast_div, Rat.cast_lt]
    constructor <;> intro h <;> linarith
  unfold MatrixCore.rneInt FloatLib.Floats.Formats.Flocq.nearestEven
  simp only [hf]
  simp only [hl, hg, Int.even_iff]
  split_ifs <;> grind

theorem quotient_rne (n d : ℕ) (hd : d ≠ 0) :
    (roundQuotientEven n d : ℤ) = MatrixCore.rneInt ((n : ℚ) / d) := by
  rw [rneInt_real]
  simpa using (Model.nearestEven_div_eq_roundQuotientEven n d hd).symm

theorem scale_ratio (n d : ℕ) (e : ℤ) :
    ((RationalBinary.scaleByPowerOfTwo n d e).1 : ℚ) /
        (RationalBinary.scaleByPowerOfTwo n d e).2 = (n : ℚ) / d * MCFloat.pow2 e := by
  apply Rat.cast_injective (α := ℝ)
  simpa [MCFloat.pow2, Model.scaledRatToReal, Model.bpow, FloatLib.Floats.Formats.Flocq.bpow,
    binaryRadix, Radix.toReal] using Model.scaleByPowerOfTwo_real n d e

theorem scaled_rne (x : ℚ) (g : ℤ) :
    (roundQuotientEven (RationalBinary.scaleByPowerOfTwo x.num.natAbs x.den (-g)).1
      (RationalBinary.scaleByPowerOfTwo x.num.natAbs x.den (-g)).2 : ℤ) =
      MatrixCore.rneInt (|x| / MCFloat.pow2 g) := by
  have hd := RationalBinary.scaleByPowerOfTwo_snd_ne_zero x.num.natAbs x.den (-g) x.den_nz
  rw [quotient_rne _ _ hd, scale_ratio, abs_ratio]
  congr 1
  simp [MCFloat.pow2, zpow_neg, div_eq_mul_inv]

/-! ## Words -/

theorem fields_nat (fmt : FloatFormat) (s : Bool) (e f : ℕ)
    (he : e < 2 ^ fmt.expWidth) (hf : f < 2 ^ fmt.fracWidth) :
    (Model.ofFields fmt s e f).bits.toNat =
      (if s then 2 ^ (fmt.expWidth + fmt.fracWidth) else 0) + e * 2 ^ fmt.fracWidth + f := by
  unfold Model.ofFields
  rw [Model.mkBits_eq_mkBitsImpl_apply]
  simp only [Model.ofBits, Model.mkBitsImpl, BitVec.toNat_ofNatLT,
    FloatFormat.expAllOnesNat, FloatFormat.fracMaskNat]
  have shift_or (a i b : ℕ) (hb : b < 2 ^ i) : Nat.shiftLeft a i ||| b = a * 2 ^ i + b := by
    calc
      _ = (a <<< i) ||| b := rfl
      _ = (a <<< i) + b := (Nat.shiftLeft_add_eq_or_of_lt hb a).symm
      _ = a * 2 ^ i + b := by rw [Nat.shiftLeft_eq]
  rw [Nat.and_two_pow_sub_one_eq_mod, Nat.and_two_pow_sub_one_eq_mod,
    Nat.mod_eq_of_lt he, Nat.mod_eq_of_lt hf, Nat.or_assoc, shift_or e _ f hf]
  have hl : e * 2 ^ fmt.fracWidth + f < 2 ^ (fmt.expWidth + fmt.fracWidth) := by
    rw [pow_add]
    nlinarith
  cases s
  · simp
  · simp only [ite_true]
    rw [shift_or 1 _ _ hl]
    simp only [one_mul, Nat.add_assoc]

theorem fields32 (e f : ℕ) (he : e < 256) (hf : f < 8388608) :
    MCFloat.bits (Model.ofFields .binary32 false e f) = e * 8388608 + f := by
  have h := fields_nat .binary32 false e f he hf
  have h1 : FloatFormat.binary32.fracWidth = 23 := rfl
  rw [h1] at h
  unfold MCFloat.bits
  rw [h]
  simp

theorem expField_bits {f : FloatFormat} (x : Model f) :
    Model.expField x = x.bits.toNat / 2 ^ f.fracWidth % 2 ^ f.expWidth := by
  rw [Model.expField_eq_expFieldImpl_apply]
  simp [Model.expFieldImpl, Model.toNatBits, FloatFormat.expAllOnesNat,
    Nat.and_two_pow_sub_one_eq_mod, Nat.shiftRight_eq_div_pow]

theorem fracField_bits {f : FloatFormat} (x : Model f) :
    Model.fracField x = x.bits.toNat % 2 ^ f.fracWidth := by
  rw [Model.fracField_eq_fracFieldImpl_apply]
  simp [Model.fracFieldImpl, Model.toNatBits, FloatFormat.fracMaskNat,
    Nat.and_two_pow_sub_one_eq_mod]

theorem signBit_bits {f : FloatFormat} (x : Model f) :
    Model.signBit x = (x.bits.toNat / 2 ^ (f.fracWidth + f.expWidth) != 0) := by
  apply Bool.eq_iff_iff.mpr
  rw [Model.signBit_eq_true_iff_signMaskNat_le]
  simp only [Model.toNatBits, bne_iff_ne]
  have hw : f.bitWidth - 1 = f.fracWidth + f.expWidth := by unfold FloatFormat.bitWidth; omega
  simp only [FloatFormat.signMaskNat, FloatFormat.signBitIndex, hw]
  have hp : 0 < 2 ^ (f.fracWidth + f.expWidth) := by positivity
  rw [← Nat.pos_iff_ne_zero, Nat.div_pos_iff]
  simp [hp]

theorem neg_bits (w : MCFloat.F32) (h : MCFloat.bits w < 2 ^ 31) :
    MCFloat.bits (Model.neg w) = 2 ^ 31 + MCFloat.bits w := by
  rw [Model.neg_eq_toggleSign_of_supportsSignedZero _ (by decide)]
  have hlt : (Model.toggleSign w).bits.toNat < 2 ^ 32 := (Model.toggleSign w).bits.isLt
  have he := expField_bits (Model.toggleSign w)
  have hf := fracField_bits (Model.toggleSign w)
  have hs := signBit_bits (Model.toggleSign w)
  rw [Model.expField_toggleSign, expField_bits] at he
  rw [Model.fracField_toggleSign, fracField_bits] at hf
  rw [Model.signBit_toggleSign, signBit_bits] at hs
  unfold MCFloat.bits at *
  generalize (Model.toggleSign w).bits.toNat = m at *
  generalize w.bits.toNat = n at *
  change n / 8388608 % 256 = m / 8388608 % 256 at he
  change n % 8388608 = m % 8388608 at hf
  change (!(n / 2147483648 != 0)) = (m / 2147483648 != 0) at hs
  have hn : n / 2147483648 = 0 := by omega
  rw [hn] at hs
  have hm : m / 2147483648 = 1 := by
    by_cases h0 : m / 2147483648 = 0
    · simp [h0] at hs
    · omega
  omega

/-! ## The `MatrixCore` word -/

/-- The `MatrixCore` word of `fl{x}`: `rne32`, signed infinity on overflow, flushed when `ftz`. -/
def refWord (ftz : Bool) (x : ℚ) : ℕ :=
  match MatrixCore.fl32 ftz x with
  | some w => w.toNat
  | none => (MatrixCore.infinity32 (decide (x < 0))).toNat

/-- The positive word for a magnitude `a > 0`, from `MatrixCore.rneFields`. -/
def posWord (a : ℚ) : ℕ :=
  if (MatrixCore.rneFields a).1 > 127 then 0x7F800000
  else if (MatrixCore.rneFields a).2 < 8388608 then (MatrixCore.rneFields a).2
  else ((MatrixCore.rneFields a).1 + 127).toNat * 8388608 + ((MatrixCore.rneFields a).2 - 8388608)

theorem posWord_lt (a : ℚ) (ha : 0 < a) : posWord a < 2 ^ 31 := by
  have h := MatrixCore.rneFields_spec ha
  unfold posWord
  split
  · decide
  · split <;> omega

theorem refWord_nonzero (x : ℚ) (hx : x ≠ 0) :
    refWord false x = (if decide (x < 0) then 2 ^ 31 else 0) + posWord |x| := by
  have ha : 0 < MatrixCore.absQ x := MatrixCore.absQ_pos hx
  have h := MatrixCore.rneFields_spec ha
  simp only [abs_eq] at h
  unfold refWord MatrixCore.fl32 MatrixCore.rne32 posWord
  simp only [hx, ite_false, abs_eq, Bool.false_and]
  generalize MatrixCore.rneFields |x| = r at h ⊢
  obtain ⟨e, m⟩ := r
  simp only at h ⊢
  by_cases ho : e > 127
  · simp only [ho, ite_true]
    cases decide (x < 0) <;> decide
  · simp only [ho, ite_false, MatrixCore.encode32]
    cases decide (x < 0) <;> simp <;> split <;> omega

/-! ## Positive magnitudes -/

theorem rneInt_small {t : ℚ} (h0 : 0 ≤ t) (h1 : t < 1 / 2) : MatrixCore.rneInt t = 0 := by
  have hf : t.floor = 0 := by
    rw [floor_eq]; apply Int.floor_eq_iff.mpr; norm_num; constructor <;> linarith
  unfold MatrixCore.rneInt
  rw [hf]
  have : ¬(1 < 2 * (t - ((0 : ℤ) : ℚ)) ∨ 2 * (t - ((0 : ℤ) : ℚ)) = 1 ∧ (0 : ℤ) % 2 = 1) := by
    push_cast; intro h; rcases h with h | ⟨h, _⟩ <;> linarith
  rw [ite_eq_right this]

theorem rneFields_eq (a : ℚ) : MatrixCore.rneFields a =
    if MatrixCore.rneInt (a / MCFloat.pow2 (MatrixCore.normExp a - 23)) = 16777216 then
      (MatrixCore.normExp a + 1, 8388608)
    else (MatrixCore.normExp a, (MatrixCore.rneInt (a / MCFloat.pow2 (MatrixCore.normExp a - 23))).toNat) :=
  rfl

theorem pow2_scale (L : ℤ) (n : ℕ) : MCFloat.pow2 (L + n) = 2 ^ n * MCFloat.pow2 L := by
  unfold MCFloat.pow2
  rw [zpow_add₀ (by norm_num), zpow_natCast, mul_comm]

theorem positive_bits (x : ℚ) (hx : x ≠ 0) :
    MCFloat.bits (Model.roundRatScaled .binary32 false x.num.natAbs x.den 0) = posWord |x| := by
  have hn : x.num.natAbs ≠ 0 := by simp [hx]
  have ha : 0 < |x| := abs_pos.mpr hx
  have c1 : FloatFormat.binary32.maxNormalExponent = 127 := rfl
  have c2 : FloatFormat.binary32.minSubnormalExponent = -149 := rfl
  have c3 : FloatFormat.binary32.minNormalExponent = -126 := rfl
  have c4 : (0 : ℤ) + Int.ofNat (FloatFormat.subnormalAlignExp .binary32) = -(-149) := rfl
  have c5 : FloatFormat.binary32.fracWidth = 23 := rfl
  have c6 : FloatFormat.binary32.exponentBias = 127 := rfl
  rw [Model.roundRatScaled_false_eq_of_isIEEE _ _ _ _ (by decide) hn x.den_nz]
  obtain ⟨hl, hu⟩ := MatrixCore.log2Floor_spec (x := |x|) ha
  simp only [pow2_eq] at hl hu
  simp only [floorLog2_eq x hx, add_zero, c1, c2, c3, c4, c5, c6, Model.pow2_eq_two_pow]
  generalize hL : MatrixCore.log2Floor |x| = L at hl hu
  have hne : MatrixCore.normExp |x| = max L (-126) := by
    unfold MatrixCore.normExp; rw [hL]
  have hspec := MatrixCore.rneFields_spec (a := |x|) ha
  unfold posWord
  rw [rneFields_eq, hne] at hspec ⊢
  have hq := pow2_pos (max L (-126) - 23)
  by_cases h1 : 127 < L
  · rw [ite_eq_left h1]
    have : max L (-126) = L := by omega
    simp only [this] at hspec ⊢
    have hfst : (if MatrixCore.rneInt (|x| / MCFloat.pow2 (L - 23)) = 16777216 then
        (L + 1, 8388608) else (L, (MatrixCore.rneInt (|x| / MCFloat.pow2 (L - 23))).toNat)).1 > 127 := by
      split <;> simp <;> omega
    rw [ite_eq_left hfst]
    decide
  rw [ite_eq_right h1]
  by_cases h2 : L < -149 - 1
  · rw [ite_eq_left h2]
    have hm : max L (-126) = -126 := by omega
    have hk : MatrixCore.rneInt (|x| / MCFloat.pow2 (-126 - 23)) = 0 := by
      apply rneInt_small (div_nonneg ha.le (pow2_pos _).le)
      rw [div_lt_iff₀ (pow2_pos _)]
      have : MCFloat.pow2 (L + 1) ≤ MCFloat.pow2 (-150) := MatrixCore.pow2_le_of_le (by omega)
      have e : MCFloat.pow2 (-150) = 1 / 2 * MCFloat.pow2 (-126 - 23) := by
        norm_num [MCFloat.pow2]
      linarith
    simp only [hm, hk]
    decide
  rw [ite_eq_right h2]
  by_cases h3 : L < -126
  · rw [ite_eq_left h3]
    have hm : max L (-126) = -126 := by omega
    simp only [hm] at hspec ⊢
    have hr := scaled_rne x (-149)
    have e149 : (-126 : ℤ) - 23 = -149 := by norm_num
    rw [e149] at hspec ⊢
    generalize hR : roundQuotientEven (RationalBinary.scaleByPowerOfTwo x.num.natAbs x.den (-(-149))).1
      (RationalBinary.scaleByPowerOfTwo x.num.natAbs x.den (-(-149))).2 = R at hr
    rw [← hr]
    have hR23 : (R : ℤ) ≤ 8388608 := by
      rw [hr]
      apply MatrixCore.rneInt_le_of_lt
      rw [div_lt_iff₀ (pow2_pos _)]
      have : MCFloat.pow2 (L + 1) ≤ MCFloat.pow2 (-126) := MatrixCore.pow2_le_of_le (by omega)
      have e : MCFloat.pow2 (-126) = ((8388608 : ℤ) : ℚ) * MCFloat.pow2 (-149) := by
        norm_num [MCFloat.pow2]
      linarith
    have hne24 : ¬ ((R : ℤ) = 16777216) := by omega
    simp only [hne24, ite_false, Int.toNat_natCast]
    by_cases hz : R = 0
    · simp only [hz]; decide
    by_cases ht : 2 ^ 23 ≤ R
    · have : R = 8388608 := by omega
      subst this; decide
    · simp only [hz, ht, ite_false]
      rw [fields32 0 R (by norm_num) (by omega)]
      simp only [show ¬ ((-126 : ℤ) > 127) by norm_num, ite_false]
      rw [ite_eq_left (by omega)]
      ring
  rw [ite_eq_right h3]
  have hm : max L (-126) = L := by omega
  simp only [hm, Int.ofNat_eq_natCast, Nat.cast_ofNat] at hspec hq ⊢
  have hr := scaled_rne x (L - 23)
  have es : ((23 : ℤ) - L) = -(L - 23) := by omega
  rw [es]
  generalize hR : roundQuotientEven (RationalBinary.scaleByPowerOfTwo x.num.natAbs x.den (-(L - 23))).1
    (RationalBinary.scaleByPowerOfTwo x.num.natAbs x.den (-(L - 23))).2 = R at hr
  rw [← hr]
  have hRlo : (8388608 : ℤ) ≤ R := by
    rw [hr]
    apply MatrixCore.le_rneInt_of_le
    rw [le_div_iff₀ (pow2_pos _)]
    have e : MCFloat.pow2 L = ((8388608 : ℤ) : ℚ) * MCFloat.pow2 (L - 23) := by
      have := pow2_scale (L - 23) 23
      rw [show L - 23 + ((23 : ℕ) : ℤ) = L by omega] at this
      rw [this]; norm_num
    linarith
  have hRhi : (R : ℤ) ≤ 16777216 := by
    rw [hr]
    apply MatrixCore.rneInt_le_of_lt
    rw [div_lt_iff₀ (pow2_pos _)]
    have e : MCFloat.pow2 (L + 1) = ((16777216 : ℤ) : ℚ) * MCFloat.pow2 (L - 23) := by
      have := pow2_scale (L - 23) 24
      rw [show L - 23 + ((24 : ℕ) : ℤ) = L + 1 by omega] at this
      rw [this]; norm_num
    linarith
  by_cases hc : R = 2 ^ (23 + 1)
  · subst hc
    simp only [ite_true, show ((2 ^ (23 + 1) : ℕ) : ℤ) = 16777216 by norm_num]
    by_cases h4 : 127 < L + 1
    · rw [ite_eq_left h4, ite_eq_left (by simpa using h4)]; decide
    · rw [ite_eq_right h4, ite_eq_right (by simpa using h4)]
      rw [fields32 _ 0 (by omega) (by norm_num)]
      simp
  · have hc' : ¬ ((R : ℤ) = 16777216) := by omega
    simp only [hc, hc', ite_false, Int.toNat_natCast]
    rw [ite_eq_right (by omega), ite_eq_right (by omega)]
    rw [fields32 _ _ (by omega) (by omega)]
    norm_num

/-! ## Signed rationals and flushing -/

/-- FloatLib's `fl{x}` word is the `MatrixCore` word, for every rational. -/
theorem round32_bits (x : ℚ) : MCFloat.bits (MCFloat.round32 x) = refWord false x := by
  by_cases hx : x = 0
  · subst hx; decide +kernel
  rw [refWord_nonzero x hx]
  have hpos := positive_bits x hx
  have hlt := posWord_lt |x| (abs_pos.mpr hx)
  unfold MCFloat.round32 Model.roundRatWithRounding Model.roundRatWithRoundingScaled
  cases hs : decide (x < 0)
  · simpa using hpos
  · rw [Model.roundRatScaled_true_eq_neg_false _ _ _ _ (by decide) x.den_nz]
    rw [neg_bits _ (by rw [hpos]; exact hlt), hpos]
    simp

theorem bits_lt (w : MCFloat.F32) : MCFloat.bits w < 2 ^ 32 := w.bits.isLt

theorem flush_bits (w : MCFloat.F32) :
    MCFloat.bits (MCFloat.flush w) =
      (if MatrixCore.isSubnormal32 (BitVec.ofNat 32 (MCFloat.bits w))
        then MatrixCore.signedZero32 (BitVec.ofNat 32 (MCFloat.bits w))
        else BitVec.ofNat 32 (MCFloat.bits w)).toNat := by
  have hlt := bits_lt w
  have hE : Model.expField w = MCFloat.bits w / 8388608 % 256 := by rw [expField_bits]; rfl
  have hF : Model.fracField w = MCFloat.bits w % 8388608 := by rw [fracField_bits]; rfl
  have hS : Model.signBit w = (MCFloat.bits w / 2147483648 != 0) := by rw [signBit_bits]; rfl
  have hsub : MatrixCore.isSubnormal32 (BitVec.ofNat 32 (MCFloat.bits w)) =
      (MCFloat.bits w / 8388608 % 256 == 0 && MCFloat.bits w % 8388608 != 0) := by
    have h32 : MCFloat.bits w % 4294967296 = MCFloat.bits w := Nat.mod_eq_of_lt hlt
    simp [MatrixCore.isSubnormal32, h32]
  have hz : (MatrixCore.signedZero32 (BitVec.ofNat 32 (MCFloat.bits w))).toNat =
      MCFloat.bits w / 2147483648 % 2 * 2147483648 := by
    simp only [MatrixCore.signedZero32, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt]
    omega
  have hzero (s : Bool) : MCFloat.bits (Model.zero .binary32 s) = if s then 2 ^ 31 else 0 := by
    cases s <;> decide
  unfold MCFloat.flush Model.isSubnormal
  rw [hE, hF, hsub]
  by_cases hc : (MCFloat.bits w / 8388608 % 256 == 0 && MCFloat.bits w % 8388608 != 0) = true
  · rw [ite_eq_left hc, ite_eq_left hc, hz]
    change MCFloat.bits (Model.zero .binary32 (Model.signBit w)) = _
    rw [hzero, hS]
    by_cases h0 : MCFloat.bits w / 2147483648 = 0
    · simp [h0]
    · have : MCFloat.bits w / 2147483648 = 1 := by omega
      simp [this]
  · rw [ite_eq_right hc, ite_eq_right hc]
    simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt]

/-- `fl{·}` with optional flushing: FloatLib's word is the `MatrixCore` word. -/
theorem fl_bits (ftz : Bool) (x : ℚ) : MCFloat.bits (MCFloat.fl ftz x) = refWord ftz x := by
  cases ftz
  · exact round32_bits x
  · unfold MCFloat.fl
    rw [ite_eq_left rfl, flush_bits, round32_bits]
    unfold refWord MatrixCore.fl32
    cases hr : MatrixCore.rne32 x with
    | some w =>
      simp only [Bool.false_and, Bool.true_and, Bool.false_eq_true, ite_false,
        BitVec.ofNat_toNat, BitVec.setWidth_eq]
    | none =>
      simp only
      cases decide (x < 0) <;> decide

end MCFloat.Equivalence
