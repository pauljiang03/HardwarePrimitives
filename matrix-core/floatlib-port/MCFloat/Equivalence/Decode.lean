import MCFloat.Equivalence.Rounding

/-! # Decoding: FloatLib's classification is `MatrixCore`'s `decode` -/

set_option linter.unusedSimpArgs false

namespace MCFloat.Equivalence
open FloatLib.Floats.Formats.BinaryInterchange

structure TermAgree (t : MCFloat.Term) (u : MatrixCore.Unpacked) : Prop where
  value : t.value = u.value
  exponent : t.exponent = u.e
  zero : t.isZero = (u.m == 0)
  small : t.small = decide (u.m < 2 ^ u.t)
  negative : t.dyadic.negative = u.negative

def Agree : MCFloat.Value → MatrixCore.Datum → Prop
  | .finite t, .finite u => TermAgree t u
  | .inf s, .infinity s' => s = s'
  | .nan, .nan => True
  | _, _ => False

theorem dyadic_toRat (s : Bool) (m : ℕ) (k : ℤ) :
    (⟨s, m, k⟩ : FloatLib.Numerics.Dyadic).toRat = (if s then -(m : ℚ) else m) * MCFloat.pow2 k := by
  cases s <;> simp [FloatLib.Numerics.Dyadic.toRat, FloatLib.Numerics.Dyadic.signedSignificand,
    MCFloat.pow2]

theorem ofNat_bits (f : FloatFormat) (n : ℕ) (hn : n < 2 ^ f.bitWidth) :
    (MCFloat.ofNat f n).bits.toNat = n := by
  change (BitVec.ofNat f.bitWidth n).toNat = n
  simp [Nat.mod_eq_of_lt hn]

theorem unpacked_value (s : Bool) (m : ℕ) (e : ℤ) (t : ℕ) :
    (⟨s, m, e, t⟩ : MatrixCore.Unpacked).value = (if s then -(m : ℚ) else m) * MCFloat.pow2 (e - t) :=
  rfl

theorem fp32_agree (n : ℕ) (hn : n < 2 ^ 32) :
    Agree (MCFloat.classify .binary32 n) (MatrixCore.fp32.decodeNat n) := by
  have hb : (MCFloat.ofNat .binary32 n).bits.toNat = n := ofNat_bits _ n hn
  unfold MCFloat.classify MCFloat.classifyModel MatrixCore.Format.decodeNat
  simp only [Model.isNaN, Model.isInf, Model.toDyadic?, Model.ieeeToDyadic?,
    Model.IEEE.isNaN, Model.IEEE.isInf, expField_bits, fracField_bits, signBit_bits, hb]
  simp (config := { decide := true }) only [show FloatFormat.binary32.encoding = .ieee from rfl,
    show FloatFormat.binary32.fracWidth = 23 from rfl, show FloatFormat.binary32.expWidth = 8 from rfl,
    show FloatFormat.expAllOnesNat .binary32 = 255 from rfl,
    show FloatFormat.binary32.exponentBias = 127 from rfl,
    show FloatFormat.ieeeMinSubnormalExponent .binary32 = -149 from rfl,
    show FloatFormat.ieeeNormalMantissaExpOffset .binary32 = 150 from rfl,
    show MatrixCore.fp32.mantissaBits = 23 from rfl, show MatrixCore.fp32.exponentBits = 8 from rfl,
    show MatrixCore.fp32.specials = .ieee from rfl, show MatrixCore.fp32.bias = 127 from rfl,
    show MatrixCore.fp32.emin = -126 from rfl, MatrixCore.Format.unpackFields, Model.pow2_eq_two_pow]
  simp only [ite_true, Nat.reducePow, Nat.reduceAdd, Nat.reduceSub]
  have hS : n / 2147483648 < 2 := by omega
  have hE : n / 8388608 % 256 < 256 := Nat.mod_lt _ (by norm_num)
  have hM : n % 8388608 < 8388608 := Nat.mod_lt _ (by norm_num)
  generalize n / 8388608 % 256 = E at *
  generalize n % 8388608 = M at *
  generalize n / 2147483648 = S at *
  obtain rfl | rfl : S = 0 ∨ S = 1 := by omega
  all_goals
    by_cases h1 : E = 255 <;> by_cases h2 : M = 0 <;> by_cases h3 : E = 0 <;>
      simp [h1, h2, h3, Agree] <;>
      (try (constructor <;> simp [MCFloat.Term.value, MCFloat.Term.isZero, dyadic_toRat,
        unpacked_value, h2, h3, hM, sub_sub] <;> (try omega)))

theorem fp16_agree (n : ℕ) (hn : n < 2 ^ 16) :
    Agree (MCFloat.classify .binary16 n) (MatrixCore.fp16.decodeNat n) := by
  have hb : (MCFloat.ofNat .binary16 n).bits.toNat = n := ofNat_bits _ n hn
  unfold MCFloat.classify MCFloat.classifyModel MatrixCore.Format.decodeNat
  simp only [Model.isNaN, Model.isInf, Model.toDyadic?, Model.ieeeToDyadic?,
    Model.IEEE.isNaN, Model.IEEE.isInf, expField_bits, fracField_bits, signBit_bits, hb]
  simp (config := { decide := true }) only [show FloatFormat.binary16.encoding = .ieee from rfl,
    show FloatFormat.binary16.fracWidth = 10 from rfl, show FloatFormat.binary16.expWidth = 5 from rfl,
    show FloatFormat.expAllOnesNat .binary16 = 31 from rfl,
    show FloatFormat.binary16.exponentBias = 15 from rfl,
    show FloatFormat.ieeeMinSubnormalExponent .binary16 = -24 from rfl,
    show FloatFormat.ieeeNormalMantissaExpOffset .binary16 = 25 from rfl,
    show MatrixCore.fp16.mantissaBits = 10 from rfl, show MatrixCore.fp16.exponentBits = 5 from rfl,
    show MatrixCore.fp16.specials = .ieee from rfl, show MatrixCore.fp16.bias = 15 from rfl,
    show MatrixCore.fp16.emin = -14 from rfl, MatrixCore.Format.unpackFields, Model.pow2_eq_two_pow]
  simp only [ite_true, Nat.reducePow, Nat.reduceAdd, Nat.reduceSub]
  have hS : n / 32768 < 2 := by omega
  have hE : n / 1024 % 32 < 32 := Nat.mod_lt _ (by norm_num)
  have hM : n % 1024 < 1024 := Nat.mod_lt _ (by norm_num)
  generalize n / 1024 % 32 = E at *
  generalize n % 1024 = M at *
  generalize n / 32768 = S at *
  obtain rfl | rfl : S = 0 ∨ S = 1 := by omega
  all_goals
    by_cases h1 : E = 31 <;> by_cases h2 : M = 0 <;> by_cases h3 : E = 0 <;>
      simp [h1, h2, h3, Agree] <;>
      (try (constructor <;> simp [MCFloat.Term.value, MCFloat.Term.isZero, dyadic_toRat,
        unpacked_value, h2, h3, hM, sub_sub] <;> (try omega)))

theorem bf16_agree (n : ℕ) (hn : n < 2 ^ 16) :
    Agree (MCFloat.classify .bfloat16 n) (MatrixCore.bf16.decodeNat n) := by
  have hb : (MCFloat.ofNat .bfloat16 n).bits.toNat = n := ofNat_bits _ n hn
  unfold MCFloat.classify MCFloat.classifyModel MatrixCore.Format.decodeNat
  simp only [Model.isNaN, Model.isInf, Model.toDyadic?, Model.ieeeToDyadic?,
    Model.IEEE.isNaN, Model.IEEE.isInf, expField_bits, fracField_bits, signBit_bits, hb]
  simp (config := { decide := true }) only [show FloatFormat.bfloat16.encoding = .ieee from rfl,
    show FloatFormat.bfloat16.fracWidth = 7 from rfl, show FloatFormat.bfloat16.expWidth = 8 from rfl,
    show FloatFormat.expAllOnesNat .bfloat16 = 255 from rfl,
    show FloatFormat.bfloat16.exponentBias = 127 from rfl,
    show FloatFormat.ieeeMinSubnormalExponent .bfloat16 = -133 from rfl,
    show FloatFormat.ieeeNormalMantissaExpOffset .bfloat16 = 134 from rfl,
    show MatrixCore.bf16.mantissaBits = 7 from rfl, show MatrixCore.bf16.exponentBits = 8 from rfl,
    show MatrixCore.bf16.specials = .ieee from rfl, show MatrixCore.bf16.bias = 127 from rfl,
    show MatrixCore.bf16.emin = -126 from rfl, MatrixCore.Format.unpackFields, Model.pow2_eq_two_pow]
  simp only [ite_true, Nat.reducePow, Nat.reduceAdd, Nat.reduceSub]
  have hS : n / 32768 < 2 := by omega
  have hE : n / 128 % 256 < 256 := Nat.mod_lt _ (by norm_num)
  have hM : n % 128 < 128 := Nat.mod_lt _ (by norm_num)
  generalize n / 128 % 256 = E at *
  generalize n % 128 = M at *
  generalize n / 32768 = S at *
  obtain rfl | rfl : S = 0 ∨ S = 1 := by omega
  all_goals
    by_cases h1 : E = 255 <;> by_cases h2 : M = 0 <;> by_cases h3 : E = 0 <;>
      simp [h1, h2, h3, Agree] <;>
      (try (constructor <;> simp [MCFloat.Term.value, MCFloat.Term.isZero, dyadic_toRat,
        unpacked_value, h2, h3, hM, sub_sub] <;> (try omega)))

theorem tf19_agree (n : ℕ) (hn : n < 2 ^ 19) :
    Agree (MCFloat.classify .tf32 n) (MatrixCore.tf19.decodeNat n) := by
  have hb : (MCFloat.ofNat .tf32 n).bits.toNat = n := ofNat_bits _ n hn
  unfold MCFloat.classify MCFloat.classifyModel MatrixCore.Format.decodeNat
  simp only [Model.isNaN, Model.isInf, Model.toDyadic?, Model.ieeeToDyadic?,
    Model.IEEE.isNaN, Model.IEEE.isInf, expField_bits, fracField_bits, signBit_bits, hb]
  simp (config := { decide := true }) only [show FloatFormat.tf32.encoding = .ieee from rfl,
    show FloatFormat.tf32.fracWidth = 10 from rfl, show FloatFormat.tf32.expWidth = 8 from rfl,
    show FloatFormat.expAllOnesNat .tf32 = 255 from rfl,
    show FloatFormat.tf32.exponentBias = 127 from rfl,
    show FloatFormat.ieeeMinSubnormalExponent .tf32 = -136 from rfl,
    show FloatFormat.ieeeNormalMantissaExpOffset .tf32 = 137 from rfl,
    show MatrixCore.tf19.mantissaBits = 10 from rfl, show MatrixCore.tf19.exponentBits = 8 from rfl,
    show MatrixCore.tf19.specials = .ieee from rfl, show MatrixCore.tf19.bias = 127 from rfl,
    show MatrixCore.tf19.emin = -126 from rfl, MatrixCore.Format.unpackFields, Model.pow2_eq_two_pow]
  simp only [ite_true, Nat.reducePow, Nat.reduceAdd, Nat.reduceSub]
  have hS : n / 262144 < 2 := by omega
  have hE : n / 1024 % 256 < 256 := Nat.mod_lt _ (by norm_num)
  have hM : n % 1024 < 1024 := Nat.mod_lt _ (by norm_num)
  generalize n / 1024 % 256 = E at *
  generalize n % 1024 = M at *
  generalize n / 262144 = S at *
  obtain rfl | rfl : S = 0 ∨ S = 1 := by omega
  all_goals
    by_cases h1 : E = 255 <;> by_cases h2 : M = 0 <;> by_cases h3 : E = 0 <;>
      simp [h1, h2, h3, Agree] <;>
      (try (constructor <;> simp [MCFloat.Term.value, MCFloat.Term.isZero, dyadic_toRat,
        unpacked_value, h2, h3, hM, sub_sub] <;> (try omega)))

theorem e4m3fnuz_agree (n : ℕ) (hn : n < 2 ^ 8) :
    Agree (MCFloat.classify .e4m3fnuz n) (MatrixCore.e4m3fnuz.decodeNat n) := by
  have hb : (MCFloat.ofNat .e4m3fnuz n).bits.toNat = n := ofNat_bits _ n hn
  have hnan : ((MCFloat.ofNat .e4m3fnuz n).bits == FloatFormat.signMask .e4m3fnuz) = (n == 128) := by
    rw [Bool.eq_iff_iff, beq_iff_eq, beq_iff_eq, ← BitVec.toNat_inj, hb]; rfl
  have hzero : ((MCFloat.ofNat .e4m3fnuz n).bits == 0) = (n == 0) := by
    rw [Bool.eq_iff_iff, beq_iff_eq, beq_iff_eq, ← BitVec.toNat_inj, hb]; rfl
  unfold MCFloat.classify MCFloat.classifyModel MatrixCore.Format.decodeNat
  simp only [Model.isNaN, Model.isInf, Model.toDyadic?, Model.isFinite, Model.isZero,
    expField_bits, fracField_bits, signBit_bits, hb, hnan, hzero]
  simp (config := { decide := true }) only [show FloatFormat.e4m3fnuz.encoding = .finiteUnsignedZero from rfl,
    show FloatFormat.e4m3fnuz.isIEEE = false from rfl,
    show FloatFormat.e4m3fnuz.fracWidth = 3 from rfl, show FloatFormat.e4m3fnuz.expWidth = 4 from rfl,
    show FloatFormat.e4m3fnuz.exponentBias = 8 from rfl,
    show FloatFormat.e4m3fnuz.minSubnormalExponent = -10 from rfl,
    show MatrixCore.e4m3fnuz.mantissaBits = 3 from rfl, show MatrixCore.e4m3fnuz.exponentBits = 4 from rfl,
    show MatrixCore.e4m3fnuz.specials = .fnuz from rfl, show MatrixCore.e4m3fnuz.bias = 8 from rfl,
    show MatrixCore.e4m3fnuz.emin = -7 from rfl, MatrixCore.Format.unpackFields, Model.pow2_eq_two_pow]
  simp only [ite_true, ite_false, Bool.false_eq_true, Nat.reducePow, Nat.reduceAdd, Nat.reduceSub]
  have hs : (n / 128 != 0) = (n / 128 % 2 == 1) := by
    rcases (show n / 128 = 0 ∨ n / 128 = 1 by omega) with h | h <;> simp [h]
  have hM : n % 8 < 8 := Nat.mod_lt _ (by norm_num)
  rw [hs]
  by_cases hN : n = 128 <;> by_cases hZ : n = 0 <;> by_cases h3 : n / 8 % 16 = 0 <;>
    simp [hN, hZ, h3, Agree] <;> (try omega) <;>
    (try simp only [show ¬(n / 128 % 2 = 1 ∧ n % 8 = 0) by omega, ite_false]) <;>
    (try (constructor <;> simp [MCFloat.Term.value, MCFloat.Term.isZero, dyadic_toRat,
      unpacked_value, hZ, h3, hM, sub_sub] <;> (try omega)))

theorem e5m2fnuz_agree (n : ℕ) (hn : n < 2 ^ 8) :
    Agree (MCFloat.classify .e5m2fnuz n) (MatrixCore.e5m2fnuz.decodeNat n) := by
  have hb : (MCFloat.ofNat .e5m2fnuz n).bits.toNat = n := ofNat_bits _ n hn
  have hnan : ((MCFloat.ofNat .e5m2fnuz n).bits == FloatFormat.signMask .e5m2fnuz) = (n == 128) := by
    rw [Bool.eq_iff_iff, beq_iff_eq, beq_iff_eq, ← BitVec.toNat_inj, hb]; rfl
  have hzero : ((MCFloat.ofNat .e5m2fnuz n).bits == 0) = (n == 0) := by
    rw [Bool.eq_iff_iff, beq_iff_eq, beq_iff_eq, ← BitVec.toNat_inj, hb]; rfl
  unfold MCFloat.classify MCFloat.classifyModel MatrixCore.Format.decodeNat
  simp only [Model.isNaN, Model.isInf, Model.toDyadic?, Model.isFinite, Model.isZero,
    expField_bits, fracField_bits, signBit_bits, hb, hnan, hzero]
  simp (config := { decide := true }) only [show FloatFormat.e5m2fnuz.encoding = .finiteUnsignedZero from rfl,
    show FloatFormat.e5m2fnuz.isIEEE = false from rfl,
    show FloatFormat.e5m2fnuz.fracWidth = 2 from rfl, show FloatFormat.e5m2fnuz.expWidth = 5 from rfl,
    show FloatFormat.e5m2fnuz.exponentBias = 16 from rfl,
    show FloatFormat.e5m2fnuz.minSubnormalExponent = -17 from rfl,
    show MatrixCore.e5m2fnuz.mantissaBits = 2 from rfl, show MatrixCore.e5m2fnuz.exponentBits = 5 from rfl,
    show MatrixCore.e5m2fnuz.specials = .fnuz from rfl, show MatrixCore.e5m2fnuz.bias = 16 from rfl,
    show MatrixCore.e5m2fnuz.emin = -15 from rfl, MatrixCore.Format.unpackFields, Model.pow2_eq_two_pow]
  simp only [ite_true, ite_false, Bool.false_eq_true, Nat.reducePow, Nat.reduceAdd, Nat.reduceSub]
  have hs : (n / 128 != 0) = (n / 128 % 2 == 1) := by
    rcases (show n / 128 = 0 ∨ n / 128 = 1 by omega) with h | h <;> simp [h]
  have hM : n % 4 < 4 := Nat.mod_lt _ (by norm_num)
  rw [hs]
  by_cases hN : n = 128 <;> by_cases hZ : n = 0 <;> by_cases h3 : n / 4 % 32 = 0 <;>
    simp [hN, hZ, h3, Agree] <;> (try omega) <;>
    (try simp only [show ¬(n / 128 % 2 = 1 ∧ n % 4 = 0) by omega, ite_false]) <;>
    (try (constructor <;> simp [MCFloat.Term.value, MCFloat.Term.isZero, dyadic_toRat,
      unpacked_value, hZ, h3, hM, sub_sub] <;> (try omega)))

/-! ## XF32 and operand formats -/

theorem xf32_tf19 (n : ℕ) (u : MatrixCore.Unpacked)
    (h : MatrixCore.fp32.decodeNat n = .finite u) :
    MatrixCore.tf19.decodeNat (n / 2 ^ 13) = .finite (MatrixCore.InputFormat.truncateXF32 u) := by
  unfold MatrixCore.Format.decodeNat at h ⊢
  simp (config := { decide := true }) only [show MatrixCore.fp32.mantissaBits = 23 from rfl,
    show MatrixCore.fp32.exponentBits = 8 from rfl, show MatrixCore.fp32.specials = .ieee from rfl,
    show MatrixCore.tf19.mantissaBits = 10 from rfl, show MatrixCore.tf19.exponentBits = 8 from rfl,
    show MatrixCore.tf19.specials = .ieee from rfl, MatrixCore.Format.unpackFields,
    show MatrixCore.fp32.emin = -126 from rfl, show MatrixCore.tf19.emin = -126 from rfl,
    show MatrixCore.fp32.bias = 127 from rfl, show MatrixCore.tf19.bias = 127 from rfl,
    Nat.reducePow, Nat.reduceAdd, Nat.reduceSub] at h ⊢
  have e1 : n / 8192 / 1024 % 256 = n / 8388608 % 256 := by omega
  have e2 : n / 8192 % 1024 = n % 8388608 / 8192 := by omega
  have e3 : n / 8192 / 262144 % 2 = n / 2147483648 % 2 := by omega
  rw [e1, e2, e3]
  by_cases hE : n / 8388608 % 256 = 255
  · simp [hE] at h; split at h <;> simp at h
  · simp only [hE, ite_false, MatrixCore.Datum.finite.injEq] at h ⊢
    subst h
    by_cases h0 : n / 8388608 % 256 = 0
    · simp [h0, MatrixCore.InputFormat.truncateXF32]
    · simp only [h0, ite_false, MatrixCore.InputFormat.truncateXF32, MatrixCore.Unpacked.mk.injEq,
        true_and, and_true]
      omega

/-- Operand formats correspond: every word is classified alike. -/
def OperandAgree (o : MCFloat.Operand) (i : MatrixCore.InputFormat) : Prop :=
  ∀ w : i.Word, Agree (o.read w.toNat) (i.read w)

theorem operand_fp32 : OperandAgree (.fmt .binary32) (.packed MatrixCore.fp32) :=
  fun w => fp32_agree w.toNat w.isLt
theorem operand_fp16 : OperandAgree (.fmt .binary16) (.packed MatrixCore.fp16) :=
  fun w => fp16_agree w.toNat w.isLt
theorem operand_bf16 : OperandAgree (.fmt .bfloat16) (.packed MatrixCore.bf16) :=
  fun w => bf16_agree w.toNat w.isLt
theorem operand_e4m3fnuz : OperandAgree (.fmt .e4m3fnuz) (.packed MatrixCore.e4m3fnuz) :=
  fun w => e4m3fnuz_agree w.toNat w.isLt
theorem operand_e5m2fnuz : OperandAgree (.fmt .e5m2fnuz) (.packed MatrixCore.e5m2fnuz) :=
  fun w => e5m2fnuz_agree w.toNat w.isLt

theorem operand_xf32 : OperandAgree .xf32 .xf32 := by
  intro w
  have hw : w.toNat < 2 ^ 32 := w.isLt
  have h := fp32_agree w.toNat hw
  change Agree (match MCFloat.classify .binary32 w.toNat with
    | .finite _ => MCFloat.classify .tf32 (w.toNat / 2 ^ 13) | v => v)
    (match MatrixCore.fp32.decodeNat w.toNat with
    | .finite x => .finite (MatrixCore.InputFormat.truncateXF32 x) | d => d)
  revert h
  cases hc : MCFloat.classify .binary32 w.toNat <;>
    cases hd : MatrixCore.fp32.decodeNat w.toNat <;> simp [Agree]
  rename_i t u
  intro _
  rw [← xf32_tf19 w.toNat u hd]
  exact tf19_agree _ (by omega)

end MCFloat.Equivalence
