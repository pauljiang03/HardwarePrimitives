import TensorCore
import MatrixCore

/-! # The two libraries read binary words the same way

`TensorCore` and `MatrixCore` decode IEEE-style words with their own definitions. On every word of
a common layout they give the same finite value, or both reject it. -/

namespace CrossVendor

theorem pow2_eq (e : Int) : TensorCore.pow2 e = MatrixCore.pow2 e := rfl

theorem absQ_eq (x : Rat) : TensorCore.absQ x = MatrixCore.absQ x := rfl

theorem sumQ_eq (xs : List Rat) : TensorCore.sumQ xs = MatrixCore.sumQ xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp only [TensorCore.sumQ, MatrixCore.sumQ, ih]

/-- The `MatrixCore` layout of a `TensorCore` format, with IEEE infinities and NaNs. -/
def layout (f : TensorCore.Format) : MatrixCore.Format :=
  ⟨f.exponentBits, f.mantissaBits, f.bias, .ieee⟩

theorem sign_eq {n k : Nat} (hn : n < 2 ^ (1 + k)) : (n / 2 ^ k != 0) = (n / 2 ^ k % 2 == 1) := by
  have h : n / 2 ^ k < 2 := by
    rw [Nat.div_lt_iff_lt_mul (Nat.two_pow_pos k)]
    rw [Nat.pow_add, Nat.pow_one] at hn
    omega
  have : n / 2 ^ k = 0 ∨ n / 2 ^ k = 1 := by
    generalize n / 2 ^ k = q at h ⊢
    omega
  rcases this with h0 | h1
  · rw [h0]; rfl
  · rw [h1]; rfl

theorem signed_value (neg : Bool) (m : Nat) (e : Int) :
    ((if neg then -(m : Int) else (m : Int) : Int) : Rat) * TensorCore.pow2 e =
      (if neg then -(m : Rat) else (m : Rat)) * MatrixCore.pow2 e := by
  cases neg <;> simp [pow2_eq, Rat.intCast_natCast, Rat.intCast_neg]

/-- Every word of an IEEE layout decodes to the same finite value in both libraries, or is
rejected by both. -/
theorem decode_value (f : TensorCore.Format) (n : Nat)
    (hn : n < 2 ^ (1 + (f.mantissaBits + f.exponentBits))) :
    (TensorCore.classifyNat f n).finite.map TensorCore.Decoded.value =
      ((layout f).decodeNat n).toFinite.map MatrixCore.Unpacked.value := by
  have hs := sign_eq hn
  unfold TensorCore.classifyNat MatrixCore.Format.decodeNat
  simp only [layout, MatrixCore.Format.unpackFields, MatrixCore.Format.emin, ← hs]
  by_cases hE : n / 2 ^ f.mantissaBits % 2 ^ f.exponentBits = 2 ^ f.exponentBits - 1
  · by_cases hM : n % 2 ^ f.mantissaBits = 0 <;>
      simp [hE, hM, TensorCore.Classification.finite, MatrixCore.Datum.toFinite]
  · by_cases hZ : n / 2 ^ f.mantissaBits % 2 ^ f.exponentBits = 0
    · have hE0 : ¬ (0 = 2 ^ f.exponentBits - 1) := fun h => hE (hZ.trans h)
      by_cases hM : n % 2 ^ f.mantissaBits = 0
      · simp [hE0, hZ, hM, TensorCore.Classification.finite, MatrixCore.Datum.toFinite,
          TensorCore.Decoded.value, MatrixCore.Unpacked.value]
      · simp only [hE0, hZ, hM, if_false, if_true, TensorCore.Classification.finite,
          MatrixCore.Datum.toFinite, Option.map_some, TensorCore.Decoded.value,
          MatrixCore.Unpacked.value, Option.some.injEq]
        exact signed_value _ _ _
    · simp only [hE, hZ, if_false, TensorCore.Classification.finite,
        MatrixCore.Datum.toFinite, Option.map_some, TensorCore.Decoded.value,
        MatrixCore.Unpacked.value, Option.some.injEq]
      exact signed_value _ _ _

/-- The FP32 value of every word is the same in both libraries. -/
theorem value32_eq (w : BitVec 32) : TensorCore.value32 w = MatrixCore.value32 w :=
  decode_value TensorCore.fp32 w.toNat w.isLt

/-- Every FP16 word has the same value in both libraries, or neither gives one. -/
theorem fp16_value_eq (w : BitVec 16) :
    (TensorCore.classify TensorCore.fp16 w).finite.map TensorCore.Decoded.value =
      (MatrixCore.fp16.decode w).toFinite.map MatrixCore.Unpacked.value :=
  decode_value TensorCore.fp16 w.toNat w.isLt

/-- Every BF16 word has the same value in both libraries, or neither gives one. -/
theorem bf16_value_eq (w : BitVec 16) :
    (TensorCore.classify TensorCore.bf16 w).finite.map TensorCore.Decoded.value =
      (MatrixCore.bf16.decode w).toFinite.map MatrixCore.Unpacked.value :=
  decode_value TensorCore.bf16 w.toNat w.isLt

end CrossVendor
