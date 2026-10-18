import TensorCore.Scalar.LeanBridge
import TensorCore.Numerics.ScalarSum

/-! Native scalar addition with the finite numerical contract used by EFT. -/

namespace TensorCore.IEEE.LeanBridge

set_option maxRecDepth 4096

open Float.Model.UnpackedFloat

theorem value32_nonzero (a : F32) (ha : NonzeroFinite32 a) :
    TensorCore.value32 a = some (finiteValue32 a) := by
  have h := (decode_finite_iff .fp32 a (sign32 a) (finiteValue32 a)).mp
    (decode32_nonzero a ha)
  exact h.1

theorem round32_ieee_positive_zero (x : ℚ) (hr : absQ x ≤ fp32.maxFinite) :
    TensorCore.round32 .nearestEven x = some (round .fp32 {} false x).bits := by
  by_cases hz : x = 0
  · subst x
    rw [round_zero]
    change TensorCore.round32 .nearestEven 0 = some (0 : F32)
    decide +kernel
  · exact round_agrees_finite .fp32 {} false x hz hr

theorem nativeAdd32_round (a b : F32) (ha : NonzeroFinite32 a) (hb : NonzeroFinite32 b)
    (hr : absQ (finiteValue32 a + finiteValue32 b) ≤ fp32.maxFinite) :
    TensorCore.round32 .nearestEven (finiteValue32 a + finiteValue32 b) =
      some (nativeAdd32 a b (native32Valid_finite a ha.1) (native32Valid_finite b hb.1)) := by
  have hv := aligned_add_value (nativeSign (sign32 a)) (nativeSign (sign32 b))
    (mantissa32 a) (mantissa32 b) (exponent32 a) (exponent32 b)
  have hround := packNormalize32_reference
    ((nativeSign (sign32 a)).apply
      (decreaseExponent (mantissa32 a) (exponent32 a) (min (exponent32 a) (exponent32 b))).1 +
     (nativeSign (sign32 b)).apply
      (decreaseExponent (mantissa32 b) (exponent32 b) (min (exponent32 a) (exponent32 b))).1)
    (min (exponent32 a) (exponent32 b)) .afterRounding (by simpa only [hv, finiteValue32] using hr)
  change _ = some (pack Float.Model.Format.binary32
    (Float.Model.UnpackedFloat.add Float.Model.Format.binary32
      (unpack Float.Model.Format.binary32 a) (unpack Float.Model.Format.binary32 b)))
  rw [unpack32_nonzero a ha, unpack32_nonzero b hb]
  simp only [Float.Model.UnpackedFloat.add]
  rw [hround, hv]
  exact round32_ieee_positive_zero _ hr

theorem zero_or_nonzero32 (a : F32) (hf : a.toNat / 8388608 % 256 < 255) :
    a = 0 ∨ a = 0x80000000 ∨ NonzeroFinite32 a := by
  by_cases hm : 0 < mantissa32 a
  · exact Or.inr (Or.inr ⟨hf, hm⟩)
  · have hn := a.isLt
    have he : a.toNat / 8388608 % 256 = 0 := by
      simp only [mantissa32] at hm
      split at hm <;> omega
    have hm' : a.toNat % 8388608 = 0 := by simpa [mantissa32, he] using hm
    have h : a.toNat = 0 ∨ a.toNat = 2147483648 := by omega
    rcases h with h | h
    · exact Or.inl (BitVec.eq_of_toNat_eq h)
    · exact Or.inr (Or.inl (BitVec.eq_of_toNat_eq h))

theorem pack_unpack32_nonzero (a : F32) (ha : NonzeroFinite32 a) :
    pack Float.Model.Format.binary32 (unpack Float.Model.Format.binary32 a) = a := by
  rw [unpack32_nonzero a ha]
  have hm : a.toNat % 8388608 < 8388608 := Nat.mod_lt _ (by decide)
  have hn := a.isLt
  have he := ha.1
  by_cases hz : a.toNat / 8388608 % 256 = 0
  · have hk : 0 < a.toNat % 8388608 := by simpa [mantissa32, hz] using ha.2
    simp only [mantissa32, exponent32, hz, ↓reduceIte]
    rw [show (-149 : ℤ) = -126 - 23 by decide,
      packFinite32_eq _ _ _ hk (by omega) (by omega) (by omega)]
    apply BitVec.eq_of_toNat_eq
    simp only [encodeBinary, fp32, BitVec.toNat_ofNat, sign32]
    by_cases hs : a.toNat / 2147483648 = 0 <;>
      simp [Format.width, hs, show (a.toNat % 8388608 : ℤ) < 8388608 by omega] <;> omega
  · simp only [mantissa32, exponent32, hz, ↓reduceIte]
    rw [show (a.toNat / 8388608 % 256 : ℤ) - 150 =
      ((a.toNat / 8388608 % 256 : ℤ) - 127) - 23 by omega,
      packFinite32_eq _ _ _ (by omega) (by omega) (by omega) (by omega)]
    apply BitVec.eq_of_toNat_eq
    simp only [encodeBinary, fp32, BitVec.toNat_ofNat, sign32]
    by_cases hs : a.toNat / 2147483648 = 0 <;>
      simp [Format.width, hs, show ¬ (8388608 + a.toNat % 8388608 : ℤ) < 8388608 by omega] <;> omega

theorem finiteValue32_ne_zero (a : F32) (ha : NonzeroFinite32 a) : finiteValue32 a ≠ 0 := by
  have hp : 0 < (mantissa32 a : ℚ) * pow2 (exponent32 a) :=
    Rat.mul_pos (Rat.natCast_pos.mpr ha.2) (pow2_pos _)
  unfold finiteValue32 nativeSign
  split <;> simp only [Sign.apply, Rat.intCast_neg, Rat.intCast_natCast] <;> grind

theorem round32_finiteValue32 (a : F32) (ha : NonzeroFinite32 a) :
    TensorCore.round32 .nearestEven (finiteValue32 a) = some a :=
  binaryValue_roundBinary fp32 (by decide) .nearestEven a (finiteValue32 a)
    (value32_nonzero a ha) (finiteValue32_ne_zero a ha)

theorem nativeAdd32_zero_left (a : F32) (ha : NonzeroFinite32 a)
    (zeroBits : F32) (hz : zeroBits = 0 ∨ zeroBits = 0x80000000)
    (hv : Native32Valid zeroBits) :
    nativeAdd32 zeroBits a hv (native32Valid_finite a ha.1) = a := by
  change pack Float.Model.Format.binary32 (Float.Model.UnpackedFloat.add _
    (unpack Float.Model.Format.binary32 zeroBits) (unpack Float.Model.Format.binary32 a)) = a
  rcases hz with rfl | rfl
  all_goals
    first
    | rw [show unpack Float.Model.Format.binary32 (0 : F32) = .zero .positive by rfl]
    | rw [show unpack Float.Model.Format.binary32 (0x80000000 : F32) = .zero .negative by rfl]
  all_goals
    have hp := pack_unpack32_nonzero a ha
    rw [unpack32_nonzero a ha] at hp ⊢
    exact hp

theorem nativeAdd32_zero_right (a : F32) (ha : NonzeroFinite32 a)
    (zeroBits : F32) (hz : zeroBits = 0 ∨ zeroBits = 0x80000000)
    (hv : Native32Valid zeroBits) :
    nativeAdd32 a zeroBits (native32Valid_finite a ha.1) hv = a := by
  change pack Float.Model.Format.binary32 (Float.Model.UnpackedFloat.add _
    (unpack Float.Model.Format.binary32 a) (unpack Float.Model.Format.binary32 zeroBits)) = a
  rcases hz with rfl | rfl
  all_goals
    first
    | rw [show unpack Float.Model.Format.binary32 (0 : F32) = .zero .positive by rfl]
    | rw [show unpack Float.Model.Format.binary32 (0x80000000 : F32) = .zero .negative by rfl]
  all_goals
    have hp := pack_unpack32_nonzero a ha
    rw [unpack32_nonzero a ha] at hp ⊢
    exact hp

theorem nonzero32_ne_negative_zero (a : F32) (ha : NonzeroFinite32 a) : a ≠ 0x80000000 := by
  intro h
  subst a
  exact (by decide : ¬ NonzeroFinite32 0x80000000) ha

/-- Finite EFT arithmetic identifies exact zero with positive zero. -/
def nativeFiniteAdd32 (a b : F32)
    (ha : a.toNat / 8388608 % 256 < 255) (hb : b.toNat / 8388608 % 256 < 255) : F32 :=
  if a = 0x80000000 ∧ b = 0x80000000 then 0
  else nativeAdd32 a b (native32Valid_finite a ha) (native32Valid_finite b hb)

/-- Every finite encoded pair uses native addition, with the EFT zero convention. -/
theorem nativeFiniteAdd32_round (a b : F32)
    (ha : a.toNat / 8388608 % 256 < 255) (hb : b.toNat / 8388608 % 256 < 255)
    (x y : ℚ) (hx : TensorCore.value32 a = some x) (hy : TensorCore.value32 b = some y)
    (hr : absQ (x + y) ≤ fp32.maxFinite) :
    TensorCore.round32 .nearestEven (x + y) = some (nativeFiniteAdd32 a b ha hb) := by
  rcases zero_or_nonzero32 a ha with rfl | rfl | ha'
  all_goals rcases zero_or_nonzero32 b hb with rfl | rfl | hb'
  case inl.inl | inl.inr.inl | inr.inl.inl | inr.inl.inr.inl =>
    simp only [show TensorCore.value32 (0 : F32) = some 0 by decide +kernel,
      show TensorCore.value32 (0x80000000 : F32) = some 0 by decide +kernel, Option.some.injEq] at hx hy
    subst x
    subst y
    decide +kernel +revert
  case inl.inr.inr | inr.inl.inr.inr =>
    have hy' := Option.some.inj (hy.symm.trans (value32_nonzero _ hb'))
    have hx' : x = 0 := Option.some.inj (hx.symm.trans (by decide +kernel))
    rw [hx', hy', Rat.zero_add]
    unfold nativeFiniteAdd32
    rw [if_neg (fun h => nonzero32_ne_negative_zero _ hb' h.2),
      nativeAdd32_zero_left _ hb' _ (by first | exact Or.inl rfl | exact Or.inr rfl)]
    exact round32_finiteValue32 _ hb'
  case inr.inr.inl | inr.inr.inr.inl =>
    have hx' := Option.some.inj (hx.symm.trans (value32_nonzero _ ha'))
    have hy' : y = 0 := Option.some.inj (hy.symm.trans (by decide +kernel))
    rw [hx', hy', Rat.add_zero]
    unfold nativeFiniteAdd32
    rw [if_neg (fun h => nonzero32_ne_negative_zero _ ha' h.1),
      nativeAdd32_zero_right _ ha' _ (by first | exact Or.inl rfl | exact Or.inr rfl)]
    exact round32_finiteValue32 _ ha'
  case inr.inr.inr.inr =>
    have hx' := Option.some.inj (hx.symm.trans (value32_nonzero _ ha'))
    have hy' := Option.some.inj (hy.symm.trans (value32_nonzero _ hb'))
    rw [hx', hy'] at hr ⊢
    unfold nativeFiniteAdd32
    rw [if_neg (fun h => nonzero32_ne_negative_zero _ ha' h.1)]
    exact nativeAdd32_round a b ha' hb' hr

end TensorCore.IEEE.LeanBridge
