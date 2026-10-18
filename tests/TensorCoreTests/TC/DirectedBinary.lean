import TensorCore.TC.FusedRounding
import TensorCore.Numerics.Binary.RoundingContract

/-! Kernel reductions cover signs, subnormals, binade carry, exact inputs, signed zeros, finite endpoints and rejection; theorem applications check the public contracts. -/

namespace TensorCore.Regression

set_option maxRecDepth 16384
set_option maxHeartbeats 4000000

theorem directed_binary_negative_and_carry :
    (roundBinary fp16 .towardNegative (1 / 3)).map BitVec.toNat = some 0x3555 ∧
    (roundBinary fp16 .towardPositive (1 / 3)).map BitVec.toNat = some 0x3556 ∧
    (roundBinary fp16 .towardNegative (-1 / 3)).map BitVec.toNat = some 0xb556 ∧
    (roundBinary fp16 .towardPositive (-1 / 3)).map BitVec.toNat = some 0xb555 ∧
    (roundBinary fp16 .towardNegative (2 - 1 / 2048)).map BitVec.toNat = some 0x3fff ∧
    (roundBinary fp16 .towardPositive (2 - 1 / 2048)).map BitVec.toNat = some 0x4000 ∧
    (roundBinary fp16 .towardNegative (-(2 - 1 / 2048))).map BitVec.toNat = some 0xc000 ∧
    (roundBinary fp16 .towardPositive (-(2 - 1 / 2048))).map BitVec.toNat = some 0xbfff := by
  decide +kernel

theorem directed_binary_subnormal :
    (roundBinary fp16 .towardNegative (1 / 33554432)).map BitVec.toNat = some 0 ∧
    (roundBinary fp16 .towardPositive (1 / 33554432)).map BitVec.toNat = some 1 ∧
    (roundBinary fp16 .towardNegative (-1 / 33554432)).map BitVec.toNat = some 0x8001 ∧
    (roundBinary fp16 .towardPositive (-1 / 33554432)).map BitVec.toNat = some 0x8000 ∧
    (roundBinary fp16 .towardNegative (2047 / 33554432)).map BitVec.toNat = some 0x03ff ∧
    (roundBinary fp16 .towardPositive (2047 / 33554432)).map BitVec.toNat = some 0x0400 ∧
    (roundBinary fp16 .towardNegative (-2047 / 33554432)).map BitVec.toNat = some 0x8400 ∧
    (roundBinary fp16 .towardPositive (-2047 / 33554432)).map BitVec.toNat = some 0x83ff := by
  decide +kernel

theorem directed_binary_range :
    (roundBinary fp16 .towardNegative 65503).map BitVec.toNat = some 0x7bfe ∧
    (roundBinary fp16 .towardPositive 65503).map BitVec.toNat = some 0x7bff ∧
    (roundBinary fp16 .towardNegative (-65503)).map BitVec.toNat = some 0xfbff ∧
    (roundBinary fp16 .towardPositive (-65503)).map BitVec.toNat = some 0xfbfe ∧
    roundBinary fp16 .towardNegative 65505 = none ∧
    roundBinary fp16 .towardPositive 65505 = none ∧
    roundBinary fp16 .towardNegative (-65505) = none ∧
    roundBinary fp16 .towardPositive (-65505) = none := by
  decide +kernel

theorem binary_all_modes_exact (mode : BinaryRoundingMode) :
    (roundBinary fp16 mode 0).map BitVec.toNat = some 0 ∧
    (roundBinary fp16 mode (1 / 16777216)).map BitVec.toNat = some 1 ∧
    (roundBinary fp16 mode (-1 / 16777216)).map BitVec.toNat = some 0x8001 ∧
    (roundBinary fp16 mode (3 / 2)).map BitVec.toNat = some 0x3e00 ∧
    (roundBinary fp16 mode (-3 / 2)).map BitVec.toNat = some 0xbe00 ∧
    (roundBinary fp16 mode 65504).map BitVec.toNat = some 0x7bff ∧
    (roundBinary fp16 mode (-65504)).map BitVec.toNat = some 0xfbff := by
  cases mode <;> decide +kernel

theorem directed_binary_formats :
    (roundBinary bf16 .towardNegative (-1 / 3)).map BitVec.toNat = some 0xbeab ∧
    (roundBinary bf16 .towardPositive (-1 / 3)).map BitVec.toNat = some 0xbeaa ∧
    (roundBinary tf19 .towardNegative (-1 / 3)).map BitVec.toNat = some 0x5f556 ∧
    (roundBinary tf19 .towardPositive (-1 / 3)).map BitVec.toNat = some 0x5f555 ∧
    (roundBinary fp32 .towardNegative (-1 / 3)).map BitVec.toNat = some 0xbeaaaaab ∧
    (roundBinary fp32 .towardPositive (-1 / 3)).map BitVec.toNat = some 0xbeaaaaaa ∧
    (roundBinary fp64 .towardNegative (-1 / 3)).map BitVec.toNat = some 0xbfd5555555555556 ∧
    (roundBinary fp64 .towardPositive (-1 / 3)).map BitVec.toNat = some 0xbfd5555555555555 := by
  decide +kernel

theorem negative_subnormal_upper_contract : TowardPositive fp16 (-1 / 33554432) 0x8000 := by
  obtain ⟨b, hb, hc⟩ := roundBinary_towardPositive_correct fp16 (by decide)
    (-1 / 33554432) (by decide +kernel)
  have he : roundBinary fp16 .towardPositive (-1 / 33554432) = some 0x8000 := by decide +kernel
  rw [he] at hb
  cases Option.some.inj hb
  exact hc

theorem negative_subnormal_lower_contract : TowardNegative fp16 (-1 / 33554432) 0x8001 := by
  obtain ⟨b, hb, hc⟩ := roundBinary_towardNegative_correct fp16 (by decide)
    (-1 / 33554432) (by decide +kernel)
  have he : roundBinary fp16 .towardNegative (-1 / 33554432) = some 0x8001 := by decide +kernel
  rw [he] at hb
  cases Option.some.inj hb
  exact hc

/-- An unusual bias and minimum permitted field sizes exercise the unrestricted format theorem. -/
theorem directed_unusual_format (x : ℚ) (hr : absQ x ≤ (Format.mk 1 2 (-7)).maxFinite) :
    (∃ b, roundBinary ⟨1, 2, -7⟩ .towardNegative x = some b ∧ TowardNegative ⟨1, 2, -7⟩ x b) ∧
    (∃ b, roundBinary ⟨1, 2, -7⟩ .towardPositive x = some b ∧ TowardPositive ⟨1, 2, -7⟩ x b) :=
  ⟨roundBinary_towardNegative_correct _ (by decide) x hr,
    roundBinary_towardPositive_correct _ (by decide) x hr⟩

def fma64Bits (mode : BinaryRoundingMode) (a b c : BitVec 64) : Option ℕ :=
  (evalInvocation (p := fp64Fma mode) ⟨[(a, b)], c⟩).toOption.map fun t => t.output.bits.toNat

theorem fma64_directed_half_ulp :
    fma64Bits .towardNegative 0x3ff0000000000000 0x3ff0000000000000 0x3ca0000000000000 = some 0x3ff0000000000000 ∧
    fma64Bits .towardPositive 0x3ff0000000000000 0x3ff0000000000000 0x3ca0000000000000 = some 0x3ff0000000000001 ∧
    fma64Bits .towardNegative 0xbff0000000000000 0x3ff0000000000000 0xbca0000000000000 = some 0xbff0000000000001 ∧
    fma64Bits .towardPositive 0xbff0000000000000 0x3ff0000000000000 0xbca0000000000000 = some 0xbff0000000000000 := by
  decide +kernel

def fma64Signed (mode : BinaryRoundingMode) (a b c : BitVec 64) : Option ℕ :=
  (fp64FmaBits (mode := mode) ⟨[(a, b)], c⟩).map BitVec.toNat

/-- IEEE 754 signed zero for exact zeros; a nonzero result rounded to zero keeps its sign. -/
theorem fma64_signed_zero :
    fma64Signed .towardNegative 0x3ff0000000000000 0x3ff0000000000000 0xbff0000000000000 = some 0x8000000000000000 ∧
    fma64Signed .nearestEven 0x3ff0000000000000 0x3ff0000000000000 0xbff0000000000000 = some 0 ∧
    fma64Signed .nearestEven 0x8000000000000000 0x3ff0000000000000 0x8000000000000000 = some 0x8000000000000000 ∧
    fma64Signed .nearestEven 0 0 0x8000000000000000 = some 0 ∧
    fma64Signed .towardNegative 0 0 0x8000000000000000 = some 0x8000000000000000 ∧
    fma64Signed .towardPositive 0x8000000000000001 0x3fe0000000000000 0 = some 0x8000000000000000 ∧
    fma64Signed .nearestEven 0x3ff0000000000000 0x3ff0000000000000 0x3ff0000000000000 = some 0x4000000000000000 := by
  decide +kernel

theorem fma64_subnormal :
    fma64Bits .towardNegative 0x8000000000000001 0x3fe0000000000000 0 = some 0x8000000000000001 ∧
    fma64Bits .towardPositive 0x8000000000000001 0x3fe0000000000000 0 = some 0x8000000000000000 := by
  decide +kernel

/-- An out-of-range exact product is allowed when the single fused result is finite. -/
theorem fma64_fused_boundaries (mode : BinaryRoundingMode) :
    fma64Bits mode 0x7fefffffffffffff 0x4000000000000000 0xffefffffffffffff = some 0x7fefffffffffffff ∧
    fma64Bits mode 0xbff0000000000000 0x3ff0000000000000 0x3ff0000000000000 = some 0 ∧
    fma64Bits mode 0x7fefffffffffffff 0x4000000000000000 0 = none ∧
    fma64Bits mode 0x7ff0000000000000 0x3ff0000000000000 0 = none := by
  cases mode <;> decide +kernel

def positiveZero16 : FiniteBinaryWord fp16 := ⟨0, ⟨⟨0, 0, 0⟩, by decide +kernel⟩⟩
def negativeZero16 : FiniteBinaryWord fp16 := ⟨0x8000, ⟨⟨0, 0, 0⟩, by decide +kernel⟩⟩

theorem finite_bijection_signed_zeros :
    binaryValue fp16 positiveZero16.val = binaryValue fp16 negativeZero16.val ∧
    positiveZero16 ≠ negativeZero16 ∧
    (decodeSignedBinary fp16 (by decide) positiveZero16).negative = false ∧
    (decodeSignedBinary fp16 (by decide) negativeZero16).negative = true ∧
    (encodeSignedBinary fp16 (by decide)
      (decodeSignedBinary fp16 (by decide) negativeZero16)).val = 0x8000 ∧
    roundBinary fp16 .towardNegative (decodeSignedBinary fp16 (by decide) negativeZero16).value = some 0 := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_, by decide +kernel⟩
  exact congrArg Subtype.val (encode_decodeSignedBinary fp16 (by decide) negativeZero16)

theorem finite_bijection_endpoints (mode : BinaryRoundingMode) :
    roundBinary fp64 mode (pow2 (-1074)) = some 1 ∧
    roundBinary fp64 mode (-fp64.maxFinite) = some 0xffefffffffffffff := by
  constructor
  · exact binaryValue_roundBinary fp64 (by decide) mode 1 _ (by decide +kernel) (by decide +kernel)
  · exact binaryValue_roundBinary fp64 (by decide) mode 0xffefffffffffffff _
      (by decide +kernel) (by decide +kernel)

end TensorCore.Regression
