import TensorCore.Kernels.EFT.Correctness
import TensorCoreTests.EFT.EFT

namespace TensorCore.Regression.BoundedEFT
open TensorCore.EFMachine
set_option maxRecDepth 16384
set_option maxHeartbeats 4000000
set_option exponentiation.threshold 1024

theorem consolidation_branches :
    EFMachine.tcEft .v100F16 r3 0x4107ffff = .ok (.scalar 0x41080000) ∧
    EFMachine.tcEft .v100F16 subnormalAccumulator 0x3f800000 =
      .ok (.boundedExact 0x3f800001) ∧
    EFMachine.tcEft .v100F16 supportOverflow 0x4e800000 =
      .ok (.boundedExact 0x4e800003) := by decide +kernel

theorem zero_and_rejections :
    EFMachine.tcEft .v100F16 ⟨List.replicate 4 (0, 0), 0x80000000⟩ 0x7f7fffff =
      .ok .allZero ∧
    EFMachine.tcEft .v100F16 ⟨[], 0⟩ 0 = .error .wrongProductCount ∧
    EFMachine.tcEft .v100F16 ⟨List.replicate 4 (0x7c00, 0), 0⟩ 0 = .error .nonfiniteInput ∧
    EFMachine.tcEft .v100F16 ⟨List.replicate 4 (0, 0), 0x7fc00000⟩ 0 = .error .nonfiniteInput ∧
    EFMachine.tcEft .v100F16 ⟨List.replicate 4 (0, 0), 0⟩ 0x7f800000 = .error .nonfiniteOutput ∧
    EFMachine.tcEft .v100F16 ⟨[(0x3c00, 0x3c00), (0, 0), (0, 0), (0, 0)], 0x7f7fffff⟩ 0 =
      .ok .outOfRange := by decide +kernel

/-- Products near 2^256 cancel exactly. -/
theorem wide_cancellation :
    (EFMachine.tcEft .ampereBF16
      ⟨[(0x7f7f, 0x7f7f), (0xff7f, 0x7f7f)] ++ List.replicate 6 (0, 0), 0x3f800000⟩
      0xff7fffff).map Result.bits = .ok (some 0x3f800000) ∧
    (EFMachine.tcEft .hopperTF32Mma
      ⟨[(0x3fbff, 0x3fbff), (0x7fbff, 0x3fbff)] ++ List.replicate 6 (0, 0), 0x3f800000⟩
      0x7f7fffff).map Result.bits = .ok (some 0x3f800000) := by decide +kernel

/-- Full gap width, negative underflow, normal carry, even ties, and range boundary. -/
theorem extraction_and_rounding_boundaries :
    (Word.split ⟨true, 1⟩ 256).low.magnitude = 1 ∧
    (Word.split ⟨false, 1⟩ 576).coarse.magnitude = 0 ∧
    (Word.round32 ⟨true, 1⟩) = some 0x80000000 ∧
    (Word.round32 ⟨false, (1 : Magnitude) <<< 122⟩) = some 0 ∧
    (Word.round32 ⟨false, (3 : Magnitude) <<< 122⟩) = some 2 ∧
    (Word.round32 ⟨false, (33554431 : Magnitude) <<< 248⟩) = some 0x40000000 ∧
    (Word.round32 ⟨false, maxMagnitude32⟩) = some 0x7f7fffff ∧
    (Word.round32 ⟨false, maxMagnitude32 + 1⟩) = none := by decide +kernel

/-- The smallest TF32 products. -/
theorem tiny_products :
    (EFMachine.tcEft .ampereTF32 ⟨[(1, 1)] ++ List.replicate 3 (0, 0), 0⟩ 0).map
      Result.bits = .ok (some 0) ∧
    (EFMachine.tcEft .ampereTF32 ⟨[(0x40001, 1)] ++ List.replicate 3 (0, 0), 0⟩ 0).map
      Result.bits = .ok (some 0x80000000) := by decide +kernel

/-- Single-bit scans at every workspace position. -/
theorem single_bit_scans : ∀ i : Fin 576,
    leadingZeros ((1 : Magnitude) <<< i.val) = BitVec.ofNat 576 (575 - i.val) ∧
    trailingZeros ((1 : Magnitude) <<< i.val) = BitVec.ofNat 576 i.val := by decide +kernel

theorem zero_and_dense_scans :
    leadingZeros 0 = 576 ∧ trailingZeros 0 = 576 ∧
    leadingZeros (-1) = 0 ∧ trailingZeros (-1) = 0 ∧
    leadingZeros (((1 : Magnitude) <<< 512) + 1) = 63 ∧
    trailingZeros (((1 : Magnitude) <<< 512) + 1) = 0 ∧
    leadingZeros (((1 : Magnitude) <<< 575) + ((1 : Magnitude) <<< 288)) = 0 ∧
    trailingZeros (((1 : Magnitude) <<< 575) + ((1 : Magnitude) <<< 288)) = 288 := by decide +kernel

/-! ## The FP8 block FMAs -/

/-- Ada and Hopper E4M3: `2 + 2^-13`, which the 13-bit block output truncates to `2`. -/
def fp8Narrow : List (BitVec 9 × BitVec 9) :=
  [(widenE4M3 0x38, widenE4M3 0x38), (widenE4M3 0x38, widenE4M3 0x38),
    (widenE4M3 0x01, widenE4M3 0x18)] ++ List.replicate 13 (0, 0)

/-- Ada E5M2: `1 + 7·2^-17`. -/
def fp8Small : List (BitVec 8 × BitVec 8) :=
  [(0x3c, 0x3c)] ++ List.replicate 7 (0x01, 0x38) ++ List.replicate 8 (0, 0)

theorem fp8_blocks :
    EFMachine.tcEft .adaE4M3 ⟨fp8Narrow, 0⟩ 0x40000000 = .ok (.scalar 0x40000200) ∧
    EFMachine.tcEft .hopperE4M3 ⟨fp8Narrow ++ List.replicate 16 (0, 0), 0⟩ 0x40000000 =
      .ok (.scalar 0x40000200) ∧
    EFMachine.tcEft .adaE5M2 ⟨fp8Small, 0⟩ 0x3f800000 = .ok (.scalar 0x3f8001c0) ∧
    EFMachine.tcEft .blackwellE4M3
      ⟨(widenE4M3 0x38, widenE4M3 0x38) :: List.replicate 31 (0, 0), 0x4b800001⟩ 0x4b800001 =
      .ok (.scalar 0x4b800002) := by decide +kernel

/-- The hardware words those blocks correct. -/
theorem fp8_block_outputs :
    (evalBlock (⟨fp8Narrow, 0⟩ : BlockInput adaE4M3F32)).toOption.map (·.output.bits) =
      some 0x40000000 ∧
    (evalBlock (⟨fp8Small, 0⟩ : BlockInput adaE5M2F32)).toOption.map (·.output.bits) =
      some 0x3f800000 ∧
    (evalBlock (⟨(widenE4M3 0x38, widenE4M3 0x38) :: List.replicate 31 (0, 0), 0x4b800001⟩ :
      BlockInput blackwellE4M3F32)).toOption.map (·.output.bits) = some 0x4b800001 := by
  decide +kernel

end TensorCore.Regression.BoundedEFT
