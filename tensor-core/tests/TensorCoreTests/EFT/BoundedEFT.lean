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

end TensorCore.Regression.BoundedEFT
