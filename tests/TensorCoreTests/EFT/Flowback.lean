import TensorCore.TC.Flowback
import TensorCore.EFT.TcEft
import TensorCoreTests.EFT.EFT
import TensorCoreTests.TC.Monotonicity

namespace TensorCore.Regression

set_option maxRecDepth 16384
set_option maxHeartbeats 4000000

/-- The V100 Table III witness in Definition III.3's terms. -/
theorem v100_witness_flowback :
    flowback v100F16F32 (List.replicate 4 (halfDecoded (-12), halfDecoded (-12)))
      oneDecoded belowOneDecoded = 4 / 16777216 ∧
    accumulatorShift v100F16F32 (List.replicate 4 (halfDecoded (-12), halfDecoded (-12)))
      oneDecoded belowOneDecoded = 1 / 16777216 ∧
    (evalPrepared ⟨v100F16F32, List.replicate 4 (halfDecoded (-12), halfDecoded (-12)),
      oneDecoded⟩).map (fun t => t.output.bits.toNat) = .ok 0x3f800000 ∧
    (evalPrepared ⟨v100F16F32, List.replicate 4 (halfDecoded (-12), halfDecoded (-12)),
      belowOneDecoded⟩).map (fun t => t.output.bits.toNat) = .ok 0x3f800001 := by
  decide +kernel

theorem flowback_without_increase :
    flowback (fp16Fp32Model 2 0 none) (List.replicate 2 (halfDecoded (-12), halfDecoded (-12)))
      oneDecoded belowOneDecoded = 2 / 16777216 ∧
    accumulatorShift (fp16Fp32Model 2 0 none)
      (List.replicate 2 (halfDecoded (-12), halfDecoded (-12))) oneDecoded belowOneDecoded =
      1 / 16777216 ∧
    (evalPrepared ⟨fp16Fp32Model 2 0 none,
      List.replicate 2 (halfDecoded (-12), halfDecoded (-12)), belowOneDecoded⟩).map
      (fun t => (t.output.bits.toNat, t.block.accumulator)) =
      .ok (0x3f800000, 16777217 / 16777216) := by
  decide +kernel

/-- Theorem III.4 as a failure of Definition III.2 on the V100 family with `K = 4`. -/
theorem v100_products_not_monotone :
    ¬ MonotoneInAccumulator v100F16F32 (List.replicate 4 (halfDecoded (-12), halfDecoded (-12))) :=
  construction_not_monotone v100F16F32 0 4 (halfDecoded (-12)) (halfDecoded (-12)) rfl
    (by simp [v100F16F32]) (by decide) (by decide +kernel) (by decide +kernel)
    (by decide) (by decide)

/-- Algorithm 1 on R3 (scalar branch) and the two exact-reference cases. -/
theorem tcEft_cases :
    (evalBlock r3).map (fun t => (t.tcEft, t.extractionExponent - t.block.alignGridExponent)) =
      .ok (.scalar 0x41080000, 3) ∧
    (evalBlock supportOverflow).map (fun t => t.tcEft) = .ok (.exactReference 0x4e800003) ∧
    (evalBlock subnormalAccumulator).map (fun t => t.tcEft) =
      .ok (.exactReference 0x3f800001) := by
  decide +kernel

/-- TC-EFT Table V for `K = 4`, and the `n + 2` operations of scalar consolidation. -/
theorem table_v_ledger :
    referenceLedger 4 = ⟨10, 5, 4, 5, 4, 1, 4, 2, 1⟩ ∧ scalarBranchOperations 4 = 7 := by
  decide

end TensorCore.Regression
