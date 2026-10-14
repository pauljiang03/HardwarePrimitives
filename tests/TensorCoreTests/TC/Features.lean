import TensorCore.TC.Canonical
import TensorCore.TC.CanonicalEAlignMin
import TensorCore.TC.ExactAlignment
import TensorCore.TC.AcceptedDomain
import TensorCore.TC.MachineRefinement
import TensorCore.TC.Padding

namespace TensorCore.Regression

private def paddingInput (padding : ℕ) : BlockInput (fp16Fp32Model 4 padding) :=
  ⟨[(0x3c00, 0x3c00), (0xc00, 0xc00), (0xc00, 0xc00), (0, 0)], 0⟩

/-- Two individually discarded half-ULP products survive one padding bit. -/
theorem extra_alignment_bit_matters :
    ((evalBlock (paddingInput 0)).toOption.map fun t => t.output.bits) = some (BitVec.ofNat 32 0x3f800000) ∧
    ((evalBlock (paddingInput 1)).toOption.map fun t => t.output.bits) = some (BitVec.ofNat 32 0x3f800001) :=
  by decide +kernel

private def onesBlock (K padding : ℕ) (eAlignMin : Option ℤ) :
    BlockInput (fp16Fp32Model K padding eAlignMin) := ⟨List.replicate K (0x3c00, 0x3c00), 0⟩

theorem canonical_model_results :
    ((evalBlock (onesBlock 8 1 (some (-132)))).toOption.map fun t => t.output.bits) =
      some (BitVec.ofNat 32 0x41000000) ∧
    ((evalBlock (onesBlock 16 2 (some (-133)))).toOption.map fun t => t.output.bits) =
      some (BitVec.ofNat 32 0x41800000) ∧
    ((evalBlock (onesBlock 37 9 none)).toOption.map fun t => t.output.bits) =
      some (BitVec.ofNat 32 0x42140000) := by decide +kernel

theorem signed_capacity_prefix :
    (machineAccumulate 8 0 [127, 1, -1]).toInt = 127 ∧
    (machineAccumulate 8 0 [127, 1]).toInt = -128 ∧
    (machineAccumulate 9 0 [127, 1]).toInt = 128 := by decide +kernel

/-- An undersized signed accumulator can change the returned FP32 encoding. -/
theorem machine_width_changes_result :
    ((evalBlockMachine 26 (onesBlock 4 0 none)).toOption.map fun t => t.output.bits) =
      some (BitVec.ofNat 32 0xc0800000) ∧
    ((evalBlockMachine 29 (onesBlock 4 0 none)).toOption.map fun t => t.output.bits) =
      some (BitVec.ofNat 32 0x40800000) := by decide +kernel

/-- With enough padding bits, the finite-domain guard sees maxFinite32 + 1. -/
theorem padding_range_boundary :
    let x0 : BlockInput (fp16Fp32Model 1 0) := ⟨[(0x3c00, 0x3c00)], 0x7f7fffff⟩
    let x104 : BlockInput (fp16Fp32Model 1 104) := ⟨[(0x3c00, 0x3c00)], 0x7f7fffff⟩
    ((evalBlock x0).toOption.map fun t => t.output.bits) = some (BitVec.ofNat 32 0x7f7fffff) ∧
    evalBlock x104 = .error .accumulatorOutOfRange := by decide +kernel

/-- A maximum-scale FP16 product with minimum subnormal c needs 156 padding bits, not 155, to retain c during alignment. -/
theorem source_padding_boundary :
    let x155 : BlockInput (fp16Fp32Model 1 155) := ⟨[(0x7800, 0x7800)], 1⟩
    let x156 : BlockInput (fp16Fp32Model 1 156) := ⟨[(0x7800, 0x7800)], 1⟩
    ((prepare x155).map fun b => b.exactDot - b.accumulator) = some (pow2 (-149)) ∧
    ((prepare x156).map fun b => b.exactDot - b.accumulator) = some 0 := by decide +kernel

end TensorCore.Regression
