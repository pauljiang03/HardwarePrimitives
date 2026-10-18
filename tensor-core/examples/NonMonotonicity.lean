import TensorCore.TC.MonotonicityRange
import TensorCore.EFT.Encoded

/-! Executable witness used by the non-monotonicity and test walkthroughs. -/

open TensorCore
namespace TensorCoreExamples.NonMonotonicity

/-- Observe output words through the production evaluator. -/
def modelBits {p : Model} (x : BlockInput p) : Except ModelError F32 :=
  (evalBlock x).map fun t => t.output.bits

def before : BlockInput v100F16F32 :=
  ⟨List.replicate 4 (0x0c00, 0x0c00), 0x3f800000⟩

def after : BlockInput v100F16F32 :=
  ⟨List.replicate 4 (0x0c00, 0x0c00), 0x3f7fffff⟩

#eval (modelBits before).map BitVec.toNat
#eval (modelBits after).map BitVec.toNat

example : value32 after.c = some (1 - pow2 (-24)) ∧
    value32 before.c = some 1 ∧ (1 - pow2 (-24) : ℚ) < 1 := by decide +kernel
example : modelBits before = .ok 0x3f800000 ∧
    modelBits after = .ok 0x3f800001 := by decide +kernel

#eval (tcEftEncoded before 0x3f800000).map fun r => r.bits.map BitVec.toNat
#eval (tcEftEncoded after 0x3f800001).map fun r => r.bits.map BitVec.toNat

example : tcEftEncoded before 0x3f800000 =
    .ok (.consolidated (.scalar 0x3f800002)) ∧
    tcEftEncoded after 0x3f800001 =
    .ok (.consolidated (.scalar 0x3f800002)) := by decide +kernel

#check nonmonotone_encoded
#check nonmonotone_range_encoded

end TensorCoreExamples.NonMonotonicity
