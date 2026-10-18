import TensorCore.TC
import TensorCore.EFT

/-! Checked calculation and proof for the first guide chapter. -/

open TensorCore
namespace TensorCoreExamples.GettingStarted

/-- Observe output words through the production evaluator. -/
def modelBits {p : Model} (x : BlockInput p) : Except ModelError F32 :=
  (evalBlock x).map fun t => t.output.bits

/-- Four products of one and a zero accumulator. -/
def ones : BlockInput v100F16F32 :=
  ⟨List.replicate 4 (0x3c00, 0x3c00), 0⟩

#eval (modelBits ones).map BitVec.toNat

example : modelBits ones = .ok 0x40800000 := by decide +kernel

/-- Each exact product is `2^-24`; the V100 model drops it on the `2^-23` grid. -/
def tiny : BlockInput v100F16F32 :=
  ⟨List.replicate 4 (0x0c00, 0x0c00), 0x3f800000⟩

#eval (modelBits tiny).map BitVec.toNat
#eval (tcEftEncoded tiny 0x3f800000).map fun r => r.bits.map BitVec.toNat

example : modelBits tiny = .ok 0x3f800000 := by decide +kernel
example : tcEftEncoded tiny 0x3f800000 =
    .ok (.consolidated (.scalar 0x3f800002)) := by decide +kernel

/-- On every input, the exact dot product is the output value plus the residual. -/
example {p : Model} {x : BlockInput p} {t : BlockTrace} (h : evalBlock x = .ok t) :
    exactDot x = some (t.output.value + t.residual) :=
  evalBlock_residual_identity h

end TensorCoreExamples.GettingStarted
