import TensorCore.Kernels.Datapath

namespace TensorCore.Regression

open EFMachine

def dpOnes : BlockInput v100F16F32 := ⟨List.replicate 4 (0x3c00, 0x3c00), 0⟩
/-- Products below the alignment grid are discarded. -/
def dpTiny : BlockInput v100F16F32 := ⟨List.replicate 4 (0x0001, 0x3c00), 0x3f800000⟩
def dpOverflow : BlockInput a100BF16F32 := ⟨(0x7f7f, 0x3f80) :: List.replicate 7 (0, 0), 0x7f7fffff⟩
def dpSubnormal : BlockInput v100F16F32 := ⟨List.replicate 4 (0, 0), 0x80000001⟩
/-- A nonzero negative sum below the smallest subnormal truncates to −0. -/
def dpNegativeZero : BlockInput a100TF32F32 := ⟨(0x4D000, 0xD000) :: List.replicate 3 (0, 0), 0⟩

example : Datapath.evalBlock .v100F16 dpOnes = .ok 0x40800000 := by decide +kernel
example : Datapath.evalBlock .v100F16 dpTiny = .ok 0x3f800000 := by decide +kernel
example : Datapath.evalBlock .ampereBF16 dpOverflow = .error .accumulatorOutOfRange := by decide +kernel
example : Datapath.evalBlock .v100F16 dpSubnormal = .ok 0x80000001 := by decide +kernel
example : Datapath.evalBlock .ampereTF32 dpNegativeZero = .ok 0x80000000 := by decide +kernel
example : Datapath.evalBlock .v100F16 ⟨[], 0⟩ = .error .wrongProductCount := by decide +kernel
example : Datapath.evalBlock .v100F16 ⟨List.replicate 4 (0x7c00, 0x3c00), 0⟩ = .error .nonfiniteInput := by
  decide +kernel

/-- The same word from the model, by the equivalence theorem. -/
example : (evalBlock dpNegativeZero).map (·.output.bits) = .ok 0x80000000 :=
  (Datapath.evalBlock_eq .ampereTF32 dpNegativeZero).symm.trans (by decide +kernel)

end TensorCore.Regression
