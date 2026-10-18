import MatrixCore

/-! # Fixed-width accumulation

`evalBlockMachine w` accumulates the CDNA 3 products in `w`-bit registers; these cases show that
the proved widths are needed. -/

open MatrixCore

namespace MatrixCoreTests.Machine

def nearFour : BlockInput cdna3F16 := ⟨List.replicate 8 0x3FFF, List.replicate 8 0x3FFF, 0⟩

/-- The aligned products as integers. -/
example : (prepare nearFour).map (fun px => alignedBits 1 0 px.p) =
    some (List.replicate 8 67043344) := by decide +kernel

/-- 30 bits give the model's output. -/
example : (evalBlockMachine 30 nearFour).map BlockTrace.d = .ok 0x41FFC004 := by decide +kernel

example : evalBlockMachine 30 nearFour = evalBlock nearFour := cdna3F16_machine_eq nearFour

/-- A 29-bit register wraps. -/
example : (evalBlockMachine 29 nearFour).map BlockTrace.d = .ok 0xBCFFF000 := by decide +kernel

/-! Odd/even grouping: each group of eight FP8 products fits 30 bits; their combination needs 31. -/
def fp8Max : BlockInput (cdna3FP8 e4m3fnuz e4m3fnuz) :=
  ⟨List.replicate 16 0x3F, List.replicate 16 0x3F, 0⟩

example : evalBlockMachine 31 fp8Max = evalBlock fp8Max := cdna3FP8_machine_eq _ _ fp8Max

/-- 31 bits give the model's output. -/
example : (evalBlockMachine 31 fp8Max).map BlockTrace.d = .ok 0x41610000 := by decide +kernel

/-- 30 bits wrap in the combination. -/
example : (evalBlockMachine 30 fp8Max).map BlockTrace.d = .ok 0xBFF80000 := by decide +kernel

end MatrixCoreTests.Machine
