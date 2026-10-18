import TensorCore.Kernels.Datapath.Correctness
import TensorCore.Kernels.EFT.Scalar
import TensorCore.TC.MmaSyncFP8

/-! # A bitvector datapath for FP8 `mma.sync`

The FP16 conversions of the operand words, two runs of Hopper's FP16 block datapath, and the
bounded FP32 adder. -/

namespace TensorCore.Datapath

/-- An FP8 `mma.sync` output on the datapath. -/
def mmaSyncFP8 (conv : BitVec 8 → F16) (c : F32) (ps : List (BitVec 8 × BitVec 8)) : Option F32 := do
  let ps16 := ps.map fun (a, b) => (conv a, conv b)
  let d₁ ← (evalBlock .hopperF16 ⟨padTo 16 (groupA ps16), 0⟩).toOption
  let d₂ ← (evalBlock .hopperF16 ⟨padTo 16 (groupB ps16), d₁⟩).toOption
  EFMachine.add32 d₂ c

theorem toOption_map {ε α β : Type} (f : α → β) (e : Except ε α) :
    (e.map f).toOption = e.toOption.map f := by
  cases e <;> rfl

/-- The datapath returns the model's word, or no word, on every input. -/
theorem mmaSyncFP8_eq (conv : BitVec 8 → F16) (c : F32) (ps : List (BitVec 8 × BitVec 8)) :
    mmaSyncFP8 conv c ps = TensorCore.mmaSyncFP8 conv c ps := by
  unfold mmaSyncFP8 TensorCore.mmaSyncFP8 hmma
  simp only [evalBlock_eq, toOption_map, EFMachine.add32_eq, addFp32]
  rfl

end TensorCore.Datapath
