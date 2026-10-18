import TensorCore.TC.Specification.Defs

/-! Independently transcribed numerical features of the supported FP32-output variants. -/

namespace TensorCore.IndependentSpec

inductive Variant where
  | v100F16
  | ampereF16
  | hopperF16
  | ampereBF16
  | hopperBF16
  | ampereTF32
  | hopperTF32Wmma
  | hopperTF32Mma
  deriving Repr, DecidableEq

def parameters : Variant → Parameters
  | .v100F16 => ⟨⟨10, 5, 15⟩, 4, 23, none⟩
  | .ampereF16 => ⟨⟨10, 5, 15⟩, 8, 24, some (-132)⟩
  | .hopperF16 => ⟨⟨10, 5, 15⟩, 16, 25, some (-133)⟩
  | .ampereBF16 => ⟨⟨7, 8, 127⟩, 8, 24, some (-132)⟩
  | .hopperBF16 => ⟨⟨7, 8, 127⟩, 16, 25, some (-133)⟩
  | .ampereTF32 => ⟨⟨10, 8, 127⟩, 4, 24, some (-132)⟩
  | .hopperTF32Wmma => ⟨⟨10, 8, 127⟩, 4, 25, some (-133)⟩
  | .hopperTF32Mma => ⟨⟨10, 8, 127⟩, 8, 25, some (-133)⟩

/-- TF32 register words have their thirteen low bits zero. -/
def paddedTF32 (ps : List (BitVec 32 × BitVec 32)) : Bool :=
  ps.all fun (a, b) => a.toNat % 8192 == 0 && b.toNat % 8192 == 0

def unpackTF32 (ps : List (BitVec 32 × BitVec 32)) : List (BitVec 19 × BitVec 19) :=
  ps.map fun (a, b) => (BitVec.ofNat 19 (a.toNat / 8192), BitVec.ofNat 19 (b.toNat / 8192))

noncomputable def tf32Bits (K padding : ℕ) (eAlignMin : Option ℤ)
    (ps : List (BitVec 32 × BitVec 32)) (c : BitVec 32) : Option (BitVec 32) :=
  if paddedTF32 ps then
    bits ⟨⟨10, 8, 127⟩, K, 23 + padding, eAlignMin⟩ ⟨unpackTF32 ps, c⟩
  else none

end TensorCore.IndependentSpec
