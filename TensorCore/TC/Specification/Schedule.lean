import TensorCore.TC.Specification.Defs

/-! Ordered composition of block FMAs. -/

namespace TensorCore.IndependentSpec

noncomputable def runChain (p : Parameters) : BitVec 32 →
    List (List (BitVec p.input.width × BitVec p.input.width)) → Option (List (BitVec 32))
  | _, [] => some []
  | c, block :: rest => do
    let d ← bits p ⟨block, c⟩
    let tail ← runChain p d rest
    return d :: tail

noncomputable def lastBits (p : Parameters) (c : BitVec 32)
    (blocks : List (List (BitVec p.input.width × BitVec p.input.width))) : Option (BitVec 32) :=
  (runChain p c blocks).map fun ds => ds.getLast?.getD c

end TensorCore.IndependentSpec
