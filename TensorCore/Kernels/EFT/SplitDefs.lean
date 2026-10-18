import TensorCore.Numerics.Encoding

/-! Bounded unsigned significand splitting. -/

namespace TensorCore.EFMachine

structure SplitMagnitude where
  coarse : BitVec 24
  low : BitVec 24
  deriving Repr, DecidableEq

/-- Split a magnitude at `gap` low bits. -/
def splitMagnitude (m : BitVec 24) (gap : BitVec 8) : SplitMagnitude :=
  if gap ≥ 24 then ⟨0, m⟩
  else
    let coarse := (m >>> gap) <<< gap
    ⟨coarse, m - coarse⟩

/-- Product of two 11-bit significands, widened to 24 bits so that it cannot wrap. -/
def multiplySignificands (a b : BitVec 11) : BitVec 24 :=
  a.zeroExtend 24 * b.zeroExtend 24

end TensorCore.EFMachine
