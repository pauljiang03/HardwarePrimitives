import TensorCore.Numerics.Encoding

/-! Tensor Core profiles. -/

namespace TensorCore


/-- Parameters of one Tensor Core normalization group. -/
structure Model where
  /-- Operand format (FP16, BF16, or packed TF32). -/
  input : Format
  /-- K, the number of products per group. -/
  nfma : ℕ
  /-- F = 23 + p: mantissa bits each term keeps after alignment. -/
  alignFracBits : ℤ
  /-- Lower bound on the alignment exponent, if the architecture has one. -/
  eAlignMin : Option ℤ
  deriving Repr, DecidableEq

/-- V100 FP16 -> FP32: `K = 4`, `(2, 23, 0)` alignment, no relevant floor. -/
def v100F16F32 : Model := ⟨fp16, 4, 23, none⟩

/-- The floor only raises a nonempty maximum; an all-zero block stays `none`. -/
def Model.applyEAlignMin (p : Model) : Option ℤ → Option ℤ
  | none => none
  | some e => some (match p.eAlignMin with | none => e | some f => max e f)

abbrev Model.Word (p : Model) := BitVec p.input.width

def Model.decode (p : Model) (x : p.Word) : Option Decoded := (classify p.input x).finite

end TensorCore
