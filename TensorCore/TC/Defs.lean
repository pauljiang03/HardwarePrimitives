import TensorCore.Numerics.Encoding

/-! Models of Tensor Cores: the numerical features of one block FMA. -/

namespace TensorCore


/-- Numerical features of one Tensor Core block FMA. -/
structure Model where
  /-- Input format of `a` and `b` (FP16, BF16, or packed TF32). -/
  input : Format
  /-- K, the FMA size N_FMA: the number of products added in a single multi-term addition. -/
  nfma : ℕ
  /-- F = 23 + p: the fractional bits each term keeps after alignment, with p extra alignment bits. -/
  alignFracBits : ℤ
  /-- The minimum alignment exponent e_align^min, if the architecture has one. -/
  eAlignMin : Option ℤ
  deriving Repr, DecidableEq

/-- V100 FP16 -> FP32: `K = 4`, `(2, 23, 0)` alignment, and no relevant minimum alignment exponent. -/
def v100F16F32 : Model := ⟨fp16, 4, 23, none⟩

/-- The minimum alignment exponent only raises a nonempty maximum; an all-zero block stays `none`. -/
def Model.applyEAlignMin (p : Model) : Option ℤ → Option ℤ
  | none => none
  | some e => some (match p.eAlignMin with | none => e | some f => max e f)

abbrev Model.Word (p : Model) := BitVec p.input.width

def Model.decode (p : Model) (x : p.Word) : Option Decoded := (classify p.input x).finite

end TensorCore
