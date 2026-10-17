import MatrixCore

/-! # Chains of MFMA blocks

A chain schedule for one output entry on the matrix-core model: a list of blocks, each block's
output word `d` the next block's `c`. -/

open MatrixCore

namespace MMAlgebra.MC

/-- A chain of blocks from `c`, each block's `d` the next block's `c`. -/
def chain (P : Model) (c : F32) (bs : List (List P.a.Word × List P.b.Word)) : Except ModelError F32 :=
  bs.foldlM (fun c ab => blockBits (P := P) ⟨ab.1, ab.2, c⟩) c

end MMAlgebra.MC
