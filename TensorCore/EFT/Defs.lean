import TensorCore.TC.Block
import TensorCore.Numerics.ScalarSum

/-! Extraction components of a Tensor Core trace. -/

namespace TensorCore

/-- Extraction grid exponent: `qE = max(qA, qD)` (TC-EFT eq. 11). -/
def BlockTrace.extractionExponent (t : BlockTrace) : ℤ :=
  max t.block.alignGridExponent (outputUlpExponent t.output.bits)

/-- Coarse retained components `hᵢ = trunc_qE(Tᵢ)` (Lemma IV.1); `c` is term zero. -/
def BlockTrace.coarse (t : BlockTrace) : List ℚ :=
  t.block.terms.map fun x => truncGrid x.value t.extractionExponent

/-- Low components `εᵢ = Tᵢ − hᵢ`. -/
def BlockTrace.lowParts (t : BlockTrace) : List ℚ :=
  t.block.terms.map fun x => x.value - truncGrid x.value t.extractionExponent

/-- `H = Σ hᵢ`. -/
def BlockTrace.retainedSum (t : BlockTrace) : ℚ := sumQ t.coarse

/-- Signed overlap correction `ε_o = D − H` (Lemma IV.4). -/
def BlockTrace.overlap (t : BlockTrace) : ℚ := t.output.value - t.retainedSum

/-- Overlapping bits of the low components, `φ(εᵢ) = trunc_qA(εᵢ)`. -/
def BlockTrace.retainedLowParts (t : BlockTrace) : List ℚ :=
  t.lowParts.map fun e => truncGrid e t.block.alignGridExponent

end TensorCore
