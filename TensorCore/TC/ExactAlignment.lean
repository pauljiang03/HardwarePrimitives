import TensorCore.TC.Canonical

/-! When alignment loses nothing. -/

namespace TensorCore

/-- Sufficient alignment precision for this actual input, retaining unnormalized-exponent metadata. -/
def PreparedBlock.AlignmentExact (b : PreparedBlock) : Prop :=
  ∀ t ∈ b.terms, t.significand ≠ 0 →
    b.alignGridExponent ≤ t.unnormalizedExp - t.mantissaBits

theorem exact_alignment_accumulator (b : PreparedBlock) (h : b.AlignmentExact) :
    b.accumulator = b.exactDot := by
  rw [accumulator_value, ← terms_value]
  congr 1
  apply List.map_congr_left
  intro t ht
  by_cases hz : t.significand = 0
  · simp [UnnormalizedProduct.value, hz, truncGrid, truncBits, Rat.div_def]
    have hf : (0 : ℚ).floor = 0 := rfl
    rw [hf]
    simp
  · exact truncGrid_exact_of_grid t.significand (t.unnormalizedExp - t.mantissaBits)
      b.alignGridExponent (h t ht hz)

/-- If the extra alignment bits make every term exactly alignable, the canonical output is a single FP32 RTZ conversion of the independently decoded ideal sum. -/
theorem evalBlock_exact_alignment {p : Model} {x : BlockInput p} {t : BlockTrace}
    (he : evalBlock x = .ok t) (ha : t.block.AlignmentExact) :
    exactDot x = some t.block.exactDot ∧
    round32 .truncate t.block.exactDot = some t.output.bits := by
  have hout := evalPrepared_output (evalBlock_evalPrepared he)
  rw [exact_alignment_accumulator t.block ha] at hout
  exact ⟨by simp [exactDot, evalBlock_prepared he], hout⟩

end TensorCore
