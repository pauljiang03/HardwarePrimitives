import TensorCore.TC.Canonical

/-! When alignment loses nothing. -/

namespace TensorCore

/-- Sufficient alignment precision for this input. -/
def PreparedBlock.AlignmentExact (b : PreparedBlock) : Prop :=
  ∀ t ∈ b.terms, t.significand ≠ 0 →
    b.alignGridExponent ≤ t.exponent - t.mantissaBits

theorem exact_alignment_accumulator (b : PreparedBlock) (h : b.AlignmentExact) :
    b.accumulator = b.exactDot := by
  rw [accumulator_value, ← terms_value]
  congr 1
  apply List.map_congr_left
  intro t ht
  by_cases hz : t.significand = 0
  · simp [DenormalizedProduct.value, hz, truncGrid, truncBits, Rat.div_def]
    have hf : (0 : ℚ).floor = 0 := rfl
    rw [hf]
    simp
  · exact truncGrid_exact_of_grid t.significand (t.exponent - t.mantissaBits)
      b.alignGridExponent (h t ht hz)

/-- With exact alignment and an FP32 block output, the output is the RTZ conversion of the exact sum. -/
theorem evalBlock_exact_alignment {p : Model} {x : BlockInput p} {t : BlockTrace}
    (he : evalBlock x = .ok t) (ha : t.block.AlignmentExact) (hw : 23 ≤ p.outputMantissaBits) :
    exactDot x = some t.block.exactDot ∧
    round32 .truncate t.block.exactDot = some t.output.bits := by
  have hout := evalBlock_output he hw
  rw [exact_alignment_accumulator t.block ha] at hout
  exact ⟨by simp [exactDot, evalBlock_prepared he], hout⟩

end TensorCore
