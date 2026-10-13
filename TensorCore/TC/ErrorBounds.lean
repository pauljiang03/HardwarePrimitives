import TensorCore.Numerics.RoundingError
import TensorCore.TC.StageResiduals
import TensorCore.Numerics.Truncation

/-! The model error bound. -/

namespace TensorCore

theorem evalPrepared_output {b : PreparedBlock} {t : BlockTrace}
    (h : evalPrepared b = .ok t) : round32 .truncate b.accumulator = some t.output.bits := by
  unfold evalPrepared at h
  cases hr : round32 .truncate b.accumulator with
  | none => simp [hr] at h
  | some bits =>
    cases hd : finite32 bits with
    | none => simp [hr, hd] at h
    | some d =>
      simp [hr, hd] at h
      cases h
      unfold finite32 at hd
      split at hd
      · contradiction
      · cases Option.some.inj hd
        rfl

theorem sum_residual_bounds (ts : List ℚ) (e : ℤ) :
    absQ (sumQ (ts.map fun x => x - truncGrid x e)) ≤ (ts.length : ℚ) * pow2 e ∧
    (ts ≠ [] → absQ (sumQ (ts.map fun x => x - truncGrid x e)) < (ts.length : ℚ) * pow2 e) := by
  induction ts with
  | nil =>
    have h : absQ (sumQ (List.map (fun x => x - truncGrid x e) [])) = 0 := by
      change absQ 0 = 0
      decide +kernel
    simp only [h, List.length_nil]
    constructor
    · grind
    · intro hn; exact False.elim (hn rfl)
  | cons x xs ih =>
    have hx := (alignment_residual x e).2
    have ht := absQ_add_le (x - truncGrid x e)
      (sumQ (xs.map fun t => t - truncGrid t e))
    have hs : ((xs.length + 1 : ℕ) : ℚ) = (xs.length : ℚ) + 1 := by
      rw [Rat.natCast_add]; rfl
    simp only [List.map_cons, sumQ, List.length_cons, hs]
    have hn : absQ ((x - truncGrid x e) + sumQ (xs.map fun t => t - truncGrid t e)) <
        ((xs.length : ℚ) + 1) * pow2 e := by grind
    exact ⟨Rat.le_of_lt hn, fun _ => hn⟩

theorem block_alignment_bound (b : PreparedBlock) :
    absQ (sumQ b.alignmentResiduals) < (b.terms.length : ℚ) * pow2 b.alignGridExponent := by
  have h := (sum_residual_bounds (b.terms.map UnnormalizedProduct.value) b.alignGridExponent).2
    (by simp [PreparedBlock.terms])
  simpa [PreparedBlock.alignmentResiduals, List.map_map, Function.comp_def] using h

/-- Two-stage error bound. -/
theorem block_error_bound (b : PreparedBlock) (d : Finite32)
    (hr : absQ b.accumulator ≤ maxFinite32)
    (hout : round32 .truncate b.accumulator = some d.bits) :
    absQ (b.exactDot - d.value) <
      (b.terms.length : ℚ) * pow2 b.alignGridExponent + pow2 (outputUlpExponent d.bits) := by
  have hd : value32 d.bits = some d.value := by simp [value32, d.valid, Finite32.value]
  have halign := block_alignment_bound b
  have houtput := output_residual_bound b.accumulator d.bits d.value hr hout hd
  have hid := block_residual_identity b d.value
  unfold PreparedBlock.extractReference at hid
  have ht := absQ_add_le (b.accumulator - d.value) (sumQ b.alignmentResiduals)
  have he : b.exactDot - d.value = (b.accumulator - d.value) + sumQ b.alignmentResiduals := by grind
  rw [he]; grind

theorem evalPrepared_error_bound {b : PreparedBlock} {t : BlockTrace}
    (h : evalPrepared b = .ok t) :
    absQ (t.block.exactDot - t.output.value) <
      (t.block.terms.length : ℚ) * pow2 t.block.alignGridExponent +
        pow2 (outputUlpExponent t.output.bits) := by
  have hb := evalPrepared_block h
  rw [hb]
  have hout := evalPrepared_output h
  exact block_error_bound b t.output (round32_range hout) hout

/-- The model error is below (number of terms) · (alignment grid step) + (one output ulp). -/
theorem evalBlock_error_bound {p : Model} {x : BlockInput p} {t : BlockTrace}
    (h : evalBlock x = .ok t) :
    absQ (t.block.exactDot - t.output.value) <
      (t.block.terms.length : ℚ) * pow2 t.block.alignGridExponent +
        pow2 (outputUlpExponent t.output.bits) :=
  evalPrepared_error_bound (evalBlock_evalPrepared h)

end TensorCore
