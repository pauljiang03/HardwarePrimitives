import TensorCore.TC.Block

/-! The exact sum equals output plus named residuals. -/

namespace TensorCore

theorem sum_stage_residuals (ts : List ℚ) (align : ℚ → ℚ) :
    sumQ ts = sumQ (ts.map align) + sumQ (ts.map fun x => x - align x) := by
  induction ts with
  | nil => change (0 : ℚ) = 0 + 0; grind
  | cons t ts ih =>
    simp only [List.map_cons, sumQ]
    grind

theorem terms_value (b : PreparedBlock) :
    sumQ (b.terms.map UnnormalizedProduct.value) = b.exactDot := by
  simp only [PreparedBlock.terms, PreparedBlock.exactDot,
    PreparedBlock.exactProducts, List.map_cons, List.map_map, sumQ]
  have h : (fun (p : Decoded × Decoded) => (unnormalizedMul p.1 p.2).value) =
      (fun p => p.1.value * p.2.value) := by
    funext p
    exact unnormalizedProduct_value p.1 p.2
  simp only [Function.comp_def] at *
  rw [h]
  rfl

theorem accumulator_value (b : PreparedBlock) :
    b.accumulator = sumQ (b.terms.map fun t => truncGrid t.value b.alignGridExponent) := by
  unfold PreparedBlock.accumulator PreparedBlock.alignedBits
  rw [← sum_coefficients]
  simp [List.map_map, Function.comp_def, truncGrid]

/-- Exact recovery applies to any supplied finite value, independently of model conformance. -/
theorem block_residual_identity (b : PreparedBlock) (d : ℚ) :
    b.exactDot = d + b.extractReference d := by
  have h := sum_stage_residuals (b.terms.map UnnormalizedProduct.value)
    (fun t => truncGrid t b.alignGridExponent)
  rw [terms_value] at h
  simp only [List.map_map, Function.comp_def] at h
  rw [← accumulator_value] at h
  change b.exactDot = d + ((b.accumulator - d) + sumQ b.alignmentResiduals)
  change b.exactDot = b.accumulator + sumQ b.alignmentResiduals at h
  grind

theorem returned_residual_identity (t : BlockTrace) :
    t.block.exactDot = t.output.value + t.residual :=
  block_residual_identity t.block t.output.value

theorem recovered_eq_exactDot (t : BlockTrace) : t.recovered = t.block.exactDot :=
  (returned_residual_identity t).symm

/-- This is substitution into the executable converter, not a nearest-value correctness proof. -/
theorem corrected_eq_round_exactDot (t : BlockTrace) :
    t.corrected = round32 .nearestEven t.block.exactDot := by
  unfold BlockTrace.corrected
  rw [recovered_eq_exactDot]

theorem evalPrepared_block {b : PreparedBlock} {t : BlockTrace}
    (h : evalPrepared b = .ok t) : t.block = b := by
  unfold evalPrepared at h
  cases hr : round32 .truncate b.accumulator with
  | none => simp [hr] at h
  | some bits =>
    cases hd : finite32 bits with
    | none => simp [hr, hd] at h
    | some d =>
      simp [hr, hd] at h
      cases h
      rfl

theorem evalBlock_prepared {p : Model} {x : BlockInput p} {t : BlockTrace}
    (h : evalBlock x = .ok t) : prepare x = some t.block := by
  unfold evalBlock at h
  split at h
  · simp at h
  · cases hp : prepare x with
    | none => simp [hp] at h
    | some b =>
      simp [hp] at h
      rw [evalPrepared_block h]

theorem evalBlock_evalPrepared {p : Model} {x : BlockInput p} {t : BlockTrace}
    (h : evalBlock x = .ok t) : evalPrepared t.block = .ok t := by
  have hp := evalBlock_prepared h
  unfold evalBlock at h
  split at h
  · simp at h
  · rw [hp] at h
    exact h

/-- End-to-end local recovery, connected to the executable encoded-input evaluator. -/
theorem evalBlock_residual_identity {p : Model} {x : BlockInput p} {t : BlockTrace}
    (h : evalBlock x = .ok t) :
    exactDot x = some (t.output.value + t.residual) := by
  simp only [exactDot, evalBlock_prepared h, Option.map_some]
  rw [returned_residual_identity]

theorem prepare_c {p : Model} {x : BlockInput p} {b : PreparedBlock}
    (h : prepare x = some b) : decode32 x.c = some b.c := by
  unfold prepare at h
  cases hc : decode32 x.c with
  | none => simp [hc] at h
  | some c =>
    cases hp : prepareProducts p x.products with
    | none => simp [hc, hp] at h
    | some ps =>
      simp [hc, hp] at h
      cases h
      rfl

theorem evalBlock_c {p : Model} {x : BlockInput p} {t : BlockTrace}
    (h : evalBlock x = .ok t) : decode32 x.c = some t.block.c :=
  prepare_c (evalBlock_prepared h)

/-- Preparation retains the encoded input's profile, even if later evaluation rejects it. -/
theorem prepare_model {p : Model} {x : BlockInput p} {b : PreparedBlock}
    (hp : prepare x = some b) : b.model = p := by
  unfold prepare at hp
  cases hc : decode32 x.c with
  | none => simp [hc] at hp
  | some c =>
    cases hps : prepareProducts p x.products with
    | none => simp [hc, hps] at hp
    | some ps =>
      simp [hc, hps] at hp
      rw [← hp]

/-- The profile of a successful trace is the profile of its input. -/
theorem evalBlock_model {p : Model} {x : BlockInput p} {t : BlockTrace}
    (h : evalBlock x = .ok t) : t.block.model = p :=
  prepare_model (evalBlock_prepared h)

end TensorCore
