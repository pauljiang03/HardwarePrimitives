import TCFloat.Model

namespace TCFloat

@[simp] theorem mul_value (a b : Term) : (a.mul b).value = a.value * b.value :=
  FloatLib.Numerics.Dyadic.mul_toRat _ _

theorem terms_value (b : Block) : (b.terms.map Term.value).sum = b.ideal := by
  simp [Block.terms, Block.ideal, List.map_map, Function.comp_def]

private theorem split_sum (ts : List Term) (g : Term → ℚ) :
    (ts.map g).sum + (ts.map fun t => t.value - g t).sum = (ts.map Term.value).sum := by
  induction ts with
  | nil => simp
  | cons t ts ih => simp only [List.map_cons, List.sum_cons]; linarith

/-- Exact accounting of alignment loss and the final output rounding loss. -/
theorem recovery (t : Trace) : t.output + t.residual = t.block.ideal := by
  have h := split_sum t.block.terms (fun x => truncGrid x.value t.block.q)
  rw [terms_value] at h
  change t.block.accumulator + t.block.residuals.sum = t.block.ideal at h
  unfold Trace.residual
  linarith

/-- EFT reconstructs the exact input sum for any supplied output value. -/
theorem overlap_recovery (t : Trace) :
    t.output - t.overlap + t.lowParts.sum = t.block.ideal := by
  have h := split_sum t.block.terms (fun x => truncGrid x.value t.extractionExponent)
  rw [terms_value] at h
  change t.retained + t.lowParts.sum = t.block.ideal at h
  unfold Trace.overlap
  linarith

theorem retained_add_low (t : Trace) : t.retained + t.lowParts.sum = t.block.ideal := by
  have := overlap_recovery t
  unfold Trace.overlap at this
  linarith

theorem exactConsolidation_correct (t : Trace) :
    t.exactConsolidation = round32 .nearestEven t.block.ideal := by
  unfold Trace.exactConsolidation
  rw [overlap_recovery]

theorem round32_success_iff (mode : Mode) (x : ℚ) :
    (round32 mode x).isSome = true ↔ |x| ≤ maxFinite32 := by
  simp [round32]

theorem exactConsolidation_range (t : Trace) :
    t.exactConsolidation.isSome = true ↔ |t.block.ideal| ≤ maxFinite32 := by
  rw [exactConsolidation_correct, round32_success_iff]

theorem representable_add_exact (a b : ℚ) (h : representable (a+b) = true) :
    add32 a b = some (a+b) := by
  simpa [representable, add32] using h

theorem scalar_rejects (t : Trace) (h : t.scalarPredicate = false) : t.scalar = none := by
  simp [Trace.scalar, h]

theorem flowback_identity (ts us : List Term) (q q' : Int) :
    (us.map fun t => truncGrid t.value q').sum =
      (ts.map fun t => truncGrid t.value q).sum +
      ((us.map fun t => truncGrid t.value q').sum -
       (ts.map fun t => truncGrid t.value q').sum) +
      ((ts.map fun t => truncGrid t.value q').sum -
       (ts.map fun t => truncGrid t.value q).sum) := by ring

/-- Truncation to a fixed grid is monotone. -/
theorem truncGrid_mono (e : Int) : Monotone (fun x => truncGrid x e) := by
  have hp : 0 < pow2 e := zpow_pos (by norm_num) _
  intro a b hab
  dsimp only [truncGrid, truncCoeff]
  split_ifs with ha hb hb
  · apply mul_le_mul_of_nonneg_right _ hp.le
    exact_mod_cast neg_le_neg (Int.floor_mono (div_le_div_of_nonneg_right (neg_le_neg hab) hp.le))
  · have hf : 0 ≤ ⌊b / pow2 e⌋ := Int.floor_nonneg.mpr (div_nonneg (le_of_not_gt hb) hp.le)
    have hg : 0 ≤ ⌊-a / pow2 e⌋ := Int.floor_nonneg.mpr (div_nonneg (neg_nonneg.mpr ha.le) hp.le)
    apply mul_le_mul_of_nonneg_right _ hp.le
    exact_mod_cast (show -⌊-a / pow2 e⌋ ≤ ⌊b / pow2 e⌋ by omega)
  · exfalso; linarith
  · apply mul_le_mul_of_nonneg_right _ hp.le
    exact_mod_cast Int.floor_mono (div_le_div_of_nonneg_right hab hp.le)

/-- Signed truncation loses strictly less than one alignment quantum. -/
theorem truncGrid_error (x : ℚ) (e : Int) : |x-truncGrid x e| < pow2 e := by
  have hp : 0 < pow2 e := zpow_pos (by norm_num) _
  have bound (y : ℚ) (hy : 0 ≤ y) : 0 ≤ y - (⌊y/pow2 e⌋ : ℚ)*pow2 e ∧
      y - (⌊y/pow2 e⌋ : ℚ)*pow2 e < pow2 e := by
    have h1 := Int.floor_le (y/pow2 e)
    have h2 := Int.lt_floor_add_one (y/pow2 e)
    have := (le_div_iff₀ hp).mp h1
    have := (div_lt_iff₀ hp).mp h2
    constructor <;> nlinarith
  unfold truncGrid truncCoeff
  split_ifs with hx
  · have h := bound (-x) (by linarith)
    push_cast
    rw [abs_of_nonpos (by linarith)]
    linarith
  · have h := bound x (le_of_not_gt hx)
    rw [abs_of_nonneg h.1]
    exact h.2

end TCFloat
