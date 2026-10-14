import TCFloat.EFT

namespace TCFloat

private theorem sum_sub (ts : List Term) (f g : Term → ℚ) :
    (ts.map fun t => f t-g t).sum = (ts.map f).sum-(ts.map g).sum := by
  induction ts with
  | nil => simp
  | cons t ts ih => simp only [List.map_cons, List.sum_cons, ih]; ring

/-- Flowback of fixed products when C selects a different alignment grid. -/
def flowback (p : TCModel) (ps : List (Term × Term)) (c c' : Term) : ℚ :=
  let before : Block := ⟨p,c,ps⟩
  let after : Block := ⟨p,c',ps⟩
  (ps.map fun (a,b) => truncGrid (a.mul b).value after.q - truncGrid (a.mul b).value before.q).sum

def accumulatorShift (p : TCModel) (ps : List (Term × Term)) (c c' : Term) : ℚ :=
  truncGrid c.value (Block.q ⟨p,c,ps⟩) - truncGrid c'.value (Block.q ⟨p,c',ps⟩)

/-- The grids the model selects, not an assumption that the grids stay fixed. -/
theorem perturbed_accumulator (p : TCModel) (ps : List (Term × Term)) (c c' : Term) :
    (Block.accumulator ⟨p,c',ps⟩) = (Block.accumulator ⟨p,c,ps⟩) +
      flowback p ps c c' - accumulatorShift p ps c c' := by
  have hs := sum_sub (ps.map fun (a,b) => a.mul b)
    (fun t => truncGrid t.value (Block.q ⟨p,c',ps⟩))
    (fun t => truncGrid t.value (Block.q ⟨p,c,ps⟩))
  simp only [List.map_map, Function.comp_def] at hs
  simp only [Block.accumulator, Block.aligned, Block.terms, List.map_cons, List.sum_cons,
    List.map_map, Function.comp_def, flowback, accumulatorShift]
  rw [hs]
  ring

/-- Flowback exceeds the lost retained C exactly when the internal accumulator rises. -/
theorem accumulator_increase_iff (p : TCModel) (ps : List (Term × Term)) (c c' : Term) :
    (Block.accumulator ⟨p,c,ps⟩) < (Block.accumulator ⟨p,c',ps⟩) ↔
      accumulatorShift p ps c c' < flowback p ps c c' := by
  rw [perturbed_accumulator p ps c c']
  constructor <;> intro h <;> linarith

/-- Without an alignment-grid change, changing C monotonically changes the accumulator. -/
theorem accumulator_monotone_same_grid (p : TCModel) (ps : List (Term × Term)) (c c' : Term)
    (hc : c.value ≤ c'.value) (hq : Block.q ⟨p,c,ps⟩ = Block.q ⟨p,c',ps⟩) :
    Block.accumulator ⟨p,c,ps⟩ ≤ Block.accumulator ⟨p,c',ps⟩ := by
  simp only [Block.accumulator, Block.aligned, Block.terms, List.map_cons, List.sum_cons,
    List.map_map, Function.comp_def, hq]
  exact add_le_add (truncGrid_mono _ hc) le_rfl

private theorem residual_sum_bound (ts : List Term) (q : Int) :
    |(ts.map fun x => x.value-truncGrid x.value q).sum| ≤ (ts.length : ℚ)*pow2 q ∧
    (ts ≠ [] → |(ts.map fun x => x.value-truncGrid x.value q).sum| < (ts.length : ℚ)*pow2 q) := by
  induction ts with
  | nil => simp
  | cons t ts ih =>
    have ht := truncGrid_error t.value q
    have ha := abs_add_le (t.value-truncGrid t.value q)
      (ts.map fun x => x.value-truncGrid x.value q).sum
    simp only [List.map_cons, List.sum_cons, List.length_cons, Nat.cast_add, Nat.cast_one]
    have hb : |t.value - truncGrid t.value q + (ts.map fun x => x.value-truncGrid x.value q).sum| <
        ((ts.length : ℚ)+1)*pow2 q := by linarith [ih.1]
    exact ⟨hb.le, fun _ => hb⟩

theorem alignment_error_bound (b : Block) :
    |b.ideal-b.accumulator| < (b.terms.length : ℚ)*pow2 b.q := by
  have hr := residual_sum_bound b.terms b.q
  have he : b.ideal-b.accumulator = b.residuals.sum := by
    have h := recovery (⟨b,0,0⟩ : Trace)
    simp only [Trace.residual, zero_add, sub_zero] at h
    linarith
  rw [he]
  exact hr.2 (by simp [Block.terms])

/-- Total error splits into alignment loss and the actual FloatLib output-rounding loss. -/
theorem total_error_bound (t : Trace) :
    |t.block.ideal-t.output| < (t.block.terms.length : ℚ)*pow2 t.block.q +
      |t.block.accumulator-t.output| := by
  have h := alignment_error_bound t.block
  have hs := abs_add_le (t.block.ideal-t.block.accumulator) (t.block.accumulator-t.output)
  have he : t.block.ideal-t.block.accumulator+(t.block.accumulator-t.output) =
      t.block.ideal-t.output := by ring
  rw [he] at hs
  linarith

/-- Full encoded FloatLib computation, suitable for closed kernel-checked examples. -/
def evalWords (p : TCModel) (ps : List (Nat × Nat)) (c : Nat) : Option Nat :=
  (prepare p ps c).bind Block.evaluate

/-- Decreasing C by one FP32 step increases the TC output: the actual V100 model. -/
theorem v100_nonmonotonic :
    evalWords v100 (List.replicate 4 (0x0c00,0x0c00)) 0x3f800000 = some 0x3f800000 ∧
    evalWords v100 (List.replicate 4 (0x0c00,0x0c00)) 0x3f7fffff = some 0x3f800001 := by
  decide +kernel

/-- The same phenomenon with the padding bit of the A100 model. -/
theorem a100_nonmonotonic :
    evalWords a100 (List.replicate 8 (0x0c00,0x0800)) 0x3f800000 = some 0x3f800000 ∧
    evalWords a100 (List.replicate 8 (0x0c00,0x0800)) 0x3f7fffff = some 0x3f800001 := by
  decide +kernel

/-- The same phenomenon with the two padding bits of the H100 model. -/
theorem h100_nonmonotonic :
    evalWords h100 (List.replicate 16 (0x0c00,0x0400)) 0x3f800000 = some 0x3f800000 ∧
    evalWords h100 (List.replicate 16 (0x0c00,0x0400)) 0x3f7fffff = some 0x3f800001 := by
  decide +kernel

end TCFloat
