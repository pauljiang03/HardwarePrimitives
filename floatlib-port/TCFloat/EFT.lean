import TCFloat.Rounding

namespace TCFloat

private theorem sum_coefficients (zs : List Int) (q : ℚ) :
    (zs.map fun (z : Int) => (z : ℚ)*q).sum = (zs.sum : ℚ)*q := by
  induction zs with
  | nil => simp
  | cons z zs ih => simp only [List.map_cons, List.sum_cons, Int.cast_add, ih, add_mul]

/-- Every prefix fits the source coefficient bound, so sequential FP32 addition is exact. -/
theorem naiveSumFrom_exact (zs : List Int) (a e : Int) (hmin : -149 ≤ e) (hmax : e ≤ 104)
    (hbound : a.natAbs + (zs.map Int.natAbs).sum < 2^24) :
    naiveSumFrom ((a : ℚ)*pow2 e) (zs.map fun (z : Int) => (z : ℚ)*pow2 e) =
      some (((a + zs.sum : Int) : ℚ)*pow2 e) := by
  induction zs generalizing a with
  | nil => simp [naiveSumFrom]
  | cons z zs ih =>
    have htri := Int.natAbs_add_le a z
    have hb : (a+z).natAbs + (zs.map Int.natAbs).sum < 2^24 := by
      simp only [List.map_cons, List.sum_cons] at hbound
      omega
    have hz : (a+z).natAbs < 2^24 := by omega
    have hr := grid_representable (a+z) e hmin hmax hz
    have ha : add32 ((a : ℚ)*pow2 e) ((z : ℚ)*pow2 e) =
        some (((a+z : Int) : ℚ)*pow2 e) := by
      convert representable_add_exact ((a : ℚ)*pow2 e) ((z : ℚ)*pow2 e) (by
        simpa [Int.cast_add, add_mul] using hr) using 1
      simp [Int.cast_add, add_mul]
    simp only [List.map_cons, naiveSumFrom, ha, Option.bind_some]
    rw [ih (a+z) hb]
    simp [add_assoc]

theorem scalarUnchecked_correct (t : Trace) (h : t.scalarPredicate = true) :
    t.scalarUnchecked = round32 .nearestEven t.block.ideal := by
  unfold Trace.scalarPredicate at h
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨hmin,hmax⟩,hgrid⟩,hbound⟩,_⟩,_⟩,hH⟩,_⟩ := h
  have hs : naiveSumFrom 0 t.lowParts = some t.lowParts.sum := by
    rw [hgrid, sum_coefficients]
    simpa using naiveSumFrom_exact t.lowCoefficients 0 t.supportExponent hmin hmax (by simpa using hbound)
  have hh : t.output + -t.overlap = t.retained := by unfold Trace.overlap; ring
  have ha : add32 t.output (-t.overlap) = some t.retained := by
    simpa [hh] using representable_add_exact t.output (-t.overlap) (by simpa [hh] using hH)
  simp only [Trace.scalarUnchecked, hs, ha, Option.bind_some]
  rw [retained_add_low]

theorem scalar_correct (t : Trace) (h : t.scalarPredicate = true) :
    t.scalar = round32 .nearestEven t.block.ideal := by
  simp [Trace.scalar, h, scalarUnchecked_correct t h]

theorem scalar_success_iff (t : Trace) : t.scalar.isSome = true ↔ t.scalarPredicate = true := by
  constructor
  · intro h
    unfold Trace.scalar at h
    split at h
    · assumption
    · simp at h
  · intro h
    rw [scalar_correct t h, round32_success_iff]
    have hh : |t.retained + t.lowParts.sum| ≤ maxFinite32 := by
      unfold Trace.scalarPredicate at h
      simp only [Bool.and_eq_true, decide_eq_true_eq] at h
      exact h.2
    rwa [retained_add_low] at hh

/-- Both consolidation branches return precisely FloatLib RNE of the independent ideal. -/
theorem algorithm_correct (t : Trace) : t.algorithm.1 = round32 .nearestEven t.block.ideal := by
  unfold Trace.algorithm
  cases hs : t.scalar with
  | some bits =>
    have hp : t.scalarPredicate = true := (scalar_success_iff t).mp (by rw [hs]; rfl)
    exact hs.symm.trans (scalar_correct t hp)
  | none =>
    rw [exactConsolidation_correct]
    cases round32 .nearestEven t.block.ideal <;> rfl

theorem algorithm_range (t : Trace) : t.algorithm.1.isSome = true ↔ |t.block.ideal| ≤ maxFinite32 := by
  rw [algorithm_correct, round32_success_iff]

private theorem zero_terms_ideal (t : Trace)
    (h : t.block.terms.all (fun x => x.dyadic.significand == 0) = true) : t.block.ideal = 0 := by
  rw [← terms_value]
  apply List.sum_eq_zero
  intro x hx
  obtain ⟨u,hu,rfl⟩ := List.mem_map.mp hx
  have hs := List.all_eq_true.mp h u hu
  exact (FloatLib.Numerics.Dyadic.toRat_eq_zero_iff _).mpr (by simpa using hs)

theorem encodedAlgorithm_correct (t : Trace) :
    t.encodedAlgorithm.1 = round32 .nearestEven t.block.ideal := by
  unfold Trace.encodedAlgorithm
  split
  · rename_i hz
    rw [zero_terms_ideal t hz]
    decide +kernel
  · exact algorithm_correct t

/-- Output of the encoded EFT has FloatLib's mathematical nearest-even denotation. -/
theorem encodedAlgorithm_nearest (t : Trace) (bits : Nat)
    (h : t.encodedAlgorithm.1 = some bits) :
    ∃ y, value32 bits = some y ∧ (y : ℝ) =
      FloatLib.Floats.Formats.BinaryInterchange.Model.roundAt .binary32 (t.block.ideal : ℝ) := by
  rw [encodedAlgorithm_correct] at h
  have hr : |t.block.ideal| ≤ maxFinite32 := (round32_success_iff _ _).mp (by rw [h]; rfl)
  obtain ⟨bits',y,hb,hy,he⟩ := round32_nearest_real t.block.ideal hr
  have : bits' = bits := Option.some.inj (hb.symm.trans h)
  subst bits'
  exact ⟨y,hy,he⟩

end TCFloat
