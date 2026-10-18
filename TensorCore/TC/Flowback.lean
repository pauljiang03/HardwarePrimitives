import TensorCore.TC.Monotonicity
import TensorCore.Numerics.RoundTrip
import TensorCore.Numerics.ScalarSum
import TensorCore.TC.ErrorBounds

/-! TC-EFT Definitions III.2 and III.3 and Equation 6. -/

namespace TensorCore

/-- Definition III.2: for fixed products, a smaller accumulator input never gives a larger output. -/
def MonotoneInAccumulator (prof : Model) (products : List (Decoded × Decoded)) : Prop :=
  ∀ (c c' : Decoded) (t t' : BlockTrace),
    evalPrepared ⟨prof, products, c⟩ = .ok t → evalPrepared ⟨prof, products, c'⟩ = .ok t' →
    c'.value < c.value → t'.output.value ≤ t.output.value

/-- Definition III.3: `ω = Σᵢ (trunc_{q'A}(Tᵢ) − trunc_{qA}(Tᵢ))`, between the grids of `c` and `c'`. -/
def flowback (prof : Model) (products : List (Decoded × Decoded)) (c c' : Decoded) : ℚ :=
  sumQ (products.map fun (a, b) =>
    truncGrid (denormalizedMul a b).value (PreparedBlock.mk prof products c').alignGridExponent -
      truncGrid (denormalizedMul a b).value (PreparedBlock.mk prof products c).alignGridExponent)

/-- Definition III.3: `ΔA = trunc_{qA}(c) − trunc_{q'A}(c')`. -/
def accumulatorShift (prof : Model) (products : List (Decoded × Decoded)) (c c' : Decoded) :
    ℚ :=
  truncGrid c.value (PreparedBlock.mk prof products c).alignGridExponent -
    truncGrid c'.value (PreparedBlock.mk prof products c').alignGridExponent

/-- `A'acc = Aacc + ω − ΔA`. -/
theorem perturbed_accumulator (prof : Model) (products : List (Decoded × Decoded))
    (c c' : Decoded) :
    (PreparedBlock.mk prof products c').accumulator =
      (PreparedBlock.mk prof products c).accumulator + flowback prof products c c' -
        accumulatorShift prof products c c' := by
  rw [accumulator_value, accumulator_value]
  simp only [PreparedBlock.terms, List.map_cons, List.map_map, sumQ, Function.comp_def]
  unfold flowback accumulatorShift
  rw [sumQ_map_sub]
  have hc : DenormalizedProduct.value ⟨c.significand, c.exponent, c.mantissaBits⟩ = c.value := rfl
  have hc' : DenormalizedProduct.value ⟨c'.significand, c'.exponent, c'.mantissaBits⟩ = c'.value := rfl
  rw [hc, hc']
  grind

/-- With an FP32 block output, the output value is the signed truncation of the accumulator. -/
theorem evalPrepared_output_value {b : PreparedBlock} {t : BlockTrace}
    (h : evalPrepared b = .ok t) (hw : 23 ≤ b.model.outputMantissaBits) :
    t.output.value = signedRounded .truncate b.accumulator := by
  have hout := evalPrepared_output h hw
  have hd : value32 t.output.bits = some t.output.value := by
    simp [value32, t.output.valid, Finite32.value]
  by_cases hz : b.accumulator = 0
  · rw [hz] at hout
    have h0 : round32 .truncate 0 = some 0 := by decide +kernel
    rw [h0] at hout
    have hb : t.output.bits = 0 := (Option.some.inj hout).symm
    rw [hb] at hd
    have hv : value32 0 = some 0 := by decide +kernel
    rw [hv] at hd
    have hs : signedRounded .truncate 0 = 0 := by decide +kernel
    rw [hz, hs]
    exact (Option.some.inj hd).symm
  · obtain ⟨b', hb', hd', _, _⟩ :=
      round32_nonzero_spec .truncate b.accumulator hz (round32_range hout)
    rw [hout] at hb'
    cases Option.some.inj hb'
    rw [hd] at hd'
    exact Option.some.inj hd'

theorem magnitudeRounded_trunc_monotone (x y : ℚ) (hx : 0 ≤ x) (hxy : x ≤ y)
    (hy : y ≤ maxFinite32) :
    magnitudeRounded .truncate x ≤ magnitudeRounded .truncate y := by
  unfold magnitudeRounded roundedSignificand roundSignificand
  by_cases hx0 : x = 0
  · subst hx0
    have hqy := pow2_pos (normExp y - 23)
    have h0 : ((((0 : ℚ) / pow2 (normExp 0 - 23)).floor : ℤ) : ℚ) * pow2 (normExp 0 - 23) = 0 := by
      rw [Rat.div_def, Rat.zero_mul, ← Rat.intCast_zero, Rat.floor_intCast]
      simp
    rw [h0]
    have hfl : (0 : ℤ) ≤ (y / pow2 (normExp y - 23)).floor := by
      apply Rat.le_floor_iff.mpr
      have := div_nonneg_of_pos _ _ (Rat.le_trans hx hxy) hqy
      simpa using this
    have : (0 : ℚ) ≤ (((y / pow2 (normExp y - 23)).floor : ℤ) : ℚ) := by
      have := Rat.intCast_le_intCast.mpr hfl
      simpa using this
    exact Rat.mul_nonneg this (Rat.le_of_lt hqy)
  · have hxpos : 0 < x := by grind
    have hypos : 0 < y := by grind
    obtain ⟨hex1, _, hexlt, hexge⟩ := normExp_bounds x hxpos (Rat.le_trans hxy hy)
    obtain ⟨_, _, _, heyge⟩ := normExp_bounds y hypos hy
    have hmx := magnitudeExponent_spec x hxpos
    have hmy := magnitudeExponent_spec y hypos
    have hmono : magnitudeExponent x ≤ magnitudeExponent y := by
      apply Classical.byContradiction
      intro hne
      have := pow2_le_of_le (show magnitudeExponent y + 1 ≤ magnitudeExponent x by omega)
      grind
    have hce : normExp x ≤ normExp y := by unfold normExp; omega
    rcases Int.lt_or_eq_of_le hce with hlt | heq
    · have hqy := pow2_pos (normExp y - 23)
      have hey : pow2 (normExp y) ≤ y := by
        rcases heyge with h | h
        · exact h
        · exfalso; omega
      have hlow : pow2 (normExp y) ≤
          (((y / pow2 (normExp y - 23)).floor : ℤ) : ℚ) * pow2 (normExp y - 23) := by
        have h23 : ((8388608 : ℤ) : ℚ) * pow2 (normExp y - 23) = pow2 (normExp y) := by
          have : ((8388608 : ℤ) : ℚ) = pow2 23 := by decide +kernel
          rw [this, ← pow2_add]
          congr 1
          omega
        have hk : (8388608 : ℤ) ≤ (y / pow2 (normExp y - 23)).floor := by
          apply Rat.le_floor_iff.mpr
          apply le_div_of_mul_le _ _ _ hqy
          rw [h23]
          exact hey
        have := Rat.mul_le_mul_of_nonneg_right (Rat.intCast_le_intCast.mpr hk) (Rat.le_of_lt hqy)
        rw [h23] at this
        exact this
      have hqx := pow2_pos (normExp x - 23)
      have hhigh : (((x / pow2 (normExp x - 23)).floor : ℤ) : ℚ) * pow2 (normExp x - 23) ≤ x := by
        have := Rat.mul_le_mul_of_nonneg_right (Rat.floor_le (x / pow2 (normExp x - 23)))
          (Rat.le_of_lt hqx)
        rwa [Rat.div_mul_cancel (Rat.ne_of_gt hqx)] at this
      have hstep := pow2_le_of_le (show normExp x + 1 ≤ normExp y by omega)
      grind
    · rw [heq]
      have hq := pow2_pos (normExp y - 23)
      have hdiv : x / pow2 (normExp y - 23) ≤ y / pow2 (normExp y - 23) :=
        div_le_div_of_le_right _ _ _ hq hxy
      have hfl := Rat.floor_monotone hdiv
      exact Rat.mul_le_mul_of_nonneg_right (Rat.intCast_le_intCast.mpr hfl) (Rat.le_of_lt hq)

/-- Signed truncation is monotone within the finite range. -/
theorem signedRounded_trunc_monotone (x y : ℚ) (hxy : x ≤ y) (hx : absQ x ≤ maxFinite32)
    (hy : absQ y ≤ maxFinite32) :
    signedRounded .truncate x ≤ signedRounded .truncate y := by
  unfold signedRounded
  have hnonneg : ∀ z : ℚ, 0 ≤ magnitudeRounded .truncate (absQ z) := by
    intro z
    unfold magnitudeRounded roundedSignificand roundSignificand
    have hq := pow2_pos (normExp (absQ z) - 23)
    have hfl : (0 : ℤ) ≤ (absQ z / pow2 (normExp (absQ z) - 23)).floor := by
      apply Rat.le_floor_iff.mpr
      have := div_nonneg_of_pos _ _ (absQ_nonneg z) hq
      simpa using this
    have : (0 : ℚ) ≤ (((absQ z / pow2 (normExp (absQ z) - 23)).floor : ℤ) : ℚ) := by
      have := Rat.intCast_le_intCast.mpr hfl
      simpa using this
    exact Rat.mul_nonneg this (Rat.le_of_lt hq)
  by_cases hxn : x < 0
  · by_cases hyn : y < 0
    · rw [if_pos hxn, if_pos hyn]
      have hab : absQ y ≤ absQ x := by
        rw [absQ_of_neg hxn, absQ_of_neg hyn]
        grind
      have := magnitudeRounded_trunc_monotone (absQ y) (absQ x) (absQ_nonneg y) hab hx
      grind
    · rw [if_pos hxn, if_neg hyn]
      have h1 := hnonneg x
      have h2 := hnonneg y
      grind
  · have hyn : ¬ y < 0 := by grind
    rw [if_neg hxn, if_neg hyn]
    have hxnn : 0 ≤ x := by grind
    have hab : absQ x ≤ absQ y := by
      rw [absQ_of_nonneg hxnn, absQ_of_nonneg (Rat.le_trans hxnn hxy)]
      exact hxy
    exact magnitudeRounded_trunc_monotone (absQ x) (absQ y) (absQ_nonneg x) hab hy

theorem signedRounded_trunc_of_finite (x : ℚ) (h : FiniteValue32 x) :
    signedRounded .truncate x = x := by
  by_cases hz : x = 0
  · subst hz
    decide +kernel
  · obtain ⟨b, _, hv⟩ := round32_exact_of_finite h
    have hr := value32_round32 .truncate b x hv hz
    obtain ⟨b', hb', hd', _, _⟩ :=
      round32_nonzero_spec .truncate x hz (finiteValue32_abs_le h)
    rw [hr] at hb'
    cases Option.some.inj hb'
    rw [hv] at hd'
    exact (Option.some.inj hd').symm

/-- Equation 6: the outputs compare as the truncations of `Aacc` and `Aacc + ω − ΔA`. -/
theorem output_condition (prof : Model) (products : List (Decoded × Decoded))
    (c c' : Decoded) (t t' : BlockTrace)
    (h : evalPrepared ⟨prof, products, c⟩ = .ok t)
    (h' : evalPrepared ⟨prof, products, c'⟩ = .ok t') (hw : 23 ≤ prof.outputMantissaBits) :
    (t.output.value < t'.output.value ↔
      signedRounded .truncate (PreparedBlock.mk prof products c).accumulator <
        signedRounded .truncate ((PreparedBlock.mk prof products c).accumulator +
          flowback prof products c c' - accumulatorShift prof products c c')) := by
  rw [evalPrepared_output_value h hw, evalPrepared_output_value h' hw,
    perturbed_accumulator prof products c c']

/-- `ω > ΔA` is necessary for an output increase. -/
theorem flowback_necessary (prof : Model) (products : List (Decoded × Decoded))
    (c c' : Decoded) (t t' : BlockTrace)
    (h : evalPrepared ⟨prof, products, c⟩ = .ok t)
    (h' : evalPrepared ⟨prof, products, c'⟩ = .ok t') (hw : 23 ≤ prof.outputMantissaBits)
    (hinc : t.output.value < t'.output.value) :
    accumulatorShift prof products c c' < flowback prof products c c' := by
  apply Classical.byContradiction
  intro hle
  have hle' : flowback prof products c c' ≤ accumulatorShift prof products c c' := by grind
  have hA := perturbed_accumulator prof products c c'
  have hr := round32_range (evalPrepared_output h hw)
  have hr' := round32_range (evalPrepared_output h' hw)
  have hmono := signedRounded_trunc_monotone _ _
    (show (PreparedBlock.mk prof products c').accumulator ≤
      (PreparedBlock.mk prof products c).accumulator by rw [hA]; grind) hr' hr
  rw [evalPrepared_output_value h hw, evalPrepared_output_value h' hw] at hinc
  grind

/-- `ω > ΔA` is sufficient when both accumulators are representable. -/
theorem flowback_sufficient (prof : Model) (products : List (Decoded × Decoded))
    (c c' : Decoded) (t t' : BlockTrace)
    (h : evalPrepared ⟨prof, products, c⟩ = .ok t)
    (h' : evalPrepared ⟨prof, products, c'⟩ = .ok t') (hw : 23 ≤ prof.outputMantissaBits)
    (hA : FiniteValue32 (PreparedBlock.mk prof products c).accumulator)
    (hA' : FiniteValue32 (PreparedBlock.mk prof products c').accumulator)
    (hgt : accumulatorShift prof products c c' < flowback prof products c c') :
    t.output.value < t'.output.value := by
  rw [evalPrepared_output_value h hw, evalPrepared_output_value h' hw,
    signedRounded_trunc_of_finite _ hA, signedRounded_trunc_of_finite _ hA',
    perturbed_accumulator prof products c c']
  grind

theorem accumulatorShift_of_exact (prof : Model) (products : List (Decoded × Decoded))
    (c c' : Decoded)
    (hc : truncGrid c.value (PreparedBlock.mk prof products c).alignGridExponent = c.value)
    (hc' : truncGrid c'.value (PreparedBlock.mk prof products c').alignGridExponent = c'.value) :
    accumulatorShift prof products c c' = c.value - c'.value := by
  unfold accumulatorShift
  rw [hc, hc']

/-- Theorem III.4: the construction is not monotone in the accumulator input once `K ≥ 3·2^p`. -/
theorem construction_not_monotone (prof : Model) (p K : ℕ) (da db : Decoded)
    (hF : prof.alignMantissaBits = 23 + p) (hfl : ∀ f ∈ prof.eAlignMin, f ≤ -1)
    (hw : 23 ≤ prof.outputMantissaBits)
    (hval : (denormalizedMul da db).value = pow2 (-(24 + p))) (hscale : (denormalizedMul da db).exponent ≤ -1)
    (hK : K < 2 ^ (24 + p)) (hthr : 3 * 2 ^ p ≤ K) :
    ¬ MonotoneInAccumulator prof (List.replicate K (da, db)) := by
  intro hmono
  obtain ⟨t, t', h, h', hv, hiff⟩ :=
    nonmonotone_perturbation prof p K da db hF hfl hw hval hscale hK
  have hlt : belowOneDecoded.value < oneDecoded.value := by decide +kernel
  have := hmono oneDecoded belowOneDecoded t t' h h' hlt
  have h1 := hiff.mpr hthr
  rw [hv] at this
  grind

end TensorCore
