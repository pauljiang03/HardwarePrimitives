import MatrixCore.MC.AlignmentMonotonicity
import MatrixCore.MC.AprioriBounds

/-! # When a rise of the products lowers the output

Larger products lower the output only if the accumulation loss grows by more than the gain of
the exact sum. -/

namespace MatrixCore

/-- The accumulation loss `R = (Σ p_ℓ + c) − S_acc`. -/
def BlockTrace.accumulationLoss {P : Model} (t : BlockTrace P) : ℚ := t.prepared.exact - t.sAcc

/-- The gain `Δ = (Σ p'_ℓ + c') − (Σ p_ℓ + c)` of the exact sum from `t` to `t'`. -/
def BlockTrace.gain {P : Model} (t t' : BlockTrace P) : ℚ := t'.prepared.exact - t.prepared.exact

/-- `S'_acc − S_acc = Δ − (R' − R)`. -/
theorem sAcc_sub_eq_gain_sub_loss {P : Model} (t t' : BlockTrace P) :
    t'.sAcc - t.sAcc = t.gain t' - (t'.accumulationLoss - t.accumulationLoss) := by
  unfold BlockTrace.gain BlockTrace.accumulationLoss; grind

theorem aligned_accumulationLoss {P : Model}
    (hacc : P.accumulation = .globalAlignment ∨ P.accumulation = .oddEvenGrouping)
    {x : BlockInput P} {t : BlockTrace P} (h : evalBlock x = .ok t) :
    t.accumulationLoss = t.prepared.exact - alignedAccumulation P t.prepared := by
  unfold BlockTrace.accumulationLoss
  rw [accumulate_aligned hacc (evalBlock_ok h).2.2.2.1]

/-- With every product at least as large and the same `c`, the gain is nonnegative. -/
theorem gain_nonneg {P : Model} {x x' : BlockInput P} {t t' : BlockTrace P}
    (h : evalBlock x = .ok t) (h' : evalBlock x' = .ok t') (hp : productsLE x x' = true)
    (hc : x.c = x'.c) : 0 ≤ t.gain t' := by
  have hs := ListRel.sumQ_le (ListRel.map (evalBlock_productsLE h h' hp))
  have hcc := evalBlock_same_c h h' hc
  unfold BlockTrace.gain Prepared.exact
  rw [hcc]
  grind

/-! ## Necessary and sufficient conditions -/

/-- An output decrease requires the loss to grow by more than the gain. -/
theorem output_decrease_requires_loss {P : Model} {x x' : BlockInput P} {t t' : BlockTrace P}
    (h : evalBlock x = .ok t) (h' : evalBlock x' = .ok t') (hlt : wordValue t'.d < wordValue t.d) :
    t'.sAcc < t.sAcc ∧ t.gain t' < t'.accumulationLoss - t.accumulationLoss := by
  have hs : t'.sAcc < t.sAcc := by
    apply Rat.not_le.mp
    intro hle
    exact Rat.not_le.mpr hlt (fl32_mono (evalBlock_ok h).2.2.2.2 (evalBlock_ok h').2.2.2.2 hle)
  have := sAcc_sub_eq_gain_sub_loss t t'
  exact ⟨hs, by grind⟩

theorem rneValue_of_finiteValue32 {y : ℚ} (hy : FiniteValue32 y) : rneValue y = y := by
  by_cases h0 : y = 0
  · subst h0; exact rneValue_zero
  · have ha := absQ_pos h0
    have hya : FiniteValue32 (absQ y) := by
      unfold absQ; split
      · exact hy.neg
      · exact hy
    have hn := (rneMagnitude_nearest ha hya).1
    rw [show absQ y - absQ y = 0 by grind, show absQ (0 : ℚ) = 0 from rfl] at hn
    have hm : rneMagnitude (absQ y) = absQ y := by
      have := absQ_eq_zero.mp (Rat.le_antisymm hn (absQ_nonneg _))
      grind
    unfold rneValue
    rw [hm]
    unfold absQ; split <;> grind

theorem wordValue_of_fl32_false {s : ℚ} {d : F32} (h : fl32 false s = some d) :
    wordValue d = rneValue s := by
  rw [fl32_false] at h
  unfold wordValue
  rw [rne32_value h]
  rfl

theorem evalBlock_output_of_finiteValue32 {P : Model} (hs : P.subnormals = true)
    {x : BlockInput P} {t : BlockTrace P} (h : evalBlock x = .ok t) (hv : FiniteValue32 t.sAcc) :
    wordValue t.d = t.sAcc := by
  have hd := (evalBlock_ok h).2.2.2.2
  rw [hs] at hd
  rw [wordValue_of_fl32_false hd, rneValue_of_finiteValue32 hv]

/-- With subnormals, the condition is sufficient when both values of `S_acc` are FP32 values. -/
theorem output_decrease_of_loss {P : Model} (hs : P.subnormals = true) {x x' : BlockInput P}
    {t t' : BlockTrace P} (h : evalBlock x = .ok t) (h' : evalBlock x' = .ok t')
    (hv : FiniteValue32 t.sAcc) (hv' : FiniteValue32 t'.sAcc)
    (hgt : t.gain t' < t'.accumulationLoss - t.accumulationLoss) :
    wordValue t'.d < wordValue t.d := by
  rw [evalBlock_output_of_finiteValue32 hs h hv, evalBlock_output_of_finiteValue32 hs h' hv']
  have := sAcc_sub_eq_gain_sub_loss t t'
  grind

/-- With subnormals and FP32 values of `S_acc`, the output falls iff the loss outgrows the gain. -/
theorem output_decrease_iff {P : Model} (hs : P.subnormals = true) {x x' : BlockInput P}
    {t t' : BlockTrace P} (h : evalBlock x = .ok t) (h' : evalBlock x' = .ok t')
    (hv : FiniteValue32 t.sAcc) (hv' : FiniteValue32 t'.sAcc) :
    wordValue t'.d < wordValue t.d ↔ t.gain t' < t'.accumulationLoss - t.accumulationLoss :=
  ⟨fun hlt => (output_decrease_requires_loss h h' hlt).2, output_decrease_of_loss hs h h' hv hv'⟩

/-- On CDNA 3 the loss outgrows the gain only through a change of alignment exponent. -/
theorem aligned_loss_exceeds_gain_changes_alignment {P : Model}
    (hacc : P.accumulation = .globalAlignment ∨ P.accumulation = .oddEvenGrouping)
    {x x' : BlockInput P} {t t' : BlockTrace P} (h : evalBlock x = .ok t)
    (h' : evalBlock x' = .ok t') (hp : productsLE x x' = true) (hc : x.c = x'.c)
    (hgt : t.gain t' < t'.accumulationLoss - t.accumulationLoss) :
    alignmentExponents P t.prepared.p ≠ alignmentExponents P t'.prepared.p := by
  intro he
  have hle := aligned_sAcc_monotone hacc h h' hp hc he
  have := sAcc_sub_eq_gain_sub_loss t t'
  grind

/-! ## How far the output can fall -/

theorem drop_le_of_errors {e e' d d' B B' : ℚ} (h : absQ (e - d) ≤ B) (h' : absQ (e' - d') ≤ B') :
    d - d' ≤ B + B' - (e' - e) := by
  rw [absQ_le_iff] at h h'
  grind

/-- How far a CDNA 3 output can fall: both blocks' error bounds minus the gain `Δ`. -/
theorem aligned_output_drop_le {P : Model}
    (hacc : P.accumulation = .globalAlignment ∨ P.accumulation = .oddEvenGrouping)
    (hcut : ∀ n, P.late.cCutoff = some n → P.late.cMantissaBits ≤ n) (hcz : P.cZeroExp ≠ none)
    {x x' : BlockInput P} {t t' : BlockTrace P} (h : evalBlock x = .ok t)
    (h' : evalBlock x' = .ok t') :
    wordValue t.d - wordValue t'.d ≤
      (alignedBound P t.prepared + flBound (!P.subnormals) t.sAcc) +
        (alignedBound P t'.prepared + flBound (!P.subnormals) t'.sAcc) - t.gain t' :=
  drop_le_of_errors (aligned_error hacc hcut hcz h) (aligned_error hacc hcut hcz h')

/-- How far a CDNA 3 output can fall, from the inputs alone. -/
theorem aligned_output_drop_apriori {P : Model} (hL : LateModel P)
    (hacc : P.accumulation = .globalAlignment ∨ P.accumulation = .oddEvenGrouping)
    (hsub : P.subnormals = true) {x x' : BlockInput P} {t t' : BlockTrace P}
    (h : evalBlock x = .ok t) (h' : evalBlock x' = .ok t') :
    wordValue t.d - wordValue t'.d ≤
      pow2 (-23) * (t.prepared.absSum + t'.prepared.absSum) +
        (t.prepared.p.length + 4) * gridTerm (productSum P t.prepared.p).1 +
        (t'.prepared.p.length + 4) * gridTerm (productSum P t'.prepared.p).1 + pow2 (-148) -
        t.gain t' := by
  have e1 := aligned_apriori hL hacc hsub h
  have e2 := aligned_apriori hL hacc hsub h'
  have hd := drop_le_of_errors e1 e2
  have c148 : pow2 (-148) = pow2 (-149) + pow2 (-149) := by decide +kernel
  unfold BlockTrace.gain
  rw [c148]
  grind

end MatrixCore
