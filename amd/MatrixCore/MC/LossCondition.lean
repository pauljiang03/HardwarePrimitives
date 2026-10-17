import MatrixCore.MC.AlignmentMonotonicity
import MatrixCore.MC.AprioriBounds

/-! # When a rise of the products lowers the output

The output of a block is `d = fl{S_acc}`. Write `R = (Σ p_ℓ + c) − S_acc` for the loss of the
accumulation (`BlockTrace.accumulationLoss`): on CDNA 3 the loss of the alignment of the products
and of the late accumulation of `c`, on CDNA 2 that of flushing, of the conversions of the
products and of the pairwise sums, and zero on CDNA 1. From one block to another the exact sum
changes by the gain `Δ` (`BlockTrace.gain`), which is nonnegative when every product is at least
as large and `c` is the same (`gain_nonneg`), and

  `S'_acc − S_acc = Δ − (R' − R)`.

This is the AMD counterpart of the TC-EFT paper's flowback condition, with the roles reversed:
there a smaller `c` raises the output only if the products recovered by the finer alignment grid
(the flowback `ω`) exceed the decrease `ΔA` of the aligned `c`; here larger products lower the
output only if the growth `R' − R` of the loss exceeds the gain `Δ`.

* An output decrease requires `R' − R > Δ`, that is `S'_acc < S_acc`, on every configuration
  (`output_decrease_requires_loss`).
* The condition is sufficient when both values of `S_acc` are binary32 values, which the final
  RNE returns unchanged (`output_decrease_of_loss`, `output_decrease_iff`).
* On CDNA 3, with every product at least as large and the same `c`, `R' − R > Δ` needs a change of
  an alignment exponent (`aligned_loss_exceeds_gain_changes_alignment`).
* The drop `d − d'` on CDNA 3 is at most the two blocks' error bounds minus the gain, from the
  computed values (`aligned_output_drop_le`) or from the inputs alone
  (`aligned_output_drop_apriori`). -/

namespace MatrixCore

/-- The loss of the accumulation of an evaluated block, `R = (Σ p_ℓ + c) − S_acc`. -/
def BlockTrace.accumulationLoss {P : Model} (t : BlockTrace P) : ℚ := t.prepared.exact - t.sAcc

/-- The gain `Δ = (Σ p'_ℓ + c') − (Σ p_ℓ + c)` of the exact sum from the block of `t` to that of
`t'`. -/
def BlockTrace.gain {P : Model} (t t' : BlockTrace P) : ℚ := t'.prepared.exact - t.prepared.exact

/-- The change of `S_acc` is the gain minus the growth of the loss:
`S'_acc − S_acc = Δ − (R' − R)`. -/
theorem sAcc_sub_eq_gain_sub_loss {P : Model} (t t' : BlockTrace P) :
    t'.sAcc - t.sAcc = t.gain t' - (t'.accumulationLoss - t.accumulationLoss) := by
  unfold BlockTrace.gain BlockTrace.accumulationLoss; grind

/-- On CDNA 3 the loss is that of Algorithm 1 or 2: `R = (Σ p_ℓ + c) − S_acc` with `S_acc` of
the alignment and the late accumulation of `c`. -/
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

/-- **An output decrease requires the loss to grow by more than the gain.** On every
configuration, if the output of the second block is smaller, then `S'_acc < S_acc`, that is
`R' − R > Δ`. -/
theorem output_decrease_requires_loss {P : Model} {x x' : BlockInput P} {t t' : BlockTrace P}
    (h : evalBlock x = .ok t) (h' : evalBlock x' = .ok t') (hlt : wordValue t'.d < wordValue t.d) :
    t'.sAcc < t.sAcc ∧ t.gain t' < t'.accumulationLoss - t.accumulationLoss := by
  have hs : t'.sAcc < t.sAcc := by
    apply Rat.not_le.mp
    intro hle
    exact Rat.not_le.mpr hlt (fl32_mono (evalBlock_ok h).2.2.2.2 (evalBlock_ok h').2.2.2.2 hle)
  have := sAcc_sub_eq_gain_sub_loss t t'
  exact ⟨hs, by grind⟩

/-- The RNE of a finite binary32 value is the value itself. -/
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

/-- Without flushing, the value of `fl{s}` is the RNE value of `s`. -/
theorem wordValue_of_fl32_false {s : ℚ} {d : F32} (h : fl32 false s = some d) :
    wordValue d = rneValue s := by
  rw [fl32_false] at h
  unfold wordValue
  rw [rne32_value h]
  rfl

/-- On a model with subnormals, an accepted block whose `S_acc` is a binary32 value returns it. -/
theorem evalBlock_output_of_finiteValue32 {P : Model} (hs : P.subnormals = true)
    {x : BlockInput P} {t : BlockTrace P} (h : evalBlock x = .ok t) (hv : FiniteValue32 t.sAcc) :
    wordValue t.d = t.sAcc := by
  have hd := (evalBlock_ok h).2.2.2.2
  rw [hs] at hd
  rw [wordValue_of_fl32_false hd, rneValue_of_finiteValue32 hv]

/-- **The condition is sufficient when both `S_acc` are binary32 values.** On a model with
subnormals (CDNA 1, CDNA 3), if `R' − R > Δ` and both values of `S_acc` are finite binary32
values, which the final RNE returns unchanged, then the output of the second block is smaller. -/
theorem output_decrease_of_loss {P : Model} (hs : P.subnormals = true) {x x' : BlockInput P}
    {t t' : BlockTrace P} (h : evalBlock x = .ok t) (h' : evalBlock x' = .ok t')
    (hv : FiniteValue32 t.sAcc) (hv' : FiniteValue32 t'.sAcc)
    (hgt : t.gain t' < t'.accumulationLoss - t.accumulationLoss) :
    wordValue t'.d < wordValue t.d := by
  rw [evalBlock_output_of_finiteValue32 hs h hv, evalBlock_output_of_finiteValue32 hs h' hv']
  have := sAcc_sub_eq_gain_sub_loss t t'
  grind

/-- **Necessary and sufficient.** On a model with subnormals, when both values of `S_acc` are
binary32 values, the output falls exactly when the loss grows by more than the gain. -/
theorem output_decrease_iff {P : Model} (hs : P.subnormals = true) {x x' : BlockInput P}
    {t t' : BlockTrace P} (h : evalBlock x = .ok t) (h' : evalBlock x' = .ok t')
    (hv : FiniteValue32 t.sAcc) (hv' : FiniteValue32 t'.sAcc) :
    wordValue t'.d < wordValue t.d ↔ t.gain t' < t'.accumulationLoss - t.accumulationLoss :=
  ⟨fun hlt => (output_decrease_requires_loss h h' hlt).2, output_decrease_of_loss hs h h' hv hv'⟩

/-- **On CDNA 3 the loss outgrows the gain only through a change of alignment exponent.** With
the same `c` and every product at least as large, `R' − R > Δ` requires different alignment
exponents (`e_max`, or a group exponent with odd/even grouping). -/
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

/-- Two outputs within `B` and `B'` of their exact sums differ by at most `B + B' − Δ`. -/
theorem drop_le_of_errors {e e' d d' B B' : ℚ} (h : absQ (e - d) ≤ B) (h' : absQ (e' - d') ≤ B') :
    d - d' ≤ B + B' - (e' - e) := by
  rw [absQ_le_iff] at h h'
  grind

/-- **How far a CDNA 3 output can fall.** For any two accepted blocks of Algorithm 1 or 2, the
drop `d − d'` is at most the sum of the two blocks' error bounds (`alignedBound` of `S_acc` and
half an ulp of the final RNE) minus the gain `Δ`; with every product at least as large and the
same `c`, `Δ ≥ 0` (`gain_nonneg`). -/
theorem aligned_output_drop_le {P : Model}
    (hacc : P.accumulation = .globalAlignment ∨ P.accumulation = .oddEvenGrouping)
    (hcut : ∀ n, P.late.cCutoff = some n → P.late.cMantissaBits ≤ n) (hcz : P.cZeroExp ≠ none)
    {x x' : BlockInput P} {t t' : BlockTrace P} (h : evalBlock x = .ok t)
    (h' : evalBlock x' = .ok t') :
    wordValue t.d - wordValue t'.d ≤
      (alignedBound P t.prepared + flBound (!P.subnormals) t.sAcc) +
        (alignedBound P t'.prepared + flBound (!P.subnormals) t'.sAcc) - t.gain t' :=
  drop_le_of_errors (aligned_error hacc hcut hcz h) (aligned_error hacc hcut hcz h')

/-- **How far a CDNA 3 output can fall, from the inputs alone.** With `A = Σ|p_ℓ| + |c|` and `n`
products per block, the drop `d − d'` is at most
`2^-23 (A + A') + (n + 4)·2^(e_max − 24) + (n' + 4)·2^(e'_max − 24) + 2^-148 − Δ`. -/
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
