import TensorCore.TC.Invocation
import TensorCore.TC.AlignmentExponent

/-! Properties of general invocations. -/

namespace TensorCore

private theorem aligned_recovery (b : PreparedBlock) :
    b.exactDot = b.accumulator + sumQ b.alignmentResiduals := by
  have h := block_residual_identity b b.accumulator
  unfold PreparedBlock.extractReference at h
  grind

theorem accumulateInvocation_recovery {p : InvocationSpec} (b : PreparedInvocation p)
    (a : LocalAccumulation) (h : accumulateInvocation b = some a) :
    b.exactDot = a.value + a.loss := by
  cases hk : p.accumulation with
  | fused =>
    simp [accumulateInvocation, hk] at h
    subst a
    simp [LocalAccumulation.loss, sumQ]
    grind
  | aligned F eAlignMin cp =>
    cases cp with
    | early =>
      simp [accumulateInvocation, hk] at h
      subst a
      have hr := aligned_recovery (b.alignedBlock F eAlignMin true)
      change b.exactDot = (b.alignedBlock F eAlignMin true).accumulator +
        sumQ (b.alignedBlock F eAlignMin true).alignmentResiduals at hr
      simpa [LocalAccumulation.loss, sumQ, Rat.add_zero] using hr
    | late ss =>
      cases hc : runRoundings ss (b.alignedBlock F eAlignMin false).accumulator with
      | none => simp [accumulateInvocation, hk, hc] at h
      | some r =>
        simp [accumulateInvocation, hk, hc] at h
        subst a
        have hr := aligned_recovery (b.alignedBlock F eAlignMin false)
        have hs := runRoundings_recovery ss _ r hc
        have hz : (b.alignedBlock F eAlignMin false).exactDot = b.exactProducts := by
          simp [PreparedInvocation.alignedBlock, PreparedBlock.exactDot,
            PreparedBlock.exactProducts, PreparedInvocation.exactProducts, Decoded.value,
            Rat.zero_add]
        rw [hz] at hr
        unfold PreparedInvocation.exactDot LocalAccumulation.loss RoundingRun.loss at *
        grind

theorem evalInvocationPrepared_spec {p : InvocationSpec} {b : PreparedInvocation p}
    {t : InvocationTrace p} (h : evalInvocationPrepared b = .ok t) :
    t.prepared = b ∧ accumulateInvocation b = some t.accumulation ∧
    runRoundings p.intermediate t.accumulation.value = some t.intermediate ∧
    p.output.roundValue t.intermediate.value = some t.output := by
  unfold evalInvocationPrepared at h
  cases ha : accumulateInvocation b with
  | none => simp [ha] at h
  | some a =>
    cases hr : runRoundings p.intermediate a.value with
    | none => simp [ha, hr] at h
    | some r =>
      cases hd : p.output.roundValue r.value with
      | none => simp [ha, hr, hd] at h
      | some d =>
        simp [ha, hr, hd] at h
        subst t
        exact ⟨rfl, rfl, hr, hd⟩

/-- Successful encoded evaluation certifies its parameters, shape, decoding, and stages. -/
theorem evalInvocation_spec {p : InvocationSpec} {x : InvocationInput p} {t : InvocationTrace p}
    (h : evalInvocation x = .ok t) :
    p.Valid ∧ x.products.length = p.nfma ∧ prepareInvocation x = some t.prepared ∧
    accumulateInvocation t.prepared = some t.accumulation ∧
    runRoundings p.intermediate t.accumulation.value = some t.intermediate ∧
    p.output.roundValue t.intermediate.value = some t.output := by
  unfold evalInvocation at h
  split at h
  · simp at h
  · rename_i hv
    split at h
    · simp at h
    · rename_i hs
      cases hp : prepareInvocation x with
      | none => simp [hp] at h
      | some b =>
        simp only [hp] at h
        have ht := evalInvocationPrepared_spec h
        refine ⟨by grind, by simpa using hs, ?_, ?_⟩
        · rw [ht.1]
        · simpa [ht.1] using ht.2

/-- Original-bit ideal equals the actual returned value plus all local stage losses. -/
theorem evalInvocation_recovery {p : InvocationSpec} {x : InvocationInput p} {t : InvocationTrace p}
    (h : evalInvocation x = .ok t) :
    invocationIdeal x = some (t.output.value + t.residual) := by
  obtain ⟨_, _, hp, ha, hr, _⟩ := evalInvocation_spec h
  have hl := accumulateInvocation_recovery t.prepared t.accumulation ha
  have hc := runRoundings_recovery p.intermediate t.accumulation.value t.intermediate hr
  simp only [invocationIdeal, hp, Option.map_some]
  congr 1
  unfold InvocationTrace.residual
  grind

/-- The final output obeys the specified executable conversion, with its own range guard. -/
theorem evalInvocation_output {p : InvocationSpec} {x : InvocationInput p} {t : InvocationTrace p}
    (h : evalInvocation x = .ok t) :
    roundBinary p.output.format p.output.mode t.intermediate.value = some t.output.bits ∧
    absQ t.intermediate.value ≤ p.output.format.maxFinite := by
  have hs := (evalInvocation_spec h).2.2.2.2.2
  exact ⟨roundingStage_output hs, (roundingStage_range hs).2⟩

end TensorCore
