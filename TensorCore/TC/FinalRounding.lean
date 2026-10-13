import TensorCore.Numerics.Binary.DirectedRounding
import TensorCore.TC.InvocationProperties
import TensorCore.TC.Models

/-! Correctness of the final rounding stages. -/

namespace TensorCore

theorem roundingStage_nearestEven_correct (s : RoundingStage) (hf : s.format.WellFormed)
    (hmode : s.mode = .nearestEven) (x : ℚ) (d : FiniteBinary s.format)
    (h : s.roundValue x = some d) : NearestEven s.format x d.bits := by
  have hout := roundingStage_output h
  have hr := (roundingStage_range h).2
  rw [hmode] at hout
  obtain ⟨bits, hb, hc⟩ := roundBinary_nearestEven_correct s.format hf x hr
  rw [hout] at hb
  cases Option.some.inj hb
  exact hc

theorem roundingStage_truncate_correct (s : RoundingStage) (hf : s.format.WellFormed)
    (hmode : s.mode = .truncate) (x : ℚ) (d : FiniteBinary s.format)
    (h : s.roundValue x = some d) : Truncated s.format x d.bits := by
  have hout := roundingStage_output h
  have hr := (roundingStage_range h).2
  rw [hmode] at hout
  obtain ⟨bits, hb, hc⟩ := roundBinary_truncate_correct s.format hf x hr
  rw [hout] at hb
  cases Option.some.inj hb
  exact hc

/-- A nearest-even output stage returns the nearest output-format value, ties to even. -/
theorem evalInvocation_output_nearestEven {p : InvocationSpec} {x : InvocationInput p}
    {t : InvocationTrace p} (h : evalInvocation x = .ok t) (hmode : p.output.mode = .nearestEven) :
    NearestEven p.output.format t.intermediate.value t.output.bits := by
  obtain ⟨hv, _, _, _, _, hout⟩ := evalInvocation_spec h
  exact roundingStage_nearestEven_correct p.output hv.2.2.2.1 hmode _ _ hout

theorem evalInvocation_output_truncate {p : InvocationSpec} {x : InvocationInput p}
    {t : InvocationTrace p} (h : evalInvocation x = .ok t) (hmode : p.output.mode = .truncate) :
    Truncated p.output.format t.intermediate.value t.output.bits := by
  obtain ⟨hv, _, _, _, _, hout⟩ := evalInvocation_spec h
  exact roundingStage_truncate_correct p.output hv.2.2.2.1 hmode _ _ hout

/-- FP64 fused specification: one correctly rounded result in the stated direction. -/
theorem binary64Fma_nearestEven {x : InvocationInput (binary64Fma .nearestEven)}
    {t : InvocationTrace (binary64Fma .nearestEven)} (h : evalInvocation x = .ok t) :
    NearestEven fp64 t.intermediate.value t.output.bits :=
  evalInvocation_output_nearestEven h rfl

theorem binary64Fma_truncate {x : InvocationInput (binary64Fma .truncate)}
    {t : InvocationTrace (binary64Fma .truncate)} (h : evalInvocation x = .ok t) :
    Truncated fp64 t.intermediate.value t.output.bits :=
  evalInvocation_output_truncate h rfl

theorem roundingStage_towardNegative_correct (s : RoundingStage) (hf : s.format.WellFormed)
    (hmode : s.mode = .towardNegative) (x : ℚ) (d : FiniteBinary s.format)
    (h : s.roundValue x = some d) : TowardNegative s.format x d.bits := by
  have hout := roundingStage_output h
  rw [hmode] at hout
  obtain ⟨bits, hb, hc⟩ := roundBinary_towardNegative_correct s.format hf x
    (roundingStage_range h).2
  rw [hout] at hb
  cases Option.some.inj hb
  exact hc

theorem roundingStage_towardPositive_correct (s : RoundingStage) (hf : s.format.WellFormed)
    (hmode : s.mode = .towardPositive) (x : ℚ) (d : FiniteBinary s.format)
    (h : s.roundValue x = some d) : TowardPositive s.format x d.bits := by
  have hout := roundingStage_output h
  rw [hmode] at hout
  obtain ⟨bits, hb, hc⟩ := roundBinary_towardPositive_correct s.format hf x
    (roundingStage_range h).2
  rw [hout] at hb
  cases Option.some.inj hb
  exact hc

theorem evalInvocation_output_towardNegative {p : InvocationSpec} {x : InvocationInput p}
    {t : InvocationTrace p} (h : evalInvocation x = .ok t) (hmode : p.output.mode = .towardNegative) :
    TowardNegative p.output.format t.intermediate.value t.output.bits := by
  obtain ⟨hv, _, _, _, _, hout⟩ := evalInvocation_spec h
  exact roundingStage_towardNegative_correct p.output hv.2.2.2.1 hmode _ _ hout

theorem evalInvocation_output_towardPositive {p : InvocationSpec} {x : InvocationInput p}
    {t : InvocationTrace p} (h : evalInvocation x = .ok t) (hmode : p.output.mode = .towardPositive) :
    TowardPositive p.output.format t.intermediate.value t.output.bits := by
  obtain ⟨hv, _, _, _, _, hout⟩ := evalInvocation_spec h
  exact roundingStage_towardPositive_correct p.output hv.2.2.2.1 hmode _ _ hout

theorem binary64Fma_towardNegative {x : InvocationInput (binary64Fma .towardNegative)}
    {t : InvocationTrace (binary64Fma .towardNegative)} (h : evalInvocation x = .ok t) :
    TowardNegative fp64 t.intermediate.value t.output.bits :=
  evalInvocation_output_towardNegative h rfl

theorem binary64Fma_towardPositive {x : InvocationInput (binary64Fma .towardPositive)}
    {t : InvocationTrace (binary64Fma .towardPositive)} (h : evalInvocation x = .ok t) :
    TowardPositive fp64 t.intermediate.value t.output.bits :=
  evalInvocation_output_towardPositive h rfl

/-- Fused FP64 rounds the independently decoded exact product plus accumulator; there is no intermediate rounding. -/
theorem binary64Fma_exact_input {mode : BinaryRoundingMode}
    {x : InvocationInput (binary64Fma mode)} {t : InvocationTrace (binary64Fma mode)}
    (h : evalInvocation x = .ok t) : invocationIdeal x = some t.intermediate.value := by
  obtain ⟨_, _, hp, ha, hr, _⟩ := evalInvocation_spec h
  simp only [accumulateInvocation, binary64Fma, Option.some.injEq] at ha
  simp only [binary64Fma, runRoundings, Option.some.injEq] at hr
  simp only [invocationIdeal, hp, Option.map_some]
  rw [← hr, ← ha]
  rfl

end TensorCore
