import TensorCore.TC.Specification.Supported
import TensorCore.TC.Specification.Schedule
import TensorCore.TC.Composition

/-! Chained groups agree with the independent specification. -/

namespace TensorCore.IndependentSpec

/-- All encoded intermediate outputs, and failures, agree for every finite schedule. -/
theorem runBlocks_eq_spec (p : Model) (c : F32) (groups : List (List (p.Word × p.Word))) :
    (runBlocks p c groups).toOption.map (fun ts => ts.map fun t => t.output.bits) =
      runGroups (parametersOf p) c groups := by
  induction groups generalizing c with
  | nil => rfl
  | cons group rest ih =>
    have hb := evalBlock_eq_spec (⟨group, c⟩ : BlockInput p)
    change (evalBlock (⟨group, c⟩ : BlockInput p)).toOption.map (fun t => t.output.bits) =
      bits (parametersOf p) ⟨group, c⟩ at hb
    simp only [runGroups, ← hb]
    cases he : evalBlock (⟨group, c⟩ : BlockInput p) with
    | error e => simp [runBlocks, he, Except.toOption]
    | ok t =>
      have hr := ih t.output.bits
      cases ht : runBlocks p t.output.bits rest with
      | error e => simp [runBlocks, he, ht, Except.toOption] at hr ⊢; rw [← hr]; rfl
      | ok ts => simp [runBlocks, he, ht, Except.toOption] at hr ⊢; rw [← hr]; rfl

/-- Projection of the preceding stronger theorem to just the final output bits. -/
theorem schedule_last_eq_spec (p : Model) (c : F32)
    (groups : List (List (p.Word × p.Word))) :
    (runBlocks p c groups).toOption.map (fun ts =>
      (ts.map fun t => t.output.bits).getLast?.getD c) =
      lastBits (parametersOf p) c groups := by
  unfold lastBits
  rw [← runBlocks_eq_spec]
  simp only [Option.map_map]
  rfl

end TensorCore.IndependentSpec
