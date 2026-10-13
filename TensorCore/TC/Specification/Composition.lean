import TensorCore.TC.Specification.Supported
import TensorCore.TC.Specification.Schedule
import TensorCore.TC.Composition

/-! Chained block FMAs agree with the independent specification. -/

namespace TensorCore.IndependentSpec

/-- All encoded intermediate outputs, and failures, agree for every finite schedule. -/
theorem runBlocks_eq_spec (p : Model) (c : F32) (blocks : List (List (p.Word × p.Word))) :
    (runBlocks p c blocks).toOption.map (fun ts => ts.map fun t => t.output.bits) =
      runChain (parametersOf p) c blocks := by
  induction blocks generalizing c with
  | nil => rfl
  | cons block rest ih =>
    have hb := evalBlock_eq_spec (⟨block, c⟩ : BlockInput p)
    change (evalBlock (⟨block, c⟩ : BlockInput p)).toOption.map (fun t => t.output.bits) =
      bits (parametersOf p) ⟨block, c⟩ at hb
    simp only [runChain, ← hb]
    cases he : evalBlock (⟨block, c⟩ : BlockInput p) with
    | error e => simp [runBlocks, he, Except.toOption]
    | ok t =>
      have hr := ih t.output.bits
      cases ht : runBlocks p t.output.bits rest with
      | error e => simp [runBlocks, he, ht, Except.toOption] at hr ⊢; rw [← hr]; rfl
      | ok ts => simp [runBlocks, he, ht, Except.toOption] at hr ⊢; rw [← hr]; rfl

/-- Projection of the preceding stronger theorem to just the final output bits. -/
theorem schedule_last_eq_spec (p : Model) (c : F32)
    (blocks : List (List (p.Word × p.Word))) :
    (runBlocks p c blocks).toOption.map (fun ts =>
      (ts.map fun t => t.output.bits).getLast?.getD c) =
      lastBits (parametersOf p) c blocks := by
  unfold lastBits
  rw [← runBlocks_eq_spec]
  simp only [Option.map_map]
  rfl

end TensorCore.IndependentSpec
