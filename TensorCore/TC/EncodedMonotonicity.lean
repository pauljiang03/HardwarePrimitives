import TensorCore.TC.Flowback

/-! TC-EFT Definition III.2 at the encoded interface. -/

namespace TensorCore

/-- `val(TC_θ(a,b,c))`, with finite-domain rejection preserved. -/
def encodedBlockValue {p : Model} (products : List (p.Word × p.Word)) (c : F32) :
    Except ModelError ℚ :=
  (evalBlock (⟨products, c⟩ : BlockInput p)).map fun t => t.output.value

def MonotoneInEncodedAccumulator (p : Model) (products : List (p.Word × p.Word)) : Prop :=
  ∀ (c c' : F32) (v v' d d' : ℚ),
    value32 c = some v → value32 c' = some v' →
    encodedBlockValue products c = .ok d → encodedBlockValue products c' = .ok d' →
    v' < v → d' ≤ d

/-- Decoded accumulator monotonicity transfers to encoded inputs and accepted output values. -/
theorem monotoneInAccumulator_encoded {p : Model} {ps : List (p.Word × p.Word)}
    {products : List (Decoded × Decoded)} (hp : prepareProducts p ps = some products)
    (hm : MonotoneInAccumulator p products) : MonotoneInEncodedAccumulator p ps := by
  intro c c' v v' d d' hv hv' hd hd' hlt
  cases hc : decode32 c with
  | none => simp [value32, hc] at hv
  | some dc =>
    cases hc' : decode32 c' with
    | none => simp [value32, hc'] at hv'
    | some dc' =>
      simp only [value32, hc, Option.map_some, Option.some.injEq] at hv
      simp only [value32, hc', Option.map_some, Option.some.injEq] at hv'
      cases he : evalBlock (⟨ps, c⟩ : BlockInput p) with
      | error e => simp [encodedBlockValue, he, Except.map] at hd
      | ok t =>
        cases he' : evalBlock (⟨ps, c'⟩ : BlockInput p) with
        | error e => simp [encodedBlockValue, he', Except.map] at hd'
        | ok t' =>
          simp only [encodedBlockValue, he, Except.map, Except.ok.injEq] at hd
          simp only [encodedBlockValue, he', Except.map, Except.ok.injEq] at hd'
          have ht : evalPrepared ⟨p, products, dc⟩ = .ok t := by
            unfold evalBlock at he
            split at he
            · contradiction
            · simpa [prepare, hc, hp] using he
          have ht' : evalPrepared ⟨p, products, dc'⟩ = .ok t' := by
            unfold evalBlock at he'
            split at he'
            · contradiction
            · simpa [prepare, hc', hp] using he'
          rw [← hd, ← hd']
          exact hm dc dc' t t' ht ht' (by rw [hv, hv']; exact hlt)

/-- A non-monotone encoded witness refutes decoded monotonicity for its fixed products. -/
theorem not_monotoneInAccumulator_of_encoded {p : Model} {ps : List (p.Word × p.Word)}
    {products : List (Decoded × Decoded)} (hp : prepareProducts p ps = some products)
    (h : ¬ MonotoneInEncodedAccumulator p ps) : ¬ MonotoneInAccumulator p products :=
  fun hm => h (monotoneInAccumulator_encoded hp hm)

end TensorCore
