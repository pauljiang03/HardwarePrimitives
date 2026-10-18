import TensorCore.TC.Canonical

/-! The exact set of inputs the model accepts. -/

namespace TensorCore

theorem round32_finite_exists (mode : RoundingMode) (x : ℚ) (hr : absQ x ≤ maxFinite32) :
    ∃ bits d, round32 mode x = some bits ∧ decode32 bits = some d := by
  by_cases hz : x = 0
  · subst x
    refine ⟨0, ⟨0, 0, 0⟩, ?_, by decide⟩
    cases mode <;> decide +kernel
  · obtain ⟨bits, hb, hv, _, _⟩ := round32_nonzero_spec mode x hz hr
    cases hd : decode32 bits with
    | none => simp [value32, hd] at hv
    | some d => exact ⟨bits, d, hb, hd⟩

theorem evalPrepared_total (b : PreparedBlock) (hr : absQ b.accumulator ≤ maxFinite32) :
    ∃ t, evalPrepared b = .ok t := by
  obtain ⟨bits, d₀, hb, hd₀⟩ := round32_finite_exists .truncate b.accumulator hr
  obtain ⟨d, hd⟩ := Option.isSome_iff_exists.mp
    (decode32_truncateMantissa32 (m := b.model.outputMantissaBits) (by rw [hd₀]; rfl))
  have hf : finite32 (truncateMantissa32 b.model.outputMantissaBits bits) = some ⟨_, d, hd⟩ := by
    unfold finite32
    split
    · rename_i he
      rw [hd] at he
      contradiction
    · rename_i d' he
      rw [hd] at he
      cases Option.some.inj he
      rfl
  exact ⟨⟨b, ⟨_, d, hd⟩⟩, by simp [evalPrepared, hb, hf]⟩

/-- Exact accepted domain: correct shape, finite decoded operands, and in-range aligned accumulator. -/
theorem evalBlock_success_iff (p : Model) (x : BlockInput p) :
    (∃ t, evalBlock x = .ok t) ↔
      x.products.length = p.nfma ∧
        ∃ b, prepare x = some b ∧ absQ b.accumulator ≤ maxFinite32 := by
  constructor
  · rintro ⟨t, ht⟩
    have hp := evalBlock_prepared ht
    obtain ⟨_, hout, _⟩ := evalPrepared_output_mantissa (evalBlock_evalPrepared ht)
    have hr := round32_range hout
    refine ⟨?_, t.block, hp, hr⟩
    unfold evalBlock at ht
    split at ht <;> simp_all
  · rintro ⟨hshape, b, hp, hr⟩
    obtain ⟨t, ht⟩ := evalPrepared_total b hr
    exact ⟨t, by simpa [evalBlock, hshape, hp] using ht⟩

end TensorCore
