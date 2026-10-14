import TensorCore.TC.Specification.Rounding
import TensorCore.TC.MachineRefinement

/-! Universal, bit-level paper/implementation agreement. -/

namespace TensorCore.IndependentSpec

set_option maxRecDepth 4096

theorem result_of_eval {p : Model} {x : BlockInput p} {t : BlockTrace}
    (h : evalBlock x = .ok t) (hw : 23 ≤ p.outputMantissaBits) :
    Result (parametersOf p) (inputOf x) t.output.bits := by
  have hp := evalBlock_prepared h
  have hv := (evalBlock_success_iff p x).mp ⟨t, h⟩
  have hr := evalBlock_output h hw
  have ha := accumulated_eq t.block
  rw [prepare_model hp] at ha
  refine ⟨hv.1, t.block.terms.map denormalizedTermOf, ?_, ?_, ?_⟩
  · rw [terms_eq, hp]; rfl
  · rw [ha]; exact round32_range hr
  · rw [ha]; exact round32_rounds _ _ hr

theorem result_unique {p : Parameters} {x : Input p} {a b : F32}
    (ha : Result p x a) (hb : Result p x b) : a = b := by
  obtain ⟨_, ta, hta, _, hra⟩ := ha
  obtain ⟨_, tb, htb, _, hrb⟩ := hb
  rw [hta] at htb
  cases Option.some.inj htb
  exact rounds_unique _ _ _ hra hrb

theorem result_iff_eval {p : Model} (x : BlockInput p) (b : F32) (hw : 23 ≤ p.outputMantissaBits) :
    Result (parametersOf p) (inputOf x) b ↔
      ∃ t, evalBlock x = .ok t ∧ t.output.bits = b := by
  constructor
  · intro h
    have hv : Valid (parametersOf p) (inputOf x) := by
      obtain ⟨hs, ts, ht, hr, _⟩ := h
      exact ⟨hs, ts, ht, hr⟩
    obtain ⟨t, ht⟩ := (valid_iff x).mp hv
    exact ⟨t, ht, result_unique (result_of_eval ht hw) h⟩
  · rintro ⟨t, ht, rfl⟩
    exact result_of_eval ht hw

theorem bits_eq_of_result {p : Parameters} {x : Input p} {b : F32}
    (h : Result p x b) : bits p x = some b := by
  classical
  unfold bits
  rw [dif_pos ⟨b, h⟩]
  exact congrArg some (result_unique (Classical.choose_spec (show ∃ b, Result p x b from ⟨b, h⟩)) h)

/-- Every encoded input of a model with a binary32 block output: successful output bits and all
rejection cases agree. -/
theorem evalBlock_eq_spec {p : Model} (x : BlockInput p) (hw : 23 ≤ p.outputMantissaBits) :
    (evalBlock x).toOption.map (fun t => t.output.bits) =
      bits (parametersOf p) (inputOf x) := by
  classical
  cases he : evalBlock x with
  | ok t => exact (bits_eq_of_result (result_of_eval he hw)).symm
  | error e =>
    have hn : ¬ ∃ b, Result (parametersOf p) (inputOf x) b := by
      rintro ⟨b, hb⟩
      obtain ⟨t, ht, _⟩ := (result_iff_eval x b hw).mp hb
      rw [he] at ht
      contradiction
    simp [bits, hn, Except.toOption]

/-- The theorem is nonvacuous on the independently specified valid domain. -/
theorem valid_success {p : Model} (x : BlockInput p)
    (hv : Valid (parametersOf p) (inputOf x)) (hw : 23 ≤ p.outputMantissaBits) :
    ∃ t, evalBlock x = .ok t ∧ bits (parametersOf p) (inputOf x) = some t.output.bits := by
  obtain ⟨t, ht⟩ := (valid_iff x).mp hv
  exact ⟨t, ht, bits_eq_of_result (result_of_eval ht hw)⟩

/-- Adequate modular accumulator widths inherit the independent-specification theorem. -/
theorem machine_eq_spec {p : Model} (x : BlockInput p) (w F carryBits : ℕ)
    (hF : p.alignMantissaBits = F) (hc : p.nfma + 1 ≤ 2 ^ carryBits)
    (hw : F + 3 + carryBits ≤ w) (hout : 23 ≤ p.outputMantissaBits) :
    (evalBlockMachine w x).toOption.map (fun t => t.output.bits) =
      bits (parametersOf p) (inputOf x) := by
  rw [evalBlockMachine_eq x w F carryBits hF hc (by omega)]
  exact evalBlock_eq_spec x hout

end TensorCore.IndependentSpec
