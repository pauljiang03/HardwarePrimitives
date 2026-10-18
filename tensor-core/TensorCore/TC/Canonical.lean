import TensorCore.TC.CanonicalDefs
import TensorCore.TC.Compatibility
import TensorCore.TC.ErrorBounds

/-! Contracts of the FP16 models. -/

namespace TensorCore

theorem fp16Fp32_invocation_compatible (K padding : ℕ) (eAlignMin : Option ℤ)
    (x : BlockInput (fp16Fp32Model K padding eAlignMin)) :
    invocationBits (x.toInvocation (23 + padding)) =
      (evalBlock x).toOption.map (fun t => t.output.bits) :=
  legacy_invocation_bits x (23 + padding) (by change fp16.WellFormed; decide) rfl (Nat.le_refl 23)

/-- Contract of the FP16 models for any FMA size and any number of padding bits. -/
theorem fp16Fp32_contract (K padding carryBits : ℕ) (eAlignMin : Option ℤ)
    (x : BlockInput (fp16Fp32Model K padding eAlignMin)) (t : BlockTrace)
    (h : evalBlock x = .ok t) (hc : K + 1 ≤ 2 ^ carryBits) :
    exactDot x = some t.block.exactDot ∧
    round32 .truncate t.block.accumulator = some t.output.bits ∧
    absQ (t.block.exactDot - t.output.value) <
      ((K + 1 : ℕ) : ℚ) * pow2 t.block.alignGridExponent +
        pow2 (outputUlpExponent t.output.bits) ∧
    t.block.machineAccumulator (26 + padding + carryBits) = t.block.accumulator := by
  have hp := evalBlock_prepared h
  have hlen := (prepare_terms_bounded hp).1
  have hshape : x.products.length = K := by
    unfold evalBlock at h
    split at h <;> simp_all [fp16Fp32Model]
  have herr := evalBlock_error_bound h (Nat.le_refl 23)
  have hw := evalBlock_machineAccumulator h (23 + padding) carryBits rfl hc
  refine ⟨by simp [exactDot, hp], evalBlock_output h (Nat.le_refl 23), ?_, ?_⟩
  · simpa [hlen, hshape] using herr
  · have he : 23 + padding + 2 + carryBits + 1 = 26 + padding + carryBits := by omega
    simpa [he] using hw

theorem ampere_machineAccumulator {x : BlockInput ampereF16F32} {t : BlockTrace}
    (h : evalBlock x = .ok t) : t.block.machineAccumulator 31 = t.block.accumulator :=
  (fp16Fp32_contract 8 1 4 (some (-132)) x t h (by decide)).2.2.2

theorem hopper_machineAccumulator {x : BlockInput hopperF16F32} {t : BlockTrace}
    (h : evalBlock x = .ok t) : t.block.machineAccumulator 33 = t.block.accumulator :=
  (fp16Fp32_contract 16 2 5 (some (-133)) x t h (by decide)).2.2.2

end TensorCore
