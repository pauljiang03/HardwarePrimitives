import TensorCore.TC.Specification.Equivalence
import TensorCore.TC.Specification.Variants

/-! The model equals the independent specification on every supported path. -/

namespace TensorCore.IndependentSpec

def implementationModel : Variant → Model
  | .v100F16 => v100F16F32
  | .ampereF16 => ampereF16F32
  | .hopperF16 => hopperF16F32
  | .ampereBF16 => a100BF16F32
  | .hopperBF16 => hopperBF16F32
  | .ampereTF32 => a100TF32F32
  | .hopperTF32Wmma => hopperTF32WmmaF32
  | .hopperTF32Mma => hopperTF32MmaF32

def supportedInput (variant : Variant) (x : BlockInput (implementationModel variant)) :
    Input (parameters variant) := by
  cases variant <;> exact ⟨x.products, x.c⟩

/-- Independent parameter transcription matches each implementation descriptor. -/
theorem supported_parameters (variant : Variant) :
    parametersOf (implementationModel variant) = parameters variant := by cases variant <;> rfl

/-- Every supported GPU path and every input, with failures observed as none. -/
theorem supported_eq_spec (variant : Variant) (x : BlockInput (implementationModel variant)) :
    (evalBlock x).toOption.map (fun t => t.output.bits) =
      bits (parameters variant) (supportedInput variant x) := by
  cases variant <;> exact evalBlock_eq_spec x

/-- Every paper-valid input of every supported path produces the specified bits. -/
theorem supported_valid_success (variant : Variant) (x : BlockInput (implementationModel variant))
    (hv : Valid (parameters variant) (supportedInput variant x)) :
    ∃ t, evalBlock x = .ok t ∧
      bits (parameters variant) (supportedInput variant x) = some t.output.bits := by
  cases variant <;> exact valid_success x hv

/-- The compatibility layer transfers the result to the public aligned invocation API. -/
theorem invocation_eq_spec {p : Model} (x : BlockInput p) (F : ℕ)
    (hf : p.input.WellFormed) (hF : p.alignFracBits = F) :
    invocationBits (x.toInvocation F) = bits (parametersOf p) (inputOf x) := by
  rw [legacy_invocation_bits x F hf hF]
  exact evalBlock_eq_spec x

/-- Register-level TF32 agreement on every correctly padded input. -/
theorem tf32_eq_spec (K neab : ℕ) (eAlignMin : Option ℤ)
    (ps : List (tf32Register.Word × tf32Register.Word)) (c : F32)
    (hp : ∀ pair ∈ ps, tf32Padded pair.1 = true ∧ tf32Padded pair.2 = true) :
    tf32InvocationBits K (23 + neab) eAlignMin ps c = tf32Bits K neab eAlignMin ps c := by
  have hpad : paddedTF32 ps = true := by
    apply List.all_eq_true.mpr
    intro pair hpair
    obtain ⟨ha, hb⟩ := hp pair hpair
    change (pair.1.toNat % 8192 == 0 && pair.2.toNat % 8192 == 0) = true
    change (pair.1.toNat % 8192 == 0) = true at ha
    change (pair.2.toNat % 8192 == 0) = true at hb
    rw [ha, hb]
    rfl
  rw [tf32_invocation_bits K neab eAlignMin ps c hp, evalBlock_eq_spec]
  simp only [tf32Bits, hpad, ↓reduceIte]
  rfl

end TensorCore.IndependentSpec
