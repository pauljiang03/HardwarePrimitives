import TensorCore.TC.Specification.Equivalence
import TensorCore.TC.Specification.Variants
import TensorCore.TC.GPUs

/-! The model equals the independent specification on every supported variant. -/

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

/-- Every supported GPU variant and every input, with failures observed as none. -/
theorem supported_eq_spec (variant : Variant) (x : BlockInput (implementationModel variant)) :
    (evalBlock x).toOption.map (fun t => t.output.bits) =
      bits (parameters variant) (supportedInput variant x) := by
  cases variant <;> exact evalBlock_eq_spec x (Nat.le_refl 23)

/-- Every paper-valid input of every supported variant produces the specified bits. -/
theorem supported_valid_success (variant : Variant) (x : BlockInput (implementationModel variant))
    (hv : Valid (parameters variant) (supportedInput variant x)) :
    ∃ t, evalBlock x = .ok t ∧
      bits (parameters variant) (supportedInput variant x) = some t.output.bits := by
  cases variant <;> exact valid_success x hv (Nat.le_refl 23)

/-- B200's FP8 block FMAs have an FP32 block output, so the specification equality covers them. -/
theorem blackwell_fp8_eq_spec :
    (∀ x : BlockInput blackwellE4M3F32, (evalBlock x).toOption.map (fun t => t.output.bits) =
      bits (parametersOf blackwellE4M3F32) (inputOf x)) ∧
    (∀ x : BlockInput blackwellE5M2F32, (evalBlock x).toOption.map (fun t => t.output.bits) =
      bits (parametersOf blackwellE5M2F32) (inputOf x)) :=
  ⟨fun x => evalBlock_eq_spec x (Nat.le_refl 23), fun x => evalBlock_eq_spec x (Nat.le_refl 23)⟩

/-- The compatibility layer transfers the result to the public aligned invocation API. -/
theorem invocation_eq_spec {p : Model} (x : BlockInput p) (F : ℕ)
    (hf : p.input.WellFormed) (hF : p.alignMantissaBits = F) (hw : 23 ≤ p.outputMantissaBits) :
    invocationBits (x.toInvocation F) = bits (parametersOf p) (inputOf x) := by
  rw [legacy_invocation_bits x F hf hF hw]
  exact evalBlock_eq_spec x hw

/-- Register-level TF32 agreement on every correctly padded input. -/
theorem tf32_eq_spec (K padding : ℕ) (eAlignMin : Option ℤ)
    (ps : List (tf32Register.Word × tf32Register.Word)) (c : F32)
    (hp : ∀ pair ∈ ps, tf32Padded pair.1 = true ∧ tf32Padded pair.2 = true) :
    tf32InvocationBits K (23 + padding) eAlignMin ps c = tf32Bits K padding eAlignMin ps c := by
  have hpad : paddedTF32 ps = true := by
    apply List.all_eq_true.mpr
    intro pair hpair
    obtain ⟨ha, hb⟩ := hp pair hpair
    change (pair.1.toNat % 8192 == 0 && pair.2.toNat % 8192 == 0) = true
    change (pair.1.toNat % 8192 == 0) = true at ha
    change (pair.2.toNat % 8192 == 0) = true at hb
    rw [ha, hb]
    rfl
  rw [tf32_invocation_bits K padding eAlignMin ps c hp, evalBlock_eq_spec _ (Nat.le_refl 23)]
  simp only [tf32Bits, hpad, ↓reduceIte]
  rfl

end TensorCore.IndependentSpec
