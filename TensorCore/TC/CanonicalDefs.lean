import TensorCore.TC.Invocation

/-! FP16 to FP32 profiles. -/

namespace TensorCore

/-- Canonical FP16 products and FP32 c/output, with arbitrary block size and extra alignment bits beyond the baseline 23. -/
@[implicit_reducible] def fp16Fp32Model (K neab : ℕ) (eAlignMin : Option ℤ := none) : Model :=
  ⟨fp16, K, (23 + neab : ℕ), eAlignMin⟩

@[implicit_reducible] def ampereF16F32 : Model := fp16Fp32Model 8 1 (some (-132))
@[implicit_reducible] def hopperF16F32 : Model := fp16Fp32Model 16 2 (some (-133))

@[implicit_reducible] def fp16Fp32Invocation (K neab : ℕ) (eAlignMin : Option ℤ := none) :
    InvocationSpec := (fp16Fp32Model K neab eAlignMin).toInvocation (23 + neab)

theorem fp16Fp32_v100 : fp16Fp32Model 4 0 none = v100F16F32 := rfl

end TensorCore
