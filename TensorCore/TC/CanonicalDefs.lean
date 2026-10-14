import TensorCore.TC.Invocation

/-! Models with FP16 input and FP32 output formats. -/

namespace TensorCore

/-- Canonical FP16 products and FP32 c and output, with any FMA size and any number of extra alignment bits beyond the baseline 23 fractional bits. -/
@[implicit_reducible] def fp16Fp32Model (K neab : ℕ) (eAlignMin : Option ℤ := none) : Model :=
  ⟨fp16, K, (23 + neab : ℕ), eAlignMin, 23⟩

@[simp] theorem fp16Fp32Model_outputFracBits (K neab : ℕ) (eAlignMin : Option ℤ) :
    (fp16Fp32Model K neab eAlignMin).outputFracBits = 23 := rfl

@[implicit_reducible] def ampereF16F32 : Model := fp16Fp32Model 8 1 (some (-132))
@[implicit_reducible] def hopperF16F32 : Model := fp16Fp32Model 16 2 (some (-133))

@[implicit_reducible] def fp16Fp32Invocation (K neab : ℕ) (eAlignMin : Option ℤ := none) :
    InvocationSpec := (fp16Fp32Model K neab eAlignMin).toInvocation (23 + neab)

theorem fp16Fp32_v100 : fp16Fp32Model 4 0 none = v100F16F32 := rfl

end TensorCore
