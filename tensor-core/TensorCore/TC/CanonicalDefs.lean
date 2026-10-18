import TensorCore.TC.Invocation

/-! Models with FP16 input and FP32 output formats. -/

namespace TensorCore

/-- FP16 products, FP32 c and output, and `F = 23 + padding` mantissa bits after alignment. -/
@[implicit_reducible] def fp16Fp32Model (K padding : ℕ) (eAlignMin : Option ℤ := none) : Model :=
  ⟨fp16, K, (23 + padding : ℕ), eAlignMin, 23⟩

@[simp] theorem fp16Fp32Model_outputMantissaBits (K padding : ℕ) (eAlignMin : Option ℤ) :
    (fp16Fp32Model K padding eAlignMin).outputMantissaBits = 23 := rfl

@[implicit_reducible] def ampereF16F32 : Model := fp16Fp32Model 8 1 (some (-132))
@[implicit_reducible] def hopperF16F32 : Model := fp16Fp32Model 16 2 (some (-133))

@[implicit_reducible] def fp16Fp32Invocation (K padding : ℕ) (eAlignMin : Option ℤ := none) :
    InvocationSpec := (fp16Fp32Model K padding eAlignMin).toInvocation (23 + padding)

theorem fp16Fp32_v100 : fp16Fp32Model 4 0 none = v100F16F32 := rfl

end TensorCore
