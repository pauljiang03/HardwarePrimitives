import TensorCore.TC.Models
import TensorCore.TC.CanonicalDefs

/-! BF16 and TF32 products with FP32 accumulation as models of the block semantics, with the numerical features of Accurate Models Table 3. -/

namespace TensorCore

/-- BF16 products, FP32 c and output, and `F = 23 + neab` fractional bits after alignment. -/
@[implicit_reducible] def bf16Fp32Model (K neab : ℕ) (eAlignMin : Option ℤ := none) :
    Model := ⟨bf16, K, 23 + neab, eAlignMin, 23⟩

/-- TF32 values in the packed 19-bit `tf19` layout, FP32 c and output. -/
@[implicit_reducible] def tf19Fp32Model (K neab : ℕ) (eAlignMin : Option ℤ := none) :
    Model := ⟨tf19, K, 23 + neab, eAlignMin, 23⟩

@[simp] theorem bf16Fp32Model_outputFracBits (K neab : ℕ) (eAlignMin : Option ℤ) :
    (bf16Fp32Model K neab eAlignMin).outputFracBits = 23 := rfl

@[simp] theorem tf19Fp32Model_outputFracBits (K neab : ℕ) (eAlignMin : Option ℤ) :
    (tf19Fp32Model K neab eAlignMin).outputFracBits = 23 := rfl

@[implicit_reducible] def a100BF16F32 : Model := bf16Fp32Model 8 1 (some (-132))
@[implicit_reducible] def hopperBF16F32 : Model := bf16Fp32Model 16 2 (some (-133))
@[implicit_reducible] def a100TF32F32 : Model := tf19Fp32Model 4 1 (some (-132))
@[implicit_reducible] def hopperTF32WmmaF32 : Model := tf19Fp32Model 4 2 (some (-133))
@[implicit_reducible] def hopperTF32MmaF32 : Model := tf19Fp32Model 8 2 (some (-133))

/-- The thirteen low bits of a TF32 register word must be zero. -/
def tf32Padded (w : tf32Register.Word) : Bool := w.toNat % 2 ^ 13 == 0

/-- The 19 value bits of a TF32 register word. -/
def tf32Unpack (w : tf32Register.Word) : BitVec 19 := BitVec.ofNat 19 (w.toNat / 2 ^ 13)

def tf32UnpackPairs (ps : List (tf32Register.Word × tf32Register.Word)) :
    List (BitVec 19 × BitVec 19) :=
  ps.map fun (a, b) => (tf32Unpack a, tf32Unpack b)

/-- The register-word input of a TF32 descriptor as a value-word input of the model. -/
def tf32Input {K F : ℕ} {eAlignMin : Option ℤ}
    (x : InvocationInput (alignedInvocation tf32Register K F eAlignMin)) (neab : ℕ) :
    BlockInput (tf19Fp32Model K neab eAlignMin) :=
  ⟨tf32UnpackPairs x.products, x.c⟩

end TensorCore
