import TensorCore.TC.CanonicalFormats
import TensorCoreTests.TC.Cases



namespace TensorCore.Regression

set_option maxRecDepth 16384
set_option maxHeartbeats 4000000

def a100Bf16Row : List (BitVec 16 × BitVec 16) :=
  [(0x3f7a, 0x3f19), (0x3f87, 0xbf26), (0xbea6, 0x3ed7), (0x3fbf, 0x3e9d), (0xbf3d, 0xbff3),
    (0x3ead, 0x3ef2), (0x3f80, 0xbfc1), (0x3fe8, 0xbf90)]

def h100Bf16Row : List (BitVec 16 × BitVec 16) :=
  a100Bf16Row ++ [(0x3f62, 0x3dbf), (0x3f5d, 0xbf31), (0xbf8c, 0xbf52), (0x3eb3, 0x400e),
    (0x3cf1, 0xbc71), (0x3e9c, 0x401e), (0x3f86, 0x3e1c), (0x3f59, 0xbea4)]

def tf32Row : List (tf32Register.Word × tf32Register.Word) :=
  [(0x3f7aa000, 0x3f194000), (0x3f87c000, 0xbf26a000), (0xbea68000, 0x3ed7e000),
    (0x3fbf0000, 0x3e9d8000)]

/-- A100 BF16 row 1: device output `bfbe56d5` from the model and from the descriptor. -/
theorem a100_bf16_published_row :
    (evalBlock (⟨a100Bf16Row, 0x3e8e06ad⟩ : BlockInput a100BF16F32)).toOption.map
      (fun t => t.output.bits.toNat) = some 0xbfbe56d5 ∧
    (invocationBits (p := a100BF16Invocation) ⟨a100Bf16Row, 0x3e8e06ad⟩).map BitVec.toNat =
      some 0xbfbe56d5 := by decide +kernel

/-- H100 BF16 row 1: device output `3f3cc4dd`. -/
theorem h100_bf16_published_row :
    (evalBlock (⟨h100Bf16Row, 0x3f342579⟩ : BlockInput hopperBF16F32)).toOption.map
      (fun t => t.output.bits.toNat) = some 0x3f3cc4dd ∧
    (invocationBits (p := hopperBF16Invocation) ⟨h100Bf16Row, 0x3f342579⟩).map BitVec.toNat =
      some 0x3f3cc4dd := by decide +kernel

/-- A100 and H100 TF32 row 1: the same four register-word pairs give `3f36f7de` on A100 and, with a different accumulator input, `3f9888df` on H100, through both the model and the descriptor. -/
theorem tf32_published_rows :
    (tf32InvocationBits 4 24 (some (-132)) tf32Row 0x3efe7b25).map BitVec.toNat =
      some 0x3f36f7de ∧
    (evalBlock (⟨tf32UnpackPairs tf32Row, 0x3efe7b25⟩ : BlockInput a100TF32F32)).toOption.map
      (fun t => t.output.bits.toNat) = some 0x3f36f7de ∧
    (tf32InvocationBits 4 25 (some (-133)) tf32Row 0x3f795773).map BitVec.toNat =
      some 0x3f9888df ∧
    (evalBlock (⟨tf32UnpackPairs tf32Row, 0x3f795773⟩ : BlockInput hopperTF32WmmaF32)).toOption.map
      (fun t => t.output.bits.toNat) = some 0x3f9888df := by decide +kernel

/-- A register word with a nonzero low bit is not a TF32 value: the descriptor rejects it, while the model would accept the truncated value word. -/
theorem tf32_unpadded_rejected :
    tf32Padded 0x3f7aa001 = false ∧
    tf32InvocationBits 4 24 (some (-132)) [(0x3f7aa001, 0x3f194000), (0, 0), (0, 0), (0, 0)] 0 =
      none ∧
    ((evalBlock (⟨tf32UnpackPairs [(0x3f7aa001, 0x3f194000), (0, 0), (0, 0), (0, 0)], 0⟩ :
      BlockInput a100TF32F32)).toOption.map (fun t => t.output.bits.toNat)).isSome = true := by
  decide +kernel

/-- The descriptor-to-model theorem applied to the published TF32 row. -/
theorem tf32_row_compatible :
    tf32InvocationBits 4 (23 + 1) (some (-132)) tf32Row 0x3efe7b25 =
      (evalBlock (⟨tf32UnpackPairs tf32Row, 0x3efe7b25⟩ : BlockInput (tf19Fp32Model 4 1 (some (-132))))).toOption.map
        (fun t => t.output.bits) :=
  tf32_invocation_bits 4 1 (some (-132)) tf32Row 0x3efe7b25 (by decide +kernel)

end TensorCore.Regression
