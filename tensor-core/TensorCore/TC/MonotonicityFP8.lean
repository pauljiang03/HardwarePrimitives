import TensorCore.TC.GPUs

/-! # Non-monotonicity of the FP8 block FMAs

`K` equal small products and zeros: lowering `c` to its FP32 predecessor raises the output exactly
when `K` reaches a threshold, for every `K` up to the FMA size. Ada and Hopper keep 13 bits after
alignment and in the output, so the threshold is 3; B200 keeps 25 and 23, so it is 12. -/

namespace TensorCore

/-- `K` copies of the pair `(a, b)`, then zeros, up to `n` products. -/
def fp8Block {P : Model} (n K : ℕ) (a b : P.Word) (c : F32) : BlockInput P :=
  ⟨List.replicate K (a, b) ++ List.replicate (n - K) (0, 0), c⟩

/-- The value of a block's output. -/
def outputValue {P : Model} (x : BlockInput P) : Option ℚ := (evalBlock x).toOption.map (·.output.value)

/-- With `c = C` the output is `C`; with `c = C'` it exceeds `C` exactly when `t ≤ K`. -/
def RaisesExactlyFrom {P : Model} (n t : ℕ) (a b : P.Word) (c c' : F32) (C : ℚ) : Prop :=
  ∀ K ≤ n, outputValue (fp8Block n K a b c) = some C ∧
    ((outputValue (fp8Block n K a b c')).all (C < ·) ↔ t ≤ K)

instance {P : Model} (n t : ℕ) (a b : P.Word) (c c' : F32) (C : ℚ) :
    Decidable (RaisesExactlyFrom n t a b c c' C) := by
  unfold RaisesExactlyFrom; infer_instance

/-- Ada and Hopper FP8: products `2^-7 · 2^-7 = 2^-14`, `c = 1` and `1 − 2^-24`; threshold 3. -/
theorem fp8_narrow_nonmonotone :
    RaisesExactlyFrom (P := adaE4M3F32) 16 3 (widenE4M3 0x04) (widenE4M3 0x04)
      0x3f800000 0x3f7fffff 1 ∧
    RaisesExactlyFrom (P := adaE5M2F32) 16 3 0x20 0x20 0x3f800000 0x3f7fffff 1 ∧
    RaisesExactlyFrom (P := hopperE4M3F32) 32 3 (widenE4M3 0x04) (widenE4M3 0x04)
      0x3f800000 0x3f7fffff 1 ∧
    RaisesExactlyFrom (P := hopperE5M2F32) 32 3 0x20 0x20 0x3f800000 0x3f7fffff 1 := by
  decide +kernel

/-- B200 FP8: E5M2 products `2^-13 · 2^-13 = 2^-26` with `c = 1`, and E4M3 products
`2^-9 · 2^-9 = 2^-18` with `c = 256`; threshold 12 = 3·2^2, as on H100 FP16. -/
theorem fp8_blackwell_nonmonotone :
    RaisesExactlyFrom (P := blackwellE5M2F32) 32 12 0x08 0x08 0x3f800000 0x3f7fffff 1 ∧
    RaisesExactlyFrom (P := blackwellE4M3F32) 32 12 (widenE4M3 0x01) (widenE4M3 0x01)
      0x43800000 0x437fffff 256 := by
  decide +kernel

end TensorCore
