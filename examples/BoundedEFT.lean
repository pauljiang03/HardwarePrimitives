import TensorCore.Kernels.EFT.Success

open TensorCore

/-- Cancel two huge BF16 products while retaining the original FP32 accumulator. -/
def cancelling : BlockInput EFMachine.Variant.ampereBF16.model :=
  ⟨[(0x7f7f, 0x7f7f), (0xff7f, 0x7f7f)] ++ List.replicate 6 (0, 0), 0x3f800000⟩

#eval EFMachine.tcEft .ampereBF16 cancelling 0x7f7fffff
#eval EFMachine.operationCount 8

/-- Optimized support searches are identical to the standard scans on every word. -/
example (m : EFMachine.Magnitude) :
    EFMachine.leadingZeros m = m.clz ∧ EFMachine.trailingZeros m = m.ctz :=
  ⟨EFMachine.leadingZeros_eq m, EFMachine.trailingZeros_eq m⟩

/-- The public contract needs only finite decoded inputs, a finite supplied D, and the independent ideal's finite range. -/
example (variant : EFMachine.Variant) (x : BlockInput variant.model) (D : F32) (s d : ℚ)
    (shape : x.products.length = variant.model.nfma)
    (inputs : exactDot x = some s) (output : value32 D = some d)
    (range : absQ s ≤ maxFinite32) :
    ∃ r b, EFMachine.tcEft variant x D = .ok r ∧ r.bits = some b ∧ NearestEven32 s b :=
  EFMachine.tcEft_success shape inputs output range
