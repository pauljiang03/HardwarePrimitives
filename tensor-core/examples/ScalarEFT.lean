import TensorCore.EFT.Scalar

open TensorCore

/-- FP64 is the correction format; the final output remains correctly rounded FP32. -/
example (t : BlockTrace) (h : t.scalarPredicateIn fp64 = true) :
    ∃ b, t.scalarCorrectedIn fp64 = some b ∧ NearestEven32 t.block.exactDot b :=
  scalarCorrectedIn_correct t fp64 h

/-- The component support/range assumptions suffice for exact summation in any ordering. -/
example (ℓ : ℤ) (zs reordered : List ℤ) (hperm : zs.Perm reordered)
    (hgrid : -1074 ≤ ℓ) (hbits : magnitudeSum zs < 2 ^ 53)
    (hrange : (magnitudeSum zs : ℚ) * pow2 ℓ ≤ fp64.maxFinite) :
    naiveSumBinary fp64 (reordered.map fun (z : ℤ) => (z : ℚ) * pow2 ℓ) =
      some ((sumZ zs : ℚ) * pow2 ℓ) :=
  naiveSumBinary_exact_perm fp64 (by decide) ℓ hgrid zs reordered hperm hbits hrange
