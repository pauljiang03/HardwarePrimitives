import CrossVendor.Formats

/-! # The two libraries round to nearest even the same way

`TensorCore.round32 .nearestEven` and `MatrixCore.rne32` are independent implementations of FP32
round-to-nearest-even. They return the same word on every rational up to the largest finite FP32
magnitude. Above it, `TensorCore.round32` returns no word, while `MatrixCore.rne32` rounds values
below the overflow threshold `2^128 − 2^103` down to the largest finite word. -/

namespace CrossVendor

theorem sign32_eq (b : BitVec 32) :
    (b.toNat / 2147483648 != 0) = MatrixCore.sign32 b := by
  have h := sign_eq (n := b.toNat) (k := 31) b.isLt
  simp only [MatrixCore.sign32]
  exact h

/-- The `TensorCore` nearest-even contract implies the `MatrixCore` one. -/
theorem nearestEven32 {x : Rat} {b : BitVec 32} (h : TensorCore.NearestEven32 x b) :
    MatrixCore.NearestEven32 x b := by
  obtain ⟨d, hd, hn, he⟩ := h
  refine ⟨d, (value32_eq b) ▸ hd, fun v y hy => ?_, fun v y hy hne heq => ?_⟩
  · have hf := TensorCore.value32_finite v y ((value32_eq v).symm ▸ hy)
    exact hn y hf
  · have hf := TensorCore.value32_finite v y ((value32_eq v).symm ▸ hy)
    exact he y hf hne heq

theorem maxFinite32_lt : TensorCore.maxFinite32 < MatrixCore.overflowThreshold32 := by
  decide +kernel

/-- **The same FP32 rounding.** Up to the largest finite magnitude, both libraries round every
rational to the same word. -/
theorem round32_eq_rne32 {x : Rat} (hx : TensorCore.absQ x ≤ TensorCore.maxFinite32) :
    TensorCore.round32 .nearestEven x = MatrixCore.rne32 x := by
  obtain ⟨b, hb, hn⟩ := TensorCore.round32_nearestEven_correct x hx
  have hlt : MatrixCore.absQ x < MatrixCore.overflowThreshold32 :=
    Std.lt_of_le_of_lt hx maxFinite32_lt
  obtain ⟨w, hw⟩ := Option.isSome_iff_exists.mp ((MatrixCore.rne32_isSome_iff x).mpr hlt)
  have hs := TensorCore.IndependentSpec.round32_sign_nearestEven x b hb
  have hr : MatrixCore.RoundsNearestEven32 x b := ⟨nearestEven32 hn, (sign32_eq b).symm.trans hs⟩
  rw [hb, hw, MatrixCore.roundsNearestEven32_unique hw hr]

end CrossVendor
