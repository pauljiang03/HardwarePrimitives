import MatrixCore.MC.Eval
import MatrixCore.MC.Prepared

/-! # Order and sign of the products

`correct_rounding` and `global_alignment` depend on the products only as a multiset, while
`pair_wise_sum` and `odd_even_grouping` depend on their order; CDNA 3 is sign-asymmetric. -/

namespace MatrixCore

theorem any_perm {xs ys : List α} (h : xs.Perm ys) (f : α → Bool) : xs.any f = ys.any f := by
  apply Bool.eq_iff_iff.mpr
  simp only [List.any_eq_true]
  exact ⟨fun ⟨a, ha, hf⟩ => ⟨a, h.subset ha, hf⟩, fun ⟨a, ha, hf⟩ => ⟨a, h.symm.subset ha, hf⟩⟩

theorem exact_perm {x y : Prepared} (hp : x.p.Perm y.p) (hc : x.c = y.c) : x.exact = y.exact := by
  unfold Prepared.exact
  rw [sumQ_perm (hp.map _), hc]

theorem alignedSum_perm (padding : ℕ) {ps qs : List Unpacked} (h : ps.Perm qs) :
    alignedSum padding ps = alignedSum padding qs := by
  unfold alignedSum
  rw [maxExp_perm h]
  split
  · rfl
  · rw [sumQ_perm (h.map _)]

/-- `correct_rounding` and `global_alignment` depend only on the multiset of products and `c`. -/
theorem accumulate_perm {P : Model}
    (hP : P.accumulation = .correctRounding ∨ P.accumulation = .globalAlignment)
    {x y : Prepared} (hp : x.p.Perm y.p) (hc : x.c = y.c) : accumulate P x = accumulate P y := by
  unfold accumulate Prepared.productOverflows
  rw [any_perm hp]
  rcases hP with h | h
  · simp only [h, exact_perm hp hc]
  · simp only [h, alignedAccumulation, productSum, alignedSum_perm P.padding hp, hc]

/-! ## Order and sign witnesses -/

/-- CDNA 2: `1, s, s, 0` and `s, s, 1, 0` with `s = 2^-23 + 2^-24` give different outputs. -/
theorem pairWiseSum_order_dependent :
    blockBits (P := cdna2F16) ⟨[0x3C00, 0x0E00, 0x0E00, 0], [0x3C00, 0x1000, 0x1000, 0], 0⟩ =
      .ok 0x3F800004 ∧
    blockBits (P := cdna2F16) ⟨[0x0E00, 0x0E00, 0x3C00, 0], [0x1000, 0x1000, 0x3C00, 0], 0⟩ =
      .ok 0x3F800003 := by decide +kernel

/-- CDNA 3 FP8: products `−1, −(2^-24 + 2^-25), 0` and `−1, 0, −(2^-24 + 2^-25)` differ. -/
theorem oddEvenGrouping_order_dependent :
    blockBits (P := cdna3FP8 e5m2fnuz e5m2fnuz)
        ⟨[0xC0, 0x92] ++ List.replicate 14 0, [0x40, 0x10] ++ List.replicate 14 0, 0⟩ =
      .ok 0xBF800001 ∧
    blockBits (P := cdna3FP8 e5m2fnuz e5m2fnuz)
        ⟨[0xC0, 0, 0x92] ++ List.replicate 13 0, [0x40, 0, 0x10] ++ List.replicate 13 0, 0⟩ =
      .ok 0xBF800000 := by decide +kernel

/-- CDNA 3 FP16: `c = 1`, `p₁ = 2^-24 + 2^-32` gives `1`; negating both gives `−(1 + 2^-23)`. -/
theorem globalAlignment_sign_asymmetric :
    blockBits (P := cdna3F16) ⟨[0x0C04] ++ List.replicate 7 0, [0x0C00] ++ List.replicate 7 0,
      0x3F800000⟩ = .ok 0x3F800000 ∧
    blockBits (P := cdna3F16) ⟨[0x8C04] ++ List.replicate 7 0, [0x0C00] ++ List.replicate 7 0,
      0xBF800000⟩ = .ok 0xBF800001 := by decide +kernel

end MatrixCore
