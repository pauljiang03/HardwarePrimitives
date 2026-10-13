import MatrixCore.MC.Eval
import MatrixCore.MC.Prepared

/-! # Order and sign of the products

The configurations differ in whether the order of the products and the sign of the inputs can
change `d`:

* `correct_rounding` (CDNA 1) and `global_alignment` (CDNA 3 fp16, bf16, tf19) depend on the
  products only as a multiset: alignment uses the maximum exponent, truncation acts on each
  product separately, and the sum is exact;
* `pair_wise_sum` (CDNA 2) and `odd_even_grouping` (CDNA 3 binary8) depend on positions;
* the RD steps of CDNA 3 make it sign-asymmetric, while correct rounding is sign-symmetric
  (`correctRounding_neg`). -/

namespace MatrixCore

theorem any_perm {xs ys : List α} (h : xs.Perm ys) (f : α → Bool) : xs.any f = ys.any f := by
  apply Bool.eq_iff_iff.mpr
  simp only [List.any_eq_true]
  exact ⟨fun ⟨a, ha, hf⟩ => ⟨a, h.subset ha, hf⟩, fun ⟨a, ha, hf⟩ => ⟨a, h.symm.subset ha, hf⟩⟩

theorem exact_perm {x y : Prepared} (hp : x.p.Perm y.p) (hc : x.c = y.c) : x.exact = y.exact := by
  unfold Prepared.exact
  rw [sumQ_perm (hp.map _), hc]

theorem alignedSum_perm (neab : ℕ) {ps qs : List Unpacked} (h : ps.Perm qs) :
    alignedSum neab ps = alignedSum neab qs := by
  unfold alignedSum
  rw [maxExp_perm h]
  split
  · rfl
  · rw [sumQ_perm (h.map _)]

/-- `correct_rounding` and `global_alignment` depend only on the multiset of products and on
`c`. -/
theorem accumulate_perm {P : Model}
    (hP : P.accumulation = .correctRounding ∨ P.accumulation = .globalAlignment)
    {x y : Prepared} (hp : x.p.Perm y.p) (hc : x.c = y.c) : accumulate P x = accumulate P y := by
  unfold accumulate Prepared.productOverflows
  rw [any_perm hp]
  rcases hP with h | h
  · simp only [h, exact_perm hp hc]
  · simp only [h, alignedAccumulation, productSum, alignedSum_perm P.neab hp, hc]

/-! ## Order and sign witnesses

Encoded words: fp16 `0x3C00 = 1`, `0x0E00 = 1.5·2^-12`, `0x1000 = 2^-11`; fp8-E5M2 FNUZ
`0x40 = 1`, `0xC0 = −1`, `0x92 = −1.5·2^-12`, `0x10 = 2^-12`; binary32 `0x3F800000 = 1`. -/

/-- CDNA 2: with `s = 2^-23 + 2^-24`, the products `1, s, s, 0` give `fl{fl{1 + s} + fl{s}} =
1 + 2^-21`, while `s, s, 1, 0` give `fl{fl{s + s} + 1} = 1 + 2^-22 + 2^-23`. -/
theorem pairWiseSum_order_dependent :
    blockBits (P := cdna2F16) ⟨[0x3C00, 0x0E00, 0x0E00, 0], [0x3C00, 0x1000, 0x1000, 0], 0⟩ =
      .ok 0x3F800004 ∧
    blockBits (P := cdna2F16) ⟨[0x0E00, 0x0E00, 0x3C00, 0], [0x1000, 0x1000, 0x3C00, 0], 0⟩ =
      .ok 0x3F800003 := by decide +kernel

/-- CDNA 3 binary8: `−1, −(2^-24 + 2^-25), 0` give `−(1 + 2^-23)` (different parities: the even
sum is shifted and RD), while `−1, 0, −(2^-24 + 2^-25)` give `−1` (same parity: truncation). -/
theorem oddEvenGrouping_order_dependent :
    blockBits (P := cdna3FP8 e5m2fnuz e5m2fnuz)
        ⟨[0xC0, 0x92] ++ List.replicate 14 0, [0x40, 0x10] ++ List.replicate 14 0, 0⟩ =
      .ok 0xBF800001 ∧
    blockBits (P := cdna3FP8 e5m2fnuz e5m2fnuz)
        ⟨[0xC0, 0, 0x92] ++ List.replicate 13 0, [0x40, 0, 0x10] ++ List.replicate 13 0, 0⟩ =
      .ok 0xBF800000 := by decide +kernel

/-- CDNA 3 is sign-asymmetric: `c = 1, p₁ = 2^-24 + 2^-32` gives `1`, but negating both gives
`−(1 + 2^-23)` rather than `−1`. fp16 `0x0C04 = (1 + 2^-8)·2^-12`, `0x0C00 = 2^-12`. -/
theorem globalAlignment_sign_asymmetric :
    blockBits (P := cdna3F16) ⟨[0x0C04] ++ List.replicate 7 0, [0x0C00] ++ List.replicate 7 0,
      0x3F800000⟩ = .ok 0x3F800000 ∧
    blockBits (P := cdna3F16) ⟨[0x8C04] ++ List.replicate 7 0, [0x0C00] ++ List.replicate 7 0,
      0xBF800000⟩ = .ok 0xBF800001 := by decide +kernel

end MatrixCore
