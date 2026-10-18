import TensorCore.Kernels.EFT.Correctness
import TensorCore.Kernels.EFT.Grid

/-! Operation counts of the 576-bit TC-EFT (source-level operations, not processor cycles). -/

namespace TensorCore.EFMachine

structure OperationCount where
  inputDecodes : ℕ
  products : ℕ
  exponentScan : ℕ
  splits : ℕ
  extractionAdds : ℕ
  scalarAdds : ℕ
  conversions : ℕ
  guardCoefficientAdds : ℕ
  residualBitScans : ℕ
  scalarDecodes : ℕ
  deriving Repr, DecidableEq

def operationCount (K : ℕ) : OperationCount :=
  let N := K + 1
  ⟨2 * K + 2, K, N, N, 2 * N + 3, N + 2,
    2 * N + 7, N, N, 2 * (N + 2)⟩

/-- Concrete maxima for the block FMA of every supported variant, including failed scalar attempts:
the FP16, BF16 and TF32 variants have at most 16 products, the FP8 variants at most 32. -/
theorem operationCount_bounds (variant : Variant) (h16 : variant.model.nfma ≤ 16) :
    let b := operationCount variant.model.nfma
    b.inputDecodes ≤ 34 ∧ b.products ≤ 16 ∧ b.exponentScan ≤ 17 ∧ b.splits ≤ 17 ∧
    b.extractionAdds ≤ 37 ∧ b.scalarAdds ≤ 19 ∧
    b.conversions ≤ 41 ∧ b.guardCoefficientAdds ≤ 17 ∧ b.residualBitScans ≤ 17 ∧
    b.scalarDecodes ≤ 38 := by
  simp only [operationCount]; omega

theorem operationCount_bounds_all (variant : Variant) :
    let b := operationCount variant.model.nfma
    b.inputDecodes ≤ 66 ∧ b.products ≤ 32 ∧ b.exponentScan ≤ 33 ∧ b.splits ≤ 33 ∧
    b.extractionAdds ≤ 69 ∧ b.scalarAdds ≤ 35 ∧
    b.conversions ≤ 73 ∧ b.guardCoefficientAdds ≤ 33 ∧ b.residualBitScans ≤ 33 ∧
    b.scalarDecodes ≤ 70 := by
  have := variant_count variant
  simp only [operationCount]; omega

/-- At most 580 bit-scan probes with 16 products, 1,060 with 32: one leading scan per conversion,
one trailing scan per residual. -/
theorem bitScan_total_bound (variant : Variant) (h16 : variant.model.nfma ≤ 16) :
    10 * ((operationCount variant.model.nfma).conversions +
      (operationCount variant.model.nfma).residualBitScans) ≤ 580 := by
  simp only [operationCount]; omega

theorem bitScan_total_bound_all (variant : Variant) :
    10 * ((operationCount variant.model.nfma).conversions +
      (operationCount variant.model.nfma).residualBitScans) ≤ 1060 := by
  have := variant_count variant
  simp only [operationCount]; omega

theorem extraction_loop_bounds {variant : Variant} {x : BlockInput variant.model} {D : F32}
    {p : Prepared} {c : Components} (hp : prepare variant x D = .ok p) (hc : extract p = some c) :
    p.terms.length ≤ 33 ∧ c.coarse.length = variant.model.nfma + 1 ∧
      c.low.length = variant.model.nfma + 1 := by
  have hlen := (prepare_spec hp).2.2.2.1
  have hs := extract_spec hc
  rw [hs.2.1, hs.2.2.1]
  simp only [List.length_map, hlen]
  exact ⟨by have h := variant_count variant; omega, trivial, trivial⟩

/-- The number of checked additions in one `sumWords` call. -/
def sumWordsAdds : List Word → ℕ
  | [] => 0
  | _ :: xs => sumWordsAdds xs + 1

theorem sumWordsAdds_eq (xs : List Word) : sumWordsAdds xs = xs.length := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [sumWordsAdds, ih]

end TensorCore.EFMachine
