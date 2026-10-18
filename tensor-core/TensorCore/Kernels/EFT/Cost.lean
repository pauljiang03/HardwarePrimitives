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

/-- Concrete maxima for the block FMA of every supported variant, including failed scalar attempts. -/
theorem operationCount_bounds (variant : Variant) :
    let b := operationCount variant.model.nfma
    b.inputDecodes ≤ 34 ∧ b.products ≤ 16 ∧ b.exponentScan ≤ 17 ∧ b.splits ≤ 17 ∧
    b.extractionAdds ≤ 37 ∧ b.scalarAdds ≤ 19 ∧
    b.conversions ≤ 41 ∧ b.guardCoefficientAdds ≤ 17 ∧ b.residualBitScans ≤ 17 ∧
    b.scalarDecodes ≤ 38 := by cases variant <;> decide

/-- At most 580 bit-scan probes: one leading scan per conversion, one trailing scan per residual. -/
theorem bitScan_total_bound (variant : Variant) :
    10 * ((operationCount variant.model.nfma).conversions +
      (operationCount variant.model.nfma).residualBitScans) ≤ 580 := by
  cases variant <;> decide

theorem extraction_loop_bounds {variant : Variant} {x : BlockInput variant.model} {D : F32}
    {p : Prepared} {c : Components} (hp : prepare variant x D = .ok p) (hc : extract p = some c) :
    p.terms.length ≤ 17 ∧ c.coarse.length = variant.model.nfma + 1 ∧
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
