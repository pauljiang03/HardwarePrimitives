import MatrixCore

/-! # Exact inner products, `D = AB + C`, and bounds from the inputs -/

open MatrixCore

namespace MatrixCoreTests.InnerProduct

/-- Nine FP16 ones on CDNA 3 (two blocks, the second padded with zeros). -/
def nine : List (BitVec 16) := List.replicate 9 0x3C00

example : exactDot cdna3F16 nine nine 0 = 9 ∧ (dotBits cdna3F16 nine nine 0).map wordValue = .ok 9 := by
  decide +kernel

/-- `D = AB + C` on CDNA 1, with `A` given by rows and `B` by columns. -/
def A : List (List (BitVec 16)) := [[0x3C00, 0x4000], [0x4200, 0x4400]]
def B : List (List (BitVec 16)) := [[0x3C00, 0x3C00], [0x4000, 0xBC00]]
def C : List (List F32) := [[0, 0x3F800000], [0x7F800000, 0]]

example : mfma cdna1F16 A B C =
    [[some (.finite 0x40400000), some (.finite 0x3F800000)],
     [some (.infinity false), some (.finite 0x40000000)]] := by decide +kernel

/-- Downstream: a finite entry of `D` is within half an ulp per block of its exact inner product. -/
example {A : List (List (BitVec 16))} {B : List (List (BitVec 16))} {C : List (List F32)}
    {i j : ℕ} {row col : List (BitVec 16)} {cRow : List F32} {c d : F32}
    (hA : A[i]? = some row) (hB : B[j]? = some col) (hC : C[i]? = some cRow)
    (hc : cRow[j]? = some c) (hd : ((mfma cdna1F16 A B C)[i]?).bind (·[j]?) = some (some (.finite d))) :
    ∃ ts : List (BlockTrace cdna1F16), lastOutput c ts = d ∧
      absQ (exactDot cdna1F16 row col c - wordValue d) ≤
        sumQ (ts.map fun t => halfUlp32 t.prepared.exact) := by
  obtain ⟨ts, _, hl, _, he⟩ := mfma_error cdna1F16 (by decide)
    (Bnd := fun t => halfUlp32 t.prepared.exact)
    (fun _ _ ht => (cdna1F16_contract ht).error) hA hB hC hc hd
  exact ⟨ts, hl, he⟩

/-- CDNA 3, `c = 1`, `p₁ = 2^-24 + 2^-32`: the error against the bound from the inputs alone. -/
def cdna3Late : BlockInput cdna3F16 :=
  ⟨0x0C04 :: List.replicate 7 0, 0x0C00 :: List.replicate 7 0, 0x3F800000⟩

example : (evalBlock cdna3Late).toOption.map (fun t =>
    decide (absQ (t.prepared.exact - wordValue t.d) ≤ pow2 (-23) * t.prepared.absSum +
      (t.prepared.p.length + 4) * gridTerm (productSum cdna3F16 t.prepared.p).1 + pow2 (-149))) =
    some true := by decide +kernel

end MatrixCoreTests.InnerProduct
