import MatrixCore

/-! # Output error bounds on the paper's examples

Each check evaluates the actual error `exact − d` and the proven bound. -/

open MatrixCore

namespace MatrixCoreTests.ErrorBounds

/-- CDNA 1, `c = 1`: a tie, so the error `2^-23` equals the bound. -/
def cdna1Tie : BlockInput cdna1F16 :=
  ⟨[0x3C00, 0x0E00, 0x0E00, 0], [0x3C00, 0x1000, 0x1000, 0], 0x3F800000⟩

example : (evalBlock cdna1Tie).toOption.map (fun t =>
    (t.prepared.exact - wordValue t.d, halfUlp32 t.prepared.exact)) =
    some (-pow2 (-23), pow2 (-23)) := by decide +kernel

/-- CDNA 2, `c = 0`: the error `2^-23` is within the pairwise bound. -/
def cdna2Pairwise : BlockInput cdna2F16 :=
  ⟨[0x3C00, 0x0E00, 0x0E00, 0], [0x3C00, 0x1000, 0x1000, 0], 0⟩

example : (evalBlock cdna2Pairwise).toOption.map (fun t =>
    (t.prepared.exact - wordValue t.d,
      decide (absQ (t.prepared.exact - wordValue t.d) ≤
        pairwiseBound cdna2F16 t.prepared + flBound true t.sAcc))) =
    some (-pow2 (-23), true) := by decide +kernel

/-- CDNA 3, `c = 1`, `p₁ = 2^-24 + 2^-32`: the error `2^-24 + 2^-32` is within the bound. -/
def cdna3Late : BlockInput cdna3F16 :=
  ⟨0x0C04 :: List.replicate 7 0, 0x0C00 :: List.replicate 7 0, 0x3F800000⟩

example : (evalBlock cdna3Late).toOption.map (fun t =>
    (t.prepared.exact - wordValue t.d,
      decide (absQ (t.prepared.exact - wordValue t.d) ≤
        alignedBound cdna3F16 t.prepared + flBound false t.sAcc))) =
    some (pow2 (-24) + pow2 (-32), true) := by decide +kernel

/-- Downstream: a CDNA 1 inner product of any length is within half an ulp per block. -/
example {a b : List (BitVec 16)} {c d : F32} (hlen : a.length = b.length)
    (h : dotBits cdna1F16 a b c = .ok d) :
    ∃ ts : List (BlockTrace cdna1F16), lastOutput c ts = d ∧
      absQ (wordValue c + sumQ (ts.map fun t => t.prepared.products) - wordValue d) ≤
        sumQ (ts.map fun t => halfUlp32 t.prepared.exact) := by
  obtain ⟨ts, _, hd, he⟩ := correctRounding_dot_error (P := cdna1F16) rfl rfl rfl hlen h
  exact ⟨ts, hd, he⟩

/-- Downstream: on CDNA 3 every block's error bound holds along an inner product. -/
example {a b : List (BitVec 16)} {c d : F32} (hlen : a.length = b.length)
    (h : dotBits cdna3F16 a b c = .ok d) :
    ∃ ts : List (BlockTrace cdna3F16), lastOutput c ts = d ∧
      absQ (wordValue c + sumQ (ts.map fun t => t.prepared.products) - wordValue d) ≤
        sumQ (ts.map fun t => alignedBound cdna3F16 t.prepared + flBound false t.sAcc) := by
  obtain ⟨ts, _, hd, he⟩ := dotBits_error_bound cdna3F16
    (B := fun t => alignedBound cdna3F16 t.prepared + flBound false t.sAcc)
    (fun _ _ ht => (cdna3F16_contract ht).error) hlen h
  exact ⟨ts, hd, he⟩

end MatrixCoreTests.ErrorBounds
