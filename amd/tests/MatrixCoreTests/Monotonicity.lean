import MatrixCore

/-! # Monotonicity in `c`, against the TC-EFT construction

The TC-EFT paper lowers `c` from `1` to `1 − 2^-24` with `K` products of `2^-(24+p)`: on NVIDIA
Tensor Cores `c` is the term holding the alignment exponent, so the smaller `c` lowers it, the
products stop being truncated, and the output rises (any term holding that exponent would do). On AMD `c` is aligned separately (CDNA 3) or the sum is exact (CDNA 1), so
the products `2^-24 = 0x0C00 · 0x0C00` are kept in both cases and the smaller `c` does not give a
larger output. `evalBlock_c_monotone` proves this for every input. -/

open MatrixCore

namespace MatrixCoreTests.Monotonicity

def k8 : List (BitVec 16) := List.replicate 8 0x0C00
def k4 : List (BitVec 16) := List.replicate 4 0x0C00

/-- CDNA 3: `1 + 8·2^-24` and `1 − 2^-24 + 8·2^-24` both give `1 + 2^-21`. -/
example : blockBits (P := cdna3F16) ⟨k8, k8, 0x3F800000⟩ = .ok 0x3F800004 ∧
    blockBits (P := cdna3F16) ⟨k8, k8, 0x3F7FFFFF⟩ = .ok 0x3F800004 := by decide +kernel

/-- CDNA 1 and CDNA 2 with four products: `1 + 2^-22` both times. -/
example : blockBits (P := cdna1F16) ⟨k4, k4, 0x3F800000⟩ = .ok 0x3F800002 ∧
    blockBits (P := cdna1F16) ⟨k4, k4, 0x3F7FFFFF⟩ = .ok 0x3F800002 ∧
    blockBits (P := cdna2F16) ⟨k4, k4, 0x3F800000⟩ = .ok 0x3F800002 ∧
    blockBits (P := cdna2F16) ⟨k4, k4, 0x3F7FFFFF⟩ = .ok 0x3F800002 := by decide +kernel

/-- For every input: lowering `c` never raises a CDNA 3 output. -/
example {a b : List (BitVec 16)} {c c' : F32} {t t' : BlockTrace cdna3F16}
    (h : evalBlock (P := cdna3F16) ⟨a, b, c⟩ = .ok t)
    (h' : evalBlock (P := cdna3F16) ⟨a, b, c'⟩ = .ok t') (hc : wordValue c ≤ wordValue c') :
    wordValue t.d ≤ wordValue t'.d :=
  evalBlock_c_monotone paper_models_monotone.2.2.2.2.2.2.1 h h' hc

/-- And for inner products of any length. -/
example {a b : List (BitVec 16)} {c c' d d' : F32} (hlen : a.length = b.length)
    (h : dotBits cdna2F16 a b c = .ok d) (h' : dotBits cdna2F16 a b c' = .ok d')
    (hc : wordValue c ≤ wordValue c') : wordValue d ≤ wordValue d' :=
  dotBits_c_monotone paper_models_monotone.2.2.2.1 hlen h h' hc

end MatrixCoreTests.Monotonicity
