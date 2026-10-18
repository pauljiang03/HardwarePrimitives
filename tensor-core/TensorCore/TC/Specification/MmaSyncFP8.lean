import TensorCore.TC.Specification.Defs

/-! Independent specification of FP8 `mma.sync` on H100, H200 and B200 (*Accurate Models*,
Sections 4.1.6 to 4.1.8): the operands converted exactly to FP16, the products at positions
`k mod 4 ∈ {0, 1}` in one FP16 block FMA from `+0`, the others in a second from its output, then `c`
added in FP32 with round-to-nearest-even. -/

namespace TensorCore.IndependentSpec

/-- Hopper's FP16 block FMA: 16 products, 25 bits after alignment, minimum alignment exponent −133. -/
def hopperFP16 : Parameters := ⟨⟨10, 5, 15⟩, 16, 25, some (-133)⟩

/-- The pairs at positions `k` (from 0) with `k mod 4 ∈ {0, 1}`. -/
def firstPairs : List α → List α
  | a :: b :: _ :: _ :: rest => a :: b :: firstPairs rest
  | xs => xs.take 2

/-- The pairs at positions `k` with `k mod 4 ∈ {2, 3}`. -/
def secondPairs : List α → List α
  | _ :: _ :: c :: d :: rest => c :: d :: secondPairs rest
  | xs => xs.drop 2

/-- Zero pairs appended up to `n` pairs. -/
def padPairs (n : ℕ) (ps : List (BitVec 16 × BitVec 16)) : List (BitVec 16 × BitVec 16) :=
  ps ++ List.replicate (n - ps.length) (0, 0)

/-- `bits` is the output of an FP8 `mma.sync`, with `conv` the exact conversion of an FP8 word to
FP16. -/
def MmaSyncFP8Result (conv : BitVec 8 → BitVec 16) (c : BitVec 32)
    (ps : List (BitVec 8 × BitVec 8)) (bits : BitVec 32) : Prop :=
  ∃ d₁ d₂ v₂ vc,
    ResultM hopperFP16 23 ⟨padPairs 16 (firstPairs (ps.map fun (a, b) => (conv a, conv b))), 0⟩ d₁ ∧
    ResultM hopperFP16 23 ⟨padPairs 16 (secondPairs (ps.map fun (a, b) => (conv a, conv b))), d₁⟩ d₂ ∧
    value32 d₂ = some v₂ ∧ value32 c = some vc ∧ magnitude (v₂ + vc) ≤ maxFinite ∧
    RoundsNearestEven (v₂ + vc) bits

end TensorCore.IndependentSpec
