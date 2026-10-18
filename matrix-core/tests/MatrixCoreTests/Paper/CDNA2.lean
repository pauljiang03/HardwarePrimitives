import MatrixCoreTests.Paper.CDNA1

/-! # CDNA 2 (MI210, MI250) test vectors of Section 4.2 -/

namespace MatrixCoreTests.CDNA2

open MatrixCore

abbrev s : ℚ := p2 (-23) + p2 (-24)

/-! ## FP16 inputs -/

/-- No subnormals: a small `c` or a subnormal operand gives `0`. -/
example : [p2 (-127), p2 (-140), p2 (-149)].all (fun c =>
    observeP cdna2F16 [0] (c : ℚ) == some (.v 0)) = true := by decide +kernel
example : observe cdna2F16 [((p2 (-24) : ℚ), 1)] (0 : ℚ) = some (.v 0) := by decide +kernel

/-- Final RNE: `p₁ = ±1` with `c = ±2^-24` or `c = ±s`. -/
example : observeP cdna2F16 [1] (p2 (-24) : ℚ) = some (.v 1) := by decide +kernel
example : observeP cdna2F16 [-1] (-p2 (-24) : ℚ) = some (.v (-1)) := by decide +kernel
example : observeP cdna2F16 [1] (s : ℚ) = some (.v (1 + p2 (-22))) := by decide +kernel
example : observeP cdna2F16 [-1] (-s : ℚ) = some (.v (-(1 + p2 (-22)))) := by decide +kernel

/-- Permuting `1, s, s` over `c, p₁, p₂` changes `d`: no global alignment. -/
example : observeP cdna2F16 [s, s] (1 : ℚ) = some (.v (1 + p2 (-22) + p2 (-23))) := by decide +kernel
example : observeP cdna2F16 [1, s] (s : ℚ) = some (.v (1 + p2 (-21))) := by decide +kernel
example : observeP cdna2F16 [s, 1] (s : ℚ) = some (.v (1 + p2 (-21))) := by decide +kernel

/-- `c = 1, p₁ = p_j = s` for `j = 2 … 16`. -/
example : ((List.range 15).map fun i => CDNA1.nfmaTest cdna2F16 16 (i + 2) true) =
    (List.range 15).map fun i =>
      some (.v (if i + 2 ≤ 4 then 1 + p2 (-22) + p2 (-23) else 1 + p2 (-21))) := by decide +kernel

/-- `p₁ = 1` or `p₂ = 1`, with `p₃ = p₄ = s`. -/
example : observeP cdna2F16 [1, 0, s, s] (0 : ℚ) = some (.v (1 + p2 (-22) + p2 (-23))) := by
  decide +kernel
example : observeP cdna2F16 [0, 1, s, s] (0 : ℚ) = some (.v (1 + p2 (-22) + p2 (-23))) := by
  decide +kernel

/-- `p₁ = p₃ = 1, p₂ = p₄ = s`, with `c = 0` and `c = 2^-23 + 2^-25`. -/
example : observeP cdna2F16 [1, s, 1, s] (0 : ℚ) = some (.v (2 + p2 (-21))) := by decide +kernel
example : observeP cdna2F16 [1, s, 1, s] (p2 (-23) + p2 (-25) : ℚ) =
    some (.v (2 + p2 (-21) + p2 (-22))) := by decide +kernel

/-- `a₁ = a₂ = 1, b₁ = −b₂ = ∞` gives NaN. -/
example : observe cdna2F16 [(1, .inf false), (1, .inf true)] (0 : ℚ) = some .nan := by decide +kernel

/-! ## BF16 inputs -/

/-- Group size `4` for `_1k` instructions and `2` otherwise. -/
example : ((List.range 15).map fun i => CDNA1.nfmaTest cdna2BF16_1k 16 (i + 2) true) =
    (List.range 15).map fun i =>
      some (.v (if i + 2 ≤ 4 then 1 + p2 (-22) + p2 (-23) else 1 + p2 (-21))) := by decide +kernel
example : ((List.range 7).map fun i => CDNA1.nfmaTest cdna2BF16 8 (i + 2) true) =
    (List.range 7).map fun i =>
      some (.v (if i + 2 ≤ 2 then 1 + p2 (-22) + p2 (-23) else 1 + p2 (-21))) := by decide +kernel

/-- Final RNE. -/
example : observeP cdna2BF16 [1] (s : ℚ) = some (.v (1 + p2 (-22))) := by decide +kernel
example : observeP cdna2BF16_1k [1] (s : ℚ) = some (.v (1 + p2 (-22))) := by decide +kernel

/-- Products are converted to FP32 before accumulation: `p₁ = 2^128, p₂ = −p₁`. -/
example : observe cdna2BF16 [((p2 64 : ℚ), (p2 64 : ℚ)), ((p2 64 : ℚ), (-p2 64 : ℚ))] (0 : ℚ) =
    some .nan := by decide +kernel
example : observe cdna2BF16_1k [((p2 64 : ℚ), (p2 64 : ℚ)), ((p2 64 : ℚ), (-p2 64 : ℚ))] (0 : ℚ) =
    some .nan := by decide +kernel

/-- Subnormals are flushed after every `fl{·}`: `p₁ = p₂ = 2^-127`. -/
example : observe cdna2BF16 [((p2 (-64) : ℚ), (p2 (-63) : ℚ)), ((p2 (-63) : ℚ), (p2 (-64) : ℚ))]
    (0 : ℚ) = some (.v 0) := by decide +kernel

/-- Infinities in `a`, `b`: `a₁ = 1, b₁ = ±∞` gives `±∞`; both signs give NaN. -/
example : observe cdna2BF16 [(1, .inf false)] (0 : ℚ) = some (.inf false) := by decide +kernel
example : observe cdna2BF16 [(1, .inf true)] (0 : ℚ) = some (.inf true) := by decide +kernel
example : observe cdna2BF16 [(1, .inf false), (1, .inf true)] (0 : ℚ) = some .nan := by decide +kernel

/-! ## FP32 inputs: SFMA as on CDNA 1 -/

example : Architecture.cdna2.model .fp32 = some sfmaF32 := rfl

end MatrixCoreTests.CDNA2
