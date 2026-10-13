import MatrixCoreTests.Paper.CDNA2

/-! # CDNA 3 (MI300A, MI300X) test vectors of Section 4.3

Products are written by value and formed from normal operands with `e_a + e_b = ⌊log₂ |p|⌋`
unless an operand pair is given. -/

namespace MatrixCoreTests.CDNA3

open MatrixCore

/-! ## fp16 inputs (Algorithm 1) -/

/-- Subnormals in input and output; final RNE. -/
example : observe cdna3F16 [((p2 (-24) : ℚ), (p2 (-24) : ℚ))] (0 : ℚ) = some (.v (p2 (-48))) := by
  decide +kernel
example : observeP cdna3F16 [0] (p2 (-140) : ℚ) = some (.v (p2 (-140))) := by decide +kernel
example : observeP cdna3F16 [1] (p2 (-23) + p2 (-24) : ℚ) = some (.v (1 + p2 (-22))) := by
  decide +kernel

/-- One extra alignment bit: `±1, ±2^-24, ±2^-24` over `c, p₁, p₂` give `±(1 + 2^-23)`. -/
example : [(1, p2 (-24), p2 (-24)), (p2 (-24), 1, p2 (-24)), (p2 (-24), p2 (-24), 1)].all
    (fun (c, q₁, q₂) =>
      observeP cdna3F16 [q₁, q₂] (c : ℚ) == some (.v (1 + p2 (-23))) &&
      observeP cdna3F16 [-q₁, -q₂] (-c : ℚ) == some (.v (-(1 + p2 (-23))))) = true := by
  decide +kernel

/-- `N_FMA = 8`: `c = 1, p₁ = p_j = 2^-24` gives `1 + 2^-23` for `j ≤ 8` (`k = 16`); beyond the
first block each block rounds `1 + 2^-24` to `1`. -/
example : ((List.range 15).map fun (i : ℕ) =>
    observeP cdna3F16 ((List.range 16).map fun l =>
      if l = 0 ∨ l = i + 1 then p2 (-24) else 0) (1 : ℚ)) =
    (List.range 15).map fun (i : ℕ) => some (.v (if i + 2 ≤ 8 then 1 + p2 (-23) else 1)) := by
  decide +kernel

/-- No interleaving: `±1, 0, ±(2^-24 + 2^-25)` over `p₁, p₂, p₃` always give `±1`. -/
example : [[1, 0, p2 (-24) + p2 (-25)], [1, p2 (-24) + p2 (-25), 0], [0, 1, p2 (-24) + p2 (-25)],
    [p2 (-24) + p2 (-25), 1, 0], [p2 (-24) + p2 (-25), 0, 1], [0, p2 (-24) + p2 (-25), 1]].all
    (fun ps => observeP cdna3F16 ps (0 : ℚ) == some (.v 1) &&
      observeP cdna3F16 (ps.map (- ·)) (0 : ℚ) == some (.v (-1))) = true := by decide +kernel

/-- Products are truncated beyond 24 fractional bits: `p₁ = ±1, p₂ = ±(2^-24 + 2^(-24-j))` gives
`±1` for `j > 0`. -/
example : (List.range 10).all (fun (i : ℕ) =>
    let q := p2 (-24) + p2 (-25 - (i : ℤ))
    observeP cdna3F16 [1, q] (0 : ℚ) == some (.v 1) &&
    observeP cdna3F16 [-1, -q] (0 : ℚ) == some (.v (-1))) = true := by decide +kernel

/-- Products are denormalized: `a₁ = b₁ = 1.5` (`p₁ = 2.25` with exponent `0`), `p₂ = 2^-23`,
`p₃ = p₄ = 2^-24` gives `2.25 + 2^-22`; with `a₁ = 2.25, b₁ = 1` it gives `2.25`. -/
example : observe cdna3F16 [((3 / 2 : ℚ), (3 / 2 : ℚ)), splitProduct (p2 (-23)),
    splitProduct (p2 (-24)), splitProduct (p2 (-24))] (0 : ℚ) = some (.v (9 / 4 + p2 (-22))) := by
  decide +kernel
example : observe cdna3F16 [((9 / 4 : ℚ), 1), splitProduct (p2 (-23)),
    splitProduct (p2 (-24)), splitProduct (p2 (-24))] (0 : ℚ) = some (.v (9 / 4)) := by
  decide +kernel

/-- `c` is added after the products: `c = 1, p₁ = p₂ = 2^-25, p₃ = 2^-24` gives `1 + 2^-23`. -/
example : observeP cdna3F16 [p2 (-25), p2 (-25), p2 (-24)] (1 : ℚ) = some (.v (1 + p2 (-23))) := by
  decide +kernel

/-- `p₁ = ±1, c = ±(2^-24 + 2^(-24-j))`: the shifted `s_c` is RD to 24 fractional bits, giving `1`
for positive and `−(1 + 2^-23)` for negative inputs. -/
example : (List.range 23).all (fun (i : ℕ) =>
    let c := p2 (-24) + p2 (-25 - (i : ℤ))
    observeP cdna3F16 [1] (c : ℚ) == some (.v 1) &&
    observeP cdna3F16 [-1] (-c : ℚ) == some (.v (-(1 + p2 (-23))))) = true := by decide +kernel

/-- The product sum is not rounded before `c` is added: `p₁ = 1, p₂ = 2^-24, c = 2^-24` gives
`1 + 2^-23`. -/
example : observeP cdna3F16 [1, p2 (-24)] (p2 (-24) : ℚ) = some (.v (1 + p2 (-23))) := by
  decide +kernel

/-- `c = ±1, p₁ = ±(2^-24 + 2^(-24-j))`: positive `1 + 2^-23` for `j < 8` and `1` for `j ≥ 8`;
negative `−(1 + 2^-23)` for every `j > 0`. -/
example : ((List.range 10).map fun (i : ℕ) =>
    observeP cdna3F16 [p2 (-24) + p2 (-25 - (i : ℤ))] (1 : ℚ)) =
    (List.range 10).map fun (i : ℕ) => some (.v (if i + 1 < 8 then 1 + p2 (-23) else 1)) := by
  decide +kernel
example : (List.range 10).all (fun (i : ℕ) =>
    observeP cdna3F16 [-(p2 (-24) + p2 (-25 - (i : ℤ)))] (-1 : ℚ) ==
      some (.v (-(1 + p2 (-23))))) = true := by decide +kernel

/-- `S_{p_i,sum}` is RD at its 32nd fractional bit: `c = 1`,
`p₁ + ⋯ = −(2^-24 + Σ_{ℓ=26}^{30+j} 2^-ℓ)` gives `1 − 2^-24` for `j ≤ 2` and `1 − 2^-23` for
`j > 2`. -/
def sumRD (j : ℕ) : List ℚ :=
  [-p2 (-24), -bits 26 (min 31 (30 + j)), if 30 + j ≥ 32 then -bits 32 (30 + j) else 0]

example : ((List.range 11).map fun (j : ℕ) => observeP cdna3F16 (sumRD j) (1 : ℚ)) =
    (List.range 11).map fun (j : ℕ) => some (.v (if j ≤ 2 then 1 - p2 (-24) else 1 - p2 (-23))) := by
  decide +kernel

/-- `c = 1, p₁ + ⋯ = −(2^-24 + Σ_{ℓ=26}^{31} 2^-ℓ) + 2^-33` gives `1 − 2^-24`. -/
example : observeP cdna3F16 [-p2 (-24), -bits 26 31, p2 (-33)] (1 : ℚ) =
    some (.v (1 - p2 (-24))) := by decide +kernel

/-- RD of the normalized `S_acc`: `c = 2 − 2^-22, p₁ = 2^-22, p₂ = 2^-23 + 2^-j` gives
`2 + 2^-22` for `j ≤ 30` and `2` for `j > 30` (`j = 24 … 32`). -/
example : ((List.range 9).map fun (i : ℕ) =>
    observeP cdna3F16 [p2 (-22), p2 (-23) + p2 (-24 - (i : ℤ))] (2 - p2 (-22) : ℚ)) =
    (List.range 9).map fun (i : ℕ) => some (.v (if 24 + i ≤ 30 then 2 + p2 (-22) else 2)) := by
  decide +kernel

/-- `c = −2 + 2^-21, p₁ = −2^-21, p₂ = −2^-22, p₃ = −Σ_{ℓ=24}^{j} 2^-ℓ` gives `−2 − 2^-22` for
`j = 28 … 30` and `−2 − 2^-21` for `j > 30`: `S_acc` is rounded down, not truncated. -/
example : ((List.range 5).map fun (i : ℕ) =>
    observeP cdna3F16 [-p2 (-21), -p2 (-22), -bits 24 (28 + i)] (-2 + p2 (-21) : ℚ)) =
    (List.range 5).map fun (i : ℕ) => some (.v (if 28 + i ≤ 30 then -2 - p2 (-22) else -2 - p2 (-21))) := by
  decide +kernel

/-- `c = 1, p₁ = 2^-24, p₂ = 2^-j` gives `1 + 2^-23` for `j = 31` and `1` for `j = 32`. -/
example : observeP cdna3F16 [p2 (-24), p2 (-31)] (1 : ℚ) = some (.v (1 + p2 (-23))) := by
  decide +kernel
example : observeP cdna3F16 [p2 (-24), p2 (-32)] (1 : ℚ) = some (.v 1) := by decide +kernel

/-- `S_acc` is normalized before its RD: `c = 1, p₁ + ⋯ = −(2^-24 + Σ_{ℓ=26}^{32} 2^-ℓ)` gives
`1 − 2^-24`. -/
example : observeP cdna3F16 [-p2 (-24), -bits 26 32] (1 : ℚ) = some (.v (1 - p2 (-24))) := by
  decide +kernel

/-- `c` is aligned to the largest product exponent even when the products cancel:
`c = 2^4, p₁ = −p₂ = 2^29` gives `0` (fp16 products reach about `2^32`; the paper's
`c = 2^10, p₁ = −p₂ = 2^35` is checked with bf16 below). -/
example : observeP cdna3F16 [p2 29, -p2 29] (p2 4 : ℚ) = some (.v 0) := by decide +kernel

/-- Infinities. -/
example : observe cdna3F16 [(.inf false, 1)] (0 : ℚ) = some (.inf false) := by decide +kernel
example : observe cdna3F16 [(.inf false, 1), (.inf true, 1)] (0 : ℚ) = some .nan := by
  decide +kernel

/-! ## bf16 inputs -/

/-- The cancellation test: `c = 2^10, p₁ = −p₂ = 2^35` gives `0`. -/
example : observeP cdna3BF16 [p2 35, -p2 35] (p2 10 : ℚ) = some (.v 0) := by decide +kernel

/-- Product overflow by magnitude: `|p₁| ≥ 2^128` gives `±∞`; `a₁ = a₂ = 1.5·2^64,
b₁ = −b₂ = 1.5·2^63` (products `±2.25·2^127`, exponent `127`) gives NaN. -/
example : observe cdna3BF16 [((p2 64 : ℚ), (p2 64 : ℚ))] (0 : ℚ) = some (.inf false) := by
  decide +kernel
example : observe cdna3BF16 [((p2 64 : ℚ), (-p2 64 : ℚ))] (0 : ℚ) = some (.inf true) := by
  decide +kernel
example : observe cdna3BF16 [((3 / 2 * p2 64 : ℚ), (3 / 2 * p2 63 : ℚ)),
    ((3 / 2 * p2 64 : ℚ), (-(3 / 2 * p2 63) : ℚ))] (0 : ℚ) = some .nan := by decide +kernel

/-- An intermediate sum may exceed `2^128` within one block: `p₁ = p₂ = 1.5·2^127`,
`p₃ = −1.5·2^127` gives `1.5·2^127`. -/
example : observeP cdna3BF16 [3 / 2 * p2 127, 3 / 2 * p2 127, -(3 / 2 * p2 127)] (0 : ℚ) =
    some (.v (3 / 2 * p2 127)) := by decide +kernel

/-- `e_{c=0} = −126`: `c = 0, p₁ = ±2^-150, p₂ = ±2^(-152-i)` gives `2^-149` for `i < 6` and `0`
otherwise on the positive axis, and `−2^-149` on the negative axis while `p₂` lies within the 24
fractional bits kept below `e_max = −150` (`i ≤ 22`). -/
example : ((List.range 24).map fun (i : ℕ) =>
    observeP cdna3BF16 [p2 (-150), p2 (-152 - (i : ℤ))] (0 : ℚ)) =
    (List.range 24).map fun (i : ℕ) => some (.v (if i < 6 then p2 (-149) else 0)) := by decide +kernel
example : (List.range 23).all (fun (i : ℕ) =>
    observeP cdna3BF16 [-p2 (-150), -p2 (-152 - (i : ℤ))] (0 : ℚ) == some (.v (-p2 (-149)))) =
    true := by decide +kernel

/-- At `i = 23`, `p₂ = −2^-175` is the 25th fractional bit below `e_max`; Algorithm 1 truncates
it when the products are aligned, leaving `S_acc = −2^-150`, which RNE rounds to `−0`. The paper's
prose reports `−2^-149` for every `i` from `0` to `23`; the magnitude truncation is confirmed by
the interleaving test above. -/
example : observeP cdna3BF16 [-p2 (-150), -p2 (-175)] (0 : ℚ) = some (.v 0) := by decide +kernel

/-- Zero products do not take part in the exponent maximum. -/
example : ((List.range 24).map fun (i : ℕ) =>
    observeP cdna3BF16 [p2 (-150), 0, p2 (-152 - (i : ℤ))] (0 : ℚ)) =
    (List.range 24).map fun (i : ℕ) => some (.v (if i < 6 then p2 (-149) else 0)) := by decide +kernel

/-- Subnormal-aware normalization before RD of `S_acc`: `c = 2^-127 − 2^-140`,
`p₁ + ⋯ = 2^-140 + 2^-150 + 2^(-154-j)` gives `2^-127 + 2^-149` for `j ≤ 3` and `2^-127` for
`j > 3`. -/
example : ((List.range 11).map fun (j : ℕ) =>
    observeP cdna3BF16 [p2 (-140), p2 (-150), p2 (-154 - (j : ℤ))] (p2 (-127) - p2 (-140) : ℚ)) =
    (List.range 11).map fun (j : ℕ) => some (.v (if j ≤ 3 then p2 (-127) + p2 (-149) else p2 (-127))) := by
  decide +kernel

/-! ## XF32 inputs -/

/-- Inputs are truncated to ten fraction bits: `a₁ = 1 + 2^-10 + 2^-11, b₁ = ±1` gives
`±(1 + 2^-10)`. -/
example : observe cdna3XF32 [((1 + p2 (-10) + p2 (-11) : ℚ), 1)] (0 : ℚ) =
    some (.v (1 + p2 (-10))) := by decide +kernel
example : observe cdna3XF32 [((1 + p2 (-10) + p2 (-11) : ℚ), -1)] (0 : ℚ) =
    some (.v (-(1 + p2 (-10)))) := by decide +kernel

/-- `N_FMA = 4` (`k = 8`). -/
example : ((List.range 7).map fun (i : ℕ) =>
    observeP cdna3XF32 ((List.range 8).map fun l =>
      if l = 0 ∨ l = i + 1 then p2 (-24) else 0) (1 : ℚ)) =
    (List.range 7).map fun (i : ℕ) => some (.v (if i + 2 ≤ 4 then 1 + p2 (-23) else 1)) := by
  decide +kernel

/-- `e_{c=0} = −126` as for fp16 and bf16. -/
example : ((List.range 24).map fun (i : ℕ) =>
    observeP cdna3XF32 [p2 (-150), p2 (-152 - (i : ℤ))] (0 : ℚ)) =
    (List.range 24).map fun (i : ℕ) => some (.v (if i < 6 then p2 (-149) else 0)) := by decide +kernel

/-! ## binary8 inputs (Algorithm 2) -/

/-- fp8-E5M2 operands for both `a` and `b`. -/
abbrev fp8 := cdna3FP8 e5m2fnuz e5m2fnuz

/-- Interleaving: `±1, 0, ±(2^-24 + 2^-25)` over `p₁, p₂, p₃` gives `±1` when `p₂ = 0`; otherwise
`1` for positive and `−(1 + 2^-23)` for negative inputs. -/
example : [[1, 0, p2 (-24) + p2 (-25)], [p2 (-24) + p2 (-25), 0, 1]].all (fun ps =>
    observeP fp8 ps (0 : ℚ) == some (.v 1) &&
    observeP fp8 (ps.map (- ·)) (0 : ℚ) == some (.v (-1))) = true := by decide +kernel
example : [[1, p2 (-24) + p2 (-25), 0], [0, 1, p2 (-24) + p2 (-25)],
    [p2 (-24) + p2 (-25), 1, 0], [0, p2 (-24) + p2 (-25), 1]].all (fun ps =>
    observeP fp8 ps (0 : ℚ) == some (.v 1) &&
    observeP fp8 (ps.map (- ·)) (0 : ℚ) == some (.v (-(1 + p2 (-23))))) = true := by decide +kernel

/-- `c` shifted against the products is RD to 24 fractional bits; the product sum shifted against
`c` is RD to 32 fractional bits. -/
example : (List.range 11).all (fun (i : ℕ) =>
    let q := p2 (-24) + p2 (-25 - (i : ℤ))
    observeP fp8 [1] (q : ℚ) == some (.v 1) &&
    observeP fp8 [-1] (-q : ℚ) == some (.v (-(1 + p2 (-23))))) = true := by decide +kernel
example : [1, 2].all (fun (i : ℕ) =>
    let q := p2 (-24) + p2 (-24 - (i : ℤ))
    observeP fp8 [q] (1 : ℚ) == some (.v (1 + p2 (-23))) &&
    observeP fp8 [-q] (-1 : ℚ) == some (.v (-(1 + p2 (-23))))) = true := by decide +kernel

/-- `p₁ = ±1, p₂ = ±2^-24, c = ±2^(-24-i)`: for `i = 1`, `1` and `−(1 + 2^-23)`; for `i > 1`,
`c` lies entirely beyond the 25th fractional bit and is truncated, giving `±1`. -/
example : observeP fp8 [1, p2 (-24)] (p2 (-25) : ℚ) = some (.v 1) := by decide +kernel
example : observeP fp8 [-1, -p2 (-24)] (-p2 (-25) : ℚ) = some (.v (-(1 + p2 (-23)))) := by
  decide +kernel
example : (List.range 20).all (fun (i : ℕ) =>
    observeP fp8 [1, p2 (-24)] (p2 (-26 - (i : ℤ)) : ℚ) == some (.v 1) &&
    observeP fp8 [-1, -p2 (-24)] (-p2 (-26 - (i : ℤ)) : ℚ) == some (.v (-1))) = true := by
  decide +kernel

/-- `p₁ = ±1, c = ±(2^-24 + 2^(-25-i))`: part of `s_c` stays within 25 fractional bits, so the
RD applies: `1` and `−1 − 2^-23`. -/
example : (List.range 20).all (fun (i : ℕ) =>
    let c := p2 (-24) + p2 (-25 - (i : ℤ))
    observeP fp8 [1] (c : ℚ) == some (.v 1) &&
    observeP fp8 [-1] (-c : ℚ) == some (.v (-1 - p2 (-23)))) = true := by decide +kernel

/-- Odd and even sums are combined before `c`: `c = ±(2^-24 + 2^-25)` with `±1, ±2^-25` over
`p₁, p₂` gives `1` and `−(1 + 2^-22)`. -/
example : [[1, p2 (-25)], [p2 (-25), 1]].all (fun ps =>
    observeP fp8 ps (p2 (-24) + p2 (-25) : ℚ) == some (.v 1) &&
    observeP fp8 (ps.map (- ·)) (-(p2 (-24) + p2 (-25)) : ℚ) == some (.v (-(1 + p2 (-22))))) =
    true := by decide +kernel

/-- Cancellation within one parity: `c = 2^-20, a₁ = b₁ = 1, a₂ = −a₄ = 2^5, b₂ = b₄ = 1` gives
`1`: `c` is aligned to the exponent `5` of the cancelled even sum. -/
example : observeP fp8 [1, p2 5, 0, -p2 5] (p2 (-20) : ℚ) = some (.v 1) := by decide +kernel

/-- The cancellation test across parities: `c = 2^4, p₁ = −p₂ = 2^29` gives `0`. -/
example : observeP fp8 [p2 29, -p2 29] (p2 4 : ℚ) = some (.v 0) := by decide +kernel

/-- Mixed formats: fp8-E4M3 `a` with fp8-E5M2 `b`. -/
example : observe (cdna3FP8 e4m3fnuz e5m2fnuz) [((3 / 2 * p2 (-7) : ℚ), (p2 (-17) : ℚ)), (1, 1)]
    (0 : ℚ) = some (.v 1) := by decide +kernel

end MatrixCoreTests.CDNA3
