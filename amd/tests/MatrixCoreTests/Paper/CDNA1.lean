import MatrixCoreTests.Support

/-! # CDNA 1 (MI100) test vectors of Section 4.1

Each `example` evaluates a test vector from the paper through the model and checks the output
the paper reports for the hardware. Products `p_ℓ` are written as operand pairs `(a_ℓ, b_ℓ)`. -/

namespace MatrixCoreTests.CDNA1

open MatrixCore

/-! ## fp32 inputs: SFMA `(…((c + p₁) + p₂) + …)` -/

/-- RNE: `p₁ = ±1` with `c = ±(2^-23 + 2^-24)` gives `±(1 + 2^-22)`; with `c = ±2^-24` it gives `±1`. -/
example : observeP sfmaF32 [1] (p2 (-23) + p2 (-24) : ℚ) = some (.v (1 + p2 (-22))) := by decide +kernel
example : observeP sfmaF32 [-1] (-(p2 (-23) + p2 (-24)) : ℚ) = some (.v (-(1 + p2 (-22)))) := by
  decide +kernel
example : observeP sfmaF32 [1] (p2 (-24) : ℚ) = some (.v 1) := by decide +kernel
example : observeP sfmaF32 [-1] (-p2 (-24) : ℚ) = some (.v (-1)) := by decide +kernel

/-- Permuting `1, 2^-23, 2^-24` over `c, p₁, p₂`: `d = 1 + 2^-23` exactly when `p₂ = 2^-23`,
otherwise `1 + 2^-22`; so `c` and `p₁` are added first. -/
example : observeP sfmaF32 [p2 (-24), p2 (-23)] (1 : ℚ) = some (.v (1 + p2 (-23))) := by decide +kernel
example : observeP sfmaF32 [1, p2 (-23)] (p2 (-24) : ℚ) = some (.v (1 + p2 (-23))) := by decide +kernel
example : observeP sfmaF32 [p2 (-23), p2 (-24)] (1 : ℚ) = some (.v (1 + p2 (-22))) := by decide +kernel
example : observeP sfmaF32 [1, p2 (-24)] (p2 (-23) : ℚ) = some (.v (1 + p2 (-22))) := by decide +kernel
example : observeP sfmaF32 [p2 (-24), 1] (p2 (-23) : ℚ) = some (.v (1 + p2 (-22))) := by decide +kernel
example : observeP sfmaF32 [p2 (-23), 1] (p2 (-24) : ℚ) = some (.v (1 + p2 (-22))) := by decide +kernel

/-- Permuting `1, s, s` with `s = 2^-23 + 2^-24` over `p₁, p₂, p₃`: `1 + 2^-21`, except
`p₁ = p₂ = s, p₃ = 1`, which gives `1 + 2^-22 + 2^-23`. -/
example : observeP sfmaF32 [1, p2 (-23) + p2 (-24), p2 (-23) + p2 (-24)] (0 : ℚ) =
    some (.v (1 + p2 (-21))) := by decide +kernel
example : observeP sfmaF32 [p2 (-23) + p2 (-24), 1, p2 (-23) + p2 (-24)] (0 : ℚ) =
    some (.v (1 + p2 (-21))) := by decide +kernel
example : observeP sfmaF32 [p2 (-23) + p2 (-24), p2 (-23) + p2 (-24), 1] (0 : ℚ) =
    some (.v (1 + p2 (-22) + p2 (-23))) := by decide +kernel

/-- Products are exact and rounded once: `p₁ = ±(2^-149 + 2^-150)` from
`a₁ = ±(2^-126 + 2^-127), b₁ = 2^-23` gives `±2^-148`. -/
example : observe sfmaF32 [((p2 (-126) + p2 (-127) : ℚ), (p2 (-23) : ℚ))] (0 : ℚ) =
    some (.v (p2 (-148))) := by decide +kernel
example : observe sfmaF32 [((-(p2 (-126) + p2 (-127)) : ℚ), (p2 (-23) : ℚ))] (0 : ℚ) =
    some (.v (-p2 (-148))) := by decide +kernel

/-- `p₁ = 2^-149, p₂ = 2^-149 + 2^-150` gives `2^-148`; `p₂ = 2^-148 + 2^-150` gives `2^-147`. -/
example : observe sfmaF32 [((p2 (-126) : ℚ), (p2 (-23) : ℚ)),
    ((p2 (-126) + p2 (-127) : ℚ), (p2 (-23) : ℚ))] (0 : ℚ) = some (.v (p2 (-148))) := by
  decide +kernel
example : observe sfmaF32 [((p2 (-126) : ℚ), (p2 (-23) : ℚ)),
    ((p2 (-125) + p2 (-127) : ℚ), (p2 (-23) : ℚ))] (0 : ℚ) = some (.v (p2 (-147))) := by
  decide +kernel

/-- `a₁ = a₂ = ±(2 − 2^-23)·2^127, b₁ = b₂ = 1` overflows to `±∞`. -/
example : observeP sfmaF32 [(2 - p2 (-23)) * p2 127, (2 - p2 (-23)) * p2 127] (0 : ℚ) =
    some (.inf false) := by decide +kernel
example : observeP sfmaF32 [-((2 - p2 (-23)) * p2 127), -((2 - p2 (-23)) * p2 127)] (0 : ℚ) =
    some (.inf true) := by decide +kernel

/-- `a₁ = −a₂ = ∞, b₁ = b₂ = 1` gives NaN. -/
example : observe sfmaF32 [(.inf false, 1), (.inf true, 1)] (0 : ℚ) = some .nan := by decide +kernel

/-- Subnormals in input and output: `a₁ = ±2^-127, b₁ = 1` gives `±2^-127`;
`a₁ = ±b₁ = 2^-65` gives `±2^-130`. -/
example : observeP sfmaF32 [p2 (-127)] (0 : ℚ) = some (.v (p2 (-127))) := by decide +kernel
example : observeP sfmaF32 [-p2 (-127)] (0 : ℚ) = some (.v (-p2 (-127))) := by decide +kernel
example : observe sfmaF32 [((p2 (-65) : ℚ), (p2 (-65) : ℚ))] (0 : ℚ) = some (.v (p2 (-130))) := by
  decide +kernel
example : observe sfmaF32 [((p2 (-65) : ℚ), (-p2 (-65) : ℚ))] (0 : ℚ) = some (.v (-p2 (-130))) := by
  decide +kernel

/-! ## fp16 inputs: `N_FMA = 4`, exact accumulation, final RNE -/

/-- Subnormal inputs: `a₁ = 2^-24, b₁ = ±2^-24` gives `±2^-48`. -/
example : observe cdna1F16 [((p2 (-24) : ℚ), (p2 (-24) : ℚ))] (0 : ℚ) = some (.v (p2 (-48))) := by
  decide +kernel
example : observe cdna1F16 [((p2 (-24) : ℚ), (-p2 (-24) : ℚ))] (0 : ℚ) = some (.v (-p2 (-48))) := by
  decide +kernel

/-- Subnormal outputs: with zero products, `d = c` for `c = ±2^e`, `e ≤ −126`. -/
example : [-126, -127, -140, -149].all (fun (e : ℤ) =>
    observeP cdna1F16 [0] (p2 e : ℚ) == some (.v (p2 e)) &&
    observeP cdna1F16 [0] (-p2 e : ℚ) == some (.v (-p2 e))) = true := by decide +kernel

/-- RNE as for fp32. -/
example : observeP cdna1F16 [1] (p2 (-23) + p2 (-24) : ℚ) = some (.v (1 + p2 (-22))) := by decide +kernel
example : observeP cdna1F16 [1] (p2 (-24) : ℚ) = some (.v 1) := by decide +kernel

/-- The SFMA test gives `1 + 2^-22 + 2^-23` for every permutation: no SFMA structure. -/
example : [[1, p2 (-23) + p2 (-24), p2 (-23) + p2 (-24)],
    [p2 (-23) + p2 (-24), 1, p2 (-23) + p2 (-24)],
    [p2 (-23) + p2 (-24), p2 (-23) + p2 (-24), 1]].all (fun ps =>
      observeP cdna1F16 ps (0 : ℚ) == some (.v (1 + p2 (-22) + p2 (-23)))) = true := by
  decide +kernel

/-- `N_FMA = 4`: with `c, p₁ ∈ {1, s}`, `p_j = s` and other products zero, `d = 1 + 2^-22 + 2^-23`
for `j ≤ 4` and `1 + 2^-21` for `j > 4` (`k = 16`). -/
def nfmaTest (P : Model) (k j : ℕ) (cOne : Bool) : Option Obs :=
  let s : ℚ := p2 (-23) + p2 (-24)
  let ps := (List.range k).map fun i =>
    if i = 0 then (if cOne then s else 1) else if i + 1 = j then s else 0
  observeP P ps (if cOne then (1 : ℚ) else s)

example : ((List.range 15).map fun i => nfmaTest cdna1F16 16 (i + 2) true) =
    (List.range 15).map fun i =>
      some (.v (if i + 2 ≤ 4 then 1 + p2 (-22) + p2 (-23) else 1 + p2 (-21))) := by decide +kernel
example : ((List.range 15).map fun i => nfmaTest cdna1F16 16 (i + 2) false) =
    (List.range 15).map fun i =>
      some (.v (if i + 2 ≤ 4 then 1 + p2 (-22) + p2 (-23) else 1 + p2 (-21))) := by decide +kernel

/-- No finite number of alignment bits: `1, 2^-24, 2^(-25-n)` over `c, p₁, p₂` always give
`1 + 2^-23` (`2^(-25-n)` a product for `n ≤ 23`, or `c`). -/
example : (List.range 24).all (fun n =>
    let t := p2 (-25 - (n : ℤ))
    observe cdna1F16 [((1 : ℚ), (1 : ℚ)), ((p2 (-12) : ℚ), (p2 (-12) : ℚ)),
      ((p2 (-12 - ((n : ℤ) + 1) / 2) : ℚ), (p2 (-13 - (n : ℤ) + ((n : ℤ) + 1) / 2) : ℚ))] (0 : ℚ) ==
      some (.v (1 + p2 (-23))) &&
    observeP cdna1F16 [1, p2 (-24)] (t : ℚ) == some (.v (1 + p2 (-23)))) = true := by
  decide +kernel

/-- `1, 2^-23 + 2^-24, −2^(-25-n)`: `d = 1 + 2^-23`, also for `c = −2^(-25-n)` down to the
subnormal range. -/
example : (List.range 125).all (fun n =>
    observeP cdna1F16 [1, p2 (-23) + p2 (-24)] (-p2 (-25 - (n : ℤ)) : ℚ) ==
      some (.v (1 + p2 (-23)))) = true := by decide +kernel

/-- `±1, ±2^-23, ±Σ_{ℓ=25}^{L} 2^-ℓ, ±2^-L`, all of one sign, give `±(1 + 2^-22)`
(`L = 26 … 48`, the sum carried by `c`). -/
example : (List.range 23).all (fun i =>
    let L := 26 + i
    observe cdna1F16 [((1 : ℚ), (1 : ℚ)), ((p2 (-12) : ℚ), (p2 (-11) : ℚ)),
      ((p2 (-24) : ℚ), (p2 (24 - (L : ℤ)) : ℚ))] (bits 25 L : ℚ) ==
      some (.v (1 + p2 (-22))) &&
    observe cdna1F16 [((-1 : ℚ), (1 : ℚ)), ((-p2 (-12) : ℚ), (p2 (-11) : ℚ)),
      ((-p2 (-24) : ℚ), (p2 (24 - (L : ℤ)) : ℚ))] (-bits 25 L : ℚ) ==
      some (.v (-(1 + p2 (-22))))) = true := by decide +kernel

/-- Infinities: `a₁ = ±∞, b₁ = 1` gives `±∞`; `a₁ = −a₂ = ∞` gives NaN. -/
example : observe cdna1F16 [(.inf false, 1)] (0 : ℚ) = some (.inf false) := by decide +kernel
example : observe cdna1F16 [(.inf true, 1)] (0 : ℚ) = some (.inf true) := by decide +kernel
example : observe cdna1F16 [(.inf false, 1), (.inf true, 1)] (0 : ℚ) = some .nan := by decide +kernel

/-! ## bf16 inputs: `N_FMA = 2` -/

example : ((List.range 7).map fun i => nfmaTest cdna1BF16 8 (i + 2) true) =
    (List.range 7).map fun i =>
      some (.v (if i + 2 ≤ 2 then 1 + p2 (-22) + p2 (-23) else 1 + p2 (-21))) := by decide +kernel

/-- Subnormal output: with zero products `d = c`. -/
example : observeP cdna1BF16 [0] (p2 (-140) : ℚ) = some (.v (p2 (-140))) := by decide +kernel

/-- Full-precision products: `p₁ = ±(2^-149 + 2^-150), p₂ = ±2^-149` give `±2^-148`;
`p₁ = ±(2^-148 + 2^-150), p₂ = ±2^-149` give `±2^-147`. -/
example : observe cdna1BF16 [(((3 : ℚ) / 2 * p2 (-75)), (p2 (-74) : ℚ)),
    ((p2 (-75) : ℚ), (p2 (-74) : ℚ))] (0 : ℚ) = some (.v (p2 (-148))) := by decide +kernel
example : observe cdna1BF16 [((-(3 : ℚ) / 2 * p2 (-75)), (p2 (-74) : ℚ)),
    ((-p2 (-75) : ℚ), (p2 (-74) : ℚ))] (0 : ℚ) = some (.v (-p2 (-148))) := by decide +kernel
example : observe cdna1BF16 [(((5 : ℚ) / 4 * p2 (-74)), (p2 (-74) : ℚ)),
    ((p2 (-75) : ℚ), (p2 (-74) : ℚ))] (0 : ℚ) = some (.v (p2 (-147))) := by decide +kernel
example : observe cdna1BF16 [((-(5 : ℚ) / 4 * p2 (-74)), (p2 (-74) : ℚ)),
    ((-p2 (-75) : ℚ), (p2 (-74) : ℚ))] (0 : ℚ) = some (.v (-p2 (-147))) := by decide +kernel

/-- `c = ±1, p₁ = ±(2^-23 + 2^-24), p₂ = ∓2^(-25-n)` gives `±(1 + 2^-23)` for
`n = 0 … 241`. -/
example : (List.range 242).all (fun n =>
    observe cdna1BF16 [(((3 : ℚ) / 2 * p2 (-12)), (p2 (-11) : ℚ)),
      ((-(p2 (-12 - ((n : ℤ) + 1) / 2)) : ℚ), (p2 (-13 - (n : ℤ) + ((n : ℤ) + 1) / 2) : ℚ))] (1 : ℚ) ==
      some (.v (1 + p2 (-23))) &&
    observe cdna1BF16 [((-(3 : ℚ) / 2 * p2 (-12)), (p2 (-11) : ℚ)),
      ((p2 (-12 - ((n : ℤ) + 1) / 2) : ℚ), (p2 (-13 - (n : ℤ) + ((n : ℤ) + 1) / 2) : ℚ))] (-1 : ℚ) ==
      some (.v (-(1 + p2 (-23))))) = true := by decide +kernel

/-- Infinity is detected at the input even when the product would be finite in binary32:
`a₁ = ±2^128` (infinite in bf16), `b₁ = 2^-20` gives `±∞`. -/
example : observe cdna1BF16 [(.inf false, (p2 (-20) : ℚ))] (0 : ℚ) = some (.inf false) := by
  decide +kernel
example : observe cdna1BF16 [(.inf true, (p2 (-20) : ℚ))] (0 : ℚ) = some (.inf true) := by
  decide +kernel

/-- Products may exceed `2^128` inside a block: `p₁ = 2^129, p₂ = −2^129` gives `0`. -/
example : observe cdna1BF16 [((p2 65 : ℚ), (p2 64 : ℚ)), ((p2 65 : ℚ), (-p2 64 : ℚ))] (0 : ℚ) =
    some (.v 0) := by decide +kernel

/-- Products below `2^-149` are not flushed: `c = ±2^-149, p₁ = ±Σ_{ℓ=151}^{156} 2^-ℓ,
p₂ = ±2^-156` gives `±2^-148`. -/
example : observe cdna1BF16 [((bits 151 156 * p2 76 : ℚ), (p2 (-76) : ℚ)),
    ((p2 (-78) : ℚ), (p2 (-78) : ℚ))] (p2 (-149) : ℚ) = some (.v (p2 (-148))) := by decide +kernel
example : observe cdna1BF16 [((-(bits 151 156 * p2 76) : ℚ), (p2 (-76) : ℚ)),
    ((-p2 (-78) : ℚ), (p2 (-78) : ℚ))] (-p2 (-149) : ℚ) = some (.v (-p2 (-148))) := by
  decide +kernel

/-- `+∞` and `−∞` give NaN. -/
example : observe cdna1BF16 [(.inf false, 1), (.inf true, 1)] (0 : ℚ) = some .nan := by decide +kernel

end MatrixCoreTests.CDNA1
