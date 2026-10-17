import MMAlgebraMC.Chain

/-! # One MFMA instruction is not one rounding

A `k = 16` fp16 instruction is four blocks on CDNA 1 and 2 and two on CDNA 3. Exchanging the
products at `k = 0` and `k = 15` would not change a correctly rounded instruction, but it changes
the output on every one of the three models. -/

open MatrixCore

namespace MMAlgebra.MC

/-- CDNA 1: three products at `k = 0, 1, 2` (`−0.5405 × −3.05·10⁻⁴`, `−124.9 × −3.904`,
`−0.05344 × 7.980`). In order the instruction returns `487.12280…` (`0x43f38fb8`); with the product
at `k = 0` moved to `k = 15`, the next binary32 value down (`0x43f38fb7`). -/
theorem cdna1_k16_swap :
    chain cdna1F16 0 [([0xb853, 0xd7ce, 0xaad7, 0], [0x8cfe, 0xc3cf, 0x47fb, 0]), ([0, 0, 0, 0], [0, 0, 0, 0]),
      ([0, 0, 0, 0], [0, 0, 0, 0]), ([0, 0, 0, 0], [0, 0, 0, 0])] = .ok 0x43f38fb8 ∧
    chain cdna1F16 0 [([0, 0xd7ce, 0xaad7, 0], [0, 0xc3cf, 0x47fb, 0]), ([0, 0, 0, 0], [0, 0, 0, 0]),
      ([0, 0, 0, 0], [0, 0, 0, 0]), ([0, 0, 0, 0xb853], [0, 0, 0, 0x8cfe])] = .ok 0x43f38fb7 := by
  decide +kernel

/-- CDNA 2: three products at `k = 0, 1, 2` (`−2.93·10⁻⁴ × 0.9873`, `−118.7 × −1.963`,
`27.97 × 0.2439`). In order `239.79177…` (`0x436fcab2`); with the product at `k = 0` moved to
`k = 15`, the next binary32 value down (`0x436fcab1`). -/
theorem cdna2_k16_swap :
    chain cdna2F16 0 [([0x8cce, 0xd76b, 0x4efe, 0], [0x3be6, 0xbfda, 0x33ce, 0]), ([0, 0, 0, 0], [0, 0, 0, 0]),
      ([0, 0, 0, 0], [0, 0, 0, 0]), ([0, 0, 0, 0], [0, 0, 0, 0])] = .ok 0x436fcab2 ∧
    chain cdna2F16 0 [([0, 0xd76b, 0x4efe, 0], [0, 0xbfda, 0x33ce, 0]), ([0, 0, 0, 0], [0, 0, 0, 0]),
      ([0, 0, 0, 0], [0, 0, 0, 0]), ([0, 0, 0, 0x8cce], [0, 0, 0, 0x3be6])] = .ok 0x436fcab1 := by
  decide +kernel

/-- CDNA 3: two products at `k = 0, 1` (`−2.33·10⁻⁵ × −1.56·10⁻⁴`, `−127.4 × 8.70·10⁻⁶`). In order
`−0.0011084491…` (`0xba914962`); with the product at `k = 0` moved to `k = 15`, the neighbor
toward zero (`0xba914961`). -/
theorem cdna3_k16_swap :
    chain cdna3F16 0 [([0x8187, 0xd7f6, 0, 0, 0, 0, 0, 0], [0x8919, 0x0092, 0, 0, 0, 0, 0, 0]),
      ([0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0])] = .ok 0xba914962 ∧
    chain cdna3F16 0 [([0, 0xd7f6, 0, 0, 0, 0, 0, 0], [0, 0x0092, 0, 0, 0, 0, 0, 0]),
      ([0, 0, 0, 0, 0, 0, 0, 0x8187], [0, 0, 0, 0, 0, 0, 0, 0x8919])] = .ok 0xba914961 := by
  decide +kernel

end MMAlgebra.MC
