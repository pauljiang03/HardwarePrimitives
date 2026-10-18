import MMAlgebraMC

/-! # Worked examples on the Matrix Core model -/

open MatrixCore MMAlgebra.MC

namespace MMAlgebraMCTests

/-- CDNA 2, products `x = 1.5 × 1.5` and `y = z = 2^-23` as in the Tensor Core example: one block
`[x y z]` sums `fl{fl{x + y} + z}`, and each addition of `2^-23` to `2.25` is a tie that rounds to
`2.25` (`0x40100000`); the chain `[x] [y z]` adds `fl{y + z} = 2^-22` to `2.25` exactly
(`0x40100001`). V100 gives the opposite pair of results. -/
theorem cdna2_block_boundary :
    chain cdna2F16 0 [([0x3e00, 0x0c00, 0x0c00, 0], [0x3e00, 0x1000, 0x1000, 0])] = .ok 0x40100000 ∧
    chain cdna2F16 0 [([0x3e00, 0, 0, 0], [0x3e00, 0, 0, 0]),
      ([0x0c00, 0x0c00, 0, 0], [0x1000, 0x1000, 0, 0])] = .ok 0x40100001 := by
  decide +kernel

/-- CDNA 1 bf16 below binary32's range: `p₀ = 2^-75 × 2^-74 = 2^-149` and `p₁ = 2^-75 × 2^-75 =
2^-150`. The block holding `p₁` alone rounds the tie `2^-150` to `+0`, so `[p₁] [p₀]` returns
`2^-149` (`0x1`), while `[p₀] [p₁]` rounds the tie `1.5 · 2^-149` to even, `2^-148` (`0x2`), as the
joint block does. The merge law of CDNA 1 fp16 needs products representable in binary32. -/
theorem cdna1BF16_tie :
    chain cdna1BF16 0 [([0x1A00, 0], [0x1A80, 0]), ([0x1A00, 0], [0x1A00, 0])] = .ok 0x2 ∧
    chain cdna1BF16 0 [([0x1A00, 0], [0x1A00, 0]), ([0x1A00, 0], [0x1A80, 0])] = .ok 0x1 ∧
    chain cdna1BF16 0 [([0x1A00, 0x1A00], [0x1A80, 0x1A00])] = .ok 0x2 := by
  decide +kernel

end MMAlgebraMCTests
