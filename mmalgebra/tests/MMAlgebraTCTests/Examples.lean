import MMAlgebraTC

/-! # Worked examples on the Tensor Core model

The hand-sized example of the documentation: products `x = 1.5 × 1.5 = 2.25` (fp16 `0x3e00`) and
`y = z = 2^-12 × 2^-11 = 2^-23` (`0x0c00 × 0x1000`). -/

open TensorCore MMAlgebra.TC

namespace MMAlgebraTCTests

/-- V100: one block `[x y z]` returns `2.25 + 2^-22` (`0x40100001`). After a block holding `x`
alone, whose output `2.25` has binary32 exponent `1`, the block `[y z]` aligns to `2^(1 − 23)` and
truncates both small products: `2.25` (`0x40100000`). The same block from `+0` returns `2^-22`, so
adding `C = 2.25` late, in an FP32 addition, gives `2.25 + 2^-22`, while adding it early, in the
block, gives `2.25`. -/
theorem v100_block_boundary :
    blockOut (p := v100F16F32) ⟨[(0x3e00, 0x3e00), (0x0c00, 0x1000), (0x0c00, 0x1000), (0, 0)], 0⟩ =
      .ok 0x40100001 ∧
    blockOut (p := v100F16F32) ⟨[(0x3e00, 0x3e00), (0, 0), (0, 0), (0, 0)], 0⟩ = .ok 0x40100000 ∧
    blockOut (p := v100F16F32) ⟨[(0x0c00, 0x1000), (0x0c00, 0x1000), (0, 0), (0, 0)], 0x40100000⟩ =
      .ok 0x40100000 ∧
    blockOut (p := v100F16F32) ⟨[(0x0c00, 0x1000), (0x0c00, 0x1000), (0, 0), (0, 0)], 0⟩ =
      .ok 0x34800000 := by
  decide +kernel

/-- A100: with one extra alignment bit, the second block aligns to `2^(1 − 24)` and keeps both
small products, so the two-block chain also returns `2.25 + 2^-22`. -/
theorem a100_block_boundary :
    blockOut (p := ampereF16F32) ⟨(0x3e00, 0x3e00) :: (0x0c00, 0x1000) :: (0x0c00, 0x1000) ::
      List.replicate 5 (0, 0), 0⟩ = .ok 0x40100001 ∧
    blockOut (p := ampereF16F32) ⟨(0x0c00, 0x1000) :: (0x0c00, 0x1000) :: List.replicate 6 (0, 0),
      0x40100000⟩ = .ok 0x40100001 := by
  decide +kernel

end MMAlgebraTCTests
