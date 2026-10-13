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

/-- The products of the exact-region example: `2047 · 2047`, `2047 · 1000`, `−1000 · 3` and `3 · 3`. -/
def exactPairs (i : ℕ) : F16 × F16 :=
  [(0x67FF, 0x67FF), (0x67FF, 0x63D0), (0xE3D0, 0x4200), (0x4200, 0x4200)].getD i (0, 0)

/-- **Inside the exact region every schedule agrees (V100).** Integer products and `c = 12345`,
total magnitude `6,252,563 < 2^24`: one block from `c`, a split-K whose partials are added before
`c`, and a reversed chain with `c` in the epilogue all return `6,246,563` (`0x4abea146`), the exact
sum, as `MMAlgebra.TC.eval_agree` says of every schedule. -/
theorem v100_exact_region :
    MMAlgebra.eval (tcMachine v100F16F32) exactPairs 0x4640E400 0x4640E400
        (.blk .init [some 0, some 1, some 2, some 3]) = some 0x4abea146 ∧
    MMAlgebra.eval (tcMachine v100F16F32) exactPairs 0x4640E400 0x4640E400
        (.add (.add (.blk .zero [some 0, some 1, none, none]) (.blk .zero [some 2, some 3, none, none]))
          .init) = some 0x4abea146 ∧
    MMAlgebra.eval (tcMachine v100F16F32) exactPairs 0x4640E400 0x4640E400
        (.add (.blk (.blk (.blk (.blk .zero [some 3, none, none, none]) [some 2, none, none, none])
          [some 1, none, none, none]) [some 0, none, none, none]) .init) = some 0x4abea146 := by
  decide +kernel

end MMAlgebraTCTests
