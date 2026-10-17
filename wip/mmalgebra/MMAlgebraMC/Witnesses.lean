import MMAlgebraMC.Chain

/-! # Base witnesses on the CDNA 1, 2 and 3 models

Kernel-checked inputs that separate the normal forms of the reduction algebra over two or three
products. On CDNA 1 fp16 every block is the binary32 value nearest to the exact sum of its inputs,
so a chain is a tree of correctly rounded nodes; on CDNA 2 a chain is a binary summation tree of
binary32 additions; CDNA 3 is rigid, like the Tensor Cores. -/

open MatrixCore

namespace MMAlgebra.MC

/-! ## CDNA 1 fp16: every node is RNE of an exact sum; three products separate the trees -/

/-- Products `p₀ = 1.258·10⁻⁴ × 19.55`, `p₁ = 3.996 × 3.105` and `p₂ = 1.202·10⁻⁴ × 7.887`. The chain
`[p₀] [p₁] [p₂]` is the tree `((p₀ + p₁) + p₂)`, because a one-product first block merges into the
next, and returns `12.4131507…` (`0x41469c44`). The tree `((p₀ + p₂) + p₁)`, the chain
`[p₀] [p₁ p₂]` (the fan `p₀ + p₁ + p₂`, by the same merge) and the single block all return the
next binary32 value down, `12.4131498…` (`0x41469c43`). -/
theorem cdna1_trees :
    chain cdna1F16 0 [([0x081f, 0, 0, 0], [0x4ce3, 0, 0, 0]), ([0x43fe, 0, 0, 0], [0x4236, 0, 0, 0]),
      ([0x07e0, 0, 0, 0], [0x47e3, 0, 0, 0])] = .ok 0x41469c44 ∧
    chain cdna1F16 0 [([0x081f, 0, 0, 0], [0x4ce3, 0, 0, 0]), ([0x07e0, 0, 0, 0], [0x47e3, 0, 0, 0]),
      ([0x43fe, 0, 0, 0], [0x4236, 0, 0, 0])] = .ok 0x41469c43 ∧
    chain cdna1F16 0 [([0x081f, 0, 0, 0], [0x4ce3, 0, 0, 0]),
      ([0x43fe, 0x07e0, 0, 0], [0x4236, 0x47e3, 0, 0])] = .ok 0x41469c43 ∧
    chain cdna1F16 0 [([0x081f, 0x43fe, 0x07e0, 0], [0x4ce3, 0x4236, 0x47e3, 0])] = .ok 0x41469c43 := by
  decide +kernel

/-! ## CDNA 2 fp16: chains are binary summation trees -/

/-- The same products on CDNA 2: the trees `((p₀ + p₁) + p₂)` and `((p₀ + p₂) + p₁)` return
`0x41469c44` and `0x41469c43`. -/
theorem cdna2_trees :
    chain cdna2F16 0 [([0x081f, 0, 0, 0], [0x4ce3, 0, 0, 0]), ([0x43fe, 0, 0, 0], [0x4236, 0, 0, 0]),
      ([0x07e0, 0, 0, 0], [0x47e3, 0, 0, 0])] = .ok 0x41469c44 ∧
    chain cdna2F16 0 [([0x081f, 0, 0, 0], [0x4ce3, 0, 0, 0]), ([0x07e0, 0, 0, 0], [0x47e3, 0, 0, 0]),
      ([0x43fe, 0, 0, 0], [0x4236, 0, 0, 0])] = .ok 0x41469c43 := by
  decide +kernel

/-! ## CDNA 3 fp16: rigid, like Tensor Cores -/

/-- Two products `p₀ = 4.42·10⁻⁵ × 2.15·10⁻⁴` and `p₁ = 0.4946 × 0.08545`: `p₀` first and the joint
block give `0.042265661…` (`0x3d2d1ec2`), `p₁` first gives the next binary32 value up
(`0x3d2d1ec3`). -/
theorem cdna3_pair :
    chain cdna3F16 0 [([0x02e6, 0, 0, 0, 0, 0, 0, 0], [0x0b09, 0, 0, 0, 0, 0, 0, 0]),
      ([0x37ea, 0, 0, 0, 0, 0, 0, 0], [0x2d78, 0, 0, 0, 0, 0, 0, 0])] = .ok 0x3d2d1ec2 ∧
    chain cdna3F16 0 [([0x37ea, 0, 0, 0, 0, 0, 0, 0], [0x2d78, 0, 0, 0, 0, 0, 0, 0]),
      ([0x02e6, 0, 0, 0, 0, 0, 0, 0], [0x0b09, 0, 0, 0, 0, 0, 0, 0])] = .ok 0x3d2d1ec3 ∧
    chain cdna3F16 0 [([0x02e6, 0x37ea, 0, 0, 0, 0, 0, 0], [0x0b09, 0x2d78, 0, 0, 0, 0, 0, 0])] =
      .ok 0x3d2d1ec2 := by
  decide +kernel

end MMAlgebra.MC
