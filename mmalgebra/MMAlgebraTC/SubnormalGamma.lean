import OzakiTC

/-! # Remark: the classical `γ_n` bound fails with a subnormal factor

Error analyses of dot products often assume that each operation rounds with unit roundoff `u`, and
bound a block of `n` terms by `γ_n Σ|aᵢbᵢ|`. On the Tensor Core model a product with a subnormal
fp16 factor keeps the exponent sum of its factors, which can far exceed its magnitude, and sets the
block's alignment grid; the other products are then truncated far more coarsely than `u` relative
to their size. `TensorCore.evalBlock_error_bound`, stated with the alignment exponent, remains
valid; a checker that assumed `γ_n` would be unsound on such inputs. -/

open TensorCore

namespace MMAlgebra.TC.SubnormalRemark


/-- A V100 block with one subnormal factor: `0x0001` is `2^-24`, with exponent `−14`. -/
def blk : BlockInput v100F16F32 := ⟨[(0x1, 0x6400), (0x2154, 0x2423), (0x20a1, 0x2489), (0x20a8, 0x2683)], 0⟩

/-- The block's output value. -/
def out : Option ℚ := (evalBlock blk).toOption.map fun t => t.output.value

/-- **A subnormal factor breaks the classical bound.** The block returns `10413·2^-24`, while its
exact sum is `5331613·2^-33`; the error exceeds `50 γ₅ Σ|aᵢbᵢ|` (`γ₅ = 5u/(1 − 5u)`, `u = 2^-24`),
so the classical bound of a block FMA that rounds with unit roundoff `u` fails by more than 50×. The
product `2^-24 · 2^10` has a small value but exponent `−4`, so it sets a coarse alignment grid for
the other products. -/
theorem v100_subnormal_exceeds_gamma :
    out = some (10413 / 16777216) ∧
    ((10413 : ℚ) / 16777216 - 5331613 / 8589934592).abs >
      50 * (5 / (2 ^ 24 - 5)) * (5331613 / 8589934592) := by decide +kernel

end MMAlgebra.TC.SubnormalRemark
