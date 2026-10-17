import MMAlgebraTC.Block

/-! # One MMA instruction is not one rounding

The library's WMMA `m16n16k16` variants are four block FMAs of size four on V100, two of size eight
on A100, and one of size sixteen on H100. If an instruction were one correctly rounded operation,
exchanging the products at `k = 0` and `k = 15` could not change its output. It changes the V100 and
A100 results; on H100 it never does (`evalBlock_bits_perm`). -/

open TensorCore

namespace MMAlgebra.TC

/-- V100: products `0.0444 × 0.2494` at `k = 0` and `−3.660 × 3.947` at `k = 1`, every other product
zero. In order, the instruction returns `−14.43653488…` (`0xc166fc0c`); with the product at `k = 0`
moved to `k = 15`, the next binary32 value down, `−14.43653583…` (`0xc166fc0d`). -/
theorem v100_wmma_swap :
    v100Wmma16.output 0 ([(0x29af, 0x33fb), (0xc352, 0x43e5)] ++ List.replicate 14 (0, 0)) =
      some 0xc166fc0c ∧
    v100Wmma16.output 0 ([(0, 0), (0xc352, 0x43e5)] ++ List.replicate 13 (0, 0) ++
      [(0x29af, 0x33fb)]) = some 0xc166fc0d := by
  decide +kernel

/-- A100: products `6.72·10⁻⁵ × −0.4978` at `k = 0` and `4.586 × 1.07·10⁻⁴` at `k = 1`. In order,
`0x39efb5df`; with the product at `k = 0` moved to `k = 15`, the next binary32 value up,
`0x39efb5e0`. -/
theorem a100_wmma_swap :
    ampereWmma16.output 0 ([(0x0467, 0xb7f7), (0x4496, 0x0703)] ++ List.replicate 14 (0, 0)) =
      some 0x39efb5df ∧
    ampereWmma16.output 0 ([(0, 0), (0x4496, 0x0703)] ++ List.replicate 13 (0, 0) ++
      [(0x0467, 0xb7f7)]) = some 0x39efb5e0 := by
  decide +kernel

end MMAlgebra.TC
