import OzakiMCTests.LongFP64
import OzakiMC.Ozaki2Choice

/-! # Two passes and the chosen configurations on the matrix-core model

* `mcMultiplier2` on CDNA 3 fp16 is exact on `11`-bit vectors whose full block FMAs exceed the
  one-pass exactness bound: nine products `2047 · 2047` (two blocks, the first of eight products
  summing to `8 · 2047² > 2^24`), with mixed signs.
* On the first entry of the binary64 oracle case `narrow64`, correctly rounded FP64 by Ozaki-I on
  the SFMA with two passes and `24`-bit slices, and by Ozaki-II on CDNA 3 fp16 with `12` moduli at
  most `2048`, return the oracle's value. -/

open MatrixCore Ozaki Ozaki.MC OzakiMCTests.LongFP64

namespace OzakiMCTests.TwoPassChoice

example : mcMultiplier2 cdna3F16 (List.replicate 9 2047) (List.replicate 9 2047) =
    some (9 * 2047 * 2047 : ℤ) := by
  decide +kernel

example : mcMultiplier2 cdna3F16 [2047, -2047, 2047, 2047, 2047, 2047, 2047, 2047, 5]
    [2047, 2047, 2047, 2047, 2047, 2047, 2047, 2047, -3] =
    some (dotZ [2047, -2047, 2047, 2047, 2047, 2047, 2047, 2047, 5]
      [2047, 2047, 2047, 2047, 2047, 2047, 2047, 2047, -3]) := by
  decide +kernel

/-- The first row and column of `narrow64`, as values. -/
def x0 : List ℚ := (A_narrow64.headD []).map val64
def y0 : List ℚ := (transpose (B_narrow64.map (·.map val64))).headD []
def c0 : ℚ := val64 ((C_narrow64.headD []).headD 0)

example : ozaki1CRE (mcMultiplier2 sfmaF32) rne64 24 [3] 84 x0 y0 = some c0 := by
  decide +kernel

example : mcOzaki2CRD cdna3F16 [(moduliBasis 10 12, 55)] 10 191 x0 y0 = some c0 := by
  decide +kernel

end OzakiMCTests.TwoPassChoice
