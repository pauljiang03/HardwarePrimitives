import OzakiMC.Rounding
import Ozaki.Native

/-! # Native binary32 dot products (Z3 `[M.1]`)

The Z3 Ozaki-I model compares Ozaki-I with native binary32 GEMM: each product rounded to binary32,
then added left to right with binary32 round to nearest. `native32` is that computation, and
`native32_error` is the classical bound it meets, `γₖ Σ|xᵢyᵢ|` with `γₖ = k u / (1 − k u)` and
`u = 2^-24`, plus a term for the subnormal range. The Z3 model checks `k u (|A||B|)` on its test
matrices; the theorem holds for every input. -/

open MatrixCore

namespace Ozaki.MC

/-- Native binary32 dot product: each product rounded, then added left to right. -/
def native32 (x y : List ℚ) : Option ℚ := nativeDot round32Value x y

/-- **Native binary32 GEMM meets the classical bound** (`[M.1]`). -/
theorem native32_error {x y : List ℚ} (hlen : x.length = y.length)
    (hk : (x.length : ℚ) * 2 ^ (-24 : ℤ) < 1) {v : ℚ} (h : native32 x y = some v) :
    Rat.abs (v - dot x y) ≤
      (x.length : ℚ) * 2 ^ (-24 : ℤ) / (1 - (x.length : ℚ) * 2 ^ (-24 : ℤ)) *
          ((List.zipWith (· * ·) x y).map Rat.abs).sum +
        2 * (x.length : ℚ) * (1 + 2 ^ (-24 : ℤ)) ^ x.length * 2 ^ (-150 : ℤ) :=
  nativeDot_error_gamma (Rat.le_of_lt (two_pow_pos _)) (Rat.le_of_lt (two_pow_pos _))
    round32Value_within hlen hk h

end Ozaki.MC
