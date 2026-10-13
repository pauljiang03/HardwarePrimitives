import OzakiTC

/-! # The Ozaki schemes on the Tensor Core model, step by step

Run with `lake env lean examples/TensorCore.lean` from `ozaki/`. Every `example` is checked by
kernel evaluation of the same definitions the theorems are about. -/

open TensorCore Ozaki Ozaki.TC

/-! ## 1. Slicing a row (Ozaki-I, step 1)

`x = (1/3, −0.7, 2^-20, 5)` split into four slices of `11` bits. `E = 3` because `5 ≤ 2^3`, so the
first slice lies on the grid `2^(3−11) = 2^-8`; every later grid is at least `12` bits lower. -/

def x : List ℚ := [1/3, -7/10, 1/1048576, 5]

#eval (split 11 4 x).1
#eval splitExp 11 x

/-- The split is exact: the slices and the residual add up to `x`, tested against `y = (1,1,1,1)`. -/
example : dot x [1, 1, 1, 1] =
    ((split 11 4 x).1.map fun sl => 2 ^ sl.grid * dot (ofInts sl.coeffs) [1, 1, 1, 1]).sum +
      dot (split 11 4 x).2 [1, 1, 1, 1] := split_dot 11 4 x [1, 1, 1, 1]

/-! ## 2. The σ-trick in binary32

For `a = 1/3` rounded to binary32 (`0x3EAAAAAB`) and the grid `2^-11`, `σ = 3 · 2^11`:
`fl(fl(a + σ) − σ)` is `a` rounded to a multiple of `2^-11`, and `fl(a − hi)` is exact. -/

def a32 : ℚ := ((value32 0x3EAAAAAB).getD 0)

example : (do
    let s1 ← add32 a32 (sigma (-11))
    let hi ← add32 s1 (-sigma (-11))
    let lo ← add32 a32 (-hi)
    return (hi, lo)) =
  some (roundNearestEven (a32 / pow2 (-11)) * pow2 (-11),
    a32 - roundNearestEven (a32 / pow2 (-11)) * pow2 (-11)) := by decide +kernel

/-! ## 3. One slice product on a V100 block

The engine encodes integers as fp16 words, pads to groups of four, and runs `runBlocks` from
`c = +0`. On `11`-bit integers with `Σ|aᵢbᵢ| ≤ 2^24` it is exact (`v100_exactOn`). -/

example : tcMultiplier v100F16F32 [2047, -2048, 5, 7] [2048, 1, 3, -9] =
    some (dotZ [2047, -2048, 5, 7] [2048, 1, 3, -9]) := by decide +kernel

#check @v100_exactOn

/-! ## 4. Ozaki-I and Ozaki-II on V100

With four slices, the ten slice products are exact and only the binary32 additions round. -/

def y : List ℚ := [3, 1/7, -2, 1/9]

#eval tcOzaki1 v100F16F32 11 4 x y
#eval tcOzaki2 v100F16F32 z3Basis 22 x y
#eval (dot x y : ℚ)

/-- The result is the IEEE binary32 sum, smallest first, of the exact scaled slice products. -/
example : tcOzaki1 v100F16F32 11 4 x y = sumWith add32 0 (exactTerms 11 4 x y) :=
  v100_ozaki1_z3 rfl rfl

/-! ## 5. CRT reconstruction

The Z3 model's moduli are pairwise coprime with `M ≈ 2^48`, and `P = 22` is the largest
precision whose products stay within `(−M/2, M/2]`. -/

#eval z3Basis
example : crt z3Basis (z3Moduli.map fun m : ℕ => (123456789012 : ℤ) % (m : ℤ)) = 123456789012 := by
  decide +kernel

#check @crt_eq
#check @z3_bits
#check @crt_fails_at_23

/-! ## 6. ADP: Ozaki-I on an INT8 engine

A `53`-bit integer in seven remapped signed bytes, an INT32 dot product of bytes in TC-EFT's
fixed-width register, and binary64 emulation of `x · y` with `55`-bit fixed point. -/

#eval ADP.remap 7 (2 ^ 53 - 1)
example : ADP.digitValue (ADP.remap 7 (2 ^ 53 - 1)) = 2 ^ 53 - 1 := ADP.remap_value (by decide) _
example : int8Dot 32 [127, -128, 5, 0] [255, 3, -7, 1] = 127 * 255 - 128 * 3 - 35 := by decide

def u : List ℚ := [1/3, 2/7]
def v : List ℚ := [3/5, -1/11]

-- Shifts `W − 1 − exp(max)` with `W = 55`: `max|u| = 1/3` has exponent `−2`, `max|v| = 3/5`
-- exponent `−1`. The emulated and the correctly rounded binary64 results:
#eval int8Ozaki 7 56 55 u v
#eval rne64 (dot u v)

/-! ## 7. Correct rounding

`tcOzaki1CR` keeps the slice products exact and checks whether both ends of `H ± B` round to the same
binary32 word; it tries three, then four slices, and otherwise rounds the exact product. Whichever
path settles it, the result is the binary32 round to nearest of `x · y`. -/

#eval tcOzaki1CR v100F16F32 11 [3, 4] x y
#eval round32Value (dot x y)

example : tcOzaki1CR v100F16F32 11 [3, 4] x y = round32Value (dot x y) :=
  tcOzaki1CR_eq v100_intExact v100_holdsInts (by decide) [3, 4] rfl (by decide)

/-- `1 + 2^-24` lies exactly halfway between `1` and `1 + 2^-23`: no bound settles it, the exact
path on V100 blocks does, and the tie goes to the even word `1`. -/
example : tcOzaki1CRE v100F16F32 11 [3, 4] 24 [1, 1 / 16777216] [1, 1] = some 1 := by
  decide +kernel

/-! ## 8. The main theorems -/

#check @tcMultiplier_exactOn
#check @tcOzaki1_error
#check @tcOzaki2_error
#check @sigma_split
#check @exactTerms_error_normwise
#check @truncProduct_error_normwise
#check @int8Ozaki_eq
#check @tcOzaki1CR_eq
#check @tcOzaki1CRE_eq
#check @adpCR_eq
