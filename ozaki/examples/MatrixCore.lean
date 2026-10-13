import OzakiMC

/-! # The Ozaki schemes on the AMD matrix-core model

Run with `lake env lean examples/MatrixCore.lean` from `ozaki/`. Every `example` is checked by
kernel evaluation of the same definitions the theorems are about. -/

open MatrixCore Ozaki Ozaki.MC

/-! ## 1. One slice product on each architecture

The engine writes each integer as an exact fp16 word, pads to whole blocks of `N_FMA`, and runs
`dotBits` from `c = +0`. CDNA 1 sums exactly and rounds once, CDNA 2 rounds a pairwise tree, and
CDNA 3 aligns the products to `24` fractional bits; on `11`-bit integers with `Σ|aᵢbᵢ| ≤ 2^24`
all three are exact. -/

def xs : List ℤ := [2047, -2048, 5, 7, 1024, -3]
def ys : List ℤ := [2048, 1, 3, -9, -1000, 2047]

example : mcMultiplier cdna1F16 xs ys = some (dotZ xs ys) := by decide +kernel
example : mcMultiplier cdna2F16 xs ys = some (dotZ xs ys) := by decide +kernel
example : mcMultiplier cdna3F16 xs ys = some (dotZ xs ys) := by decide +kernel

#check @mcMultiplier_exactOn
#check @cdna3F16_exactMultiplier

/-! ## 2. Ozaki-I and Ozaki-II on CDNA 3

The same row and column as in `examples/TensorCore.lean`. -/

def x : List ℚ := [1/3, -7/10, 1/1048576, 5]
def y : List ℚ := [3, 1/7, -2, 1/9]

#eval mcOzaki1 cdna3F16 11 4 x y
#eval mcOzaki2 cdna3F16 z3Basis 22 x y
#eval (dot x y : ℚ)

/-- The result is the binary32 sum, smallest first, of the exact scaled slice products. -/
example : mcOzaki1 cdna3F16 11 4 x y = sumWith fp32Add 0 (exactTerms 11 4 x y) :=
  cdna3F16_ozaki1_z3 rfl rfl

/-! ## 3. Where the conditions bind

bf16 holds `256` but not `2047`, so bf16 paths take `8`-bit slices; seven products `2047²` in one
CDNA 3 group exceed `2^24`; and the fp16 paths keep a group exact where the binary32 SFMA, which
rounds after every product, does not. -/

#check @bfloat16_holds_256
#check @cdna3F16_full_group
#check @fp16_exact_where_sfma_is_not

/-! ## 4. Correct rounding

The correctly rounded Ozaki-I on CDNA 3 fp16 returns the binary32 round to nearest of `x · y`, the
same word as on the Tensor Core model. -/

#eval mcOzaki1CR cdna3F16 11 [3, 4] x y

example : mcOzaki1CR cdna3F16 11 [3, 4] x y = round32Value (dot x y) :=
  mcOzaki1CR_eq (cdna3F16_exactMultiplier (by decide)) [3, 4] rfl (by decide)

/-! ## 5. The main theorems -/

#check @evalBlock_int
#check @dotBits_int
#check @mcOzaki1_error
#check @mcOzaki2_error
#check @encodeExact_int
#check @round32Value_within
#check @mcOzaki1CR_eq
#check @mcOzaki1CRE_eq
