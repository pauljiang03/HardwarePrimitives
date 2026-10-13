import OzakiMC.Schemes

/-! # Where the conditions bind on AMD matrix cores

Kernel-checked evaluations of the matrix-core model that show the conditions of the exactness
theorems at work. Operand words are fp16 (`0x67FF = 2047`, `0x3C00 = 1`, `0xE7FF = −2047`) or
binary32 (`0x44FFE000 = 2047`, `0x3F800000 = 1`, `0xC4FFE000 = −2047`).

* fp16 holds every integer up to `2048`; bf16 holds `256` but not `2047`, so bf16 variants take
  `8`-bit slices.
* A CDNA 3 block FMA of eight `11`-bit products can exceed `2^24`: seven products `2047²` total
  `29331463`, which the final RNE returns as `29331464` (the Tensor Core model, which truncates,
  returns `29331462`). With `11`-bit slices a CDNA 3 block FMA must carry at most four nonzero
  products.
* The fp16 variants keep a block FMA exact before one rounding, unlike the binary32 SFMA, which
  rounds after every product, as the Z3 models' matrix multiplier does: products
  `5 × 2047², 1, −2 × 2047²` give the exact `12570628` on CDNA 1, 2 and 3 fp16, and `12570626` on
  the SFMA. The exactness bound is a sufficient condition, not a necessary one. -/

open MatrixCore

namespace Ozaki.MC

/-- fp16 holds `2047` and `2048`. -/
theorem binary16_holds_2047 : binary16.encodeExact 2047 = some 0x67FF ∧
    binary16.encodeExact 2048 = some 0x6800 := by decide +kernel

/-- bf16 holds `256` but not `2047`. -/
theorem bfloat16_holds_256 : bfloat16.encodeExact 256 = some 0x4380 ∧
    bfloat16.encodeExact 2047 = none := by decide +kernel

/-- A CDNA 3 block FMA of `11`-bit products exceeds the exactness bound: `7 × 2047² = 29331463` is
returned as `29331464`. -/
theorem cdna3F16_full_blockFMA :
    (blockBits (P := cdna3F16) ⟨List.replicate 7 0x67FF ++ [0], List.replicate 8 0x67FF, 0⟩).map
      value32 = .ok (some 29331464) ∧
    (7 * 2047 * 2047 : ℤ) = 29331463 := by decide +kernel

/-- The operands of the next witness, as fp16 words. -/
def wideA16 : List (BitVec 16) := List.replicate 5 0x67FF ++ [0x3C00] ++ List.replicate 2 0xE7FF
def wideB16 : List (BitVec 16) := List.replicate 5 0x67FF ++ [0x3C00] ++ List.replicate 2 0x67FF

/-- The same operands as binary32 words. -/
def wideA32 : List (BitVec 32) :=
  List.replicate 5 0x44FFE000 ++ [0x3F800000] ++ List.replicate 2 0xC4FFE000
def wideB32 : List (BitVec 32) :=
  List.replicate 5 0x44FFE000 ++ [0x3F800000] ++ List.replicate 2 0x44FFE000

/-- The fp16 variants are exact where the binary32 SFMA is not: `5 × 2047² + 1 − 2 × 2047² =
12570628` on CDNA 1, 2 and 3 fp16, and `12570626` on the SFMA. -/
theorem fp16_exact_where_sfma_is_not :
    (dotBits cdna1F16 wideA16 wideB16 0).map value32 = .ok (some 12570628) ∧
    (dotBits cdna2F16 wideA16 wideB16 0).map value32 = .ok (some 12570628) ∧
    (dotBits cdna3F16 wideA16 wideB16 0).map value32 = .ok (some 12570628) ∧
    (dotBits sfmaF32 wideA32 wideB32 0).map value32 = .ok (some 12570626) ∧
    (3 * 2047 * 2047 + 1 : ℤ) = 12570628 := by decide +kernel

end Ozaki.MC
