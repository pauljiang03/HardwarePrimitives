import OzakiTC.Schemes

/-! # Where the conditions bind

Kernel-checked evaluations of the Tensor Core model that show each condition of the exactness
theorems at work, and how the model differs from the Z3 models' matrix multiplier (binary32
additions with round to nearest). Operand words are fp16: `0x6800 = 2048`, `0x67FF = 2047`,
`0x6BFF = 4094`, `0x3C00 = 1`, `0xE7FF = −2047`.

* fp16 holds every integer up to `2048` but not `4095`: slices of more than `11` bits cannot be
  encoded (the Z3 model's mutation check `[S1.11]`).
* The extreme `11`-bit block, four products `2048 · 2048 = 2^22`, totals exactly `2^24` and is
  returned exactly on V100.
* With `12`-bit magnitudes the exactness bound is exceeded: `4094² + 2047² = 20951045` is not a
  binary32 number and V100 returns `20951044` (the Z3 sanity query `[Z.5]`).
* A full A100 block FMA of eight `11`-bit products can exceed `2^24`: seven products `2047²` total
  `29331463`, returned as `29331462`. With `11`-bit slices an A100 or H100 block FMA must carry at
  most four nonzero products, or the slices must be `10`-bit.
* The Tensor Core accumulates a block FMA exactly before one final rounding, unlike binary32
  additions: products `5 × 2047², 1, −2 × 2047²` give the exact `12570628` on A100, and
  `12570626` with binary32 additions in order. The exactness bound is a sufficient condition for the
  hardware, not a necessary one. -/

open TensorCore

namespace Ozaki.TC

/-- fp16 holds `2048 = 2^11`. -/
theorem fp16_holds_2048 : encodeInt fp16 2048 = some 0x6800 := by decide +kernel

/-- fp16 holds `2047`. -/
theorem fp16_holds_2047 : encodeInt fp16 2047 = some 0x67FF := by decide +kernel

/-- fp16 cannot hold `4095`, which needs twelve significant bits. -/
theorem fp16_not_4095 : encodeInt fp16 4095 = none := by decide +kernel

/-- Four products `2048 · 2048` total exactly `2^24`, returned exactly on V100 (`0x4B800000`). -/
theorem v100_extreme_slices :
    (evalBlock (p := v100F16F32) ⟨List.replicate 4 (0x6800, 0x6800), 0⟩).map
      (fun t => t.output.bits) = .ok 0x4B800000 := by decide +kernel

/-- `12`-bit magnitudes exceed the exactness bound: `4094² + 2047² = 20951045` is returned as
`20951044`. -/
theorem v100_twelve_bit_magnitudes :
    (evalBlock (p := v100F16F32) ⟨[(0x6BFF, 0x6BFF), (0x67FF, 0x67FF), (0, 0), (0, 0)], 0⟩).map
      (fun t => t.output.value) = .ok 20951044 ∧
    (4094 * 4094 + 2047 * 2047 : ℤ) = 20951045 := by decide +kernel

/-- A full A100 block FMA of `11`-bit products exceeds the exactness bound: `7 × 2047² = 29331463`
is returned as `29331462`. -/
theorem a100_full_blockFMA :
    (evalBlock (p := ampereF16F32) ⟨List.replicate 7 (0x67FF, 0x67FF) ++ [(0, 0)], 0⟩).map
      (fun t => t.output.value) = .ok 29331462 ∧
    (7 * 2047 * 2047 : ℤ) = 29331463 := by decide +kernel

/-- The products of the next witness. -/
def wideProducts : List (F16 × F16) :=
  List.replicate 5 (0x67FF, 0x67FF) ++ [(0x3C00, 0x3C00)] ++ List.replicate 2 (0xE7FF, 0x67FF)

/-- The A100 block is exact where binary32 additions are not: `5 × 2047² + 1 − 2 × 2047² =
12570628`, while adding the products in binary32 gives `12570626`. -/
theorem a100_exact_where_binary32_is_not :
    (evalBlock (p := ampereF16F32) ⟨wideProducts, 0⟩).map (fun t => t.output.value) =
      .ok 12570628 ∧
    naiveSum32 (wideProducts.map fun q => ((decode16 q.1).map Decoded.value).getD 0 *
      ((decode16 q.2).map Decoded.value).getD 0) = some 12570626 ∧
    (3 * 2047 * 2047 + 1 : ℤ) = 12570628 := by decide +kernel

end Ozaki.TC
