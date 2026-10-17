import MMAlgebraMC.ParityLaw

/-! # CDNA 3 binary8: a cross-vendor witness and pinned accumulation

* `xvendor_cdna3`: the CDNA 3 side of an input with four different results on Ada, Hopper,
  Blackwell and CDNA 3 (the NVIDIA side is `MMAlgebra.TC.xvendor_nvidia`).
* Pinned accumulation needs the pins in different parity groups. A pin pair `±2^α` fixes the
  alignment exponent of the group that holds it; with odd/even grouping the other group is aligned
  to its own maximum and its sum is then rounded down to the common grid, so with both pins in one
  group the order of the products still matters (`cdna3FP8_pins_one_group`). With one pin in each
  group both groups sit on the grid `2^(α−24)` and the block returns `c + Σ trunc_{α−24}(p_ℓ)`
  whatever the order (`cdna3FP8_pins_straddle` on an instance; the parity law,
  `blockBits_parityEquiv`, says the order matters only through the parity classes). -/

open MatrixCore

namespace MMAlgebra.MC

/-- Operand pairs of a `k`-long inner product with the given pairs in the given slots (counting from
0) and zero pairs elsewhere. -/
def placeSlots (k : ℕ) (xs : List (ℕ × (BitVec 8 × BitVec 8))) : List (BitVec 8 × BitVec 8) :=
  (List.range k).map fun i => (xs.lookup i).getD (0, 0)

/-! ## One input, four results

The input of `MMAlgebra.TC.xvendor_nvidia` in E4M3 FNUZ words: `k = 32`, `c = 0`, nonzero
products in slots 11, 13 and 21, `(−7/16)·(13/256)`, `(−9/4)·(−36)` and `(−96)·128`, with exact sum
`−12207.0222…`. E4M3 FNUZ words: `0xb6 = −7/16`, `0x1d = 13/256`, `0xc9 = −9/4`, `0xe9 = −36`,
`0xf4 = −96`, `0x78 = 128`. CDNA 3 sums two blocks of 16 with odd/even grouping. -/

/-- **The CDNA 3 side of the cross-vendor witness.** CDNA 3 returns `−12207.0224609375`, the
binary32 value nearest the exact sum, where Ada returns `−12208`, Hopper `−12207` and Blackwell
`−12207.021484375` (`MMAlgebra.TC.xvendor_nvidia`). -/
theorem xvendor_cdna3 :
    dotBits (cdna3FP8 e4m3fnuz e4m3fnuz)
      ((placeSlots 32 [(11, (0xb6, 0x1d)), (13, (0xc9, 0xe9)), (21, (0xf4, 0x78))]).map Prod.fst)
      ((placeSlots 32 [(11, (0xb6, 0x1d)), (13, (0xc9, 0xe9)), (21, (0xf4, 0x78))]).map Prod.snd)
      0 = .ok 0xC63EBC17 := by
  decide +kernel

/-! ## Pinned accumulation: the pins must straddle the parity groups

E4M3 FNUZ words: `0x78 = 128` and `0xF8 = −128` give the pins `128·128 = 2^14` and
`−128·128 = −2^14`; `0x3D·0xC4 = (13/16)·(−3/2) = −39/32` and `0x22·0x97 = (5/64)·(−15/512) =
−75/32768`. Each product truncated toward zero to the grid `2^(14−24) = 2^-10` gives
`−39/32 − 2^-9 = −1.220703125` (`0xBF9C4000`); rounding the small product down instead gives
`−39/32 − 3·2^-10 = −1.2216796875` (`0xBF9C6000`). Slots are counted from 0 here: slots 0 and 2
are in one parity group, slots 1 and 4 in different groups. -/

/-- **Both pins in one parity group: the order matters.** Exchanging the two products between the
group that holds the pins and the other group changes the output. -/
theorem cdna3FP8_pins_one_group :
    pairBlock (cdna3FP8 e4m3fnuz e4m3fnuz)
        (placeSlots 16 [(0, (0x78, 0x78)), (2, (0xF8, 0x78)), (1, (0x3D, 0xC4)), (4, (0x22, 0x97))]) =
      .ok 0xBF9C4000 ∧
    pairBlock (cdna3FP8 e4m3fnuz e4m3fnuz)
        (placeSlots 16 [(0, (0x78, 0x78)), (2, (0xF8, 0x78)), (1, (0x22, 0x97)), (4, (0x3D, 0xC4))]) =
      .ok 0xBF9C6000 := by
  decide +kernel

/-- **One pin in each parity group: the order does not matter.** Exchanging the two products
between the groups returns the pinned value `−39/32 − 2^-9` both times. -/
theorem cdna3FP8_pins_straddle :
    pairBlock (cdna3FP8 e4m3fnuz e4m3fnuz)
        (placeSlots 16 [(0, (0x78, 0x78)), (1, (0xF8, 0x78)), (2, (0x3D, 0xC4)), (3, (0x22, 0x97))]) =
      .ok 0xBF9C4000 ∧
    pairBlock (cdna3FP8 e4m3fnuz e4m3fnuz)
        (placeSlots 16 [(0, (0x78, 0x78)), (1, (0xF8, 0x78)), (2, (0x22, 0x97)), (3, (0x3D, 0xC4))]) =
      .ok 0xBF9C4000 := by
  decide +kernel

end MMAlgebra.MC
