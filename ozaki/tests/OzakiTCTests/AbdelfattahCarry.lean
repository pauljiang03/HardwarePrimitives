import Ozaki.AbdelfattahCarry

/-! # The spare-carry recursion of Abdelfattah et al.

Kernel checks of `Ozaki.AbdelfattahCarry`: (4.21) at the paper's example; the shift reading's
counterexample level, whose sum is an odd multiple of its finest grid above `2^53` of them; the
recursion's levels for the paper's INT8 configuration; and, on every level start up to `299`, the
count reading's accepted levels meeting the sum-of-magnitudes condition, for the paper's INT8
configuration and for `11`-bit fp16 slices. -/

local notation "ℕ" => Nat
local notation "ℤ" => Int
local notation "ℚ" => Rat

open Ozaki

namespace OzakiTCTests.AbdelfattahCarry

example : afEta 7 1 255 = 0 ∧ afEta 7 1 256 = -128 := by decide +kernel

example : afShiftLevel.sum =
    (((2 ^ 31 - 1) * (2 * 2 ^ 21 + 3 * 2 ^ 14 + 4 * 2 ^ 7 + 5) : ℕ) : ℚ) * 2 ^ (-28 : ℤ) := by
  decide +kernel

example : 2 ^ 53 < (2 ^ 31 - 1) * (2 * 2 ^ 21 + 3 * 2 ^ 14 + 4 * 2 ^ 7 + 5) ∧
    ((2 ^ 31 - 1) * (2 * 2 ^ 21 + 3 * 2 ^ 14 + 4 * 2 ^ 7 + 5)) % 2 = 1 := by decide

example : afQ 53 31 7 0 = 3 ∧ afQ 53 31 7 3 = 3 ∧ afQ 53 31 7 6 = 3 := by decide +kernel

example : ∀ K ∈ List.range 300, diagFits 53 (2 ^ 31) 7 K (afQ 53 31 7 K) = true := by
  decide +kernel

example : ∀ K ∈ List.range 300, diagFits 53 (2 ^ 32) 12 K (afQ 53 32 12 K) = true := by
  decide +kernel

end OzakiTCTests.AbdelfattahCarry
