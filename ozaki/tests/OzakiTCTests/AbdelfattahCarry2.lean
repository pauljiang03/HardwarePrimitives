import Ozaki.AbdelfattahCarry2

/-! # The spare-carry recursion against `diagFits`: the general theorems on concrete settings

* The first-level statement on INT8 slices (`t = 7`, `T′ = 31`, binary64): the recursion accepts
  three diagonals at `K = 0`, the magnitude condition four.
* The late-level statement on two-bit slices at `K = 15 = 4 · 2^2 − 1`.
* Soundness for one-bit slices, applied, and checked against `diagFits` over a range of levels. -/

open Ozaki

namespace OzakiTCTests.AbdelfattahCarry2

example : diagFits 53 (2 ^ 31) 7 0 (afQ 53 31 7 0 + 1) = true ∧
    afAccept 53 31 7 0 (afQ 53 31 7 0 + 1) = false :=
  af_strict_zero (by decide) (by decide)

example : afQ 53 31 7 0 + 1 = 4 := by decide +kernel

example : diagFits 53 (2 ^ 40) 2 15 (afQ 53 40 2 15 + 1) = true ∧
    afAccept 53 40 2 15 (afQ 53 40 2 15 + 1) = false :=
  af_strict_late (by decide) (by decide) (by decide +kernel)

/-- One-bit slices: the recursion's accepted level at `K = 0` fits, by the general theorem. -/
example : diagFits 11 (2 ^ 6) 1 0 4 = true :=
  afAccept_diagFits_pos (by decide) (by decide) (by decide +kernel)

/-- One-bit slices, every level start below `40` and every count below `10` (`p = 30`, `T′ = 10`):
whatever the recursion accepts, `diagFits` accepts. -/
example : ∀ K ∈ List.range 40, ∀ Q ∈ List.range' 1 10,
    afAccept 30 10 1 K Q = true → diagFits 30 (2 ^ 10) 1 K Q = true := by
  decide +kernel

end OzakiTCTests.AbdelfattahCarry2
