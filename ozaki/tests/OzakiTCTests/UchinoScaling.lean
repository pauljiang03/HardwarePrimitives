import Ozaki.UchinoScaling
import OzakiTCTests.PublishedAccum

/-! # Uchino, Ozaki and Imamura's scaling, end to end, on numbers

The twelve moduli of `tests/OzakiTCTests/PublishedAccum.lean` (`P ≈ 2^94.8`) and its vectors `x`,
`y` as a `1 × 4` times `4 × 1` product, with the binary32 quantities of Algorithm 2:

* `c0 = single▽(−0.5/(1 − 4u)) = −(1/2 + 3u)` and `P' = single▽(log₂(P − 1)/2 − 0.5) =
  12294999 · 2^-18`, with `2^(2P') ≤ (P − 1)/2`;
* `μ' = 6`, `ν' = 7`, `Ā = [28, 30, 22, 35]`, `B̄ = [29, 31, 41, 6]`, `c̄ = d̄ = 2854`,
  `e = f = RN(log₂ 2854) = 6018181 · 2^-19`, `F = fl▽(fma(c0, e, P')) = 10790453 · 2^-18`, and
  `g = h = ⌊F⌋ = 41`;
* Lemma 1 (`uchino_lemma1_of`) for these shifts, and the slack inequality of their proof;
* every hypothesis of `ozaki2Uchino_scaled_error` with binary64 reconstruction (`G1 = 53`,
  `P1 = fl(P)` on the grid `2^42`, `K = 2^12`, `k = 2^20`, `t = 2^-21`), so that the computed
  value is within `2^-45` of `x · y`;
* why the slack is needed: a product `c = (P − 1)/2 − 5`, inside the range `2|c| ≤ P − 1` that
  Lemma 1 guarantees without it, is reconstructed as `c − P`. -/

local notation "ℕ" => Nat
local notation "ℤ" => Int
local notation "ℚ" => Rat

open Ozaki OzakiTCTests.PublishedAccum

namespace OzakiTCTests.UchinoScaling

def u32 : ℚ := 2 ^ (-24 : ℤ)
def c0 : ℚ := -(1 / 2 + 3 * u32)
def P' : ℚ := 12294999 / 262144
def e : ℚ := 6018181 / 524288
def F : ℚ := 10790453 / 262144

/-- `c0` is `−0.5/(1 − 4u)` rounded down to binary32 (spacing `u` in `[1/2, 1)`). -/
example : c0 ≤ -1 / (2 * (1 - 4 * u32)) ∧ -1 / (2 * (1 - 4 * u32)) - u32 < c0 := by
  decide +kernel

/-- `P'` is `log₂(P − 1)/2 − 0.5` rounded down (spacing `2^-18`): `2^(2P') ≤ (P − 1)/2 ≤
2^(2(P' + 2^-18))`. -/
theorem hP' : Ge2 (((P : ℚ) - 1) / 2) (2 * P') :=
  ge2_mono (y := 49622 / 529) ⟨49622, 529, by decide, by decide +kernel, by decide +kernel⟩ (by decide +kernel)

example : Le2 (((P : ℚ) - 1) / 2) (2 * (P' + 1 / 262144)) :=
  le2_mono (x := 60597 / 646) (by decide +kernel) ⟨60597, 646, by decide, by decide +kernel, by decide +kernel⟩
    (by decide +kernel)

/-- The scaled bounds `Ā`, `B̄` and their product `c̄`. -/
example : barScale 6 x = [28, 30, 22, 35] ∧ barScale 7 y = [29, 31, 41, 6] ∧
    dotZ (barScale 6 x) (barScale 7 y) = 2854 := by decide +kernel

/-- `log₂ 2854 ≤ e/(1 − 4u)`, the half of their (1) that Lemma 1 uses, at `e = RN(log₂ 2854)`. -/
theorem he : Le2 2854 (e / (1 - 4 * u32)) :=
  le2_mono (x := 7840 / 683) (by decide) ⟨7840, 683, by decide, by decide +kernel, by decide +kernel⟩
    (by decide +kernel)

/-- `F` is `c0 e + P'` rounded down, and `⌊F⌋ = 41`. -/
example : F ≤ c0 * e + P' ∧ c0 * e + P' - 1 / 262144 < F ∧ F.floor = 41 := by decide +kernel

/-- **Lemma 1** for the computed shifts `μ = 6 + 41`, `ν = 7 + 41`: `|A'||B'| ≤ (P − 1)/2`. -/
example : (dotAbs (scaleTrunc (6 + 41) x) (scaleTrunc (7 + 41) y) : ℚ) ≤ ((P : ℚ) - 1) / 2 :=
  uchino_lemma1_of (u := u32) (c0 := c0) (Fr := F) (Fc := F) (by decide +kernel) (by decide +kernel)
    (by decide) hP' (by decide +kernel) (by decide) he (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide) he (by decide +kernel) (by decide +kernel)

/-- The slack of their proof holds here: `2^(2·41) · 2854 ≤ 2^(2P' − 2^-20)`. -/
theorem hslack : Le2 (2 ^ (2 * (41 : ℤ)) * 2854) (2 * P' - 1 / ((2 ^ 20 : ℕ) : ℚ)) :=
  le2_mono (x := 187 / 2) (by decide +kernel) ⟨187, 2, by decide, by decide +kernel, by decide +kernel⟩
    (by decide +kernel)

/-! ## End to end -/

theorem hB : B.Valid := by decide +kernel

/-- `P1 = fl(P)` lies on the grid `2^42`. -/
theorem hP1g : GridMultiple 42 P1 := ⟨(P1 * 2 ^ (-42 : ℤ)).floor, by decide +kernel⟩

/-- **Ozaki-II with their scaling and reconstruction, end to end**: every hypothesis of
`ozaki2Uchino_scaled_error` holds, and the computed value is within `2^-45` of `x · y` (the
truncation error dominates). -/
theorem e2e (v : ℚ)
    (hv : ozaki2Uchino exactEngine (roundRNE 53 (-1022) 1023) B G1 P1 P2 Pinv s2 (6 + 41) (7 + 41)
      x y = some v) :
    Rat.abs (v - dot x y) ≤ 2 ^ (-45 : ℤ) := by
  refine Rat.le_trans (ozaki2Uchino_scaled_error (exactEngine_exactOn 7 (4 * (2 ^ 7 * 2 ^ 7)))
    (by decide) (by decide) rfl rfl hB (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (M := (P : ℚ)) (by decide +kernel) (by decide +kernel) (g0 := 42) (by decide +kernel)
    (by decide) (by decide) (K := 2 ^ (12 : ℤ)) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide) hP1g (by decide +kernel) (by decide)
    (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide)
    (by decide) hP' (k := 2 ^ 20) (by decide) (t := 2 ^ (-21 : ℤ)) (by decide +kernel)
    (by decide +kernel) (μ' := 6) (ν' := 7) (g := 41) (h := 41) (mr := 2854) (mc := 2854)
    (by decide +kernel) hslack (by decide +kernel) hslack (by decide +kernel) hv) ?_
  decide +kernel

/-- The algorithm returns a value, and it is that close. -/
example : ∃ v, ozaki2Uchino exactEngine (roundRNE 53 (-1022) 1023) B G1 P1 P2 Pinv s2 (6 + 41)
    (7 + 41) x y = some v ∧ Rat.abs (v - dot x y) ≤ 2 ^ (-45 : ℤ) := by
  decide +kernel

/-! ## Lemma 1 alone does not suffice for the reconstruction -/

def cbad : ℤ := ((P : ℤ) - 1) / 2 - 5

/-- A product with `2|c| ≤ P − 1` (all that Lemma 1 gives without their slack) whose residues the
binary64 reconstruction turns into `c − P` (up to its rounding error): `fl(P_inv C1)` rounds to
the wrong side of `q + 1/2`. Their slack, `2|c| ≤ (P − 1) 2^(−2^-20)`, excludes it. -/
example : 2 * cbad.natAbs ≤ P - 1 ∧
    ∃ v, uchinoRecon (roundRNE 53 (-1022) 1023) P1 P2 Pinv (B.weights.map (weightHi G1)) s2
        (moduli12.map fun m => symMod cbad m) = some v ∧
      (P : ℚ) / 2 < Rat.abs (v - cbad) ∧ Rat.abs (v - (cbad - P)) ≤ 2 ^ (41 : ℤ) := by
  decide +kernel

end OzakiTCTests.UchinoScaling
