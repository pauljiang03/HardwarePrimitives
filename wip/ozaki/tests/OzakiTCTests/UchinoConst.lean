import Ozaki.UchinoConst
import OzakiTCTests.PublishedAccum

/-! # The closed-form reconstruction bound, on numbers

On the twelve-moduli instance of `tests/OzakiTCTests/PublishedAccum.lean` (`P ≈ 2^95`, high parts
on the grid `2^53`, binary64 `P1`, `P2`, `P_inv`), for the `88`-bit product and for the product
below `2^53`:

* the first fused multiply-add `fma(−Q, P1, C1)` is exact, the hypothesis of `uchino_R64` (their
  configuration makes it so);
* the hypotheses of `uchino_R64` hold with `ρ = Σ ⌊p_ℓ/2⌋ = 1430` and `K = 2^12 = 2^(1+⌈log₂ ρ⌉)`;
* the reconstruction is within their `R64` (plus the underflow term). -/

local notation "ℕ" => Nat
local notation "ℤ" => Int
local notation "ℚ" => Rat

open Ozaki OzakiTCTests.PublishedAccum

namespace OzakiTCTests.UchinoConst

def u : ℚ := 2 ^ (-(53 : ℤ))
def η : ℚ := 2 ^ (-1075 : ℤ)
def ρ : ℚ := ((moduli12.map fun m => m / 2).sum : ℕ)
def K : ℚ := 2 ^ (12 : ℤ)

example : ρ = 1430 ∧ 2 * ρ ≤ K ∧ K < 4 * ρ := by decide +kernel

/-- The setting of `uchino_R64`: weights below `P`, high parts within `K u P`, `|P − P1| ≤ u P`,
`N u ≤ 1/8`, and `Σ|W_ℓ| ≤ ρ` for both residue vectors. -/
example : (∀ a ∈ B.weights, 0 ≤ a ∧ (a : ℚ) ≤ P ∧ (a : ℚ) - weightHi G1 a ≤ K * u * P) ∧
    Rat.abs ((P : ℚ) - P1) ≤ u * P ∧ (B.weights.length : ℚ) * u ≤ 1 / 8 ∧
    absSum (ofInts W) ≤ ρ ∧ absSum (ofInts Ws) ≤ ρ := by
  decide +kernel

/-- The first fused multiply-add is exact for both products. -/
example : roundRNE 53 (-1022) 1023 (-(q : ℚ) * P1 + dot (B.weights.map (weightHi G1)) (ofInts W)) =
      some (-(q : ℚ) * P1 + dot (B.weights.map (weightHi G1)) (ofInts W)) ∧
    roundRNE 53 (-1022) 1023 (-(qs : ℚ) * P1 + dot (B.weights.map (weightHi G1)) (ofInts Ws)) =
      some (-(qs : ℚ) * P1 + dot (B.weights.map (weightHi G1)) (ofInts Ws)) := by
  decide +kernel

/-- The reconstructions are within `R64` plus the underflow term. -/
example : ∃ v, uchinoRecon (roundRNE 53 (-1022) 1023) P1 P2 Pinv (B.weights.map (weightHi G1)) s2 W =
      some v ∧ Rat.abs (v - cprod) ≤ (1 + 3 * u) * (K * (B.weights.length + 2) * (u * u) * ρ * P) +
        3 * u * Rat.abs (cprod : ℚ) + uchinoEta u η B.weights.length ρ := by
  decide +kernel

example : ∃ v, uchinoRecon (roundRNE 53 (-1022) 1023) P1 P2 Pinv (B.weights.map (weightHi G1)) s2 Ws =
      some v ∧ Rat.abs (v - cs) ≤ (1 + 3 * u) * (K * (B.weights.length + 2) * (u * u) * ρ * P) +
        3 * u * Rat.abs (cs : ℚ) + uchinoEta u η B.weights.length ρ := by
  decide +kernel

end OzakiTCTests.UchinoConst
