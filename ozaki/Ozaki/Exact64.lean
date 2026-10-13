import Ozaki.Binary
import Ozaki.Success
import Ozaki.Width

/-! # Binary64 inputs: the exact fallback and the register

Binary64 values are multiples of `2^-1074` with magnitude below `2^1024`. So:

* `vanish64`: `smax` slices of `b` bits with `smax (b + 1) > 2098` leave nothing over (`175` slices
  of `11` bits, `234` of `8`), and the exact fallback of the correctly rounded schemes ends;
* `vanish32Q`: binary32 values (multiples of `2^-149`, magnitude below `2^128`) need
  `smax (b + 1) > 277`;
* `exactTerms_sum_register32`: for binary32 inputs the exact slice sum is `N · 2^(−298−2b)` with
  `|N| ≤ (s(s+1)/2) · k · 2^(554 + 2b)`, a register of `578 + ⌈log₂ (s(s+1)/2 · k)⌉` bits for
  `b = 11`. -/

local notation "ℕ" => Nat
local notation "ℤ" => Int
local notation "ℚ" => Rat

namespace Ozaki

/-- Inputs on the grid `2^m` with magnitudes at most `2^E` leave nothing over after `smax` slices
when `E − smax (b+1) < m`. -/
theorem vanish_of_grid {b smax : ℕ} {m E : ℤ} (hbE : (b : ℤ) - 1 ≤ E)
    (hsmax : E - m < (smax : ℤ) * ((b : ℤ) + 1)) {x y : List ℚ}
    (hx : ∀ a ∈ x, GridMultiple m a ∧ Rat.abs a ≤ 2 ^ E)
    (hy : ∀ a ∈ y, GridMultiple m a ∧ Rat.abs a ≤ 2 ^ E) (hpos : 0 < smax) :
    ∃ s ∈ List.range' 1 smax, residualsVanish b s x y = true := by
  have hex := splitExp_le b (fun a ha => (hx a ha).2) hbE
  have hey := splitExp_le b (fun a ha => (hy a ha).2) hbE
  exact residualsVanish_of_gridMultiple hpos (fun a ha => (hx a ha).1) (fun a ha => (hy a ha).1)
    (by omega) (by omega)

/-- **Binary64 inputs leave nothing over** after `smax` slices when `smax (b + 1) > 2098`. -/
theorem vanish64 {b smax : ℕ} (hb : b ≤ 1025) (hsmax : 2098 < smax * (b + 1)) {x y : List ℚ}
    (hx : ∀ a ∈ x, Binary64Value a) (hy : ∀ a ∈ y, Binary64Value a) :
    ∃ s ∈ List.range' 1 smax, residualsVanish b s x y = true := by
  have hc : ((smax * (b + 1) : ℕ) : ℤ) = (smax : ℤ) * ((b : ℤ) + 1) := by simp
  have h : (2098 : ℤ) < (smax : ℤ) * ((b : ℤ) + 1) := by rw [← hc]; omega
  have hpos : 0 < smax := by
    rcases Nat.eq_zero_or_pos smax with h0 | h0
    · subst h0; simp at hsmax
    · exact h0
  exact vanish_of_grid (m := -1074) (E := 1024) (by omega) (by omega)
    (fun a ha => ⟨binary64Value_gridMultiple (hx a ha), Rat.le_of_lt (binary64Value_abs_lt (hx a ha))⟩)
    (fun a ha => ⟨binary64Value_gridMultiple (hy a ha), Rat.le_of_lt (binary64Value_abs_lt (hy a ha))⟩)
    hpos

/-- **Binary32 inputs leave nothing over** after `smax` slices when `smax (b + 1) > 277`. -/
theorem vanish32Q {b smax : ℕ} (hb : b ≤ 129) (hsmax : 277 < smax * (b + 1)) {x y : List ℚ}
    (hx : ∀ a ∈ x, Binary32Value a) (hy : ∀ a ∈ y, Binary32Value a) :
    ∃ s ∈ List.range' 1 smax, residualsVanish b s x y = true := by
  have hc : ((smax * (b + 1) : ℕ) : ℤ) = (smax : ℤ) * ((b : ℤ) + 1) := by simp
  have h : (277 : ℤ) < (smax : ℤ) * ((b : ℤ) + 1) := by rw [← hc]; omega
  have hpos : 0 < smax := by
    rcases Nat.eq_zero_or_pos smax with h0 | h0
    · subst h0; simp at hsmax
    · exact h0
  have habs : ∀ v, Binary32Value v → Rat.abs v ≤ 2 ^ (128 : ℤ) := fun v hv => by
    have := formatValue_abs_lt hv
    exact Rat.le_of_lt (by simpa using this)
  exact vanish_of_grid (m := -149) (E := 128) (by omega) (by omega)
    (fun a ha => ⟨binary32Value_gridMultiple (hx a ha), habs a (hx a ha)⟩)
    (fun a ha => ⟨binary32Value_gridMultiple (hy a ha), habs a (hy a ha)⟩) hpos

/-- **The exact slice sum of binary32 inputs fits a register** of `578 + ⌈log₂ (s(s+1)/2 · k)⌉`
bits for `11`-bit slices: `H = N · 2^(−298−2b)` with `|N| ≤ (s(s+1)/2) · k · 2^(554 + 2b)`. -/
theorem exactTerms_sum_register32 {b s : ℕ} (hb : b ≤ 129) {x y : List ℚ}
    (hx : ∀ a ∈ x, GridMultiple (-149) a ∧ Rat.abs a ≤ 2 ^ (128 : ℤ))
    (hy : ∀ a ∈ y, GridMultiple (-149) a ∧ Rat.abs a ≤ 2 ^ (128 : ℤ)) :
    ∃ N : ℤ, (exactTerms b s x y).sum = (N : ℚ) * 2 ^ (2 * ((-149 : ℤ) - b)) ∧
      ((N.natAbs : ℕ) : ℚ) ≤ (trianglePairs s).length * x.length * 2 ^ ((554 : ℤ) + 2 * b) := by
  obtain ⟨N, hN, hb'⟩ := exactTerms_sum_register (b := b) (s := s) (fun a ha => (hx a ha).1)
    (fun a ha => (hy a ha).1)
  refine ⟨N, hN, Rat.le_trans hb' ?_⟩
  have hex := splitExp_le b (fun a ha => (hx a ha).2) (by omega)
  have hey := splitExp_le b (fun a ha => (hy a ha).2) (by omega)
  have hle : (2 : ℚ) ^ (splitExp b x + splitExp b y - 2 * ((-149 : ℤ) - b)) ≤
      2 ^ ((554 : ℤ) + 2 * b) := two_pow_le (by omega)
  have h0 : (0 : ℚ) ≤ (trianglePairs s).length * x.length :=
    Rat.mul_nonneg Rat.natCast_nonneg Rat.natCast_nonneg
  exact Rat.mul_le_mul_of_nonneg_left hle h0

end Ozaki
