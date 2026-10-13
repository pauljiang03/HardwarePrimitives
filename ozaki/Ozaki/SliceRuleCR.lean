import Ozaki.SliceRule
import Ozaki.ModuliRule
import Ozaki.CRTValid
import Ozaki.SharpBounds

/-! # Slice and moduli rules for correct rounding

The rules of `Ozaki.SliceRule` and `Ozaki.ModuliRule` target an error of
`2^-t · k · max|x| · max|y|`: the factor `k` makes the bound grow with the inner dimension. That is
enough for an error bound, but the rounding test of correct rounding decides an entry only when its
bound is small against the spacing of the result, and a simulation at realistic sizes
(`scripts/fallback_sim.py`) found that the first test almost never succeeds once `k ≥ 256` under the
plain rule. The rules here add `⌈log₂ k⌉` bits:

* `clog2 k`, the least `c` with `k ≤ 2^c` (`le_two_pow_clog2`);
* `slicesForCR b t k = slicesFor b (t + clog2 k)`: then the slicing bound of the first test is at
  most `2^-t · max|x| · max|y|`, with no factor `k` (`ozaki1Bound_le_cr`), and at most
  `2^(c−t) |x · y|` whenever cancellation loses at most `c` bits, `max|x| max|y| ≤ 2^c |x · y|`
  (`ozaki1Bound_le_cr_rel`). With `t` the output precision `p` plus a few bits the bound is a small
  fraction of the output's unit in the last place, `ulp(v) > 2^-p |v|`, for every product whose
  cancellation stays below those bits;
* `moduliForCR b t k = moduliFor b (t + clog2 k) k`: Ozaki-II with `P = t + clog2 k + 2` has the
  same guarantee for its truncation (`truncation_le_cr`), and meets the reconstruction condition
  (`moduliForCR_spec`).

Every basis the moduli rule produces is valid, by `crtBasis_valid` (`moduliBasis_valid_all`), so the
kernel checks of particular bases are no longer needed. -/

local notation "ℕ" => Nat
local notation "ℤ" => Int
local notation "ℚ" => Rat

namespace Ozaki

/-! ## `⌈log₂ k⌉` -/

/-- The least `c` with `k ≤ 2^c`. -/
def clog2 (k : ℕ) : ℕ := if k ≤ 1 then 0 else Nat.log2 (k - 1) + 1

theorem le_two_pow_clog2 (k : ℕ) : k ≤ 2 ^ clog2 k := by
  unfold clog2
  split
  · simp only [Nat.pow_zero]; omega
  · have := Nat.lt_log2_self (n := k - 1); omega

/-! ## The slice rule for correct rounding -/

/-- The slice rule's defining inequality holds at the slice count it picks. -/
theorem slicesFor_spec {b t : ℕ} (hs : 0 < slicesFor b t) :
    (slicesFor b t + 1) * 2 ^ (t + 2) ≤ 2 ^ (slicesFor b t * (b + 1)) := by
  unfold slicesFor at hs ⊢
  cases h : (List.range' 1 199).find? fun s => decide ((s + 1) * 2 ^ (t + 2) ≤ 2 ^ (s * (b + 1))) with
  | none => rw [h] at hs; simp at hs
  | some s =>
    simp only [Option.getD_some]
    exact of_decide_eq_true (List.find?_some (p := fun s =>
      decide ((s + 1) * 2 ^ (t + 2) ≤ 2 ^ (s * (b + 1)))) h)

/-- **The slice count for correct rounding**: `⌈log₂ k⌉` more bits than the plain rule. -/
def slicesForCR (b t k : ℕ) : ℕ := slicesFor b (t + clog2 k)

/-- **The bound of the first test, without the factor `k`.** With `s = slicesForCR b t k` slices and
at most `k` entries, Ozaki-I's slicing bound is at most `2^-t · max|x| · max|y|`. -/
theorem ozaki1Bound_le_cr {b t k : ℕ} (hs : 0 < slicesForCR b t k) {x y : List ℚ}
    (hk : x.length ≤ k) (hx : maxAbs x ≠ 0) (hy : maxAbs y ≠ 0) :
    ozaki1Bound b (slicesForCR b t k) x y ≤ maxAbs x * maxAbs y * 2 ^ (-(t : ℤ)) := by
  have h := slicing_term_le_maxAbs (slicesFor_spec hs) hx hy
  unfold ozaki1Bound
  unfold slicesForCR at h ⊢
  refine Rat.le_trans h ?_
  have hc := le_two_pow_clog2 k
  have hlen : (x.length : ℚ) ≤ 2 ^ ((clog2 k : ℕ) : ℤ) := by
    rw [two_pow_natCast]; exact Rat.natCast_le_natCast.mpr (Nat.le_trans hk hc)
  have hmx := maxAbs_nonneg x
  have hmy := maxAbs_nonneg y
  have hm : 0 ≤ maxAbs x * maxAbs y * 2 ^ (-(((t + clog2 k : ℕ)) : ℤ)) :=
    Rat.mul_nonneg (Rat.mul_nonneg hmx hmy) (Rat.le_of_lt (two_pow_pos _))
  have e : (x.length : ℚ) * maxAbs x * maxAbs y * 2 ^ (-(((t + clog2 k : ℕ)) : ℤ)) =
      x.length * (maxAbs x * maxAbs y * 2 ^ (-(((t + clog2 k : ℕ)) : ℤ))) := by grind
  rw [e]
  have e2 : (2 : ℚ) ^ (-(t : ℤ)) =
      2 ^ ((clog2 k : ℕ) : ℤ) * 2 ^ (-(((t + clog2 k : ℕ)) : ℤ)) := by
    rw [← two_pow_add]; congr 1; push_cast; omega
  calc (x.length : ℚ) * (maxAbs x * maxAbs y * 2 ^ (-(((t + clog2 k : ℕ)) : ℤ)))
      ≤ 2 ^ ((clog2 k : ℕ) : ℤ) * (maxAbs x * maxAbs y * 2 ^ (-(((t + clog2 k : ℕ)) : ℤ))) :=
        Rat.mul_le_mul_of_nonneg_right hlen hm
    _ = maxAbs x * maxAbs y * 2 ^ (-(t : ℤ)) := by rw [e2]; grind

/-- **Relative to the product.** If cancellation loses at most `c` bits,
`max|x| max|y| ≤ 2^c |x · y|`, the bound of the first test is at most `2^(c−t) |x · y|`. -/
theorem ozaki1Bound_le_cr_rel {b t k : ℕ} (hs : 0 < slicesForCR b t k) {x y : List ℚ}
    (hk : x.length ≤ k) (hx : maxAbs x ≠ 0) (hy : maxAbs y ≠ 0) {c : ℤ}
    (hcanc : maxAbs x * maxAbs y ≤ 2 ^ c * Rat.abs (dot x y)) :
    ozaki1Bound b (slicesForCR b t k) x y ≤ 2 ^ (c - t) * Rat.abs (dot x y) := by
  refine Rat.le_trans (ozaki1Bound_le_cr hs hk hx hy) ?_
  have hp := two_pow_pos (-(t : ℤ))
  have := Rat.mul_le_mul_of_nonneg_right hcanc (Rat.le_of_lt hp)
  have e : (2 : ℚ) ^ (c - t) = 2 ^ c * 2 ^ (-(t : ℤ)) := by
    rw [← two_pow_add]; congr 1
  calc maxAbs x * maxAbs y * 2 ^ (-(t : ℤ)) ≤ 2 ^ c * Rat.abs (dot x y) * 2 ^ (-(t : ℤ)) := this
    _ = 2 ^ (c - t) * Rat.abs (dot x y) := by rw [e]; grind

/-! ## The moduli rule for correct rounding -/

/-- **The moduli count for correct rounding**: `⌈log₂ k⌉` more bits than the plain rule, so
`P = t + clog2 k + 2`. -/
def moduliForCR (b t k : ℕ) : ℕ := moduliFor b (t + clog2 k) k

/-- The rule meets the reconstruction condition with `P = t + clog2 k + 2`. -/
theorem moduliForCR_spec {b t k : ℕ} (hn : 0 < moduliForCR b t k) {L : ℕ} (hL : L ≤ k) :
    2 * L * (2 ^ (t + clog2 k + 2) * 2 ^ (t + clog2 k + 2)) <
      (moduliBasis b (moduliForCR b t k)).modulus :=
  moduliFor_spec hn hL

/-- **Ozaki-II's truncation without the factor `k`.** With `P = t + clog2 k + 2` and at most `k`
entries, the truncation error is at most `2^-t · max|x| · max|y|`. -/
theorem truncation_le_cr {t k : ℕ} {x y : List ℚ} (hlen : x.length = y.length)
    (hk : x.length ≤ k) (hx : maxAbs x ≠ 0) (hy : maxAbs y ≠ 0) :
    Rat.abs (dot x y - 2 ^ (-(scaleShift (t + clog2 k + 2) x + scaleShift (t + clog2 k + 2) y)) *
        (dotZ (scaleTrunc (scaleShift (t + clog2 k + 2) x) x)
          (scaleTrunc (scaleShift (t + clog2 k + 2) y) y) : ℚ)) ≤
      maxAbs x * maxAbs y * 2 ^ (-(t : ℤ)) := by
  refine Rat.le_trans (truncProduct_error_normwise4 _ hlen hx hy) ?_
  have hc := le_two_pow_clog2 k
  have hlenq : (x.length : ℚ) ≤ 2 ^ ((clog2 k : ℕ) : ℤ) := by
    rw [two_pow_natCast]; exact Rat.natCast_le_natCast.mpr (Nat.le_trans hk hc)
  have hm : 0 ≤ 4 * (maxAbs x * maxAbs y) * 2 ^ (-(((t + clog2 k + 2 : ℕ)) : ℤ)) :=
    Rat.mul_nonneg (Rat.mul_nonneg (by decide) (Rat.mul_nonneg (maxAbs_nonneg x) (maxAbs_nonneg y)))
      (Rat.le_of_lt (two_pow_pos _))
  have e : 4 * (x.length : ℚ) * maxAbs x * maxAbs y * 2 ^ (-(((t + clog2 k + 2 : ℕ)) : ℤ)) =
      x.length * (4 * (maxAbs x * maxAbs y) * 2 ^ (-(((t + clog2 k + 2 : ℕ)) : ℤ))) := by grind
  rw [e]
  have e2 : (2 : ℚ) ^ (-(t : ℤ)) =
      2 ^ ((clog2 k : ℕ) : ℤ) * 4 * 2 ^ (-(((t + clog2 k + 2 : ℕ)) : ℤ)) := by
    rw [show (4 : ℚ) = 2 ^ (2 : ℤ) by rfl, ← two_pow_add, ← two_pow_add]; congr 1; push_cast; omega
  calc (x.length : ℚ) * (4 * (maxAbs x * maxAbs y) * 2 ^ (-(((t + clog2 k + 2 : ℕ)) : ℤ)))
      ≤ 2 ^ ((clog2 k : ℕ) : ℤ) * (4 * (maxAbs x * maxAbs y) *
          2 ^ (-(((t + clog2 k + 2 : ℕ)) : ℤ))) := Rat.mul_le_mul_of_nonneg_right hlenq hm
    _ = maxAbs x * maxAbs y * 2 ^ (-(t : ℤ)) := by rw [e2]; grind

/-- **Every basis of the moduli rule is valid**, for every width and count. -/
theorem moduliBasis_valid_all (b n : ℕ) : (moduliBasis b n).Valid :=
  crtBasis_valid (fun m hm => Nat.lt_of_lt_of_le (by decide) ((moduliList_pairwise _ _).1 m hm))
    (moduliList_pairwise _ _).2

end Ozaki
