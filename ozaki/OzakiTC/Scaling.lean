import OzakiTC.Schemes
import Ozaki.Checks

/-! # Power-of-two scaling in binary32

The scheme library multiplies by powers of two in exact rational arithmetic. The Z3 models do it
in binary32 and check at runtime that nothing is lost: the constant `2^e` is a binary32 number
(Ozaki-I `[H.2]`, Ozaki-II `[H.3]`), a slice product times `2^(gₜ + hᵤ)` is exact (Ozaki-I
`[S3.2]`), and an input times `2^sₓ` is exact (Ozaki-II `[S1.2]`). Here, for every input:

* `pow2_finiteValue32`: `2^e` is a binary32 value for `−149 ≤ e ≤ 127`;
* `int_mul_pow2_finiteValue32`: an integer `|z| ≤ 2^24` times `2^g` is a binary32 value for
  `−149 ≤ g ≤ 103`, so `scaled_slice_product_exact`: the binary32 product of a slice product and
  its scale is exact, and `exactTerm_finiteValue32`: every exact term of Ozaki-I is a binary32
  value when its scale is in range;
* `scale_finiteValue32`: a binary32 value times `2^s` is a binary32 value when it stays below
  `maxFinite32` and either `s ≥ 0` or the result is at least `2^-126`; `scaleShift_exact32`: the
  scaling step of Ozaki-II is exact on every entry under that condition. -/

open TensorCore

namespace Ozaki.TC

/-- A binary32 value is returned unchanged by the binary32 rounding. -/
theorem round32Value_of_finite {q : ℚ} (h : FiniteValue32 q) : round32Value q = some q :=
  roundRNE_of_formatValue (by decide) (finiteValue32_binary32 h)

/-- **Powers of two are binary32 values** (Ozaki-I `[H.2]`, Ozaki-II `[H.3]`): `2^e` for
`−149 ≤ e ≤ 127`. -/
theorem pow2_finiteValue32 {e : ℤ} (h1 : -149 ≤ e) (h2 : e ≤ 127) : FiniteValue32 ((2 : ℚ) ^ e) := by
  by_cases he : -126 ≤ e
  · refine ⟨2 ^ 23, e, he, h2, by decide, ?_⟩
    rw [pow2_eq, show ((2 ^ 23 : ℤ) : ℚ) = (2 : ℚ) ^ (23 : ℤ) by decide, ← two_pow_add]
    congr 1; omega
  · have := grid_finiteValue32 1 e h1 (by omega) (by decide)
    rwa [Rat.intCast_one, Rat.one_mul, pow2_eq] at this

/-- **Scaled integers are binary32 values.** An integer of magnitude at most `2^24` times `2^g`,
`−149 ≤ g ≤ 103`. -/
theorem int_mul_pow2_finiteValue32 (z : ℤ) {g : ℤ} (hz : z.natAbs ≤ 2 ^ 24) (hg1 : -149 ≤ g)
    (hg2 : g ≤ 103) : FiniteValue32 ((z : ℚ) * 2 ^ g) := by
  by_cases hlt : z.natAbs < 2 ^ 24
  · have := grid_finiteValue32 z g hg1 (by omega) hlt
    rwa [pow2_eq] at this
  · have hz2 : z = (z / 2) * 2 := by omega
    have := grid_finiteValue32 (z / 2) (g + 1) (by omega) (by omega) (by omega)
    rw [pow2_eq, two_pow_succ] at this
    have e : ((z / 2 : ℤ) : ℚ) * (2 ^ g * 2) = (z : ℚ) * 2 ^ g := by
      conv => rhs; rw [hz2]
      rw [Rat.intCast_mul]; have : ((2 : ℤ) : ℚ) = 2 := rfl
      rw [this]; grind
    rwa [e] at this

/-- **Rescaling a slice product is exact** (Ozaki-I `[S3.2]`). A result `z` of the matrix multiplier
with `|z| ≤ 2^24` times `2^g`, rounded to binary32, is `z · 2^g` for `−149 ≤ g ≤ 103`. -/
theorem scaled_slice_product_exact (z : ℤ) {g : ℤ} (hz : z.natAbs ≤ 2 ^ 24) (hg1 : -149 ≤ g)
    (hg2 : g ≤ 103) : round32Value ((z : ℚ) * 2 ^ g) = some ((z : ℚ) * 2 ^ g) :=
  round32Value_of_finite (int_mul_pow2_finiteValue32 z hz hg1 hg2)

/-- **Every exact term of Ozaki-I is a binary32 value** when `k 2^(2b) ≤ 2^24` and its scale
`2^(gₜ + hᵤ)` has `−149 ≤ gₜ + hᵤ ≤ 103`. -/
theorem exactTerm_finiteValue32 {b s : ℕ} {x y : List ℚ} (hk : x.length * (2 ^ b * 2 ^ b) ≤ 2 ^ 24)
    {t u : ℕ} (ht : t < s) (hu : u < s)
    (hg1 : -149 ≤ ((split b s x).1.getD t default).grid + ((split b s y).1.getD u default).grid)
    (hg2 : ((split b s x).1.getD t default).grid + ((split b s y).1.getD u default).grid ≤ 103) :
    FiniteValue32 (exactTerm (split b s x).1 (split b s y).1 (t, u)) := by
  unfold exactTerm
  rw [Rat.mul_comm]
  exact int_mul_pow2_finiteValue32 _ (Nat.le_trans (slice_product_bound b s x y ht hu) hk) hg1 hg2

/-- **Scaling a binary32 value by `2^s` is exact** when the result is at most `maxFinite32` and
either `s ≥ 0` or the result is at least `2^-126` (Ozaki-II `[S1.2]`). -/
theorem scale_finiteValue32 {a : ℚ} (ha : FiniteValue32 a) {s : ℤ}
    (hs : 0 ≤ s ∨ (2 : ℚ) ^ (-126 : ℤ) ≤ Rat.abs (a * 2 ^ s))
    (hr : Rat.abs (a * 2 ^ s) ≤ maxFinite32) : FiniteValue32 (a * 2 ^ s) := by
  obtain ⟨k, e, he1, he2, hk, rfl⟩ := ha
  rw [pow2_eq] at hr hs ⊢
  have hval : (k : ℚ) * 2 ^ (e - 23) * 2 ^ s = (k : ℚ) * 2 ^ (e - 23 + s) := by
    rw [two_pow_add, Rat.mul_assoc]
  rw [hval] at hr hs ⊢
  generalize hl : e - 23 + s = l at hr hs ⊢
  have hkq : Rat.abs (k : ℚ) < 2 ^ (24 : ℤ) := by
    rw [abs_intCast, show (2 : ℚ) ^ (24 : ℤ) = ((2 ^ 24 : ℕ) : ℚ) from two_pow_natCast 24]
    exact Rat.natCast_lt_natCast.mpr hk
  -- the grid is not below `2^-149`
  have hlo : -149 ≤ l := by
    rcases hs with hs | hs
    · omega
    · by_cases hneg : -149 ≤ l
      · exact hneg
      exfalso
      have h1 : Rat.abs ((k : ℚ) * 2 ^ l) < 2 ^ (24 + l) := by
        rw [abs_mul, abs_two_pow, two_pow_add]
        exact Rat.mul_lt_mul_of_pos_right hkq (two_pow_pos l)
      have h2 : (2 : ℚ) ^ (24 + l) ≤ 2 ^ (-126 : ℤ) := two_pow_le (by omega)
      grind
  by_cases hhi : l ≤ 104
  · have := grid_finiteValue32 k l hlo hhi hk
    rwa [pow2_eq] at this
  · -- move the excess exponent into the coefficient
    obtain ⟨n, hn⟩ : ∃ n : ℕ, l = 104 + n := ⟨(l - 104).toNat, by omega⟩
    subst hn
    have hpow : (2 : ℚ) ^ ((104 : ℤ) + n) = ((2 ^ n : ℕ) : ℚ) * 2 ^ (104 : ℤ) := by
      rw [two_pow_add, two_pow_natCast, Rat.mul_comm]
    have hk' : ((k * 2 ^ n : ℤ) : ℚ) = (k : ℚ) * ((2 ^ n : ℕ) : ℚ) := by
      rw [Rat.intCast_mul]; congr 1
    have hv : (k : ℚ) * 2 ^ ((104 : ℤ) + n) = ((k * 2 ^ n : ℤ) : ℚ) * 2 ^ (104 : ℤ) := by
      rw [hpow, hk', Rat.mul_assoc]
    rw [hv] at hr ⊢
    have hbound : (k * 2 ^ n).natAbs < 2 ^ 24 := by
      have hmf : maxFinite32 = (((2 ^ 24 - 1 : ℕ)) : ℚ) * 2 ^ (104 : ℤ) := by
        unfold maxFinite32; rw [pow2_eq]
      rw [hmf, abs_mul, abs_two_pow, abs_intCast] at hr
      have h104 := two_pow_pos (104 : ℤ)
      have hle : (((k * 2 ^ n).natAbs : ℕ) : ℚ) ≤ ((2 ^ 24 - 1 : ℕ) : ℚ) := by
        by_cases h : (((k * 2 ^ n).natAbs : ℕ) : ℚ) ≤ ((2 ^ 24 - 1 : ℕ) : ℚ)
        · exact h
        exfalso
        have := Rat.mul_lt_mul_of_pos_right (show ((2 ^ 24 - 1 : ℕ) : ℚ) <
          (((k * 2 ^ n).natAbs : ℕ) : ℚ) by grind) h104
        grind
      have := Rat.natCast_le_natCast.mp hle
      omega
    have := grid_finiteValue32 (k * 2 ^ n) 104 (by omega) (by omega) hbound
    rwa [pow2_eq] at this

/-- **The scaling step of Ozaki-II is exact in binary32** (`[S1.2]`). For an entry `a` of a
binary32 vector `x` and `P ≤ 127`, `fl(a · 2^sₓ) = a · 2^sₓ` when `sₓ ≥ 0` or `|a · 2^sₓ| ≥ 2^-126`;
an entry that would land below `2^-126` truncates to `0` in the next step anyway. -/
theorem scaleShift_exact32 (P : ℕ) (hP : P ≤ 127) {x : List ℚ} {a : ℚ} (hax : a ∈ x)
    (ha : FiniteValue32 a)
    (hs : 0 ≤ scaleShift P x ∨ (2 : ℚ) ^ (-126 : ℤ) ≤ Rat.abs (a * 2 ^ scaleShift P x)) :
    round32Value (a * 2 ^ scaleShift P x) = some (a * 2 ^ scaleShift P x) := by
  apply round32Value_of_finite
  apply scale_finiteValue32 ha hs
  have h1 := abs_le_scaleShift P x a hax
  have h2 : Rat.abs (a * 2 ^ scaleShift P x) ≤ 2 ^ (P : ℤ) := by
    rw [abs_mul_two_pow]
    have := Rat.mul_le_mul_of_nonneg_right h1 (Rat.le_of_lt (two_pow_pos (scaleShift P x)))
    rwa [← two_pow_add, show (P : ℤ) - scaleShift P x + scaleShift P x = P by omega] at this
  have h3 : (2 : ℚ) ^ (P : ℤ) ≤ 2 ^ (127 : ℤ) := two_pow_le (by omega)
  have h4 : (2 : ℚ) ^ (127 : ℤ) ≤ maxFinite32 := by decide +kernel
  exact Rat.le_trans h2 (Rat.le_trans h3 h4)

end Ozaki.TC
