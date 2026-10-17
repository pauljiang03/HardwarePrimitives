import Ozaki.Correct

/-! # Round to nearest even in any binary format

A binary format with `p` significand bits (the hidden bit included) and exponents `emin … emax`
has the finite values `k · 2^(e − (p − 1))` with `|k| < 2^p` and `emin ≤ e ≤ emax`
(`FormatValue`); binary64 is `p = 53`, `emin = −1022`, `emax = 1023`, binary32 is `24`, `−126`,
`127`. `roundRNE p emin emax` rounds a rational to the nearest such value, ties to even: on the
grid `2^(max(⌊log₂|q|⌋, emin) − (p − 1))` it takes the nearest integer, ties to even, and it fails
(`none`) exactly when the rounded magnitude exceeds the largest finite value, as IEEE 754 overflows.

It meets the two conditions of the correct-rounding framework of `Ozaki.Correct`
(`roundRNE_nearest`, `roundRNE_intervals`) and the standard error model (`roundRNE_within`), so
the correctly rounded schemes can round to any format on any hardware model; `rne64` and `rne32Q`
are binary64 and binary32. The library depends on no hardware model.

The proof that the result is a nearest value compares it with every representable `w`. If `w`'s
exponent is at least the grid's, `w` lies on the grid, and the nearest integer is nearest. If it is
smaller, `|w| < 2^e ≤ |q|`, and `2^e` is a grid point between `w` and `q`. -/

local notation "ℕ" => Nat
local notation "ℤ" => Int
local notation "ℚ" => Rat

namespace Ozaki

/-! ## Formats -/

/-- The finite values of a binary format with `p` significand bits (hidden bit included) and
exponents `emin … emax`: `k · 2^(e − (p − 1))` with `|k| < 2^p`. -/
def FormatValue (p : ℕ) (emin emax : ℤ) (v : ℚ) : Prop :=
  ∃ k e : ℤ, emin ≤ e ∧ e ≤ emax ∧ k.natAbs < 2 ^ p ∧ v = (k : ℚ) * 2 ^ (e - ((p : ℤ) - 1))

/-- The same values without an upper limit on the exponent. -/
def UValue (p : ℕ) (emin : ℤ) (v : ℚ) : Prop :=
  ∃ k e : ℤ, emin ≤ e ∧ k.natAbs < 2 ^ p ∧ v = (k : ℚ) * 2 ^ (e - ((p : ℤ) - 1))

/-- The largest finite value, `(2^p − 1) · 2^(emax − (p − 1))`. -/
def maxFormat (p : ℕ) (emax : ℤ) : ℚ := ((2 ^ p - 1 : ℕ) : ℚ) * 2 ^ (emax - ((p : ℤ) - 1))

theorem FormatValue.uValue {p : ℕ} {emin emax : ℤ} {v : ℚ} (h : FormatValue p emin emax v) :
    UValue p emin v := by
  obtain ⟨k, e, h1, _, h3, h4⟩ := h
  exact ⟨k, e, h1, h3, h4⟩

theorem UValue.neg {p : ℕ} {emin : ℤ} {v : ℚ} (h : UValue p emin v) : UValue p emin (-v) := by
  obtain ⟨k, e, h1, h3, h4⟩ := h
  refine ⟨-k, e, h1, by rw [Int.natAbs_neg]; exact h3, ?_⟩
  rw [h4, Rat.intCast_neg, Rat.neg_mul]

theorem FormatValue.neg {p : ℕ} {emin emax : ℤ} {v : ℚ} (h : FormatValue p emin emax v) :
    FormatValue p emin emax (-v) := by
  obtain ⟨k, e, h1, h2, h3, h4⟩ := h
  refine ⟨-k, e, h1, h2, by rw [Int.natAbs_neg]; exact h3, ?_⟩
  rw [h4, Rat.intCast_neg, Rat.neg_mul]

/-! ## The rounding -/

/-- The grid exponent for a magnitude `a`: `max(⌊log₂ a⌋, emin) − (p − 1)`. -/
def rneGrid (p : ℕ) (emin : ℤ) (a : ℚ) : ℤ := max (floorLog2 a) emin - ((p : ℤ) - 1)

/-- A magnitude rounded to the nearest point of its grid, ties to even. -/
def rneMag (p : ℕ) (emin : ℤ) (a : ℚ) : ℚ :=
  (roundNearestEven (a / 2 ^ rneGrid p emin a) : ℚ) * 2 ^ rneGrid p emin a

/-- Round to nearest even without an exponent limit above. -/
def rneU (p : ℕ) (emin : ℤ) (q : ℚ) : ℚ := if q < 0 then -rneMag p emin (-q) else rneMag p emin q

/-- **Round to nearest even** in the format with `p` significand bits and exponents
`emin … emax`; `none` when the rounded magnitude exceeds the largest finite value. -/
def roundRNE (p : ℕ) (emin emax : ℤ) (q : ℚ) : Option ℚ :=
  if Rat.abs (rneU p emin q) ≤ maxFormat p emax then some (rneU p emin q) else none

/-! ## The nearest integer and the nearest grid point -/

/-- `roundNearestEven t` is an integer nearest to `t`. -/
theorem roundNearestEven_nearest (t : ℚ) (j : ℤ) :
    Rat.abs (t - roundNearestEven t) ≤ Rat.abs (t - j) := by
  have h := roundNearestEven_error t
  by_cases hj : j = roundNearestEven t
  · subst hj; exact Rat.le_refl
  · have hd : (1 : ℚ) ≤ Rat.abs ((roundNearestEven t : ℚ) - j) := by
      rw [← Rat.intCast_sub, abs_intCast]
      have h1 : 1 ≤ (roundNearestEven t - j).natAbs := Int.natAbs_pos.mpr (by omega)
      exact_mod_cast h1
    have htri := abs_sub_le (t - j) (t - roundNearestEven t)
    have e : (t - j) - (t - roundNearestEven t) = (roundNearestEven t : ℚ) - j := by grind
    rw [e] at htri
    grind

theorem abs_sub_mul_two_pow (a : ℚ) (m g : ℤ) :
    Rat.abs (a - (m : ℚ) * 2 ^ g) = Rat.abs (a / 2 ^ g - m) * 2 ^ g := by
  rw [← abs_mul_two_pow]
  congr 1
  have h : a / 2 ^ g * 2 ^ g = a := Rat.div_mul_cancel (two_pow_ne_zero g)
  grind

/-- The rounded magnitude is at least as close to `a` as any point of its grid. -/
theorem rneMag_le_grid (p : ℕ) (emin : ℤ) (a : ℚ) (j : ℤ) :
    Rat.abs (a - rneMag p emin a) ≤ Rat.abs (a - (j : ℚ) * 2 ^ rneGrid p emin a) := by
  unfold rneMag
  rw [abs_sub_mul_two_pow, abs_sub_mul_two_pow]
  exact Rat.mul_le_mul_of_nonneg_right (roundNearestEven_nearest _ j)
    (Rat.le_of_lt (two_pow_pos _))

theorem roundNearestEven_zero : roundNearestEven 0 = 0 := by
  have := roundNearestEven_intCast 0
  simpa using this

theorem rneMag_zero (p : ℕ) (emin : ℤ) : rneMag p emin 0 = 0 := by
  unfold rneMag
  have h : (0 : ℚ) / 2 ^ rneGrid p emin 0 = 0 := by rw [div_two_pow]; grind
  rw [h, roundNearestEven_zero]
  simp

theorem rneU_zero (p : ℕ) (emin : ℤ) : rneU p emin 0 = 0 := by
  unfold rneU
  rw [if_neg (Rat.lt_irrefl), rneMag_zero]

/-! ## The magnitude on its grid -/

section Magnitude

variable {p : ℕ} {emin : ℤ}

theorem rneGrid_def (p : ℕ) (emin : ℤ) (a : ℚ) :
    rneGrid p emin a = max (floorLog2 a) emin - ((p : ℤ) - 1) := rfl

/-- The magnitude scaled to its grid lies below `2^p`. -/
theorem scaled_lt {a : ℚ} (ha : 0 < a) :
    a / 2 ^ rneGrid p emin a < ((2 ^ p : ℕ) : ℚ) := by
  obtain ⟨_, hlt⟩ := floorLog2_spec ha
  rw [div_two_pow, ← two_pow_natCast]
  have h1 : a * 2 ^ (-rneGrid p emin a) < 2 ^ (floorLog2 a + 1) * 2 ^ (-rneGrid p emin a) :=
    Rat.mul_lt_mul_of_pos_right hlt (two_pow_pos _)
  have h2 : (2 : ℚ) ^ (floorLog2 a + 1) * 2 ^ (-rneGrid p emin a) ≤ 2 ^ ((p : ℕ) : ℤ) := by
    rw [← two_pow_add]; apply two_pow_le; rw [rneGrid_def]; omega
  grind

/-- A normal magnitude scaled to its grid is at least `2^(p − 1)`. -/
theorem scaled_ge (hp : 0 < p) {a : ℚ} (ha : 0 < a) (hE : emin ≤ floorLog2 a) :
    ((2 ^ (p - 1) : ℕ) : ℚ) ≤ a / 2 ^ rneGrid p emin a := by
  have := hp
  obtain ⟨hle, _⟩ := floorLog2_spec ha
  rw [div_two_pow, ← two_pow_natCast]
  have h : (2 : ℚ) ^ (((p - 1 : ℕ)) : ℤ) = 2 ^ floorLog2 a * 2 ^ (-rneGrid p emin a) := by
    rw [← two_pow_add]; congr 1; rw [rneGrid_def]; omega
  rw [h]
  exact Rat.mul_le_mul_of_nonneg_right hle (Rat.le_of_lt (two_pow_pos _))

theorem scaled_nonneg {a : ℚ} (ha : 0 ≤ a) (g : ℤ) : 0 ≤ a / 2 ^ g := by
  rw [div_two_pow]; exact Rat.mul_nonneg ha (Rat.le_of_lt (two_pow_pos _))

/-- **The rounded magnitude is a format value** with no upper exponent limit, and either its
exponent is `emin` or `2^e` is at most the rounded magnitude. -/
theorem rneMag_repr (hp : 0 < p) {a : ℚ} (ha : 0 < a) :
    ∃ k e : ℤ, emin ≤ e ∧ k.natAbs < 2 ^ p ∧ 0 ≤ k ∧
      rneMag p emin a = (k : ℚ) * 2 ^ (e - ((p : ℤ) - 1)) ∧
      (e = emin ∨ (2 : ℚ) ^ e ≤ rneMag p emin a) := by
  have hn0 : 0 ≤ roundNearestEven (a / 2 ^ rneGrid p emin a) :=
    le_roundNearestEven (by rw [Rat.intCast_zero]; exact scaled_nonneg (Rat.le_of_lt ha) _)
  have hnp : roundNearestEven (a / 2 ^ rneGrid p emin a) ≤ ((2 ^ p : ℕ) : ℤ) :=
    roundNearestEven_le (by rw [Rat.intCast_natCast]; exact Rat.le_of_lt (scaled_lt ha))
  have hge : emin ≤ floorLog2 a →
      ((2 ^ (p - 1) : ℕ) : ℤ) ≤ roundNearestEven (a / 2 ^ rneGrid p emin a) := fun hE =>
    le_roundNearestEven (by rw [Rat.intCast_natCast]; exact scaled_ge hp ha hE)
  have hmag : rneMag p emin a = (roundNearestEven (a / 2 ^ rneGrid p emin a) : ℚ) *
      2 ^ (max (floorLog2 a) emin - ((p : ℤ) - 1)) := rfl
  generalize roundNearestEven (a / 2 ^ rneGrid p emin a) = n at hn0 hnp hge hmag
  by_cases hlt : n < ((2 ^ p : ℕ) : ℤ)
  · refine ⟨n, max (floorLog2 a) emin, by omega, ?_, hn0, hmag, ?_⟩
    · have := Int.natAbs_of_nonneg hn0; omega
    · by_cases hE : emin ≤ floorLog2 a
      · right
        have h2 : (2 : ℚ) ^ max (floorLog2 a) emin =
            ((2 ^ (p - 1) : ℕ) : ℚ) * 2 ^ (max (floorLog2 a) emin - ((p : ℤ) - 1)) := by
          rw [← two_pow_natCast, ← two_pow_add]; congr 1; omega
        rw [hmag, h2]
        apply Rat.mul_le_mul_of_nonneg_right _ (Rat.le_of_lt (two_pow_pos _))
        have h3 : (((2 ^ (p - 1) : ℕ) : ℤ) : ℚ) ≤ (n : ℚ) := Rat.intCast_le_intCast.mpr (hge hE)
        rwa [Rat.intCast_natCast] at h3
      · left; omega
  · have hnp' : n = ((2 ^ p : ℕ) : ℤ) := by omega
    refine ⟨((2 ^ (p - 1) : ℕ) : ℤ), max (floorLog2 a) emin + 1, by omega, ?_,
      Int.natCast_nonneg _, ?_, Or.inr ?_⟩
    · rw [Int.natAbs_natCast]; exact Nat.pow_lt_pow_right (by decide) (by omega)
    · rw [hmag, hnp', Rat.intCast_natCast, Rat.intCast_natCast, ← two_pow_natCast,
        ← two_pow_natCast, ← two_pow_add, ← two_pow_add]
      congr 1; omega
    · rw [hmag, hnp', Rat.intCast_natCast, ← two_pow_natCast, ← two_pow_add]
      exact two_pow_le (by omega)

/-- **The rounded magnitude is a nearest value**: no value of the format, at any exponent, is
closer to `a`. -/
theorem rneMag_nearest (hp : 0 < p) {a : ℚ} (ha : 0 < a) {w : ℚ} (hw : UValue p emin w) :
    Rat.abs (a - rneMag p emin a) ≤ Rat.abs (a - w) := by
  have := hp
  obtain ⟨k, e', he', hk, rfl⟩ := hw
  by_cases hge : max (floorLog2 a) emin ≤ e'
  · -- `w` lies on the grid
    have hw : (k : ℚ) * 2 ^ (e' - ((p : ℤ) - 1)) =
        ((k * ((2 ^ (e' - max (floorLog2 a) emin).toNat : ℕ) : ℤ) : ℤ) : ℚ) *
          2 ^ rneGrid p emin a := by
      have hle : rneGrid p emin a ≤ e' - ((p : ℤ) - 1) := by rw [rneGrid_def]; omega
      have ht : (e' - ((p : ℤ) - 1) - rneGrid p emin a).toNat =
          (e' - max (floorLog2 a) emin).toNat := by rw [rneGrid_def]; congr 1; omega
      rw [two_pow_eq_natCast_mul hle, ht, Rat.intCast_mul, Rat.intCast_natCast]
      grind
    rw [hw]
    exact rneMag_le_grid p emin a _
  · -- `w` lies below `2^E ≤ a`, and `2^E` is on the grid
    obtain ⟨hle, _⟩ := floorLog2_spec ha
    have hpos := two_pow_pos (e' - ((p : ℤ) - 1))
    have h1 : (k : ℚ) ≤ ((k.natAbs : ℕ) : ℚ) := by rw [← abs_intCast]; exact le_abs_self _
    have hk' : ((k.natAbs : ℕ) : ℚ) < ((2 ^ p : ℕ) : ℚ) := Rat.natCast_lt_natCast.mpr hk
    have e1 : (k : ℚ) * 2 ^ (e' - ((p : ℤ) - 1)) ≤
        ((k.natAbs : ℕ) : ℚ) * 2 ^ (e' - ((p : ℤ) - 1)) :=
      Rat.mul_le_mul_of_nonneg_right h1 (Rat.le_of_lt hpos)
    have e2 : ((k.natAbs : ℕ) : ℚ) * 2 ^ (e' - ((p : ℤ) - 1)) <
        ((2 ^ p : ℕ) : ℚ) * 2 ^ (e' - ((p : ℤ) - 1)) := Rat.mul_lt_mul_of_pos_right hk' hpos
    have e3 : ((2 ^ p : ℕ) : ℚ) * 2 ^ (e' - ((p : ℤ) - 1)) = 2 ^ (e' + 1) := by
      rw [← two_pow_natCast, ← two_pow_add]; congr 1; omega
    have e4 : (2 : ℚ) ^ (e' + 1) ≤ 2 ^ floorLog2 a := two_pow_le (by omega)
    have hgrid : (2 : ℚ) ^ floorLog2 a =
        (((2 ^ (p - 1) : ℕ) : ℤ) : ℚ) * 2 ^ rneGrid p emin a := by
      rw [Rat.intCast_natCast, ← two_pow_natCast, ← two_pow_add]; congr 1; rw [rneGrid_def]; omega
    have h2 := rneMag_le_grid p emin a ((2 ^ (p - 1) : ℕ) : ℤ)
    rw [← hgrid, abs_of_nonneg (by grind : (0 : ℚ) ≤ a - 2 ^ floorLog2 a)] at h2
    rw [abs_of_nonneg (by grind : (0 : ℚ) ≤ a - (k : ℚ) * 2 ^ (e' - ((p : ℤ) - 1)))]
    grind

/-- The rounding error of a magnitude: half a grid step, at most `2^-p a + 2^(emin − p)`. -/
theorem rneMag_error {a : ℚ} (ha : 0 < a) :
    Rat.abs (rneMag p emin a - a) ≤ 2 ^ (-(p : ℤ)) * a + 2 ^ (emin - p) := by
  have h1 := roundNearestEven_error (a / 2 ^ rneGrid p emin a)
  have h2 : Rat.abs (rneMag p emin a - a) =
      Rat.abs (a / 2 ^ rneGrid p emin a - roundNearestEven (a / 2 ^ rneGrid p emin a)) *
        2 ^ rneGrid p emin a := by
    rw [abs_sub_comm]; exact abs_sub_mul_two_pow a _ _
  have hg := two_pow_pos (rneGrid p emin a)
  have h3 : Rat.abs (rneMag p emin a - a) * 2 ≤ 2 ^ rneGrid p emin a := by
    rw [h2]
    have := Rat.mul_le_mul_of_nonneg_right h1 (Rat.le_of_lt hg)
    grind
  have hstep : (2 : ℚ) ^ rneGrid p emin a = 2 ^ (rneGrid p emin a - 1) * 2 := by
    rw [← two_pow_succ]; congr 1; omega
  have hη := two_pow_pos (emin - p)
  have hu : 0 ≤ (2 : ℚ) ^ (-(p : ℤ)) * a := Rat.mul_nonneg (Rat.le_of_lt (two_pow_pos _)) (Rat.le_of_lt ha)
  by_cases hE : emin ≤ floorLog2 a
  · obtain ⟨hle, _⟩ := floorLog2_spec ha
    have h4 : (2 : ℚ) ^ (rneGrid p emin a - 1) = 2 ^ (-(p : ℤ)) * 2 ^ floorLog2 a := by
      rw [← two_pow_add]; congr 1; rw [rneGrid_def]; omega
    have h5 : (2 : ℚ) ^ (-(p : ℤ)) * 2 ^ floorLog2 a ≤ 2 ^ (-(p : ℤ)) * a :=
      Rat.mul_le_mul_of_nonneg_left hle (Rat.le_of_lt (two_pow_pos _))
    grind
  · have h4 : (2 : ℚ) ^ (rneGrid p emin a - 1) = 2 ^ (emin - p) := by
      congr 1; rw [rneGrid_def]; omega
    grind

end Magnitude

/-! ## Signed rounding without an upper limit -/

section Unbounded

variable {p : ℕ} {emin : ℤ}

/-- The rounding is a nearest value of the format with no upper exponent limit. -/
theorem rneU_nearest (hp : 0 < p) (q : ℚ) {w : ℚ} (hw : UValue p emin w) :
    Rat.abs (q - rneU p emin q) ≤ Rat.abs (q - w) := by
  unfold rneU
  split
  · rename_i hq
    have h := rneMag_nearest hp (show 0 < -q by grind) hw.neg
    have e1 : q - -rneMag p emin (-q) = -((-q) - rneMag p emin (-q)) := by grind
    have e2 : q - w = -((-q) - -w) := by grind
    rw [e1, e2, abs_neg, abs_neg]
    exact h
  · rename_i hq
    by_cases h0 : q = 0
    · subst h0
      rw [rneMag_zero, show (0 : ℚ) - 0 = 0 by grind, abs_zero]
      exact abs_nonneg _
    · exact rneMag_nearest hp (by grind) hw

/-- The rounding as `k · 2^(e − (p − 1))`, with `e = emin` or `2^e ≤ |rounding|`. -/
theorem rneU_repr (hp : 0 < p) (q : ℚ) :
    ∃ k e : ℤ, emin ≤ e ∧ k.natAbs < 2 ^ p ∧
      rneU p emin q = (k : ℚ) * 2 ^ (e - ((p : ℤ) - 1)) ∧
      (e = emin ∨ (2 : ℚ) ^ e ≤ Rat.abs (rneU p emin q)) := by
  unfold rneU
  split
  · rename_i hq
    obtain ⟨k, e, h1, h2, _, h4, h5⟩ := rneMag_repr (emin := emin) hp (show 0 < -q by grind)
    refine ⟨-k, e, h1, by rw [Int.natAbs_neg]; exact h2, by rw [h4, Rat.intCast_neg, Rat.neg_mul], ?_⟩
    rcases h5 with h5 | h5
    · exact Or.inl h5
    · right; rw [abs_neg]; exact Rat.le_trans h5 (le_abs_self _)
  · rename_i hq
    by_cases h0 : q = 0
    · subst h0
      refine ⟨0, emin, Int.le_refl _, by simpa using Nat.two_pow_pos p, by rw [rneMag_zero]; simp,
        Or.inl rfl⟩
    · obtain ⟨k, e, h1, h2, _, h4, h5⟩ := rneMag_repr (emin := emin) hp (show 0 < q by grind)
      refine ⟨k, e, h1, h2, h4, ?_⟩
      rcases h5 with h5 | h5
      · exact Or.inl h5
      · exact Or.inr (Rat.le_trans h5 (le_abs_self _))

theorem rneU_uValue (hp : 0 < p) (q : ℚ) : UValue p emin (rneU p emin q) := by
  obtain ⟨k, e, h1, h2, h3, _⟩ := rneU_repr (emin := emin) hp q
  exact ⟨k, e, h1, h2, h3⟩

theorem rneU_rounds (hp : 0 < p) :
    RoundsToNearest (UValue p emin) (fun q => some (rneU p emin q)) := by
  intro q v h
  simp only [Option.some.injEq] at h
  subst h
  exact ⟨rneU_uValue hp q, fun w hw => rneU_nearest hp q hw⟩

/-- **The rounding is monotone.** -/
theorem rneU_monotone (hp : 0 < p) {a b : ℚ} (hab : a ≤ b) : rneU p emin a ≤ rneU p emin b :=
  round_monotone (rneU_rounds hp) hab rfl rfl

/-- A value of the format rounds to itself. -/
theorem rneU_of_uValue (hp : 0 < p) {w : ℚ} (hw : UValue p emin w) : rneU p emin w = w := by
  have h := rneU_nearest hp w hw
  rw [show w - w = 0 by grind, abs_zero] at h
  have h0 : Rat.abs (w - rneU p emin w) = 0 := Rat.le_antisymm h (abs_nonneg _)
  have := abs_eq_zero.mp h0
  grind

/-- The rounding of a positive number is within `2^-p |q| + 2^(emin − p)`. -/
theorem rneU_error (q : ℚ) :
    Rat.abs (rneU p emin q - q) ≤ 2 ^ (-(p : ℤ)) * Rat.abs q + 2 ^ (emin - p) := by
  unfold rneU
  split
  · rename_i hq
    have h := rneMag_error (p := p) (emin := emin) (show 0 < -q by grind)
    rw [abs_of_neg hq]
    have e : -rneMag p emin (-q) - q = -(rneMag p emin (-q) - -q) := by grind
    rw [e, abs_neg]
    exact h
  · rename_i hq
    by_cases h0 : q = 0
    · subst h0
      rw [rneMag_zero, show (0 : ℚ) - 0 = 0 by grind, abs_zero, Rat.mul_zero, Rat.zero_add]
      exact Rat.le_of_lt (two_pow_pos _)
    · have hq' : 0 < q := by grind
      rw [abs_of_nonneg (Rat.le_of_lt hq')]
      exact rneMag_error hq'

end Unbounded

/-! ## The format's range -/

section Range

variable {p : ℕ} {emin emax : ℤ}

theorem maxFormat_uValue (hle : emin ≤ emax) : UValue p emin (maxFormat p emax) := by
  have h2 : 0 < 2 ^ p := Nat.two_pow_pos p
  refine ⟨((2 ^ p - 1 : ℕ) : ℤ), emax, hle, by rw [Int.natAbs_natCast]; omega, ?_⟩
  unfold maxFormat
  rw [Rat.intCast_natCast]

theorem maxFormat_formatValue (hle : emin ≤ emax) :
    FormatValue p emin emax (maxFormat p emax) := by
  have h2 : 0 < 2 ^ p := Nat.two_pow_pos p
  refine ⟨((2 ^ p - 1 : ℕ) : ℤ), emax, hle, Int.le_refl _, by rw [Int.natAbs_natCast]; omega, ?_⟩
  unfold maxFormat
  rw [Rat.intCast_natCast]

theorem maxFormat_lt : maxFormat p emax < 2 ^ (emax + 1) := by
  have h2 : 0 < 2 ^ p := Nat.two_pow_pos p
  have h1 : ((2 ^ p - 1 : ℕ) : ℚ) < ((2 ^ p : ℕ) : ℚ) := Rat.natCast_lt_natCast.mpr (by omega)
  have h3 : ((2 ^ p : ℕ) : ℚ) * 2 ^ (emax - ((p : ℤ) - 1)) = 2 ^ (emax + 1) := by
    rw [← two_pow_natCast, ← two_pow_add]; congr 1; omega
  unfold maxFormat
  rw [← h3]
  exact Rat.mul_lt_mul_of_pos_right h1 (two_pow_pos _)

/-- Every value of the format is at most the largest finite value. -/
theorem formatValue_abs_le {v : ℚ} (hv : FormatValue p emin emax v) :
    Rat.abs v ≤ maxFormat p emax := by
  obtain ⟨k, e, _, h2, h3, rfl⟩ := hv
  have hk : k.natAbs ≤ 2 ^ p - 1 := by omega
  unfold maxFormat
  apply mul_le_mul_abs
  · rw [abs_intCast]; exact Rat.natCast_le_natCast.mpr hk
  · rw [abs_two_pow]; exact two_pow_le (by omega)

/-- Every value of the format is below `2^(emax + 1)`. -/
theorem formatValue_abs_lt {v : ℚ} (hv : FormatValue p emin emax v) :
    Rat.abs v < 2 ^ (emax + 1) :=
  lt_of_le_of_lt' (formatValue_abs_le hv) maxFormat_lt

/-- Every value of the format is a multiple of its smallest grid step `2^(emin − (p − 1))`. -/
theorem formatValue_gridMultiple {v : ℚ} (hv : FormatValue p emin emax v) :
    GridMultiple (emin - ((p : ℤ) - 1)) v := by
  obtain ⟨k, e, h1, _, _, rfl⟩ := hv
  refine ⟨k * ((2 ^ (e - emin).toNat : ℕ) : ℤ), ?_⟩
  have ht : (e - ((p : ℤ) - 1) - (emin - ((p : ℤ) - 1))).toNat = (e - emin).toNat := by
    congr 1; omega
  rw [two_pow_eq_natCast_mul (show emin - ((p : ℤ) - 1) ≤ e - ((p : ℤ) - 1) by omega), ht,
    Rat.intCast_mul, Rat.intCast_natCast]
  grind

/-- The rounding fits the format exactly when its magnitude is at most the largest finite value;
then it is a value of the format. -/
theorem rneU_formatValue (hp : 0 < p) (hle : emin ≤ emax) {q : ℚ}
    (hM : Rat.abs (rneU p emin q) ≤ maxFormat p emax) : FormatValue p emin emax (rneU p emin q) := by
  obtain ⟨k, e, h1, h2, h3, h4⟩ := rneU_repr (emin := emin) hp q
  refine ⟨k, e, h1, ?_, h2, h3⟩
  rcases h4 with h4 | h4
  · omega
  · have h5 : (2 : ℚ) ^ e < 2 ^ (emax + 1) := by
      have := maxFormat_lt (p := p) (emax := emax)
      grind
    have := two_pow_lt_iff.mp h5
    omega

end Range

/-! ## The rounding of the format -/

section Format

variable {p : ℕ} {emin emax : ℤ}

theorem roundRNE_eq_some {q v : ℚ} :
    roundRNE p emin emax q = some v ↔
      v = rneU p emin q ∧ Rat.abs (rneU p emin q) ≤ maxFormat p emax := by
  unfold roundRNE
  split
  · rename_i h; simp only [Option.some.injEq]; constructor
    · intro e; exact ⟨e.symm, h⟩
    · intro e; exact e.1.symm
  · rename_i h; simp only [reduceCtorEq, false_iff]; intro e; exact h e.2

theorem roundRNE_isSome_iff {q : ℚ} :
    (roundRNE p emin emax q).isSome = true ↔ Rat.abs (rneU p emin q) ≤ maxFormat p emax := by
  unfold roundRNE
  split <;> simp_all

/-- **Round to nearest.** Every result is a value of the format, and no value of the format is
closer to the input. -/
theorem roundRNE_nearest (hp : 0 < p) (hle : emin ≤ emax) :
    RoundsToNearest (FormatValue p emin emax) (roundRNE p emin emax) := by
  intro q v h
  obtain ⟨rfl, hM⟩ := roundRNE_eq_some.mp h
  exact ⟨rneU_formatValue hp hle hM, fun w hw => rneU_nearest hp q hw.uValue⟩

/-- **The rounding succeeds on intervals**: between two inputs that do not overflow, nothing
overflows. -/
theorem roundRNE_intervals (hp : 0 < p) : RoundsOnIntervals (roundRNE p emin emax) := by
  intro a b q h1 h2 ha hb
  rw [roundRNE_isSome_iff] at ha hb ⊢
  have m1 := rneU_monotone (emin := emin) hp h1
  have m2 := rneU_monotone (emin := emin) hp h2
  rw [abs_le_iff] at ha hb ⊢
  grind

/-- Every input within the largest finite value is rounded without overflow. -/
theorem roundRNE_isSome (hp : 0 < p) (hle : emin ≤ emax) {q : ℚ}
    (hq : Rat.abs q ≤ maxFormat p emax) : (roundRNE p emin emax q).isSome = true := by
  rw [roundRNE_isSome_iff]
  have hM := rneU_of_uValue hp (maxFormat_uValue (emin := emin) (p := p) hle)
  have hM' := rneU_of_uValue hp (maxFormat_uValue (emin := emin) (p := p) hle).neg
  rw [abs_le_iff] at hq ⊢
  obtain ⟨l, u⟩ := hq
  have m1 := rneU_monotone (emin := emin) hp l
  have m2 := rneU_monotone (emin := emin) hp u
  rw [hM'] at m1
  rw [hM] at m2
  exact ⟨m1, m2⟩

/-- **The standard model**: `|fl(q) − q| ≤ 2^-p |q| + 2^(emin − p)`. -/
theorem roundRNE_within : RoundWithin (roundRNE p emin emax) (2 ^ (-(p : ℤ))) (2 ^ (emin - p)) := by
  intro q v h
  obtain ⟨rfl, _⟩ := roundRNE_eq_some.mp h
  exact rneU_error q

/-- A value of the format rounds to itself. -/
theorem roundRNE_of_formatValue (hp : 0 < p) {v : ℚ} (hv : FormatValue p emin emax v) :
    roundRNE p emin emax v = some v := by
  unfold roundRNE
  rw [rneU_of_uValue hp hv.uValue, if_pos (formatValue_abs_le hv)]

end Format

/-! ## Binary64 and binary32 -/

/-- Binary64 round to nearest even, as a value; `none` on overflow. -/
def rne64 : ℚ → Option ℚ := roundRNE 53 (-1022) 1023

/-- Binary32 round to nearest even, as a value; `none` on overflow. -/
def rne32Q : ℚ → Option ℚ := roundRNE 24 (-126) 127

/-- The finite binary64 values. -/
abbrev Binary64Value : ℚ → Prop := FormatValue 53 (-1022) 1023

/-- The finite binary32 values. -/
abbrev Binary32Value : ℚ → Prop := FormatValue 24 (-126) 127

theorem rne64_nearest : RoundsToNearest Binary64Value rne64 :=
  roundRNE_nearest (by decide) (by decide)

theorem rne64_intervals : RoundsOnIntervals rne64 := roundRNE_intervals (by decide)

theorem rne64_within : RoundWithin rne64 (2 ^ (-53 : ℤ)) (2 ^ (-1075 : ℤ)) := by
  have h := roundRNE_within (p := 53) (emin := -1022) (emax := 1023)
  have e1 : (-((53 : ℕ) : ℤ)) = (-53 : ℤ) := by omega
  have e2 : (-1022 : ℤ) - ((53 : ℕ) : ℤ) = -1075 := by omega
  rw [e1, e2] at h
  exact h

theorem rne64_isSome {q : ℚ} (hq : Rat.abs q ≤ maxFormat 53 1023) : (rne64 q).isSome = true :=
  roundRNE_isSome (by decide) (by decide) hq

theorem rne64_of_value {v : ℚ} (hv : Binary64Value v) : rne64 v = some v :=
  roundRNE_of_formatValue (by decide) hv

/-- Binary64 values are multiples of `2^-1074`. -/
theorem binary64Value_gridMultiple {v : ℚ} (hv : Binary64Value v) : GridMultiple (-1074) v := by
  have h := formatValue_gridMultiple hv
  have e : (-1022 : ℤ) - (((53 : ℕ) : ℤ) - 1) = -1074 := by omega
  rw [e] at h
  exact h

/-- Binary64 values are below `2^1024`. -/
theorem binary64Value_abs_lt {v : ℚ} (hv : Binary64Value v) : Rat.abs v < 2 ^ (1024 : ℤ) :=
  formatValue_abs_lt hv

theorem rne32Q_nearest : RoundsToNearest Binary32Value rne32Q :=
  roundRNE_nearest (by decide) (by decide)

theorem rne32Q_intervals : RoundsOnIntervals rne32Q := roundRNE_intervals (by decide)

theorem rne32Q_within : RoundWithin rne32Q (2 ^ (-24 : ℤ)) (2 ^ (-150 : ℤ)) := by
  have h := roundRNE_within (p := 24) (emin := -126) (emax := 127)
  have e1 : (-((24 : ℕ) : ℤ)) = (-24 : ℤ) := by omega
  have e2 : (-126 : ℤ) - ((24 : ℕ) : ℤ) = -150 := by omega
  rw [e1, e2] at h
  exact h

theorem rne32Q_of_value {v : ℚ} (hv : Binary32Value v) : rne32Q v = some v :=
  roundRNE_of_formatValue (by decide) hv

/-- Binary32 values are multiples of `2^-149`. -/
theorem binary32Value_gridMultiple {v : ℚ} (hv : Binary32Value v) : GridMultiple (-149) v := by
  have h := formatValue_gridMultiple hv
  have e : (-126 : ℤ) - (((24 : ℕ) : ℤ) - 1) = -149 := by omega
  rw [e] at h
  exact h

/-! ## Examples -/

/-- `1 + 2^-53` is halfway between `1` and `1 + 2^-52`; the tie goes to the even `1`. -/
example : rne64 (1 + 2 ^ (-53 : ℤ)) = some 1 := by decide +kernel

/-- `1 + 3 · 2^-54` is nearer to `1 + 2^-52`. -/
example : rne64 (1 + 3 * 2 ^ (-54 : ℤ)) = some (1 + 2 ^ (-52 : ℤ)) := by decide +kernel

/-- A third of the smallest subnormal rounds to zero; two thirds round up to it. -/
example : rne64 (2 ^ (-1074 : ℤ) / 3) = some 0 := by decide +kernel
example : rne64 (2 * 2 ^ (-1074 : ℤ) / 3) = some (2 ^ (-1074 : ℤ)) := by decide +kernel

/-- Just below the overflow threshold `maxFormat + 2^970`, the result is the largest finite value;
at the threshold and beyond, it overflows. -/
example : rne64 (maxFormat 53 1023 + 2 ^ (969 : ℤ)) = some (maxFormat 53 1023) := by decide +kernel
example : rne64 (maxFormat 53 1023 + 2 ^ (970 : ℤ)) = none := by decide +kernel
example : rne64 (2 ^ (1024 : ℤ)) = none := by decide +kernel

/-- Negative ties also go to even. -/
example : rne64 (-(1 + 2 ^ (-52 : ℤ) + 2 ^ (-53 : ℤ))) = some (-(1 + 2 ^ (-51 : ℤ))) := by
  decide +kernel

/-- Binary32: `1/3` rounds to `0x3EAAAAAB`, `11184811 · 2^-25`. -/
example : rne32Q (1 / 3) = some (11184811 / 33554432) := by decide +kernel

end Ozaki
