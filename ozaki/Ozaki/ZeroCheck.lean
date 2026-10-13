import Ozaki.BoundedOzaki
import Ozaki.SignedZero

/-! # Exact-zero results without the exact fallback

The rounding test of correctly rounded Ozaki-I uses the slicing bound
`B = (s + 1) k 2^(E + F − s(b+1))` (`ozaki1Bound`). When every product `xᵢ yᵢ` is zero but `x` and
`y` are not, as for sparse rows and columns with disjoint supports, the slice products add up to
`H = 0` while `B > 0`, so `H ± B` round to different values and the entry always takes the exact
fallback.

The slicing error comes only from indices where both entries are nonzero: a slice coefficient or a
residual of `x` vanishes wherever `x` does (`split_vanishes`), and likewise for `y`. So `k` in the
bound can be replaced by the **number of nonzero positions** `N = #{i : xᵢ ≠ 0 ∧ yᵢ ≠ 0}`
(`exactTerms_error_overlap`):

  `|x · y − H| ≤ (s + 1) N 2^(E + F − s(b+1))`.

`N` is the integer dot product of the `0`/`1` support indicators of `x` and `y`, which every exact
matrix multiplier computes exactly (`overlapMultiplier_eq`): one extra dot product per output entry
(for a GEMM, one extra product of `0`/`1` matrices), whatever the slice count. The bound is never
larger than the normwise one (`N ≤ k`, `supportOverlap_le_length`), equals it on dense data, and is
`0` exactly when every product is zero (`supportOverlap_eq_zero_iff`). With a truncated sum, the
truncation loss is charged only to the nonzero slice products (`truncatedSum_error_nonzero`).

* `ozaki1CREZ`, `ozaki1CRWZ`: correctly rounded Ozaki-I with the bound that counts only nonzero
  positions, with the exact sum or a `W`-bit truncated sum, and the exact fallback on the matrix
  multiplier (`ozaki1CREZ_eq`, `ozaki1CRWZ_eq`);
* **the rounding test succeeds on exact zeros**: when every product is zero, the first test returns
  `0`, whatever the exact fallback would return (`ozaki1CREZ_zero`, `ozaki1CRWZ_zero`);
* `ozaki1CRBZ`: the same in bounded integer registers (`ozaki1TestBZ_eq`, `ozaki1CRBZ_eq`);
* `ozaki1CRWSZ`: with IEEE signed zeros (`ozaki1CRWSZ_eq`); an entry whose products are all zero
  gets the sign `crSigned` specifies without the exact fallback (`ozaki1CRWSZ_zero`). -/

local notation "ℕ" => Nat
local notation "ℤ" => Int
local notation "ℚ" => Rat

namespace Ozaki

/-! ## Supports -/

/-- `v` vanishes wherever `x` does, entry by entry (and has its length). -/
inductive VanishesWith : List ℚ → List ℚ → Prop
  | nil : VanishesWith [] []
  | cons {a c : ℚ} {v x : List ℚ} : (c = 0 → a = 0) → VanishesWith v x →
      VanishesWith (a :: v) (c :: x)

theorem vanishesWith_refl : ∀ x : List ℚ, VanishesWith x x
  | [] => VanishesWith.nil
  | _ :: x => VanishesWith.cons (fun h => h) (vanishesWith_refl x)

theorem VanishesWith.trans {u v x : List ℚ} (h1 : VanishesWith u v) (h2 : VanishesWith v x) :
    VanishesWith u x := by
  induction h1 generalizing x with
  | nil => cases h2; exact VanishesWith.nil
  | cons ha _ ih =>
    cases h2 with
    | cons hb hr => exact VanishesWith.cons (fun hc => ha (hb hc)) (ih hr)

theorem vanishesWith_map {f : ℚ → ℚ} (hf : f 0 = 0) : ∀ x : List ℚ, VanishesWith (x.map f) x
  | [] => VanishesWith.nil
  | a :: x => VanishesWith.cons (fun h => by rw [h, hf]) (vanishesWith_map hf x)

theorem zero_div_two_pow (g : ℤ) : (0 : ℚ) / 2 ^ g = 0 := by rw [Rat.div_def, Rat.zero_mul]

/-- A slice's coefficients and what it leaves vanish where `x` does. -/
theorem split_vanishes (b : ℕ) :
    ∀ (s : ℕ) (prev : ℤ) (x : List ℚ), VanishesWith (splitFrom b s prev x).2 x ∧
      ∀ sl ∈ (splitFrom b s prev x).1, VanishesWith (ofInts sl.coeffs) x
  | 0, _, x => ⟨vanishesWith_refl x, by simp [splitFrom]⟩
  | s + 1, prev, x => by
    have hrest : VanishesWith (sliceRest (sliceGrid b prev x) x) x :=
      vanishesWith_map (by
        rw [zero_div_two_pow, roundNearestEven_zero, Rat.intCast_zero, Rat.zero_mul]; grind) x
    have hcoef : VanishesWith (ofInts (sliceCoeffs (sliceGrid b prev x) x)) x := by
      unfold ofInts sliceCoeffs
      rw [List.map_map]
      exact vanishesWith_map (f := fun a => ((roundNearestEven (a / 2 ^ sliceGrid b prev x) : ℤ) : ℚ))
        (by rw [zero_div_two_pow, roundNearestEven_zero]; rfl) x
    obtain ⟨ih1, ih2⟩ := split_vanishes b s (sliceGrid b prev x) (sliceRest (sliceGrid b prev x) x)
    refine ⟨ih1.trans hrest, ?_⟩
    intro sl hsl
    simp only [splitFrom, List.mem_cons] at hsl
    rcases hsl with rfl | hsl
    · exact hcoef
    · exact (ih2 sl hsl).trans hrest

/-! ## The number of nonzero positions -/

/-- The support indicator: `1` where `xᵢ ≠ 0`, `0` where `xᵢ = 0`. -/
def nzVec (x : List ℚ) : List ℤ := x.map fun a => if a = 0 then 0 else 1

/-- **The number of nonzero positions** `#{i : xᵢ ≠ 0 ∧ yᵢ ≠ 0}`, the integer dot product of the
indicators. -/
def supportOverlap (x y : List ℚ) : ℤ := dotZ (nzVec x) (nzVec y)

theorem supportOverlap_cons (a c : ℚ) (x y : List ℚ) :
    supportOverlap (a :: x) (c :: y) = (if a = 0 then 0 else 1) * (if c = 0 then 0 else 1) + supportOverlap x y := by
  simp [supportOverlap, nzVec]

theorem supportOverlap_nil_left (y : List ℚ) : supportOverlap [] y = 0 := by simp [supportOverlap, nzVec]

theorem supportOverlap_nil_right (x : List ℚ) : supportOverlap x [] = 0 := by simp [supportOverlap, nzVec]

theorem supportOverlap_nonneg : ∀ x y : List ℚ, 0 ≤ supportOverlap x y
  | [], y => by rw [supportOverlap_nil_left]; omega
  | _ :: _, [] => by rw [supportOverlap_nil_right]; omega
  | a :: x, c :: y => by
    rw [supportOverlap_cons]
    have := supportOverlap_nonneg x y
    split <;> split <;> omega

/-- The number of nonzero positions is at most the length. -/
theorem supportOverlap_le_length : ∀ x y : List ℚ, supportOverlap x y ≤ x.length
  | [], y => by rw [supportOverlap_nil_left]; simp
  | _ :: _, [] => by rw [supportOverlap_nil_right, List.length_cons]; omega
  | a :: x, c :: y => by
    rw [supportOverlap_cons, List.length_cons]
    have := supportOverlap_le_length x y
    split <;> split <;> omega

/-- Every product `xᵢ yᵢ` is zero. -/
def ProductsZero (x y : List ℚ) : Prop := ∀ p ∈ List.zipWith (· * ·) x y, p = 0

/-- **The number of nonzero positions is zero exactly when every product is zero.** -/
theorem supportOverlap_eq_zero_iff : ∀ x y : List ℚ, supportOverlap x y = 0 ↔ ProductsZero x y
  | [], y => by simp [supportOverlap_nil_left, ProductsZero]
  | _ :: _, [] => by simp [supportOverlap_nil_right, ProductsZero]
  | a :: x, c :: y => by
    rw [supportOverlap_cons]
    have ih := supportOverlap_eq_zero_iff x y
    have hn := supportOverlap_nonneg x y
    unfold ProductsZero at ih ⊢
    simp only [List.zipWith_cons_cons, List.mem_cons, forall_eq_or_imp]
    constructor
    · intro h
      have hz : supportOverlap x y = 0 := by split at h <;> split at h <;> omega
      refine ⟨?_, ih.mp hz⟩
      by_cases ha : a = 0
      · rw [ha, Rat.zero_mul]
      · by_cases hc : c = 0
        · rw [hc, Rat.mul_zero]
        · rw [if_neg ha, if_neg hc] at h; omega
    · rintro ⟨hp, hr⟩
      rw [ih.mpr hr]
      have : a = 0 ∨ c = 0 := by
        rcases Rat.mul_eq_zero.mp hp with h | h
        · exact Or.inl h
        · exact Or.inr h
      rcases this with h | h <;> simp [h]

/-- **A dot product of vectors supported where `x` and `y` are**, with entries at most `A` and `B`,
is at most `N A B` for the number `N` of nonzero positions. -/
theorem abs_dot_le_overlap {A B : ℚ} (hA : 0 ≤ A) (hB : 0 ≤ B) {a x : List ℚ}
    (hax : VanishesWith a x) : ∀ {b y : List ℚ}, VanishesWith b y → (∀ c ∈ a, Rat.abs c ≤ A) →
      (∀ c ∈ b, Rat.abs c ≤ B) → Rat.abs (dot a b) ≤ (supportOverlap x y : ℚ) * (A * B) := by
  induction hax with
  | nil =>
    intro b y _ _ _
    rw [dot_nil_left, supportOverlap_nil_left, abs_zero]; simp
  | @cons a0 c0 a x h0 _ ih =>
    intro b y hby ha hb
    cases hby with
    | nil =>
      rw [dot_nil_right, supportOverlap_nil_right, abs_zero]; simp
    | @cons b0 d0 b y h1 hr =>
      rw [dot_cons, supportOverlap_cons]
      have hAB := Rat.mul_nonneg hA hB
      have hrest := ih hr (fun c hc => ha c (by simp [hc])) (fun c hc => hb c (by simp [hc]))
      have hsum := abs_add_le (a0 * b0) (dot a b)
      have hprod : Rat.abs (a0 * b0) ≤
          ((((if c0 = 0 then 0 else 1) * (if d0 = 0 then 0 else 1) : ℤ)) : ℚ) * (A * B) := by
        by_cases hc : c0 = 0
        · rw [h0 hc, Rat.zero_mul, abs_zero, if_pos hc]; simp
        · by_cases hd : d0 = 0
          · rw [h1 hd, Rat.mul_zero, abs_zero, if_pos hd]; simp
          · rw [if_neg hc, if_neg hd]
            have := mul_le_mul_abs (ha a0 (by simp)) (hb b0 (by simp))
            simpa using this
      rw [Rat.intCast_add, Rat.add_mul]
      grind

/-- A dot product of vectors supported where `x` and `y` are vanishes when `x` and `y` have
disjoint supports. -/
theorem dot_eq_zero_of_overlap {a x b y : List ℚ} (hax : VanishesWith a x) (hby : VanishesWith b y)
    (hz : supportOverlap x y = 0) : dot a b = 0 := by
  have := abs_dot_le_overlap (A := maxAbs a) (B := maxAbs b) (maxAbs_nonneg a) (maxAbs_nonneg b)
    hax hby (fun _ hc => abs_le_maxAbs hc) (fun _ hc => abs_le_maxAbs hc)
  rw [hz] at this
  simp only [Rat.intCast_zero, Rat.zero_mul] at this
  exact abs_eq_zero.mp (Rat.le_antisymm this (abs_nonneg _))

/-! ## The slicing error with the number of nonzero positions -/

/-- **Slicing error with the number of nonzero positions.**
`|x · y − Σ terms| ≤ (s + 1) N 2^(E + F − s(b+1))`, with
`N` the number of indices where both `xᵢ` and `yᵢ` are nonzero. -/
theorem exactTerms_error_overlap (b s : ℕ) (x y : List ℚ) :
    Rat.abs (dot x y - (exactTerms b s x y).sum) ≤
      ((s + 1 : ℕ) : ℚ) * (supportOverlap x y : ℚ) * 2 ^ (splitExp b x + splitExp b y - s * (b + 1)) := by
  rw [dot_eq_exactTerms_add b s x y]
  generalize hB : (2 : ℚ) ^ (splitExp b x + splitExp b y - s * (b + 1)) = B
  have hBpos : 0 < B := by rw [← hB]; exact two_pow_pos _
  have hk : (0 : ℚ) ≤ (supportOverlap x y : ℚ) := by
    have := supportOverlap_nonneg x y
    exact Rat.intCast_nonneg.mpr this
  -- the residual of `x` against `y`
  have h1 : Rat.abs (dot (split b s x).2 y) ≤ (supportOverlap x y : ℚ) * B := by
    have := abs_dot_le_overlap (Rat.le_of_lt (two_pow_pos _)) (Rat.le_of_lt (two_pow_pos _))
      (split_vanishes b s b x).1 (vanishesWith_refl y) (split_residual_le b s x)
      (abs_le_two_pow_splitExp b y)
    rw [← two_pow_add] at this
    rw [← hB]
    have he : splitExp b x - s * (b + 1) + splitExp b y = splitExp b x + splitExp b y -
      s * (b + 1) := by omega
    rwa [he] at this
  -- each slice of `x` against a residual of `y`
  have h2 : ∀ t ∈ List.range s, Rat.abs (2 ^ ((split b s x).1.getD t default).grid *
      dot (ofInts ((split b s x).1.getD t default).coeffs) (split b (s - t) y).2) ≤
        (supportOverlap x y : ℚ) * B := by
    intro t ht
    have htl := List.mem_range.mp ht
    have hmem := getD_mem (l := (split b s x).1) (t := t) (by rw [(split_length b s x).1]; exact htl)
    generalize hsl : (split b s x).1.getD t default = sl at hmem
    have hgrid := split_grid_le b s x t sl (by
      rw [← hsl, List.getD_eq_getElem?_getD,
        List.getElem?_eq_getElem (by rw [(split_length b s x).1]; exact htl)]; rfl)
    have hc : ∀ a ∈ ofInts sl.coeffs, Rat.abs a ≤ (2 : ℚ) ^ (b : ℤ) := by
      intro a ha
      obtain ⟨q, hq, rfl⟩ := List.mem_map.mp ha
      rw [two_pow_natCast]
      exact abs_intCast_le (split_coeff_bound b s x sl hmem q hq)
    have hd := abs_dot_le_overlap (Rat.le_of_lt (two_pow_pos _)) (Rat.le_of_lt (two_pow_pos _))
      ((split_vanishes b s b x).2 sl hmem) (split_vanishes b (s - t) b y).1 hc
      (split_residual_le b (s - t) y)
    rw [← two_pow_add] at hd
    rw [abs_mul, abs_two_pow]
    have hm := Rat.mul_le_mul_of_nonneg_left hd (Rat.le_of_lt (two_pow_pos sl.grid))
    refine Rat.le_trans hm ?_
    rw [← hB]
    have hexp : sl.grid + ((b : ℤ) + (splitExp b y - ((s - t : ℕ) : ℤ) * (b + 1))) ≤
        splitExp b x + splitExp b y - s * (b + 1) := by
      have hst : ((s - t : ℕ) : ℤ) = s - t := by omega
      rw [hst]
      have : ((s : ℤ) - t) * (b + 1) = s * (b + 1) - t * (b + 1) := Int.sub_mul _ _ _
      omega
    have := two_pow_le hexp
    rw [two_pow_add] at this
    have := Rat.mul_le_mul_of_nonneg_left this hk
    grind
  have h3 := sum_le_length_mul h2
  rw [List.length_range] at h3
  have h4 := abs_sum_le (List.range s) (fun t => 2 ^ ((split b s x).1.getD t default).grid *
    dot (ofInts ((split b s x).1.getD t default).coeffs) (split b (s - t) y).2)
  have h5 := abs_add_le (dot (split b s x).2 y) ((List.range s).map fun t =>
    2 ^ ((split b s x).1.getD t default).grid *
      dot (ofInts ((split b s x).1.getD t default).coeffs) (split b (s - t) y).2).sum
  have h6 : (exactTerms b s x y).sum + dot (split b s x).2 y +
      ((List.range s).map fun t => 2 ^ ((split b s x).1.getD t default).grid *
        dot (ofInts ((split b s x).1.getD t default).coeffs) (split b (s - t) y).2).sum -
      (exactTerms b s x y).sum = dot (split b s x).2 y +
      ((List.range s).map fun t => 2 ^ ((split b s x).1.getD t default).grid *
        dot (ofInts ((split b s x).1.getD t default).coeffs) (split b (s - t) y).2).sum := by grind
  rw [h6, natCast_succ]
  grind

theorem getD_mem_or [Inhabited α] (l : List α) (i : ℕ) :
    l.getD i default ∈ l ∨ l.getD i default = default := by
  by_cases h : i < l.length
  · exact Or.inl (getD_mem h)
  · right; rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)]; rfl

/-- With disjoint supports the product of a slice of `x` and a slice of `y` is zero. -/
theorem slice_dotZ_zero {b s : ℕ} {x y : List ℚ} (hz : supportOverlap x y = 0) {sl sl' : Slice}
    (h1 : sl ∈ (split b s x).1 ∨ sl = default) (h2 : sl' ∈ (split b s y).1 ∨ sl' = default) :
    dotZ sl.coeffs sl'.coeffs = 0 := by
  rcases h1 with h1 | rfl
  · rcases h2 with h2 | rfl
    · have := dot_eq_zero_of_overlap ((split_vanishes b s b x).2 sl h1)
        ((split_vanishes b s b y).2 sl' h2) hz
      rw [dot_ofInts] at this
      exact_mod_cast this
    · exact dotZ_nil_right _
  · exact dotZ_nil_left _

/-- With disjoint supports every slice product is zero. -/
theorem exactTerms_zero_of_overlap {b s : ℕ} {x y : List ℚ} (hz : supportOverlap x y = 0) :
    ∀ t ∈ exactTerms b s x y, t = 0 := by
  intro t ht
  obtain ⟨⟨u, v⟩, _, rfl⟩ := List.mem_map.mp ht
  unfold exactTerm
  rw [slice_dotZ_zero hz (getD_mem_or _ _) (getD_mem_or _ _)]
  simp


/-! ## The number of nonzero positions on the matrix multiplier -/

/-- The number of nonzero positions from the matrix multiplier: the product of the `0`/`1` support
indicators, read back as an integer. -/
def overlapMultiplier (mult : MatrixMultiplier) (x y : List ℚ) : Option ℤ :=
  (mult (nzVec x) (nzVec y)).bind fun v => if v.den = 1 then some v.num else none

theorem nzVec_length (x : List ℚ) : (nzVec x).length = x.length := by simp [nzVec]

theorem nzVec_natAbs_le (x : List ℚ) : ∀ z ∈ nzVec x, z.natAbs ≤ 1 := by
  intro z hz
  obtain ⟨a, _, rfl⟩ := List.mem_map.mp hz
  split <;> simp

/-- **Every exact matrix multiplier computes the number of nonzero positions exactly**: the
indicators are `0` or `1`, so their products total at most `k`. -/
theorem overlapMultiplier_eq {mult : MatrixMultiplier} {b bound : ℕ} (hmult : mult.ExactOn b bound) {x y : List ℚ}
    (hlen : x.length = y.length) (hbound : x.length * (2 ^ b * 2 ^ b) ≤ bound) :
    overlapMultiplier mult x y = some (supportOverlap x y) := by
  have h1 : ∀ z ∈ nzVec x, z.natAbs ≤ 2 ^ b := fun z hz =>
    Nat.le_trans (nzVec_natAbs_le x z hz) Nat.one_le_two_pow
  have h2 : ∀ z ∈ nzVec y, z.natAbs ≤ 2 ^ b := fun z hz =>
    Nat.le_trans (nzVec_natAbs_le y z hz) Nat.one_le_two_pow
  have hd : dotAbs (nzVec x) (nzVec y) ≤ bound := by
    refine Nat.le_trans (dotAbs_le _ _ 1 1 (nzVec_natAbs_le x) (nzVec_natAbs_le y)) ?_
    rw [nzVec_length]
    refine Nat.le_trans ?_ hbound
    exact Nat.mul_le_mul_left _ (Nat.mul_le_mul Nat.one_le_two_pow Nat.one_le_two_pow)
  have he : mult (nzVec x) (nzVec y) = some ((supportOverlap x y : ℤ) : ℚ) :=
    hmult _ _ (by rw [nzVec_length, nzVec_length, hlen]) h1 h2 hd
  unfold overlapMultiplier
  rw [he, Option.bind_some, if_pos (Rat.den_intCast _), Rat.num_intCast]

/-! ## The rounding test with the number of nonzero positions -/

/-- The slicing bound with the number `N` of nonzero positions in place of `k`. -/
def ozaki1BoundZ (b s : ℕ) (N : ℤ) (x y : List ℚ) : ℚ :=
  ((s + 1 : ℕ) : ℚ) * (N : ℚ) * 2 ^ (splitExp b x + splitExp b y - s * (b + 1))

/-- The bound that counts only nonzero positions is never larger than the normwise one. -/
theorem ozaki1BoundZ_le (b s : ℕ) (x y : List ℚ) :
    ozaki1BoundZ b s (supportOverlap x y) x y ≤ ozaki1Bound b s x y := by
  unfold ozaki1BoundZ ozaki1Bound
  have h := supportOverlap_le_length x y
  have hq : (supportOverlap x y : ℚ) ≤ (x.length : ℚ) := by
    have : ((supportOverlap x y : ℤ) : ℚ) ≤ (((x.length : ℕ) : ℤ) : ℚ) := Rat.intCast_le_intCast.mpr h
    rwa [Rat.intCast_natCast] at this
  have hs : (0 : ℚ) ≤ ((s + 1 : ℕ) : ℚ) := Rat.natCast_nonneg
  have hp := two_pow_pos (splitExp b x + splitExp b y - s * (b + 1))
  have := Rat.mul_le_mul_of_nonneg_left hq hs
  exact Rat.mul_le_mul_of_nonneg_right this (Rat.le_of_lt hp)

/-- The enclosure from `s` slices with the number `N` of nonzero positions: the slice products
added exactly. -/
def ozaki1EnclosureZ (mult : MatrixMultiplier) (b s : ℕ) (N : ℤ) (x y : List ℚ) : Option (ℚ × ℚ) :=
  (ozaki1 mult exactAdd b s x y).map fun H => (H, ozaki1BoundZ b s N x y)

/-- The number of nonzero terms. -/
def nonzeroCount (ts : List ℚ) : ℕ := ts.countP fun t => t ≠ 0

/-- The enclosure from `s` slices with a `W`-bit truncated sum and the number of nonzero positions:
the truncation loss is charged to the nonzero slice products only. -/
def ozaki1TruncatedEnclosureZ (mult : MatrixMultiplier) (b s W : ℕ) (N : ℤ) (x y : List ℚ) :
    Option (ℚ × ℚ) :=
  (ozaki1Terms mult b s x y).map fun ts =>
    (truncatedSum (truncationGrid b W x y) ts,
      ozaki1BoundZ b s N x y + (nonzeroCount ts : ℚ) * 2 ^ truncationGrid b W x y)

theorem floorGrid_zero (q : ℤ) : floorGrid q 0 = 0 := by
  unfold floorGrid
  rw [Rat.zero_mul]
  have : (0 : ℚ).floor = 0 := rfl
  rw [this, Rat.intCast_zero, Rat.zero_mul]

/-- **The truncation loses nothing on zero terms**:
`|Σ tᵢ − truncated sum| ≤ (number of nonzero tᵢ) 2^q`. -/
theorem truncatedSum_error_nonzero (q : ℤ) : ∀ ts : List ℚ,
    Rat.abs (ts.sum - truncatedSum q ts) ≤ (nonzeroCount ts : ℚ) * 2 ^ q
  | [] => by
    simp only [truncatedSum, List.map_nil, List.sum_nil, nonzeroCount, List.countP_nil]
    rw [show (0 : ℚ) - 0 = 0 by grind, abs_zero]; simp
  | t :: ts => by
    have ih := truncatedSum_error_nonzero q ts
    have hsplit : (t :: ts).sum - truncatedSum q (t :: ts) =
        (t - floorGrid q t) + (ts.sum - truncatedSum q ts) := by
      simp only [truncatedSum, List.sum_cons, List.map_cons]; grind
    rw [hsplit]
    refine Rat.le_trans (abs_add_le _ _) ?_
    by_cases ht : t = 0
    · subst ht
      rw [floorGrid_zero, show (0 : ℚ) - 0 = 0 by grind, abs_zero]
      have : nonzeroCount (0 :: ts) = nonzeroCount ts := by simp [nonzeroCount]
      rw [this]; grind
    · obtain ⟨h1, h2⟩ := floorGrid_error q t
      have : nonzeroCount (t :: ts) = nonzeroCount ts + 1 := by simp [nonzeroCount, ht]
      rw [this, natCast_succ, abs_of_nonneg h1]; grind

/-- On an exact matrix multiplier, the enclosure with the number of nonzero positions contains
`x · y`. -/
theorem ozaki1EnclosureZ_sound {mult : MatrixMultiplier} {b bound : ℕ} (hmult : mult.ExactOn b bound)
    (s : ℕ) {x y : List ℚ} (hlen : x.length = y.length)
    (hbound : x.length * (2 ^ b * 2 ^ b) ≤ bound) {H B : ℚ}
    (he : ozaki1EnclosureZ mult b s (supportOverlap x y) x y = some (H, B)) : Rat.abs (dot x y - H) ≤ B := by
  unfold ozaki1EnclosureZ at he
  rw [ozaki1_eq_sumWith hmult exactAdd s hlen hbound, sumWith_exactAdd] at he
  simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at he
  obtain ⟨rfl, rfl⟩ := he
  rw [show (0 : ℚ) + (exactTerms b s x y).sum = (exactTerms b s x y).sum by grind]
  exact exactTerms_error_overlap b s x y

/-- On an exact matrix multiplier, the truncated enclosure with the number of nonzero positions
contains `x · y`. -/
theorem ozaki1TruncatedEnclosureZ_sound {mult : MatrixMultiplier} {b bound : ℕ} (hmult : mult.ExactOn b bound)
    (s W : ℕ) {x y : List ℚ} (hlen : x.length = y.length)
    (hbound : x.length * (2 ^ b * 2 ^ b) ≤ bound) {H B : ℚ}
    (he : ozaki1TruncatedEnclosureZ mult b s W (supportOverlap x y) x y = some (H, B)) :
    Rat.abs (dot x y - H) ≤ B := by
  unfold ozaki1TruncatedEnclosureZ at he
  rw [ozaki1Terms_eq hmult s hlen hbound] at he
  simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at he
  obtain ⟨rfl, rfl⟩ := he
  have h1 := exactTerms_error_overlap b s x y
  have h2 := truncatedSum_error_nonzero (truncationGrid b W x y) (exactTerms b s x y)
  have hsplit : dot x y - truncatedSum (truncationGrid b W x y) (exactTerms b s x y) =
      (dot x y - (exactTerms b s x y).sum) +
        ((exactTerms b s x y).sum - truncatedSum (truncationGrid b W x y) (exactTerms b s x y)) := by
    grind
  rw [hsplit]
  refine Rat.le_trans (abs_add_le _ _) ?_
  unfold ozaki1BoundZ
  grind

/-! ## The schemes -/

/-- The enclosures for the slice counts `ss`, all with the number of nonzero positions, which the
matrix multiplier computes once. -/
def overlapTests (mult : MatrixMultiplier) (enc : ℕ → ℤ → Option (ℚ × ℚ)) (ss : List ℕ) (x y : List ℚ) :
    List (Option (ℚ × ℚ)) :=
  match overlapMultiplier mult x y with
  | some N => ss.map fun s => enc s N
  | none => []

theorem overlapTests_eq {mult : MatrixMultiplier} {b bound : ℕ} (hmult : mult.ExactOn b bound)
    (enc : ℕ → ℤ → Option (ℚ × ℚ)) (ss : List ℕ) {x y : List ℚ} (hlen : x.length = y.length)
    (hbound : x.length * (2 ^ b * 2 ^ b) ≤ bound) :
    overlapTests mult enc ss x y = ss.map fun s => enc s (supportOverlap x y) := by
  unfold overlapTests
  rw [overlapMultiplier_eq hmult hlen hbound]

/-- **Correctly rounded Ozaki-I with the bound that counts only nonzero positions**, the slice
products added exactly: slice counts `ss` in turn, then the exact fallback on the matrix
multiplier. -/
def ozaki1CREZ (mult : MatrixMultiplier) (rnd : ℚ → Option ℚ) (b : ℕ) (ss : List ℕ) (smax : ℕ)
    (x y : List ℚ) : Option ℚ :=
  roundingTest rnd (overlapTests mult (fun s N => ozaki1EnclosureZ mult b s N x y) ss x y)
    (ozaki1ExactFallback mult b smax x y)

/-- **Correctly rounded Ozaki-I with the bound that counts only nonzero positions and a `W`-bit
truncated sum.** -/
def ozaki1CRWZ (mult : MatrixMultiplier) (rnd : ℚ → Option ℚ) (b W : ℕ) (ss : List ℕ) (smax : ℕ)
    (x y : List ℚ) : Option ℚ :=
  roundingTest rnd (overlapTests mult (fun s N => ozaki1TruncatedEnclosureZ mult b s W N x y) ss x y)
    (ozaki1ExactFallback mult b smax x y)

theorem ozaki1CREZ_eq {R : ℚ → Prop} {rnd : ℚ → Option ℚ} (h : RoundsToNearest R rnd)
    (hI : RoundsOnIntervals rnd) {mult : MatrixMultiplier} {b bound : ℕ} (hmult : mult.ExactOn b bound)
    (ss : List ℕ) {smax : ℕ} {x y : List ℚ} (hlen : x.length = y.length)
    (hbound : x.length * (2 ^ b * 2 ^ b) ≤ bound)
    (hvanish : ∃ s ∈ List.range' 1 smax, residualsVanish b s x y = true) :
    ozaki1CREZ mult rnd b ss smax x y = rnd (dot x y) := by
  unfold ozaki1CREZ
  rw [overlapTests_eq hmult _ ss hlen hbound]
  apply roundingTest_eq h hI _ _ _ (ozaki1ExactFallback_eq hmult hlen hbound hvanish)
  intro c hc H B hcB
  obtain ⟨s, _, rfl⟩ := List.mem_map.mp hc
  exact ozaki1EnclosureZ_sound hmult s hlen hbound hcB

theorem ozaki1CRWZ_eq {R : ℚ → Prop} {rnd : ℚ → Option ℚ} (h : RoundsToNearest R rnd)
    (hI : RoundsOnIntervals rnd) {mult : MatrixMultiplier} {b bound : ℕ} (hmult : mult.ExactOn b bound)
    (W : ℕ) (ss : List ℕ) {smax : ℕ} {x y : List ℚ} (hlen : x.length = y.length)
    (hbound : x.length * (2 ^ b * 2 ^ b) ≤ bound)
    (hvanish : ∃ s ∈ List.range' 1 smax, residualsVanish b s x y = true) :
    ozaki1CRWZ mult rnd b W ss smax x y = rnd (dot x y) := by
  unfold ozaki1CRWZ
  rw [overlapTests_eq hmult _ ss hlen hbound]
  apply roundingTest_eq h hI _ _ _ (ozaki1ExactFallback_eq hmult hlen hbound hvanish)
  intro c hc H B hcB
  obtain ⟨s, _, rfl⟩ := List.mem_map.mp hc
  exact ozaki1TruncatedEnclosureZ_sound hmult s W hlen hbound hcB

/-! ## The rounding test succeeds on exact zeros -/

theorem sum_eq_zero_of_all {ts : List ℚ} (h : ∀ t ∈ ts, t = 0) : ts.sum = 0 := by
  induction ts with
  | nil => rfl
  | cons t ts ih =>
    rw [List.sum_cons, h t (by simp), ih (fun u hu => h u (by simp [hu]))]; grind

/-- With disjoint supports the enclosure is `(0, 0)`. -/
theorem ozaki1EnclosureZ_zero {mult : MatrixMultiplier} {b bound : ℕ} (hmult : mult.ExactOn b bound)
    (s : ℕ) {x y : List ℚ} (hlen : x.length = y.length)
    (hbound : x.length * (2 ^ b * 2 ^ b) ≤ bound) (hz : supportOverlap x y = 0) :
    ozaki1EnclosureZ mult b s (supportOverlap x y) x y = some (0, 0) := by
  unfold ozaki1EnclosureZ ozaki1BoundZ
  rw [ozaki1_eq_sumWith hmult exactAdd s hlen hbound, sumWith_exactAdd,
    sum_eq_zero_of_all (exactTerms_zero_of_overlap hz), hz]
  simp <;> grind

/-- With disjoint supports the truncated enclosure is `(0, 0)`: every slice product is zero, so
the truncation loses nothing. -/
theorem ozaki1TruncatedEnclosureZ_zero {mult : MatrixMultiplier} {b bound : ℕ} (hmult : mult.ExactOn b bound)
    (s W : ℕ) {x y : List ℚ} (hlen : x.length = y.length)
    (hbound : x.length * (2 ^ b * 2 ^ b) ≤ bound) (hz : supportOverlap x y = 0) :
    ozaki1TruncatedEnclosureZ mult b s W (supportOverlap x y) x y = some (0, 0) := by
  have hall := exactTerms_zero_of_overlap (b := b) (s := s) hz
  have hw : truncatedSum (truncationGrid b W x y) (exactTerms b s x y) = 0 := by
    unfold truncatedSum
    apply sum_eq_zero_of_all
    intro t ht
    obtain ⟨u, hu, rfl⟩ := List.mem_map.mp ht
    rw [hall u hu, floorGrid_zero]
  have hn : nonzeroCount (exactTerms b s x y) = 0 := by
    unfold nonzeroCount
    rw [List.countP_eq_zero]
    intro t ht; simp [hall t ht]
  unfold ozaki1TruncatedEnclosureZ ozaki1BoundZ
  rw [ozaki1Terms_eq hmult s hlen hbound, Option.map_some, hw, hn, hz]
  simp <;> grind

theorem roundEnclosure_zero {rnd : ℚ → Option ℚ} (h0 : rnd 0 = some 0) :
    roundEnclosure rnd 0 0 = some 0 := by
  unfold roundEnclosure
  rw [show (0 : ℚ) - 0 = 0 by grind, show (0 : ℚ) + 0 = 0 by grind, h0]
  simp

/-- **The first test succeeds on exact zeros**: when every product `xᵢ yᵢ` is zero, `ozaki1CREZ`
returns `0` from its first slice count, whatever the remaining tests and the exact fallback would
return. -/
theorem ozaki1CREZ_zero {rnd : ℚ → Option ℚ} (h0 : rnd 0 = some 0) {mult : MatrixMultiplier}
    {b bound : ℕ} (hmult : mult.ExactOn b bound) (s : ℕ) (ss : List ℕ) {x y : List ℚ}
    (hlen : x.length = y.length) (hbound : x.length * (2 ^ b * 2 ^ b) ≤ bound)
    (hz : ProductsZero x y) (exact : Option ℚ) :
    roundingTest rnd (overlapTests mult (fun s N => ozaki1EnclosureZ mult b s N x y) (s :: ss) x y)
      exact = some 0 := by
  have hz' := (supportOverlap_eq_zero_iff x y).mpr hz
  rw [overlapTests_eq hmult _ _ hlen hbound, List.map_cons]
  unfold roundingTest
  rw [ozaki1EnclosureZ_zero hmult s hlen hbound hz', Option.bind_some, roundEnclosure_zero h0]

theorem ozaki1CRWZ_zero {rnd : ℚ → Option ℚ} (h0 : rnd 0 = some 0) {mult : MatrixMultiplier}
    {b bound : ℕ} (hmult : mult.ExactOn b bound) (s W : ℕ) (ss : List ℕ) {x y : List ℚ}
    (hlen : x.length = y.length) (hbound : x.length * (2 ^ b * 2 ^ b) ≤ bound)
    (hz : ProductsZero x y) (exact : Option ℚ) :
    roundingTest rnd (overlapTests mult (fun s N => ozaki1TruncatedEnclosureZ mult b s W N x y) (s :: ss)
      x y) exact = some 0 := by
  have hz' := (supportOverlap_eq_zero_iff x y).mpr hz
  rw [overlapTests_eq hmult _ _ hlen hbound, List.map_cons]
  unfold roundingTest
  rw [ozaki1TruncatedEnclosureZ_zero hmult s W hlen hbound hz', Option.bind_some,
    roundEnclosure_zero h0]

/-! ## The rounding test in bounded integers -/

theorem tval_ne_zero_iff (t : ℤ × ℤ) : tval t ≠ 0 ↔ t.1 ≠ 0 := by
  unfold tval
  have hp := two_pow_pos t.2
  constructor
  · intro h h1; apply h; rw [h1]; simp
  · intro h h1
    rcases Rat.mul_eq_zero.mp h1 with h2 | h2
    · exact h (by exact_mod_cast h2)
    · exact absurd h2 (Rat.ne_of_gt hp)

theorem nonzeroCount_map_tval : ∀ ts : List (ℤ × ℤ),
    nonzeroCount (ts.map tval) = ts.countP fun t => t.1 ≠ 0
  | [] => rfl
  | t :: ts => by
    have ih := nonzeroCount_map_tval ts
    unfold nonzeroCount at ih ⊢
    rw [List.map_cons, List.countP_cons, List.countP_cons, ih]
    by_cases h : t.1 = 0
    · have : ¬ tval t ≠ 0 := fun h' => (tval_ne_zero_iff t).mp h' h
      simp [h, this]
    · have : tval t ≠ 0 := (tval_ne_zero_iff t).mpr h
      simp [h, this]

/-- **The bounded test with the number of nonzero positions**: the truncated sum in the register of
`ozaki1TestB`,
the bound `(s + 1) N 2^c + n' 2^q` with `n'` the number of nonzero slice products, both as integers,
and the integer enclosure test. -/
def ozaki1TestBZ (mult : MatrixMultiplier) (p : ℕ) (emin emax : ℤ) (b s W : ℕ) (N : ℤ) (x y : List ℚ) :
    Option ℚ :=
  match (trianglePairs s).mapM (pairInt mult (split b s x).1 (split b s y).1) with
  | none => none
  | some ts =>
    roundEnclosureB p emin emax
      (fixedSum (W + bitlen (ts.length * (x.length + 2)) + 1)
        (ts.map (floorPart (truncationGrid b W x y))))
      (truncationGrid b W x y) (((s + 1 : ℕ) : ℤ) * N)
      (splitExp b x + splitExp b y - s * (b + 1)) (ts.countP fun t => t.1 ≠ 0)

/-- **The bounded test is the enclosure test** on the truncated enclosure with the number of nonzero
positions. -/
theorem ozaki1TestBZ_eq {mult : MatrixMultiplier} {b bound : ℕ} (hmult : mult.ExactOn b bound)
    (p : ℕ) (emin emax : ℤ) (s W : ℕ) (N : ℤ) {x y : List ℚ} (hlen : x.length = y.length)
    (hbound : x.length * (2 ^ b * 2 ^ b) ≤ bound) :
    ozaki1TestBZ mult p emin emax b s W N x y =
      (ozaki1TruncatedEnclosureZ mult b s W N x y).bind
        fun e => roundEnclosure (roundRNE p emin emax) e.1 e.2 := by
  unfold ozaki1TestBZ ozaki1TruncatedEnclosureZ
  rw [mapM_eq_some_map fun _ hp => pairInt_exact hmult hlen hbound hp,
    ozaki1Terms_eq hmult s hlen hbound, Option.map_some, Option.bind_some]
  simp only
  rw [fixedSum_eq (by omega) (by
      rw [List.length_map, show ∀ a c : ℕ, a + c + 1 - 1 = a + c from fun _ _ => rfl]
      exact ozaki1TestB_register b s W x y),
    roundEnclosureB_eq, exactTerms_eq_map, truncatedSum_int, nonzeroCount_map_tval]
  congr 2
  unfold ozaki1BoundZ
  rw [Rat.intCast_mul, Rat.intCast_natCast]
  all_goals simp only [List.length_map]

/-- The bounded tests for the slice counts in turn, with the number `N` of nonzero positions, then
the bounded exact fallback. -/
def ozaki1CRBZFrom (mult : MatrixMultiplier) (p : ℕ) (emin emax : ℤ) (b W : ℕ) (N : ℤ) (smax : ℕ)
    (x y : List ℚ) : List ℕ → Option ℚ
  | [] => ozaki1ExactFallbackB mult p emin emax b smax x y
  | s :: ss =>
    match ozaki1TestBZ mult p emin emax b s W N x y with
    | some w => some w
    | none => ozaki1CRBZFrom mult p emin emax b W N smax x y ss

/-- **Correctly rounded Ozaki-I with the bound that counts only nonzero positions, in bounded
registers**: the number of nonzero positions from the matrix multiplier once, the bounded tests for
the slice counts `ss` in turn, then the bounded exact fallback. -/
def ozaki1CRBZ (mult : MatrixMultiplier) (p : ℕ) (emin emax : ℤ) (b W : ℕ) (ss : List ℕ) (smax : ℕ)
    (x y : List ℚ) : Option ℚ :=
  match overlapMultiplier mult x y with
  | some N => ozaki1CRBZFrom mult p emin emax b W N smax x y ss
  | none => ozaki1ExactFallbackB mult p emin emax b smax x y

theorem ozaki1CRBZFrom_eq {mult : MatrixMultiplier} {b bound : ℕ} (hmult : mult.ExactOn b bound)
    (p : ℕ) (emin emax : ℤ) (W : ℕ) (smax : ℕ) {x y : List ℚ} (hlen : x.length = y.length)
    (hbound : x.length * (2 ^ b * 2 ^ b) ≤ bound) :
    ∀ ss : List ℕ, ozaki1CRBZFrom mult p emin emax b W (supportOverlap x y) smax x y ss =
      roundingTest (roundRNE p emin emax)
        (ss.map fun s => ozaki1TruncatedEnclosureZ mult b s W (supportOverlap x y) x y)
        (ozaki1ExactFallback mult b smax x y)
  | [] => by
    unfold ozaki1CRBZFrom
    rw [ozaki1ExactFallbackB_eq hmult p emin emax smax hlen hbound]
    rfl
  | s :: ss => by
    have ih := ozaki1CRBZFrom_eq hmult p emin emax W smax hlen hbound ss
    unfold ozaki1CRBZFrom
    rw [ozaki1TestBZ_eq hmult p emin emax s W _ hlen hbound, List.map_cons]
    unfold roundingTest
    rw [← ih]
    cases (ozaki1TruncatedEnclosureZ mult b s W (supportOverlap x y) x y).bind
      (fun e => roundEnclosure (roundRNE p emin emax) e.1 e.2) <;> rfl

/-- **The bounded scheme is the rational one** with `rnd = roundRNE p emin emax`. -/
theorem ozaki1CRBZ_eq_CRWZ {mult : MatrixMultiplier} {b bound : ℕ} (hmult : mult.ExactOn b bound)
    (p : ℕ) (emin emax : ℤ) (W : ℕ) (ss : List ℕ) (smax : ℕ) {x y : List ℚ}
    (hlen : x.length = y.length) (hbound : x.length * (2 ^ b * 2 ^ b) ≤ bound) :
    ozaki1CRBZ mult p emin emax b W ss smax x y =
      ozaki1CRWZ mult (roundRNE p emin emax) b W ss smax x y := by
  unfold ozaki1CRBZ ozaki1CRWZ
  rw [overlapMultiplier_eq hmult hlen hbound, overlapTests_eq hmult _ ss hlen hbound]
  exact ozaki1CRBZFrom_eq hmult p emin emax W smax hlen hbound ss

/-- **Correctly rounded in bounded registers**: on an exact matrix multiplier, for every input whose
exact fallback ends within `smax` slices. -/
theorem ozaki1CRBZ_eq {p : ℕ} {emin emax : ℤ} (hp : 0 < p) (hle : emin ≤ emax) {mult : MatrixMultiplier}
    {b bound : ℕ} (hmult : mult.ExactOn b bound) (W : ℕ) (ss : List ℕ) {smax : ℕ}
    {x y : List ℚ} (hlen : x.length = y.length) (hbound : x.length * (2 ^ b * 2 ^ b) ≤ bound)
    (hvanish : ∃ s ∈ List.range' 1 smax, residualsVanish b s x y = true) :
    ozaki1CRBZ mult p emin emax b W ss smax x y = roundRNE p emin emax (dot x y) := by
  rw [ozaki1CRBZ_eq_CRWZ hmult p emin emax W ss smax hlen hbound]
  exact ozaki1CRWZ_eq (roundRNE_nearest hp hle) (roundRNE_intervals hp) hmult W ss hlen hbound
    hvanish

/-- Binary64 inputs, correctly rounded to binary64. -/
theorem ozaki1CRBZ64_eq {mult : MatrixMultiplier} {b bound : ℕ} (hmult : mult.ExactOn b bound) (W : ℕ)
    (ss : List ℕ) {smax : ℕ} (hb : b ≤ 1025) (hsmax : 2098 < smax * (b + 1)) {x y : List ℚ}
    (hlen : x.length = y.length) (hbound : x.length * (2 ^ b * 2 ^ b) ≤ bound)
    (hx : ∀ a ∈ x, Binary64Value a) (hy : ∀ a ∈ y, Binary64Value a) :
    ozaki1CRBZ mult 53 (-1022) 1023 b W ss smax x y = rne64 (dot x y) :=
  ozaki1CRBZ_eq (by decide) (by decide) hmult W ss hlen hbound (vanish64 hb hsmax hx hy)

/-- Binary32 inputs, correctly rounded to binary32. -/
theorem ozaki1CRBZ32_eq {mult : MatrixMultiplier} {b bound : ℕ} (hmult : mult.ExactOn b bound) (W : ℕ)
    (ss : List ℕ) {smax : ℕ} (hb : b ≤ 129) (hsmax : 277 < smax * (b + 1)) {x y : List ℚ}
    (hlen : x.length = y.length) (hbound : x.length * (2 ^ b * 2 ^ b) ≤ bound)
    (hx : ∀ a ∈ x, Binary32Value a) (hy : ∀ a ∈ y, Binary32Value a) :
    ozaki1CRBZ mult 24 (-126) 127 b W ss smax x y = rne32Q (dot x y) :=
  ozaki1CRBZ_eq (by decide) (by decide) hmult W ss hlen hbound (vanish32Q hb hsmax hx hy)

/-- **The first test succeeds on exact zeros in bounded registers too**: when every product is zero,
the first bounded test returns `0`, whatever the remaining tests and the exact fallback would
return. -/
theorem ozaki1CRBZFrom_zero {mult : MatrixMultiplier} {b bound : ℕ} (hmult : mult.ExactOn b bound)
    (p : ℕ) (emin emax : ℤ) (W smax s : ℕ) (ss : List ℕ) {x y : List ℚ}
    (hlen : x.length = y.length) (hbound : x.length * (2 ^ b * 2 ^ b) ≤ bound)
    (hz : ProductsZero x y) :
    ozaki1TestBZ mult p emin emax b s W (supportOverlap x y) x y = some 0 ∧
      ozaki1CRBZFrom mult p emin emax b W (supportOverlap x y) smax x y (s :: ss) = some 0 := by
  have hz' := (supportOverlap_eq_zero_iff x y).mpr hz
  have hc : ozaki1TestBZ mult p emin emax b s W (supportOverlap x y) x y = some 0 := by
    rw [ozaki1TestBZ_eq hmult p emin emax s W _ hlen hbound,
      ozaki1TruncatedEnclosureZ_zero hmult s W hlen hbound hz', Option.bind_some]
    exact roundEnclosure_zero (roundRNE_zero' p emin emax)
  refine ⟨hc, ?_⟩
  unfold ozaki1CRBZFrom
  rw [hc]

/-! ## Signed zeros -/

/-- The sign bit an enclosure decides for its rounding `r`. An enclosure of radius `0` is the exact
value, so its sign bit is `sumNeg`'s, including for an exact zero; otherwise as
`signFromEnclosure`. -/
def signFromEnclosureZ (H B r : ℚ) (z : Bool) : Option Bool :=
  if B = 0 then some (sumNeg H z) else signFromEnclosure H B r

theorem signFromEnclosure_sound {R : ℚ → Prop} {rnd : ℚ → Option ℚ} (h : RoundsToNearest R rnd)
    (h0 : rnd 0 = some 0) {H B v r : ℚ} {n : Bool} (z : Bool) (hv : Rat.abs (v - H) ≤ B)
    (hr : rnd v = some r) (hs : signFromEnclosure H B r = some n) : n = sumNeg v z := by
  obtain ⟨h1, h2⟩ := (abs_le_iff _ _).mp hv
  unfold signFromEnclosure at hs
  by_cases hr0 : r ≠ 0
  · rw [if_pos hr0] at hs
    cases hs
    obtain ⟨hv0, hsign⟩ := sign_of_round h h0 hr hr0
    unfold sumNeg; rw [if_neg hv0]; exact hsign
  · rw [if_neg hr0] at hs
    split at hs
    · cases hs
      have hvpos : 0 < v := by grind
      unfold sumNeg
      rw [if_neg (by grind)]
      simp; grind
    · split at hs
      · cases hs
        have hvneg : v < 0 := by grind
        unfold sumNeg
        rw [if_neg (by grind)]
        simp [hvneg]
      · cases hs

theorem signFromEnclosureZ_sound {R : ℚ → Prop} {rnd : ℚ → Option ℚ} (h : RoundsToNearest R rnd)
    (h0 : rnd 0 = some 0) {H B v r : ℚ} {n : Bool} (z : Bool) (hv : Rat.abs (v - H) ≤ B)
    (hr : rnd v = some r) (hs : signFromEnclosureZ H B r z = some n) : n = sumNeg v z := by
  unfold signFromEnclosureZ at hs
  split at hs
  · rename_i hB
    cases hs
    rw [hB] at hv
    obtain ⟨h1, h2⟩ := (abs_le_iff _ _).mp hv
    have : v = H := by grind
    rw [this]
  · exact signFromEnclosure_sound h h0 z hv hr hs

/-- The signed rounding test with `signFromEnclosureZ`: try the enclosures in order, accepting one
whose ends round alike and whose sign is decided; after the last, the exact value. -/
def roundingTestSignedZ (rnd : ℚ → Option ℚ) : List (Option (ℚ × ℚ)) → Option ℚ → Bool → Option Signed
  | [], exact, z => exact.bind fun v => (rnd v).map fun r => ⟨r, sumNeg v z⟩
  | c :: cs, exact, z =>
    match c.bind (fun p => (roundEnclosure rnd p.1 p.2).bind fun r =>
        (signFromEnclosureZ p.1 p.2 r z).map fun n => (⟨r, n⟩ : Signed)) with
    | some w => some w
    | none => roundingTestSignedZ rnd cs exact z

/-- **The signed rounding test returns the correctly rounded value with the IEEE sign.** -/
theorem roundingTestSignedZ_eq {R : ℚ → Prop} {rnd : ℚ → Option ℚ} (h : RoundsToNearest R rnd)
    (hI : RoundsOnIntervals rnd) (h0 : rnd 0 = some 0) {v : ℚ} (z : Bool) :
    ∀ (cs : List (Option (ℚ × ℚ))) (exact : Option ℚ),
      (∀ c ∈ cs, ∀ H B, c = some (H, B) → Rat.abs (v - H) ≤ B) → exact = some v →
      roundingTestSignedZ rnd cs exact z = (rnd v).map fun r => ⟨r, sumNeg v z⟩
  | [], exact, _, hex => by subst hex; rfl
  | c :: cs, exact, hcs, hex => by
    unfold roundingTestSignedZ
    split
    · rename_i w hw
      cases c with
      | none => simp at hw
      | some p =>
        obtain ⟨H, B⟩ := p
        simp only [Option.bind_some] at hw
        have hv := hcs _ List.mem_cons_self H B rfl
        cases hre : roundEnclosure rnd H B with
        | none => simp [hre] at hw
        | some r =>
          simp only [hre, Option.bind_some] at hw
          have hrv := roundEnclosure_eq h hI hv hre
          rw [hrv, Option.map_some]
          cases hs : signFromEnclosureZ H B r z with
          | none => simp [hs] at hw
          | some n =>
            simp only [hs, Option.map_some, Option.some.injEq] at hw
            subst hw
            rw [signFromEnclosureZ_sound h h0 z hv hrv hs]
    · exact roundingTestSignedZ_eq h hI h0 z cs exact
        (fun c' hc' => hcs c' (List.mem_cons_of_mem _ hc')) hex

/-- **Correctly rounded Ozaki-I with the bound that counts only nonzero positions, a `W`-bit
truncated sum and signed zeros.** -/
def ozaki1CRWSZ (mult : MatrixMultiplier) (rnd : ℚ → Option ℚ) (b W : ℕ) (ss : List ℕ) (smax : ℕ)
    (xs ys : List Signed) : Option Signed :=
  roundingTestSignedZ rnd
    (overlapTests mult (fun s N => ozaki1TruncatedEnclosureZ mult b s W N (vals xs) (vals ys)) ss
      (vals xs) (vals ys))
    (ozaki1ExactFallback mult b smax (vals xs) (vals ys)) (allNegZero xs ys)

/-- **Signed correct rounding.** On an exact matrix multiplier, `ozaki1CRWSZ` returns the correctly
rounded dot product with IEEE's sign for zero results. -/
theorem ozaki1CRWSZ_eq {R : ℚ → Prop} {rnd : ℚ → Option ℚ} (h : RoundsToNearest R rnd)
    (hI : RoundsOnIntervals rnd) (h0 : rnd 0 = some 0) {mult : MatrixMultiplier} {b bound : ℕ}
    (hmult : mult.ExactOn b bound) (W : ℕ) (ss : List ℕ) {smax : ℕ} {xs ys : List Signed}
    (hlen : xs.length = ys.length)
    (hbound : xs.length * (2 ^ b * 2 ^ b) ≤ bound)
    (hvanish : ∃ s ∈ List.range' 1 smax, residualsVanish b s (vals xs) (vals ys) = true) :
    ozaki1CRWSZ mult rnd b W ss smax xs ys = crSigned rnd xs ys := by
  have hl : (vals xs).length = (vals ys).length := by simp [vals, hlen]
  have hb : (vals xs).length * (2 ^ b * 2 ^ b) ≤ bound := by simpa [vals] using hbound
  unfold ozaki1CRWSZ crSigned
  rw [overlapTests_eq hmult _ ss hl hb]
  apply roundingTestSignedZ_eq h hI h0 _ _ _ _ (ozaki1ExactFallback_eq hmult hl hb hvanish)
  intro c hc H B hcB
  obtain ⟨s, _, rfl⟩ := List.mem_map.mp hc
  exact ozaki1TruncatedEnclosureZ_sound hmult s W hl hb hcB

/-- **The first test succeeds on signed exact zeros**: when every product is zero, `ozaki1CRWSZ`
returns `0` with the sign `crSigned` specifies (`−0` exactly when every product is `−0`), whatever
the exact fallback would return. -/
theorem ozaki1CRWSZ_zero {rnd : ℚ → Option ℚ} (h0 : rnd 0 = some 0) {mult : MatrixMultiplier}
    {b bound : ℕ} (hmult : mult.ExactOn b bound) (s W : ℕ) (ss : List ℕ) {xs ys : List Signed}
    (hlen : xs.length = ys.length) (hbound : xs.length * (2 ^ b * 2 ^ b) ≤ bound)
    (hz : ProductsZero (vals xs) (vals ys)) (exact : Option ℚ) :
    roundingTestSignedZ rnd
      (overlapTests mult (fun s N => ozaki1TruncatedEnclosureZ mult b s W N (vals xs) (vals ys))
        (s :: ss) (vals xs) (vals ys)) exact (allNegZero xs ys) =
      some ⟨0, allNegZero xs ys⟩ := by
  have hl : (vals xs).length = (vals ys).length := by simp [vals, hlen]
  have hb : (vals xs).length * (2 ^ b * 2 ^ b) ≤ bound := by simpa [vals] using hbound
  have hz' := (supportOverlap_eq_zero_iff _ _).mpr hz
  rw [overlapTests_eq hmult _ _ hl hb, List.map_cons]
  unfold roundingTestSignedZ
  rw [ozaki1TruncatedEnclosureZ_zero hmult s W hl hb hz', Option.bind_some, roundEnclosure_zero h0]
  simp [signFromEnclosureZ, sumNeg]

end Ozaki
