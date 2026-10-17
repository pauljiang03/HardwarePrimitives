import Ozaki.Correct

/-! # How wide the exact slice sum is

The correctly rounded schemes add the scaled slice products exactly. In an implementation that sum
lives in a fixed-point integer register; this file bounds the register. If every input is a multiple
of `2^m` (binary32: `m = −149`), a slice with a nonzero coefficient lies on a grid at least
`2^(m − b)` (`splitFrom_grid_ge`), so every scaled slice product, and the exact sum `H`, is a
multiple of `2^(2(m − b))` (`exactTerms_sum_register`), and

  `H = N · 2^(2(m−b))` with `|N| ≤ (s(s+1)/2) · k · 2^(E + F − 2(m − b))`.

For binary32 inputs (`E, F ≤ 128`) and `11`-bit slices, `|N| ≤ (s(s+1)/2) · k · 2^576`: a
two's-complement register of `578 + ⌈log₂ (s(s+1)/2 · k)⌉` bits with lowest bit `2^-320` holds `H`
exactly, comparable to TC-EFT's `576`-bit register for one block. The width follows the inputs'
exponent range, not the slice count: rows that mix very different magnitudes spread the slice
grids. -/

local notation "ℕ" => Nat
local notation "ℤ" => Int
local notation "ℚ" => Rat

namespace Ozaki

/-- A nonzero multiple of `2^m` has magnitude at least `2^m`. -/
theorem le_abs_of_gridMultiple {m : ℤ} {a : ℚ} (ha : GridMultiple m a) (hne : a ≠ 0) :
    2 ^ m ≤ Rat.abs a := by
  obtain ⟨z, rfl⟩ := ha
  have hz : z ≠ 0 := by rintro rfl; simp at hne
  rw [abs_mul_two_pow, abs_intCast]
  have h1 : (1 : ℚ) ≤ ((z.natAbs : ℕ) : ℚ) := by
    have : 1 ≤ z.natAbs := by omega
    exact_mod_cast this
  have := two_pow_pos m
  have := Rat.mul_le_mul_of_nonneg_right h1 (Rat.le_of_lt this)
  rwa [Rat.one_mul] at this

theorem exists_ne_zero_of_maxAbs {x : List ℚ} (h : maxAbs x ≠ 0) : ∃ a ∈ x, a ≠ 0 := by
  apply Classical.byContradiction
  intro hall
  apply h
  have hle : maxAbs x ≤ 0 := maxAbs_le (Rat.le_refl) fun a ha => by
    have : a = 0 := by
      apply Classical.byContradiction; intro hne; exact hall ⟨a, ha, hne⟩
    rw [this, abs_zero]; exact Rat.le_refl
  have := maxAbs_nonneg x
  grind

/-- **Slices of on-grid vectors stay on a grid.** If every entry of `x` is a multiple of `2^m`, a
slice with a nonzero coefficient lies on a grid at least `2^(m − b)`. -/
theorem splitFrom_grid_ge (b : ℕ) {m : ℤ} :
    ∀ (s : ℕ) (prev : ℤ) (x : List ℚ), (∀ a ∈ x, GridMultiple m a) →
      ∀ sl ∈ (splitFrom b s prev x).1, (∃ q ∈ sl.coeffs, q ≠ 0) → m - b ≤ sl.grid
  | 0, _, _, _ => by simp [splitFrom]
  | s + 1, prev, x, hx => by
    intro sl hsl hq
    simp only [splitFrom, List.mem_cons] at hsl
    rcases hsl with rfl | hsl
    · obtain ⟨q, hqm, hq0⟩ := hq
      by_cases hM : maxAbs x = 0
      · exfalso
        obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hqm
        have h0 := eq_zero_of_maxAbs hM a ha
        apply hq0
        rw [h0, show (0 : ℚ) / 2 ^ (sliceGrid b prev x) = ((0 : ℤ) : ℚ) by
            rw [Rat.div_def, Rat.zero_mul, Rat.intCast_zero],
          roundNearestEven_intCast]
      · simp only [sliceGrid, if_neg hM]
        have hpos : 0 < maxAbs x := by have := maxAbs_nonneg x; grind
        obtain ⟨a, ha, hne⟩ := exists_ne_zero_of_maxAbs hM
        have h1 := le_abs_of_gridMultiple (hx a ha) hne
        have h2 := abs_le_maxAbs ha
        have h3 := (ceilLog2_spec hpos).2
        have : (2 : ℚ) ^ m ≤ 2 ^ ceilLog2 (maxAbs x) := by grind
        have := two_pow_le_iff.mp this
        omega
    · exact splitFrom_grid_ge b s _ _ (fun r hr => by
        obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hr
        exact gridMultiple_sliceRest (hx a ha)) sl hsl hq

theorem dotZ_eq_zero_of_coeffs {q q' : List ℤ} (h : ∀ c ∈ q, c = 0) : dotZ q q' = 0 := by
  induction q generalizing q' with
  | nil => simp [dotZ]
  | cons a q ih =>
    cases q' with
    | nil => simp [dotZ]
    | cons c q' =>
      rw [dotZ_cons, h a List.mem_cons_self, ih (fun d hd => h d (List.mem_cons_of_mem _ hd))]
      simp

theorem gridMultiple_sum {m : ℤ} : ∀ {l : List ℚ}, (∀ a ∈ l, GridMultiple m a) →
    GridMultiple m l.sum
  | [], _ => ⟨0, by simp⟩
  | a :: l, h => by
    obtain ⟨z, hz⟩ := h a List.mem_cons_self
    obtain ⟨w, hw⟩ := gridMultiple_sum (l := l) fun c hc => h c (List.mem_cons_of_mem _ hc)
    refine ⟨z + w, ?_⟩
    rw [List.sum_cons, hz, hw, Rat.intCast_add]; grind

/-- Every exact term of on-grid vectors is a multiple of `2^(2(m − b))`. -/
theorem exactTerm_gridMultiple {b s : ℕ} {m : ℤ} {x y : List ℚ} (hx : ∀ a ∈ x, GridMultiple m a)
    (hy : ∀ a ∈ y, GridMultiple m a) {p : ℕ × ℕ} (hp : p ∈ trianglePairs s) :
    GridMultiple (2 * (m - b)) (exactTerm (split b s x).1 (split b s y).1 p) := by
  obtain ⟨t, u⟩ := p
  have htu := mem_trianglePairs.mp hp
  obtain ⟨hlx, _, _⟩ := split_length b s x
  obtain ⟨hly, _, _⟩ := split_length b s y
  have hmx := getD_mem (l := (split b s x).1) (t := t) (by omega)
  have hmy := getD_mem (l := (split b s y).1) (t := u) (by omega)
  unfold exactTerm
  dsimp only
  generalize (split b s x).1.getD t default = sx at hmx ⊢
  generalize (split b s y).1.getD u default = sy at hmy ⊢
  by_cases hz : dotZ sx.coeffs sy.coeffs = 0
  · exact ⟨0, by rw [hz]; simp⟩
  · have hqx : ∃ q ∈ sx.coeffs, q ≠ 0 := by
      apply Classical.byContradiction; intro hn
      exact hz (dotZ_eq_zero_of_coeffs fun c hc => by
        apply Classical.byContradiction; intro hc0; exact hn ⟨c, hc, hc0⟩)
    have hqy : ∃ q ∈ sy.coeffs, q ≠ 0 := by
      apply Classical.byContradiction; intro hn
      rw [dotZ_comm] at hz
      exact hz (dotZ_eq_zero_of_coeffs fun c hc => by
        apply Classical.byContradiction; intro hc0; exact hn ⟨c, hc, hc0⟩)
    have hgx := splitFrom_grid_ge b s b x hx sx hmx hqx
    have hgy := splitFrom_grid_ge b s b y hy sy hmy hqy
    refine ⟨dotZ sx.coeffs sy.coeffs *
      ((2 ^ (sx.grid + sy.grid - 2 * (m - b)).toNat : ℕ) : ℤ), ?_⟩
    have hg : (2 : ℚ) ^ (sx.grid + sy.grid) =
        2 ^ (((sx.grid + sy.grid - 2 * (m - b)).toNat : ℕ) : ℤ) * 2 ^ (2 * (m - b)) := by
      rw [← two_pow_add]; congr 1; omega
    rw [hg, Rat.intCast_mul, Rat.intCast_natCast, ← two_pow_natCast]
    grind

/-- **The exact slice sum fits a fixed-point register.** For inputs on the grid `2^m`,
`Σ terms = N · 2^(2(m−b))` with `|N| ≤ (s(s+1)/2) · k · 2^(E + F − 2(m−b))`. -/
theorem exactTerms_sum_register {b s : ℕ} {m : ℤ} {x y : List ℚ}
    (hx : ∀ a ∈ x, GridMultiple m a) (hy : ∀ a ∈ y, GridMultiple m a) :
    ∃ N : ℤ, (exactTerms b s x y).sum = (N : ℚ) * 2 ^ (2 * (m - b)) ∧
      ((N.natAbs : ℕ) : ℚ) ≤ (trianglePairs s).length * x.length *
        2 ^ (splitExp b x + splitExp b y - 2 * (m - b)) := by
  obtain ⟨N, hN⟩ := gridMultiple_sum (m := 2 * (m - b)) (l := exactTerms b s x y) (by
    intro a ha
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp ha
    exact exactTerm_gridMultiple hx hy hp)
  refine ⟨N, hN, ?_⟩
  have hsum : Rat.abs (exactTerms b s x y).sum ≤
      (trianglePairs s).length * (x.length * 2 ^ (splitExp b x + splitExp b y)) := by
    refine Rat.le_trans (abs_sum_le _ _) ?_
    have := sum_le_length_mul (l := trianglePairs s)
      (f := Rat.abs ∘ exactTerm (split b s x).1 (split b s y).1)
      (B := x.length * 2 ^ (splitExp b x + splitExp b y))
      (fun p hp => abs_exactTerm_le b s x y hp)
    simpa [Function.comp_def] using this
  rw [hN, abs_mul_two_pow, abs_intCast] at hsum
  have hpos := two_pow_pos (2 * (m - b))
  have hsplit : (2 : ℚ) ^ (splitExp b x + splitExp b y) =
      2 ^ (splitExp b x + splitExp b y - 2 * (m - b)) * 2 ^ (2 * (m - b)) := by
    rw [← two_pow_add]; congr 1; omega
  rw [hsplit] at hsum
  have : ((N.natAbs : ℕ) : ℚ) * 2 ^ (2 * (m - b)) ≤
      ((trianglePairs s).length * x.length * 2 ^ (splitExp b x + splitExp b y - 2 * (m - b))) *
        2 ^ (2 * (m - b)) := by grind
  apply Classical.byContradiction
  intro hn
  have hlt := Rat.mul_lt_mul_of_pos_right (Rat.not_le.mp hn) hpos
  grind

end Ozaki
