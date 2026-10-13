import Ozaki.Ozaki1
import Ozaki.Ozaki2
import Ozaki.Native
import Ozaki.Binary

/-! # Sharper error bounds

The bounds of `Ozaki.Ozaki1`, `Ozaki.Ozaki2` and `Ozaki.Native` are normwise or carry `O(u²)`
terms. This file proves sharper ones, from the literature where it has them:

* **Ozaki-I, entry by entry** (`exactTerms_error_sharp`). The slicing error is at most
  `(s + 1) Σᵢ min(2 |xᵢyᵢ|, 2^(E + F − s(b+1)))` instead of `(s + 1) k 2^(E + F − s(b+1))`: every
  slice and residual of an entry is at most twice the entry (`abs_rne_le_two`,
  `abs_sub_rne_le`), so an entry whose product is small, or zero, contributes little, or nothing
  (`exactTerms_eq_of_products_zero`). Its corollary in the form of Abdelfattah, Dongarra, Fasi,
  Mikaitis and Tisseur, *Analysis of floating-point matrix multiplication computed via integer
  arithmetic* (arXiv:2506.11277, v3 2026, §4.1–4.3, (4.6), (4.14), (4.18)), with row and column
  scaling factors `κ`, is `exactTerms_error_kappa`: `(s + 1) 2^(−s(b+1)) κₓ κ_y Σ |xᵢyᵢ|`. Their
  slices truncate a fixed-point representation with one scale per row; ours round to nearest on
  grids recomputed from what is left (Ozaki, Ogita, Oishi and Rump 2012), so the constants differ
  but the shape is theirs.
* **Ozaki-II's truncation, mixed** (`truncProduct_error_mixed`): for any shifts `s, t`,
  `|x · y − 2^(−s−t) a · c| ≤ 2^(−s) Σ|yᵢ| + 2^(−t) Σ|xᵢ|`. Truncation toward zero keeps
  `|aᵢ| ≤ 2^s |xᵢ|`, so there is no cross term: Uchino, Ozaki and Imamura, *Error analysis of
  matrix multiplication emulation using Ozaki-II scheme* (arXiv:2602.02549, 2026, Lemma 2, (19))
  bound the same quantity by the same two terms plus `k 2^(−s−t)`, for their scaling; this
  statement holds for every scaling, theirs included. With Ozaki-II's own shifts the normwise bound
  halves, to `4 k max|x| max|y| 2^(−P)` (`truncProduct_error_normwise4`).
* **Native dot products** (`nativeDot_error_jr`): Jeannerod and Rump, *Improved error bounds for
  inner products in floating-point arithmetic* (SIAM J. Matrix Anal. Appl. 34(2), 2013,
  Theorem 4.2 via Proposition 4.1): rounding to nearest, any `k`, no underflow in the products,
  `|fl(x · y) − x · y| ≤ k u Σ|xᵢyᵢ|`, without `γₖ`'s denominator or a condition on `k u`. Their
  Proposition 3.1 (after Rump, BIT 52, 2012), `(n − 1) u Σ|aᵢ|` for summing floating-point
  numbers, holds with underflow (`sumWith_error_jr`); with underflow in the products the bound
  becomes `(k u + (k − 1) u²) Σ|xᵢyᵢ| + k (1 + (k − 1) u) η` (`nativeDot_error_jr_underflow`).
  Jeannerod and Rump show that the no-underflow hypothesis is needed for `k u`. The proofs are
  theirs, specialized to left-to-right evaluation; they need only round to nearest, error at most
  `u · ufp` for sums, and `±ufp` representable (`JRAdd`), which IEEE round to nearest even has
  (`roundRNE_jrAdd`).
* **Ozaki-I's recombination** (`ozaki1_error_jr`): when the scaled slice products are
  floating-point numbers, as on the Tensor Core in binary32, Proposition 3.1 bounds the rounded
  recombination by `(n − 1) u Σ|tⱼ|` for `n` terms, with no `η`, in place of `((1 + u)^n − 1)`. -/

local notation "ℕ" => Nat
local notation "ℤ" => Int
local notation "ℚ" => Rat

namespace Ozaki

/-! ## Entrywise relations -/

/-- `Entrywise R u x`: `u` and `x` have the same length and `R uᵢ xᵢ` for every `i`. -/
def Entrywise (R : ℚ → ℚ → Prop) : List ℚ → List ℚ → Prop
  | [], [] => True
  | a :: u, c :: x => R a c ∧ Entrywise R u x
  | _, _ => False

theorem Entrywise.length {R : ℚ → ℚ → Prop} : ∀ {u x : List ℚ}, Entrywise R u x → u.length = x.length
  | [], [], _ => rfl
  | [], _ :: _, h => h.elim
  | _ :: _, [], h => h.elim
  | _ :: _, _ :: _, h => by simp [Entrywise.length h.2]

theorem Entrywise.mono {R S : ℚ → ℚ → Prop} (hRS : ∀ a c, R a c → S a c) :
    ∀ {u x : List ℚ}, Entrywise R u x → Entrywise S u x
  | [], [], _ => trivial
  | [], _ :: _, h => h.elim
  | _ :: _, [], h => h.elim
  | _ :: _, _ :: _, h => ⟨hRS _ _ h.1, Entrywise.mono hRS h.2⟩

theorem Entrywise.trans {R S T : ℚ → ℚ → Prop} (hT : ∀ a b c, R a b → S b c → T a c) :
    ∀ {u v x : List ℚ}, Entrywise R u v → Entrywise S v x → Entrywise T u x
  | [], [], [], _, _ => trivial
  | [], [], _ :: _, _, h => h.elim
  | [], _ :: _, _, h, _ => h.elim
  | _ :: _, [], _, h, _ => h.elim
  | _ :: _, _ :: _, [], _, h => h.elim
  | _ :: _, _ :: _, _ :: _, h1, h2 => ⟨hT _ _ _ h1.1 h2.1, Entrywise.trans hT h1.2 h2.2⟩

/-- Add a property of every entry of `u`. -/
theorem Entrywise.and_left {R : ℚ → ℚ → Prop} {P : ℚ → Prop} :
    ∀ {u x : List ℚ}, Entrywise R u x → (∀ a ∈ u, P a) → Entrywise (fun a c => R a c ∧ P a) u x
  | [], [], _, _ => trivial
  | [], _ :: _, h, _ => h.elim
  | _ :: _, [], h, _ => h.elim
  | _ :: _, _ :: _, h, hP =>
    ⟨⟨h.1, hP _ List.mem_cons_self⟩, Entrywise.and_left h.2 fun a ha => hP a (List.mem_cons_of_mem _ ha)⟩

theorem Entrywise.map_self {R : ℚ → ℚ → Prop} {f : ℚ → ℚ} :
    ∀ {x : List ℚ}, (∀ a ∈ x, R (f a) a) → Entrywise R (x.map f) x
  | [], _ => trivial
  | _ :: _, h => ⟨h _ List.mem_cons_self, Entrywise.map_self fun a ha => h a (List.mem_cons_of_mem _ ha)⟩

theorem Entrywise.refl {R : ℚ → ℚ → Prop} : ∀ {x : List ℚ}, (∀ a ∈ x, R a a) → Entrywise R x x
  | [], _ => trivial
  | _ :: _, h => ⟨h _ List.mem_cons_self, Entrywise.refl fun a ha => h a (List.mem_cons_of_mem _ ha)⟩

theorem Entrywise.map_left {R : ℚ → ℚ → Prop} {f : ℚ → ℚ} :
    ∀ {u x : List ℚ}, Entrywise (fun a c => R (f a) c) u x → Entrywise R (u.map f) x
  | [], [], _ => trivial
  | [], _ :: _, h => h.elim
  | _ :: _, [], h => h.elim
  | _ :: _, _ :: _, h => ⟨h.1, Entrywise.map_left h.2⟩

/-! ## One slice of one entry -/

/-- Rounding to the nearest integer never moves a number by more than its magnitude. -/
theorem abs_sub_rne_le (t : ℚ) : Rat.abs (t - roundNearestEven t) ≤ Rat.abs t := by
  have h := roundNearestEven_error t
  by_cases h0 : roundNearestEven t = 0
  · rw [h0, Rat.intCast_zero, show t - 0 = t by grind]; exact Rat.le_refl
  · have h1 : (1 : ℚ) ≤ Rat.abs (roundNearestEven t : ℚ) := by
      rw [abs_intCast]
      have : 1 ≤ (roundNearestEven t).natAbs := by omega
      exact_mod_cast this
    have h2 := abs_add_le t ((roundNearestEven t : ℚ) - t)
    rw [show t + ((roundNearestEven t : ℚ) - t) = roundNearestEven t by grind,
      abs_sub_comm (roundNearestEven t : ℚ) t] at h2
    generalize Rat.abs (t - roundNearestEven t) = d at *
    generalize Rat.abs (roundNearestEven t : ℚ) = r at *
    generalize Rat.abs t = A at *
    grind

/-- The nearest integer is at most twice the number. -/
theorem abs_rne_le_two (t : ℚ) : Rat.abs (roundNearestEven t : ℚ) ≤ 2 * Rat.abs t := by
  have h2 := abs_sub_rne_le t
  have h3 := abs_add_le t ((roundNearestEven t : ℚ) - t)
  rw [show t + ((roundNearestEven t : ℚ) - t) = roundNearestEven t by grind,
    abs_sub_comm (roundNearestEven t : ℚ) t] at h3
  generalize Rat.abs (t - roundNearestEven t) = d at *
  generalize Rat.abs (roundNearestEven t : ℚ) = r at *
  generalize Rat.abs t = A at *
  grind

/-- What a slice leaves of an entry is at most the entry. -/
theorem sliceRest_entrywise (g : ℤ) (x : List ℚ) :
    Entrywise (fun a c => Rat.abs a ≤ Rat.abs c) (sliceRest g x) x := by
  unfold sliceRest
  refine Entrywise.map_self fun a _ => ?_
  rw [abs_sub_mul_two_pow, abs_sub_comm]
  have := Rat.mul_le_mul_of_nonneg_right (abs_sub_rne_le (a / 2 ^ g)) (Rat.le_of_lt (two_pow_pos g))
  rw [abs_div_two_pow, Rat.div_mul_cancel (two_pow_ne_zero g)] at this
  rw [abs_sub_comm]; exact this

/-- The slice of an entry, `rne(a / 2^g) · 2^g`, is at most twice the entry. -/
theorem sliceValue_entrywise (g : ℤ) (x : List ℚ) :
    Entrywise (fun a c => Rat.abs a ≤ 2 * Rat.abs c)
      ((ofInts (sliceCoeffs g x)).map fun a => 2 ^ g * a) x := by
  unfold ofInts sliceCoeffs
  rw [List.map_map, List.map_map]
  refine Entrywise.map_self fun a _ => ?_
  simp only [Function.comp]
  rw [abs_mul, abs_two_pow]
  have := Rat.mul_le_mul_of_nonneg_left (abs_rne_le_two (a / 2 ^ g)) (Rat.le_of_lt (two_pow_pos g))
  rw [abs_div_two_pow] at this
  have e : (2 : ℚ) ^ g * (2 * (Rat.abs a / 2 ^ g)) = 2 * Rat.abs a := by
    rw [Rat.div_def]
    have := Rat.mul_inv_cancel (2 ^ g) (two_pow_ne_zero g)
    grind
  rw [e] at this; exact this

/-- Every residual of a split is at most the entry it came from. -/
theorem splitFrom_rest_entrywise (b s : ℕ) :
    ∀ (prev : ℤ) (x : List ℚ),
      Entrywise (fun a c => Rat.abs a ≤ Rat.abs c) (splitFrom b s prev x).2 x := by
  induction s with
  | zero => intro _ x; exact Entrywise.refl (x := x) fun _ _ => Rat.le_refl
  | succ s ih =>
    intro prev x
    have h1 := ih (sliceGrid b prev x) (sliceRest (sliceGrid b prev x) x)
    have h2 := sliceRest_entrywise (sliceGrid b prev x) x
    have h3 := Entrywise.trans (R := fun a c => Rat.abs a ≤ Rat.abs c)
      (S := fun a c => Rat.abs a ≤ Rat.abs c) (T := fun a c => Rat.abs a ≤ Rat.abs c)
      (fun _ _ _ e1 e2 => Rat.le_trans e1 e2) h1 h2
    exact h3

/-- Every slice of a split, entry by entry, is at most twice the entry. -/
theorem splitFrom_slice_entrywise (b s : ℕ) :
    ∀ (prev : ℤ) (x : List ℚ), ∀ sl ∈ (splitFrom b s prev x).1,
      Entrywise (fun a c => Rat.abs a ≤ 2 * Rat.abs c)
        ((ofInts sl.coeffs).map fun a => 2 ^ sl.grid * a) x := by
  induction s with
  | zero => intro _ _ sl h; simp [splitFrom] at h
  | succ s ih =>
    intro prev x sl h
    have h' : sl = ⟨sliceGrid b prev x, sliceCoeffs (sliceGrid b prev x) x⟩ ∨
        sl ∈ (splitFrom b s (sliceGrid b prev x) (sliceRest (sliceGrid b prev x) x)).1 := by
      simpa [splitFrom] using h
    rcases h' with rfl | h'
    · exact sliceValue_entrywise _ x
    · have h1 := ih _ _ sl h'
      have h2 := sliceRest_entrywise (sliceGrid b prev x) x
      exact Entrywise.trans (R := fun a c => Rat.abs a ≤ 2 * Rat.abs c)
        (S := fun a c => Rat.abs a ≤ Rat.abs c) (T := fun a c => Rat.abs a ≤ 2 * Rat.abs c)
        (fun _ _ _ e1 e2 => by
          have := Rat.mul_le_mul_of_nonneg_left e2 (show (0 : ℚ) ≤ 2 by decide)
          exact Rat.le_trans e1 this) h1 h2

/-! ## Capped products -/

/-- `min(2 |c d|, M)`. -/
def capTerm (M c d : ℚ) : ℚ := if 2 * Rat.abs (c * d) ≤ M then 2 * Rat.abs (c * d) else M

/-- `Σᵢ min(2 |xᵢ yᵢ|, M)`. -/
def capSum (M : ℚ) (x y : List ℚ) : ℚ := (List.zipWith (capTerm M) x y).sum

theorem capTerm_le (M c d : ℚ) : capTerm M c d ≤ M := by
  unfold capTerm; split <;> grind

theorem capTerm_le_two (M c d : ℚ) : capTerm M c d ≤ 2 * Rat.abs (c * d) := by
  unfold capTerm; split <;> grind

theorem le_capTerm {M c d v : ℚ} (h1 : v ≤ 2 * Rat.abs (c * d)) (h2 : v ≤ M) : v ≤ capTerm M c d := by
  unfold capTerm; split <;> grind

theorem capSum_cons (M a b : ℚ) (x y : List ℚ) :
    capSum M (a :: x) (b :: y) = capTerm M a b + capSum M x y := by
  simp [capSum, List.zipWith_cons_cons, List.sum_cons]

/-- **A dot product of capped entries.** If `|uᵢ| ≤ 2|xᵢ|`, `|uᵢ| ≤ A`, `|wᵢ| ≤ |yᵢ|`, `|wᵢ| ≤ B`
and `A B ≤ M`, then `|u · w| ≤ Σᵢ min(2 |xᵢyᵢ|, M)`. -/
theorem abs_dot_le_capSum {A B M : ℚ} (hA : 0 ≤ A) (hAB : A * B ≤ M) :
    ∀ {u w x y : List ℚ},
      Entrywise (fun a c => Rat.abs a ≤ 2 * Rat.abs c ∧ Rat.abs a ≤ A) u x →
      Entrywise (fun b d => Rat.abs b ≤ Rat.abs d ∧ Rat.abs b ≤ B) w y →
      Rat.abs (dot u w) ≤ capSum M x y
  | [], _, [], _, _, _ => by simp [dot, capSum]
  | [], _, _ :: _, _, h, _ => h.elim
  | _ :: _, _, [], _, h, _ => h.elim
  | _ :: _, [], _ :: _, [], _, _ => by simp [dot, capSum]
  | _ :: _, [], _ :: _, _ :: _, _, h => h.elim
  | _ :: _, _ :: _, _ :: _, [], _, h => h.elim
  | a :: u, b :: w, c :: x, d :: y, hu, hw => by
    rw [dot_cons, capSum_cons]
    have ih := abs_dot_le_capSum hA hAB hu.2 hw.2
    obtain ⟨⟨h1, h2⟩, _⟩ := hu
    obtain ⟨⟨h3, h4⟩, _⟩ := hw
    have hb := abs_nonneg b
    have ha := abs_nonneg a
    have e1 : Rat.abs a * Rat.abs b ≤ 2 * Rat.abs (c * d) := by
      rw [abs_mul]
      have := Rat.mul_le_mul_of_nonneg_right h1 hb
      have := Rat.mul_le_mul_of_nonneg_left h3 (show (0 : ℚ) ≤ 2 * Rat.abs c by
        have := abs_nonneg c; grind)
      grind
    have e2 : Rat.abs a * Rat.abs b ≤ M := by
      have := Rat.mul_le_mul_of_nonneg_right h2 hb
      have := Rat.mul_le_mul_of_nonneg_left h4 hA
      grind
    have := le_capTerm e1 e2
    have := abs_add_le (a * b) (dot u w)
    rw [abs_mul] at this
    grind

theorem capSum_nonneg {M : ℚ} (hM : 0 ≤ M) : ∀ x y : List ℚ, 0 ≤ capSum M x y
  | [], _ => by simp [capSum]
  | _ :: _, [] => by simp [capSum]
  | a :: x, b :: y => by
    rw [capSum_cons]
    have := capSum_nonneg hM x y
    have : 0 ≤ capTerm M a b := by
      unfold capTerm; split
      · have := abs_nonneg (a * b); grind
      · exact hM
    grind

/-- The capped sum is at most `k M`. -/
theorem capSum_le_length {M : ℚ} (hM : 0 ≤ M) (x y : List ℚ) : capSum M x y ≤ x.length * M :=
  sum_zipWith_le hM x y fun a _ b _ => capTerm_le M a b

/-- The capped sum is at most `2 Σ|xᵢyᵢ|`. -/
theorem capSum_le_two : ∀ (M : ℚ) (x y : List ℚ),
    capSum M x y ≤ 2 * ((List.zipWith (· * ·) x y).map Rat.abs).sum
  | _, [], _ => by simp [capSum]
  | _, _ :: _, [] => by simp [capSum]
  | M, a :: x, b :: y => by
    rw [capSum_cons]
    simp only [List.zipWith_cons_cons, List.map_cons, List.sum_cons]
    have := capSum_le_two M x y
    have := capTerm_le_two M a b
    grind

/-- **The `κ` form.** If `M ≤ K |c d|` for every pair of nonzero entries, the capped sum is at most
`K Σ|xᵢyᵢ|`. -/
theorem capSum_le_mul {M K : ℚ} (hM : 0 ≤ M) {x y : List ℚ}
    (h : ∀ c ∈ x, ∀ d ∈ y, c ≠ 0 → d ≠ 0 → M ≤ K * Rat.abs (c * d)) :
    capSum M x y ≤ K * ((List.zipWith (· * ·) x y).map Rat.abs).sum := by
  induction x generalizing y with
  | nil => simp [capSum]
  | cons a x ih =>
    cases y with
    | nil => simp [capSum]
    | cons b y =>
      rw [capSum_cons]
      simp only [List.zipWith_cons_cons, List.map_cons, List.sum_cons]
      have ih' := ih (y := y) fun c hc d hd => h c (List.mem_cons_of_mem _ hc) d (List.mem_cons_of_mem _ hd)
      have hab : capTerm M a b ≤ K * Rat.abs (a * b) := by
        by_cases ha : a = 0
        · subst ha
          unfold capTerm
          rw [Rat.zero_mul, abs_zero, Rat.mul_zero, Rat.mul_zero, if_pos hM]; exact Rat.le_refl
        · by_cases hb : b = 0
          · subst hb
            unfold capTerm
            rw [Rat.mul_zero, abs_zero, Rat.mul_zero, Rat.mul_zero, if_pos hM]; exact Rat.le_refl
          · exact Rat.le_trans (capTerm_le M a b) (h a List.mem_cons_self b List.mem_cons_self ha hb)
      rw [Rat.mul_add]
      grind

/-! ## Ozaki-I, entry by entry -/

/-- **Slicing error, entry by entry.** `|x · y − Σ terms| ≤ (s + 1) Σᵢ min(2|xᵢyᵢ|, 2^(E+F−s(b+1)))`,
with `E` and `F` the exponents of `x` and `y`. Never more than `exactTerms_error`'s
`(s + 1) k 2^(E+F−s(b+1))` (`exactTerms_error_sharp_le`), and zero when every product is zero. -/
theorem exactTerms_error_sharp (b s : ℕ) (x y : List ℚ) :
    Rat.abs (dot x y - (exactTerms b s x y).sum) ≤
      ((s + 1 : ℕ) : ℚ) * capSum (2 ^ (splitExp b x + splitExp b y - s * (b + 1))) x y := by
  rw [dot_eq_exactTerms_add b s x y]
  generalize hM : (2 : ℚ) ^ (splitExp b x + splitExp b y - s * (b + 1)) = M
  have hMpos : 0 < M := by rw [← hM]; exact two_pow_pos _
  -- the residual of `x` against `y`
  have h1 : Rat.abs (dot (split b s x).2 y) ≤ capSum M x y := by
    have hu : Entrywise (fun a c => Rat.abs a ≤ 2 * Rat.abs c ∧
        Rat.abs a ≤ 2 ^ (splitExp b x - s * (b + 1))) (split b s x).2 x :=
      Entrywise.and_left ((splitFrom_rest_entrywise b s b x).mono fun a c h => by
        have := abs_nonneg c; grind) (split_residual_le b s x)
    have hw : Entrywise (fun a c => Rat.abs a ≤ Rat.abs c ∧ Rat.abs a ≤ 2 ^ splitExp b y) y y :=
      Entrywise.and_left (by
        have := Entrywise.map_self (R := fun a c => Rat.abs a ≤ Rat.abs c) (f := id) (x := y)
          (fun a _ => Rat.le_refl)
        simpa using this) (abs_le_two_pow_splitExp b y)
    refine abs_dot_le_capSum (Rat.le_of_lt (two_pow_pos _)) ?_ hu hw
    rw [← hM, ← two_pow_add]
    exact two_pow_le (by omega)
  -- each slice of `x` against a residual of `y`
  have h2 : ∀ t ∈ List.range s, Rat.abs (2 ^ ((split b s x).1.getD t default).grid *
      dot (ofInts ((split b s x).1.getD t default).coeffs) (split b (s - t) y).2) ≤
        capSum M x y := by
    intro t ht
    have htl := List.mem_range.mp ht
    have hmem := getD_mem (l := (split b s x).1) (t := t) (by rw [(split_length b s x).1]; exact htl)
    generalize hsl : (split b s x).1.getD t default = sl at hmem
    have hgrid := split_grid_le b s x t sl (by
      rw [← hsl, List.getD_eq_getElem?_getD,
        List.getElem?_eq_getElem (by rw [(split_length b s x).1]; exact htl)]; rfl)
    rw [← dot_map_mul_left]
    have hu : Entrywise (fun a c => Rat.abs a ≤ 2 * Rat.abs c ∧
        Rat.abs a ≤ 2 ^ (splitExp b x - t * (b + 1))) ((ofInts sl.coeffs).map fun a => 2 ^ sl.grid * a) x := by
      refine Entrywise.and_left (splitFrom_slice_entrywise b s b x sl hmem) ?_
      intro a ha
      obtain ⟨q', hq', rfl⟩ := List.mem_map.mp ha
      obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hq'
      rw [abs_mul, abs_two_pow]
      have hc := abs_intCast_le (split_coeff_bound b s x sl hmem q hq)
      rw [← two_pow_natCast] at hc
      have := Rat.mul_le_mul_of_nonneg_left hc (Rat.le_of_lt (two_pow_pos sl.grid))
      rw [← two_pow_add] at this
      exact Rat.le_trans this (two_pow_le (by omega))
    have hw : Entrywise (fun a c => Rat.abs a ≤ Rat.abs c ∧
        Rat.abs a ≤ 2 ^ (splitExp b y - ((s - t : ℕ) : ℤ) * (b + 1))) (split b (s - t) y).2 y :=
      Entrywise.and_left (splitFrom_rest_entrywise b (s - t) b y) (split_residual_le b (s - t) y)
    refine abs_dot_le_capSum (Rat.le_of_lt (two_pow_pos _)) ?_ hu hw
    rw [← hM, ← two_pow_add]
    refine two_pow_le ?_
    have hst : ((s - t : ℕ) : ℤ) = s - t := by omega
    rw [hst]
    have : ((s : ℤ) - t) * (b + 1) = s * (b + 1) - t * (b + 1) := Int.sub_mul _ _ _
    omega
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

/-- The entrywise bound is never larger than `exactTerms_error`'s. -/
theorem exactTerms_error_sharp_le (b s : ℕ) (x y : List ℚ) :
    ((s + 1 : ℕ) : ℚ) * capSum (2 ^ (splitExp b x + splitExp b y - s * (b + 1))) x y ≤
      ((s + 1 : ℕ) : ℚ) * x.length * 2 ^ (splitExp b x + splitExp b y - s * (b + 1)) := by
  have := capSum_le_length (Rat.le_of_lt (two_pow_pos (splitExp b x + splitExp b y - s * (b + 1)))) x y
  have := Rat.mul_le_mul_of_nonneg_left this (show (0 : ℚ) ≤ ((s + 1 : ℕ) : ℚ) from Rat.natCast_nonneg)
  grind

/-- **Exact when every product vanishes.** If `xᵢyᵢ = 0` for every `i` (for instance rows and
columns with disjoint supports), the exact terms add up to `x · y` exactly, for any `s`. -/
theorem exactTerms_eq_of_products_zero (b s : ℕ) {x y : List ℚ}
    (h : ∀ z ∈ List.zipWith (· * ·) x y, z = 0) :
    (exactTerms b s x y).sum = dot x y := by
  have he := exactTerms_error_sharp b s x y
  have hc := capSum_le_two (2 ^ (splitExp b x + splitExp b y - s * (b + 1))) x y
  have h0 : ((List.zipWith (· * ·) x y).map Rat.abs).sum ≤ 0 := by
    have := sum_le_length_mul (l := List.zipWith (· * ·) x y) (f := Rat.abs) (B := 0)
      fun z hz => by rw [h z hz, abs_zero]; exact Rat.le_refl
    rw [Rat.mul_zero] at this; exact this
  have hn := capSum_nonneg (Rat.le_of_lt (two_pow_pos (splitExp b x + splitExp b y - s * (b + 1)))) x y
  have hs : (0 : ℚ) ≤ ((s + 1 : ℕ) : ℚ) := Rat.natCast_nonneg
  have hz : capSum (2 ^ (splitExp b x + splitExp b y - s * (b + 1))) x y = 0 := by grind
  rw [hz, Rat.mul_zero] at he
  have := abs_eq_zero.mp (Rat.le_antisymm he (abs_nonneg _))
  grind

/-- **Slicing error with scaling factors** (the form of Abdelfattah et al. (4.14), (4.18)). If
`2^E ≤ κₓ |xᵢ|` for every nonzero `xᵢ` and `2^F ≤ κ_y |yᵢ|` for every nonzero `yᵢ` (for instance
`κₓ = 2 max|x| / min_{xᵢ≠0} |xᵢ|`), then `|x · y − Σ terms| ≤ (s + 1) 2^(−s(b+1)) κₓ κ_y Σ|xᵢyᵢ|`. -/
theorem exactTerms_error_kappa (b s : ℕ) {x y : List ℚ} {κx κy : ℚ} (hκx : 0 ≤ κx) (hκy : 0 ≤ κy)
    (hx : ∀ c ∈ x, c ≠ 0 → (2 : ℚ) ^ splitExp b x ≤ κx * Rat.abs c)
    (hy : ∀ d ∈ y, d ≠ 0 → (2 : ℚ) ^ splitExp b y ≤ κy * Rat.abs d) :
    Rat.abs (dot x y - (exactTerms b s x y).sum) ≤
      ((s + 1 : ℕ) : ℚ) * 2 ^ (-((s * (b + 1) : ℕ) : ℤ)) * κx * κy *
        ((List.zipWith (· * ·) x y).map Rat.abs).sum := by
  refine Rat.le_trans (exactTerms_error_sharp b s x y) ?_
  have hK : ∀ c ∈ x, ∀ d ∈ y, c ≠ 0 → d ≠ 0 →
      (2 : ℚ) ^ (splitExp b x + splitExp b y - s * (b + 1)) ≤
        2 ^ (-((s * (b + 1) : ℕ) : ℤ)) * κx * κy * Rat.abs (c * d) := by
    intro c hc d hd hc0 hd0
    have e : (2 : ℚ) ^ (splitExp b x + splitExp b y - s * (b + 1)) =
        2 ^ (-((s * (b + 1) : ℕ) : ℤ)) * (2 ^ splitExp b x * 2 ^ splitExp b y) := by
      rw [← two_pow_add, ← two_pow_add]; congr 1; push_cast; omega
    rw [e, abs_mul]
    have h1 := hx c hc hc0
    have h2 := hy d hd hd0
    have hp := two_pow_pos (-((s * (b + 1) : ℕ) : ℤ))
    have hE := two_pow_pos (splitExp b x)
    have hF := two_pow_pos (splitExp b y)
    have hd' : 0 ≤ κy * Rat.abs d := Rat.mul_nonneg hκy (abs_nonneg d)
    have m1 := Rat.mul_le_mul_of_nonneg_right h1 (Rat.le_of_lt hF)
    have m2 := Rat.mul_le_mul_of_nonneg_left h2 (Rat.mul_nonneg hκx (abs_nonneg c))
    have m3 : (2 : ℚ) ^ splitExp b x * 2 ^ splitExp b y ≤ κx * Rat.abs c * (κy * Rat.abs d) :=
      Rat.le_trans m1 m2
    have := Rat.mul_le_mul_of_nonneg_left m3 (Rat.le_of_lt hp)
    have e2 : (2 : ℚ) ^ (-((s * (b + 1) : ℕ) : ℤ)) * (κx * Rat.abs c * (κy * Rat.abs d)) =
        2 ^ (-((s * (b + 1) : ℕ) : ℤ)) * κx * κy * (Rat.abs c * Rat.abs d) := by grind
    rw [e2] at this; exact this
  have := capSum_le_mul (Rat.le_of_lt (two_pow_pos _)) hK
  have := Rat.mul_le_mul_of_nonneg_left this (show (0 : ℚ) ≤ ((s + 1 : ℕ) : ℚ) from Rat.natCast_nonneg)
  grind

/-- **Ozaki-I error, entry by entry.** `ozaki1_error` with the slicing term
`(s + 1) Σᵢ min(2|xᵢyᵢ|, 2^(E+F−s(b+1)))`. -/
theorem ozaki1_error_sharp {mult : MatrixMultiplier} {add : ℚ → ℚ → Option ℚ} {b bound s : ℕ} {u η : ℚ}
    (hmult : mult.ExactOn b bound) (hu : 0 ≤ u) (hη : 0 ≤ η) (hadd : AddWithin add u η)
    {x y : List ℚ} (hlen : x.length = y.length) (hbound : x.length * (2 ^ b * 2 ^ b) ≤ bound)
    {v : ℚ} (hv : ozaki1 mult add b s x y = some v) :
    Rat.abs (v - dot x y) ≤
      ((1 + u) ^ (trianglePairs s).length - 1) *
          ((trianglePairs s).length * (x.length * 2 ^ (splitExp b x + splitExp b y))) +
        (trianglePairs s).length * (1 + u) ^ (trianglePairs s).length * η +
        ((s + 1 : ℕ) : ℚ) * capSum (2 ^ (splitExp b x + splitExp b y - s * (b + 1))) x y := by
  rw [ozaki1_eq_sumWith hmult add s hlen hbound] at hv
  have hr := sumWith_error hu hη hadd hv
  have hlenT : (exactTerms b s x y).length = (trianglePairs s).length := by simp [exactTerms]
  rw [hlenT] at hr
  have hT : ((exactTerms b s x y).map Rat.abs).sum ≤
      (trianglePairs s).length * (x.length * 2 ^ (splitExp b x + splitExp b y)) := by
    unfold exactTerms
    rw [List.map_map]
    exact sum_le_length_mul (fun p hp => abs_exactTerm_le b s x y hp)
  have hpow : (0 : ℚ) ≤ (1 + u) ^ (trianglePairs s).length - 1 := by
    have := one_le_pow_one_add hu (trianglePairs s).length
    grind
  have hT' := Rat.mul_le_mul_of_nonneg_left hT hpow
  have hs := exactTerms_error_sharp b s x y
  have htri : Rat.abs (v - dot x y) ≤ Rat.abs (v - (exactTerms b s x y).sum) +
      Rat.abs (dot x y - (exactTerms b s x y).sum) := by
    have := abs_add_le (v - (exactTerms b s x y).sum) ((exactTerms b s x y).sum - dot x y)
    rw [abs_sub_comm ((exactTerms b s x y).sum) (dot x y)] at this
    have h : v - (exactTerms b s x y).sum + ((exactTerms b s x y).sum - dot x y) = v - dot x y := by
      grind
    rwa [h] at this
  grind

/-! ## Ozaki-II's truncation, mixed -/

theorem sum_zipWith_add_split (f g : ℚ → ℚ) : ∀ (x y : List ℚ), x.length = y.length →
    (List.zipWith (fun a b => f b + g a) x y).sum = (y.map f).sum + (x.map g).sum
  | [], [], _ => by simp only [List.zipWith_nil_left, List.map_nil, List.sum_nil]; grind
  | [], _ :: _, h => by simp at h
  | _ :: _, [], h => by simp at h
  | a :: x, b :: y, h => by
    simp only [List.zipWith_cons_cons, List.sum_cons, List.map_cons]
    rw [sum_zipWith_add_split f g x y (by simpa using h)]
    grind

theorem sum_zipWith_mono {F G : ℚ → ℚ → ℚ} : ∀ (x y : List ℚ),
    (∀ a ∈ x, ∀ b ∈ y, F a b ≤ G a b) → (List.zipWith F x y).sum ≤ (List.zipWith G x y).sum
  | [], _, _ => by simp
  | _ :: _, [], _ => by simp
  | a :: x, b :: y, h => by
    simp only [List.zipWith_cons_cons, List.sum_cons]
    have h1 := h a List.mem_cons_self b List.mem_cons_self
    have h2 := sum_zipWith_mono x y fun a' ha b' hb =>
      h a' (List.mem_cons_of_mem _ ha) b' (List.mem_cons_of_mem _ hb)
    grind

/-- Truncation toward zero: `|trunc(a 2^s)| ≤ 2^s |a|`. -/
theorem abs_truncInt_le (a : ℚ) (s : ℤ) : Rat.abs (truncInt (a * 2 ^ s) : ℚ) ≤ 2 ^ s * Rat.abs a := by
  have := (truncInt_spec (a * 2 ^ s)).2
  rw [abs_mul_two_pow] at this
  grind

/-- The componentwise truncation bound of `truncProduct_error` is at most the mixed one. -/
theorem truncSum_le_mixed (s t : ℤ) {x y : List ℚ} (hlen : x.length = y.length) :
    (List.zipWith (fun a b => 2 ^ (-s) * Rat.abs b +
        2 ^ (-(s + t)) * Rat.abs (truncInt (a * 2 ^ s) : ℚ)) x y).sum ≤
      2 ^ (-s) * absSum y + 2 ^ (-t) * absSum x := by
  have hm := sum_zipWith_mono
    (F := fun a b => 2 ^ (-s) * Rat.abs b + 2 ^ (-(s + t)) * Rat.abs (truncInt (a * 2 ^ s) : ℚ))
    (G := fun a b => 2 ^ (-s) * Rat.abs b + 2 ^ (-t) * Rat.abs a) x y (fun a _ b _ => by
      have h1 := Rat.mul_le_mul_of_nonneg_left (abs_truncInt_le a s)
        (Rat.le_of_lt (two_pow_pos (-(s + t))))
      have e : (2 : ℚ) ^ (-(s + t)) * (2 ^ s * Rat.abs a) = 2 ^ (-t) * Rat.abs a := by
        rw [← Rat.mul_assoc, ← two_pow_add, show -(s + t) + s = -t by omega]
      rw [e] at h1
      grind)
  refine Rat.le_trans hm ?_
  rw [sum_zipWith_add_split (fun b => 2 ^ (-s) * Rat.abs b) (fun a => 2 ^ (-t) * Rat.abs a) x y hlen]
  unfold absSum
  rw [sum_map_mul_left, sum_map_mul_left]
  exact Rat.le_refl

/-- **Ozaki-II's truncation error, mixed.** For any shifts `s, t`,
`|x · y − 2^(−s−t) (a · c)| ≤ 2^(−s) Σ|yᵢ| + 2^(−t) Σ|xᵢ|` with `a = trunc(2^s x)`,
`c = trunc(2^t y)`. Uchino, Ozaki and Imamura's Lemma 2 (arXiv:2602.02549, (19)) has the same two
terms plus `k 2^(−s−t)`; truncation toward zero removes it. -/
theorem truncProduct_error_mixed (s t : ℤ) {x y : List ℚ} (hlen : x.length = y.length) :
    Rat.abs (dot x y - 2 ^ (-(s + t)) * (dotZ (scaleTrunc s x) (scaleTrunc t y) : ℚ)) ≤
      2 ^ (-s) * absSum y + 2 ^ (-t) * absSum x :=
  Rat.le_trans (truncProduct_error s t x y hlen) (truncSum_le_mixed s t hlen)

/-- `Σ|xᵢ| ≤ k max|x|`. -/
theorem absSum_le_length_maxAbs (x : List ℚ) : absSum x ≤ x.length * maxAbs x :=
  sum_le_length_mul fun _ ha => abs_le_maxAbs ha

/-- Ozaki-II's shift: `2^(−sₓ) < 2 max|x| 2^(−P)` for a nonzero `x`. -/
theorem two_pow_neg_scaleShift_lt (P : ℕ) {x : List ℚ} (hx : maxAbs x ≠ 0) :
    (2 : ℚ) ^ (-scaleShift P x) < 2 * maxAbs x * 2 ^ (-(P : ℤ)) := by
  have hpos : 0 < maxAbs x := by have := maxAbs_nonneg x; grind
  have hE := ceilLog2_spec hpos
  have hsx : scaleShift P x = P - ceilLog2 (maxAbs x) := by unfold scaleShift; rw [if_neg hx]
  rw [hsx]
  have e : (2 : ℚ) ^ (-((P : ℤ) - ceilLog2 (maxAbs x))) =
      2 ^ (ceilLog2 (maxAbs x) - 1) * 2 * 2 ^ (-(P : ℤ)) := by
    rw [← two_pow_succ, ← two_pow_add]; congr 1; omega
  rw [e]
  have := Rat.mul_lt_mul_of_pos_right hE.1 (two_pow_pos (-(P : ℤ)))
  grind

/-- **Ozaki-II's truncation error with its own shifts, mixed:**
`|x · y − 2^(−sₓ−s_y) (a · c)| ≤ 2^(1−P) (max|x| Σ|yᵢ| + max|y| Σ|xᵢ|)`. -/
theorem truncProduct_error_mixed_max (P : ℕ) {x y : List ℚ} (hlen : x.length = y.length)
    (hx : maxAbs x ≠ 0) (hy : maxAbs y ≠ 0) :
    Rat.abs (dot x y - 2 ^ (-(scaleShift P x + scaleShift P y)) *
        (dotZ (scaleTrunc (scaleShift P x) x) (scaleTrunc (scaleShift P y) y) : ℚ)) ≤
      2 * 2 ^ (-(P : ℤ)) * (maxAbs x * absSum y + maxAbs y * absSum x) := by
  refine Rat.le_trans (truncProduct_error_mixed _ _ hlen) ?_
  have h1 := Rat.mul_le_mul_of_nonneg_right (Rat.le_of_lt (two_pow_neg_scaleShift_lt P hx))
    (absSum_nonneg y)
  have h2 := Rat.mul_le_mul_of_nonneg_right (Rat.le_of_lt (two_pow_neg_scaleShift_lt P hy))
    (absSum_nonneg x)
  grind

/-- **Ozaki-II's truncation error, normwise**, half of `truncProduct_error_normwise`'s:
`|x · y − 2^(−sₓ−s_y) (a · c)| ≤ 4 k max|x| max|y| 2^(−P)`. -/
theorem truncProduct_error_normwise4 (P : ℕ) {x y : List ℚ} (hlen : x.length = y.length)
    (hx : maxAbs x ≠ 0) (hy : maxAbs y ≠ 0) :
    Rat.abs (dot x y - 2 ^ (-(scaleShift P x + scaleShift P y)) *
        (dotZ (scaleTrunc (scaleShift P x) x) (scaleTrunc (scaleShift P y) y) : ℚ)) ≤
      4 * x.length * maxAbs x * maxAbs y * 2 ^ (-(P : ℤ)) := by
  refine Rat.le_trans (truncProduct_error_mixed_max P hlen hx hy) ?_
  have hy' := absSum_le_length_maxAbs y
  have hx' := absSum_le_length_maxAbs x
  rw [← hlen] at hy'
  have hmx := maxAbs_nonneg x
  have hmy := maxAbs_nonneg y
  have a1 := Rat.mul_le_mul_of_nonneg_left hy' hmx
  have a2 := Rat.mul_le_mul_of_nonneg_left hx' hmy
  have hP := two_pow_pos (-(P : ℤ))
  have hsum : maxAbs x * absSum y + maxAbs y * absSum x ≤ 2 * (x.length * maxAbs x * maxAbs y) := by
    grind
  have := Rat.mul_le_mul_of_nonneg_left hsum (show (0 : ℚ) ≤ 2 * 2 ^ (-(P : ℤ)) by grind)
  grind

/-- **Ozaki-II error, mixed.** `ozaki2_error` with the truncation term
`2^(−sₓ) Σ|yᵢ| + 2^(−s_y) Σ|xᵢ|`. -/
theorem ozaki2_error_mixed {mult : MatrixMultiplier} {b bound : ℕ} (hmult : mult.ExactOn b bound)
    {round : ℚ → Option ℚ} {u η : ℚ} (hround : RoundWithin round u η)
    {B : CRTBasis} (hB : B.Valid) (hmb : ∀ m ∈ B.moduli, m ≤ 2 ^ (b + 1))
    (P : ℕ) {x y : List ℚ} (hlen : x.length = y.length)
    (hbound : x.length * (2 ^ b * 2 ^ b) ≤ bound)
    (hrange : 2 * x.length * (2 ^ P * 2 ^ P) < B.modulus) {v : ℚ}
    (hv : ozaki2 mult round B P x y = some v) :
    Rat.abs (v - dot x y) ≤
      u * Rat.abs ((dotZ (scaleTrunc (scaleShift P x) x) (scaleTrunc (scaleShift P y) y) : ℚ) *
        2 ^ (-(scaleShift P x + scaleShift P y))) + η +
      (2 ^ (-scaleShift P x) * absSum y + 2 ^ (-scaleShift P y) * absSum x) := by
  have h := ozaki2_error hmult hround hB hmb P hlen hbound hrange hv
  have := truncSum_le_mixed (scaleShift P x) (scaleShift P y) hlen
  grind

/-! ## Native dot products and summation: Jeannerod and Rump -/

/-- Rump's unit in the first place: `2^⌊log₂ |q|⌋`, and `0` for `0`. -/
def ufp (q : ℚ) : ℚ := if q = 0 then 0 else 2 ^ floorLog2 (Rat.abs q)

theorem ufp_nonneg (q : ℚ) : 0 ≤ ufp q := by
  unfold ufp; split
  · exact Rat.le_refl
  · exact Rat.le_of_lt (two_pow_pos _)

theorem ufp_le_abs (q : ℚ) : ufp q ≤ Rat.abs q := by
  unfold ufp; split
  · rename_i h; subst h; rw [abs_zero]; exact Rat.le_refl
  · rename_i h; exact (floorLog2_spec (Rat.abs_pos_iff.mpr h)).1

/-- What Jeannerod and Rump's proofs need of a rounding `rnd` onto a set `R` of values with unit
roundoff `u`: it rounds to nearest, and the sum of two values of `R` is rounded exactly, or within
`u · ufp` with `±ufp` in `R`. IEEE round to nearest even has it (`roundRNE_jrAdd`): in the
subnormal range the sum of two floating-point numbers is one, and above it the error is half a
unit in the last place, `u · ufp`. -/
def JRAdd (R : ℚ → Prop) (rnd : ℚ → Option ℚ) (u : ℚ) : Prop :=
  RoundsToNearest R rnd ∧
    ∀ a b v, R a → R b → rnd (a + b) = some v →
      v = a + b ∨ (Rat.abs (v - (a + b)) ≤ u * ufp (a + b) ∧ R (ufp (a + b)) ∧ R (-ufp (a + b)))

/-- The values a rounding to nearest onto `R` returns lie in `R`. -/
theorem mapM_mem_of_nearest {R : ℚ → Prop} {rnd : ℚ → Option ℚ} (hN : RoundsToNearest R rnd) :
    ∀ (zs ps : List ℚ), zs.mapM rnd = some ps → ∀ q ∈ ps, R q
  | [], ps, h => by
    simp only [List.mapM_nil, pure, Option.some.injEq] at h
    subst h; simp
  | z :: zs, ps, h => by
    rw [List.mapM_cons] at h
    cases hz : rnd z with
    | none => simp [hz] at h
    | some p =>
      cases hzs : zs.mapM rnd with
      | none => simp [hz, hzs] at h
      | some qs =>
        simp only [hz, hzs, Option.bind_eq_bind, Option.bind_some, pure, Option.some.injEq] at h
        subst h
        intro q hq
        rcases List.mem_cons.mp hq with rfl | hq
        · exact (hN z q hz).1
        · exact mapM_mem_of_nearest hN zs qs hzs q hq

section JR

variable {R : ℚ → Prop} {rnd : ℚ → Option ℚ} {u : ℚ}

/-- A value of `R` rounds to itself. -/
theorem JRAdd.round_self (hJ : JRAdd R rnd u) {t v : ℚ} (ht : R t) (h : rnd t = some v) : v = t := by
  have := (hJ.1 t v h).2 t ht
  rw [show t - t = 0 by grind, abs_zero] at this
  have := abs_eq_zero.mp (Rat.le_antisymm this (abs_nonneg _))
  grind

/-- The error of adding `a` and `b` is at most `|b|` (Jeannerod and Rump, Lemma 2.2). -/
theorem JRAdd.err_le_right (hJ : JRAdd R rnd u) {a b v : ℚ} (ha : R a) (h : rnd (a + b) = some v) :
    Rat.abs (v - (a + b)) ≤ Rat.abs b := by
  have := (hJ.1 _ v h).2 a ha
  rw [abs_sub_comm, show a + b - a = b by grind] at this
  exact this

/-- The error of adding `a` and `b` is at most `|a|`. -/
theorem JRAdd.err_le_left (hJ : JRAdd R rnd u) {a b v : ℚ} (hb : R b) (h : rnd (a + b) = some v) :
    Rat.abs (v - (a + b)) ≤ Rat.abs a := by
  have := (hJ.1 _ v h).2 b hb
  rw [abs_sub_comm, show a + b - b = a by grind] at this
  exact this

/-- The error of adding `a` and `b` is at most `u |a + b|`. -/
theorem JRAdd.err_le_u (hu : 0 ≤ u) (hJ : JRAdd R rnd u) {a b v : ℚ} (ha : R a) (hb : R b)
    (h : rnd (a + b) = some v) : Rat.abs (v - (a + b)) ≤ u * Rat.abs (a + b) := by
  rcases hJ.2 a b v ha hb h with rfl | ⟨h1, _, _⟩
  · rw [show a + b - (a + b) = 0 by grind, abs_zero]
    exact Rat.mul_nonneg hu (abs_nonneg _)
  · exact Rat.le_trans h1 (Rat.mul_le_mul_of_nonneg_left (ufp_le_abs _) hu)

/-- **One step of summing floating-point numbers** (Jeannerod and Rump, Proposition 3.1): adding
`a ∈ R` to an accumulator within `m u P` of `S` (`|S| ≤ P`) gives a result within
`(m + 1) u (P + |a|)` of `S + a`. -/
theorem jr_step_float (hu : 0 ≤ u) (hJ : JRAdd R rnd u) {acc a S P v : ℚ} {m : ℕ}
    (hacc : R acc) (ha : R a) (he : Rat.abs (acc - S) ≤ m * u * P) (hSP : Rat.abs S ≤ P)
    (hv : rnd (acc + a) = some v) :
    Rat.abs (v - (S + a)) ≤ ((m : ℚ) + 1) * u * (P + Rat.abs a) := by
  have hm : (0 : ℚ) ≤ m := Rat.natCast_nonneg
  have hA := abs_nonneg a
  have hδ : Rat.abs (v - (acc + a)) ≤ u * (P + ((m : ℚ) + 1) * Rat.abs a) := by
    by_cases hsmall : Rat.abs a ≤ u * P
    · have h1 := hJ.err_le_right hacc hv
      have : 0 ≤ u * (((m : ℚ) + 1) * Rat.abs a) :=
        Rat.mul_nonneg hu (Rat.mul_nonneg (by grind) hA)
      grind
    · have h1 := hJ.err_le_u hu hacc ha hv
      have h2 : Rat.abs (acc + a) ≤ Rat.abs (acc - S) + Rat.abs S + Rat.abs a := by
        have := abs_add_le (acc - S) S
        have := abs_add_le (acc - S + S) a
        rw [show acc - S + S + a = acc + a by grind] at this
        rw [show acc - S + S = acc by grind] at *
        grind
      have h3 : (m : ℚ) * (u * P) ≤ m * Rat.abs a :=
        Rat.mul_le_mul_of_nonneg_left (Rat.le_of_lt (Rat.not_le.mp hsmall)) hm
      have h4 : Rat.abs (acc + a) ≤ P + ((m : ℚ) + 1) * Rat.abs a := by grind
      have := Rat.mul_le_mul_of_nonneg_left h4 hu
      grind
  have := abs_add_le (v - (acc + a)) (acc - S)
  rw [show v - (acc + a) + (acc - S) = v - (S + a) by grind] at this
  grind

/-- **Summing floating-point numbers left to right** (Jeannerod and Rump, Proposition 3.1, after
Rump 2012): from an accumulator within `m u P` of `S`, adding `ts ⊆ R` one by one ends within
`(m + n) u (P + Σ|tᵢ|)` of `S + Σtᵢ`. Underflow is allowed. -/
theorem jr_sumWith_float (hu : 0 ≤ u) (hJ : JRAdd R rnd u) :
    ∀ (ts : List ℚ) (acc S P v : ℚ) (m : ℕ), R acc → (∀ t ∈ ts, R t) →
      Rat.abs (acc - S) ≤ m * u * P → Rat.abs S ≤ P →
      sumWith (addOfRound rnd) acc ts = some v →
      Rat.abs (v - (S + ts.sum)) ≤ ((m : ℚ) + ts.length) * u * (P + (ts.map Rat.abs).sum)
  | [], acc, S, P, v, m, _, _, he, _, hv => by
    simp only [sumWith, Option.some.injEq] at hv
    subst hv
    simp only [List.sum_nil, List.length_nil, List.map_nil]
    rw [show S + 0 = S by grind, show ((0 : ℕ) : ℚ) = 0 from rfl, show P + 0 = P by grind]
    grind
  | t :: ts, acc, S, P, v, m, hacc, hts, he, hSP, hv => by
    simp only [sumWith, addOfRound] at hv
    cases h1 : rnd (acc + t) with
    | none => simp [h1] at hv
    | some w =>
      rw [h1, Option.bind_some] at hv
      have ht := hts t List.mem_cons_self
      have hstep := jr_step_float hu hJ hacc ht he hSP h1
      have hw : R w := (hJ.1 _ w h1).1
      have hstep' : Rat.abs (w - (S + t)) ≤ ((m + 1 : ℕ) : ℚ) * u * (P + Rat.abs t) := by
        rw [natCast_succ]; exact hstep
      have hSP' : Rat.abs (S + t) ≤ P + Rat.abs t := Rat.le_trans (abs_add_le S t) (by grind)
      have ih := jr_sumWith_float hu hJ ts w (S + t) (P + Rat.abs t) v (m + 1) hw
        (fun t' ht' => hts t' (List.mem_cons_of_mem _ ht')) hstep' hSP' hv
      simp only [List.sum_cons, List.length_cons, List.map_cons, natCast_succ] at ih ⊢
      rw [show S + (t + ts.sum) = S + t + ts.sum by grind,
        show ((m : ℚ) + (ts.length + 1)) = (m + 1 + ts.length) by grind,
        show P + (Rat.abs t + (ts.map Rat.abs).sum) = P + Rat.abs t + (ts.map Rat.abs).sum by grind]
      exact ih

/-- **Recursive summation of floating-point numbers** (Jeannerod and Rump, Proposition 3.1):
`|fl(Σ tᵢ) − Σ tᵢ| ≤ (n − 1) u Σ|tᵢ|` for `n` values of `R` added left to right from `0`, with
no condition on `n` and underflow allowed. -/
theorem sumWith_error_jr (hu : 0 ≤ u) (hJ : JRAdd R rnd u) {ts : List ℚ} (hts : ∀ t ∈ ts, R t)
    {v : ℚ} (hv : sumWith (addOfRound rnd) 0 ts = some v) :
    Rat.abs (v - ts.sum) ≤ ((ts.length - 1 : ℕ) : ℚ) * u * (ts.map Rat.abs).sum := by
  cases ts with
  | nil =>
    simp only [sumWith, Option.some.injEq] at hv
    subst hv
    simp only [List.sum_nil, List.map_nil]
    rw [show (0 : ℚ) - 0 = 0 by grind, abs_zero]; grind
  | cons t ts =>
    simp only [sumWith, addOfRound] at hv
    cases h1 : rnd (0 + t) with
    | none => simp [h1] at hv
    | some w =>
      rw [h1, Option.bind_some] at hv
      have ht := hts t List.mem_cons_self
      rw [show (0 : ℚ) + t = t by grind] at h1
      have hw := hJ.round_self ht h1
      subst hw
      have := jr_sumWith_float hu hJ ts w w (Rat.abs w) v 0 ht
        (fun t' ht' => hts t' (List.mem_cons_of_mem _ ht'))
        (by rw [show w - w = 0 by grind, abs_zero]; grind) Rat.le_refl hv
      simp only [List.sum_cons, List.length_cons, List.map_cons, Nat.add_sub_cancel]
      rw [show ((0 : ℕ) : ℚ) = 0 from rfl, Rat.zero_add] at this
      exact this

/-- **One step of a dot product** (Jeannerod and Rump, Proposition 4.1): adding `p = fl(z)`, with
`|p − z| ≤ u |z|`, to an accumulator within `n u P` of `S` (`n ≥ 1`, `|S| ≤ P`) gives a result
within `(n + 1) u (P + |z|)` of `S + z`. -/
theorem jr_step_rounded (hu : 0 ≤ u) (hJ : JRAdd R rnd u) {acc p S P z v : ℚ} {n : ℕ}
    (hn : 1 ≤ n) (hacc : R acc) (hp : R p) (he1 : Rat.abs (acc - S) ≤ n * u * P)
    (hSP : Rat.abs S ≤ P) (he2 : Rat.abs (p - z) ≤ u * Rat.abs z)
    (hv : rnd (acc + p) = some v) :
    Rat.abs (v - (S + z)) ≤ ((n : ℚ) + 1) * u * (P + Rat.abs z) := by
  have hn' : (1 : ℚ) ≤ n := by exact_mod_cast hn
  have hz := abs_nonneg z
  have hP : 0 ≤ P := Rat.le_trans (abs_nonneg S) hSP
  -- `|s| ≤ n u P + P + u |z| + |z|` for `s = acc + p`
  have hs : Rat.abs (acc + p) ≤ Rat.abs (acc - S) + Rat.abs S + Rat.abs (p - z) + Rat.abs z := by
    have e : acc + p = (acc - S) + S + (p - z) + z := by grind
    rw [e]
    have := abs_add_le ((acc - S) + S + (p - z)) z
    have := abs_add_le ((acc - S) + S) (p - z)
    have := abs_add_le (acc - S) S
    grind
  have hδ : Rat.abs (v - (acc + p)) ≤ u * (P + n * Rat.abs z) := by
    have hnz : u * Rat.abs z ≤ u * (n * Rat.abs z) := by
      have := Rat.mul_le_mul_of_nonneg_right hn' hz
      exact Rat.mul_le_mul_of_nonneg_left (by grind) hu
    by_cases hsmall : Rat.abs z ≤ u * P
    · have h1 := hJ.err_le_right hacc hv
      have h2 : Rat.abs p ≤ Rat.abs (p - z) + Rat.abs z := by
        have := abs_add_le (p - z) z; rwa [show p - z + z = p by grind] at this
      grind
    · have hbig : u * P < Rat.abs z := Rat.not_le.mp hsmall
      rcases hJ.2 acc p v hacc hp hv with rfl | ⟨h1, hR1, hR2⟩
      · rw [show acc + p - (acc + p) = 0 by grind, abs_zero]
        exact Rat.mul_nonneg hu (by have := Rat.mul_nonneg (show (0 : ℚ) ≤ n from Rat.natCast_nonneg) hz; grind)
      · by_cases hu2 : ufp (acc + p) ≤ P + n * Rat.abs z
        · exact Rat.le_trans h1 (Rat.mul_le_mul_of_nonneg_left hu2 hu)
        · have hlt : P + n * Rat.abs z < ufp (acc + p) := Rat.not_le.mp hu2
          -- `±ufp(s)` is a value of `R`, at distance `|s| − ufp(s)` from `s`
          have hcomp : Rat.abs (v - (acc + p)) ≤ Rat.abs (acc + p) - ufp (acc + p) := by
            have hu0 := ufp_le_abs (acc + p)
            by_cases hsg : 0 ≤ acc + p
            · have := (hJ.1 _ v hv).2 _ hR1
              rw [abs_of_nonneg hsg] at hu0
              rw [abs_sub_comm (acc + p) v,
                abs_of_nonneg (show 0 ≤ acc + p - ufp (acc + p) by grind)] at this
              rw [abs_of_nonneg hsg]; exact this
            · have hneg : acc + p < 0 := Rat.not_le.mp hsg
              have := (hJ.1 _ v hv).2 _ hR2
              rw [abs_of_neg hneg] at hu0
              have e : acc + p - -ufp (acc + p) = -(-(acc + p) - ufp (acc + p)) := by grind
              rw [abs_sub_comm (acc + p) v, e, abs_neg,
                abs_of_nonneg (show 0 ≤ -(acc + p) - ufp (acc + p) by grind)] at this
              rw [abs_of_neg hneg]; grind
          have hmul : ((n : ℚ) - 1) * (u * P) ≤ ((n : ℚ) - 1) * Rat.abs z :=
            Rat.mul_le_mul_of_nonneg_left (Rat.le_of_lt hbig) (by grind)
          have hnP : (n : ℚ) * u * P = (n : ℚ) * (u * P) := by grind
          have hnuP := Rat.mul_le_mul_of_nonneg_left (Rat.le_of_lt hbig) (show (0 : ℚ) ≤ u from hu)
          have : 0 ≤ u * (n * Rat.abs z) := Rat.mul_nonneg hu (Rat.mul_nonneg (by grind) hz)
          grind
  have := abs_add_le (v - (acc + p)) (acc - S)
  have := abs_add_le (v - (acc + p) + (acc - S)) (p - z)
  rw [show v - (acc + p) + (acc - S) + (p - z) = v - (S + z) by grind] at this
  have : u * Rat.abs z ≤ u * Rat.abs z := Rat.le_refl
  grind

/-- **Summing rounded values left to right** (Jeannerod and Rump, Proposition 4.1): from an
accumulator within `n u P` of `S` (`n ≥ 1`), adding `fl(zᵢ)` one by one, each within `u |zᵢ|`
of `zᵢ`, ends within `(n + m) u (P + Σ|zᵢ|)` of `S + Σzᵢ`. -/
theorem jr_sumWith_rounded (hu : 0 ≤ u) (hJ : JRAdd R rnd u) :
    ∀ (zs ps : List ℚ) (acc S P v : ℚ) (n : ℕ), 1 ≤ n → R acc →
      Rat.abs (acc - S) ≤ n * u * P → Rat.abs S ≤ P →
      zs.mapM rnd = some ps → (∀ z ∈ zs, ∀ p, rnd z = some p → Rat.abs (p - z) ≤ u * Rat.abs z) →
      sumWith (addOfRound rnd) acc ps = some v →
      Rat.abs (v - (S + zs.sum)) ≤ ((n : ℚ) + zs.length) * u * (P + (zs.map Rat.abs).sum)
  | [], ps, acc, S, P, v, n, _, _, he, _, hmap, _, hv => by
    simp only [List.mapM_nil, pure, Option.some.injEq] at hmap
    subst hmap
    simp only [sumWith, Option.some.injEq] at hv
    subst hv
    simp only [List.sum_nil, List.length_nil, List.map_nil]
    rw [show S + 0 = S by grind, show ((0 : ℕ) : ℚ) = 0 from rfl, show P + 0 = P by grind]
    grind
  | z :: zs, ps, acc, S, P, v, n, hn, hacc, he, hSP, hmap, hz, hv => by
    rw [List.mapM_cons] at hmap
    cases hz1 : rnd z with
    | none => simp [hz1] at hmap
    | some p =>
      cases hzs : zs.mapM rnd with
      | none => simp [hz1, hzs] at hmap
      | some qs =>
        simp only [hz1, hzs, Option.bind_eq_bind, Option.bind_some, pure, Option.some.injEq] at hmap
        subst hmap
        simp only [sumWith, addOfRound] at hv
        cases h1 : rnd (acc + p) with
        | none => simp [h1] at hv
        | some w =>
          rw [h1, Option.bind_some] at hv
          have hp : R p := (hJ.1 z p hz1).1
          have he2 := hz z List.mem_cons_self p hz1
          have hstep := jr_step_rounded hu hJ hn hacc hp he hSP he2 h1
          have hw : R w := (hJ.1 _ w h1).1
          have hstep' : Rat.abs (w - (S + z)) ≤ ((n + 1 : ℕ) : ℚ) * u * (P + Rat.abs z) := by
            rw [natCast_succ]; exact hstep
          have hSP' : Rat.abs (S + z) ≤ P + Rat.abs z := Rat.le_trans (abs_add_le S z) (by grind)
          have ih := jr_sumWith_rounded hu hJ zs qs w (S + z) (P + Rat.abs z) v (n + 1) (by omega) hw
            hstep' hSP' hzs (fun z' hz' => hz z' (List.mem_cons_of_mem _ hz')) hv
          simp only [List.sum_cons, List.length_cons, List.map_cons, natCast_succ] at ih ⊢
          rw [show S + (z + zs.sum) = S + z + zs.sum by grind,
            show ((n : ℚ) + (zs.length + 1)) = (n + 1 + zs.length) by grind,
            show P + (Rat.abs z + (zs.map Rat.abs).sum) = P + Rat.abs z + (zs.map Rat.abs).sum by
              grind]
          exact ih

/-- **The native dot product, Jeannerod and Rump** (Theorem 4.2, left to right): if every product
is rounded within `u |xᵢyᵢ|` (no underflow), then `|fl(x · y) − x · y| ≤ k u Σ|xᵢyᵢ|` for `k`
products, for every `k`. -/
theorem nativeDot_error_jr (hu : 0 ≤ u) (hJ : JRAdd R rnd u) {x y : List ℚ}
    (hz : ∀ z ∈ List.zipWith (· * ·) x y, ∀ p, rnd z = some p → Rat.abs (p - z) ≤ u * Rat.abs z)
    {v : ℚ} (h : nativeDot rnd x y = some v) :
    Rat.abs (v - dot x y) ≤
      (List.zipWith (· * ·) x y).length * u * ((List.zipWith (· * ·) x y).map Rat.abs).sum := by
  unfold nativeDot at h
  have hd : dot x y = (List.zipWith (· * ·) x y).sum := rfl
  rw [hd]
  revert h hz
  generalize List.zipWith (· * ·) x y = Z
  intro hz h
  cases Z with
  | nil =>
    simp only [Option.some.injEq] at h
    subst h
    simp only [List.sum_nil, List.map_nil, List.length_nil]
    rw [show (0 : ℚ) - 0 = 0 by grind, abs_zero]; grind
  | cons z zs =>
    cases hz1 : rnd z with
    | none => simp [hz1] at h
    | some p =>
      cases hzs : zs.mapM rnd with
      | none => simp [hz1, hzs] at h
      | some ps =>
        simp only [hz1, hzs, Option.bind_some] at h
        have hp : R p := (hJ.1 z p hz1).1
        have he := hz z List.mem_cons_self p hz1
        have := jr_sumWith_rounded hu hJ zs ps p z (Rat.abs z) v 1 (Nat.le_refl 1) hp
          (by rw [show ((1 : ℕ) : ℚ) = 1 from rfl, Rat.one_mul]; exact he) Rat.le_refl hzs
          (fun z' hz' => hz z' (List.mem_cons_of_mem _ hz')) h
        simp only [List.sum_cons, List.length_cons, List.map_cons, natCast_succ]
        rw [show ((1 : ℕ) : ℚ) = 1 from rfl] at this
        rw [show ((zs.length : ℚ) + 1) = 1 + zs.length by grind]
        exact this

/-- **The native dot product with underflow**: with a rounding of relative error `u` and absolute
error `η` on the products, `|fl(x · y) − x · y| ≤ (k u + (k − 1) u²) Σ|xᵢyᵢ| + k (1 + (k − 1) u) η`.
The products' rounding errors are added to Jeannerod and Rump's summation bound, which allows
underflow; the `u²` term is the price of not assuming normal products (Jeannerod and Rump's
`γ''ₙ`, §4). -/
theorem nativeDot_error_jr_underflow {η : ℚ} (hu : 0 ≤ u) (hJ : JRAdd R rnd u)
    (hr : RoundWithin rnd u η) {x y : List ℚ} {v : ℚ} (h : nativeDot rnd x y = some v) :
    Rat.abs (v - dot x y) ≤
      ((List.zipWith (· * ·) x y).length * u +
          (((List.zipWith (· * ·) x y).length : ℚ) - 1) * u * u) *
          ((List.zipWith (· * ·) x y).map Rat.abs).sum +
        (List.zipWith (· * ·) x y).length *
          (1 + (((List.zipWith (· * ·) x y).length : ℚ) - 1) * u) * η := by
  unfold nativeDot at h
  have hd : dot x y = (List.zipWith (· * ·) x y).sum := rfl
  rw [hd]
  revert h
  generalize List.zipWith (· * ·) x y = Z
  intro h
  cases Z with
  | nil =>
    simp only [Option.some.injEq] at h
    subst h
    simp only [List.sum_nil, List.map_nil, List.length_nil]
    rw [show (0 : ℚ) - 0 = 0 by grind, abs_zero]; grind
  | cons z zs =>
    cases hz1 : rnd z with
    | none => simp [hz1] at h
    | some p =>
      cases hzs : zs.mapM rnd with
      | none => simp [hz1, hzs] at h
      | some ps =>
        simp only [hz1, hzs, Option.bind_some] at h
        have hp : R p := (hJ.1 z p hz1).1
        have hps := mapM_mem_of_nearest hJ.1 zs ps hzs
        have hsum := jr_sumWith_float hu hJ ps p p (Rat.abs p) v 0 hp hps
          (by rw [show p - p = 0 by grind, abs_zero]; grind) Rat.le_refl h
        have hmap : (z :: zs).mapM rnd = some (p :: ps) := by
          rw [List.mapM_cons]; simp [hz1, hzs]
        obtain ⟨hl, hs, ha⟩ := mapM_round_bounds hr (z :: zs) (p :: ps) hmap
        simp only [List.length_cons] at hl
        have hlen : ps.length = zs.length := by omega
        simp only [List.sum_cons, List.map_cons, List.length_cons, natCast_succ] at hs ha ⊢
        rw [hlen, show ((0 : ℕ) : ℚ) = 0 from rfl, Rat.zero_add] at hsum
        generalize hA : Rat.abs z + (zs.map Rat.abs).sum = A at *
        generalize hQ : Rat.abs p + (ps.map Rat.abs).sum = Q at *
        generalize hK : (zs.length : ℚ) = K at *
        have hK0 : 0 ≤ K := by rw [← hK]; exact Rat.natCast_nonneg
        have hKu : 0 ≤ K * u := Rat.mul_nonneg hK0 hu
        have hQ' := Rat.mul_le_mul_of_nonneg_left ha hKu
        have htri := abs_add_le (v - (p + ps.sum)) (p + ps.sum - (z + zs.sum))
        rw [show v - (p + ps.sum) + (p + ps.sum - (z + zs.sum)) = v - (z + zs.sum) by grind] at htri
        rw [show K + 1 - 1 = K by grind]
        grind

end JR


/-! ## IEEE round to nearest even has what Jeannerod and Rump need -/

section IEEE

variable {p : ℕ} {emin emax : ℤ}

/-- `2^e` is a value of the format for `emin ≤ e ≤ emax`. -/
theorem formatValue_two_pow (hp : 0 < p) {e : ℤ} (h1 : emin ≤ e) (h2 : e ≤ emax) :
    FormatValue p emin emax ((2 : ℚ) ^ e) := by
  refine ⟨((2 ^ (p - 1) : ℕ) : ℤ), e, h1, h2, ?_, ?_⟩
  · have : 2 ^ (p - 1) < 2 ^ p := Nat.pow_lt_pow_right (by decide) (by omega)
    simpa using this
  · rw [Rat.intCast_natCast, ← two_pow_natCast, ← two_pow_add]; congr 1; omega

/-- `2^e` is a value of the format without an upper limit on the exponent, for `emin ≤ e`. -/
theorem uValue_two_pow (hp : 0 < p) {e : ℤ} (h1 : emin ≤ e) : UValue p emin ((2 : ℚ) ^ e) := by
  refine ⟨((2 ^ (p - 1) : ℕ) : ℤ), e, h1, ?_, ?_⟩
  · have : 2 ^ (p - 1) < 2 ^ p := Nat.pow_lt_pow_right (by decide) (by omega)
    simpa using this
  · rw [Rat.intCast_natCast, ← two_pow_natCast, ← two_pow_add]; congr 1; omega

/-- A rounding that does not overflow has an input below `2^(emax + 1)`. -/
theorem abs_lt_of_roundRNE (hp : 0 < p) (hle : emin ≤ emax) {q v : ℚ}
    (h : roundRNE p emin emax q = some v) : Rat.abs q < 2 ^ (emax + 1) := by
  obtain ⟨_, hM⟩ := roundRNE_eq_some.mp h
  have hU := uValue_two_pow (emin := emin) hp (e := emax + 1) (by omega)
  have hM' := maxFormat_lt (p := p) (emax := emax)
  refine Rat.not_le.mp fun hc => ?_
  by_cases hq : 0 ≤ q
  · rw [abs_of_nonneg hq] at hc
    have := rneU_monotone (emin := emin) hp hc
    rw [rneU_of_uValue hp hU] at this
    have := le_abs_self (rneU p emin q)
    grind
  · have hq' : q < 0 := Rat.not_le.mp hq
    rw [abs_of_neg hq'] at hc
    have h2 : q ≤ -2 ^ (emax + 1) := by grind
    have := rneU_monotone (emin := emin) hp h2
    rw [rneU_of_uValue hp hU.neg] at this
    have := neg_abs_le (rneU p emin q)
    grind

/-- The sum of two values of the format below `2^emin` (in the subnormal range) is a value of the
format: addition there is exact. -/
theorem formatValue_add_small (hp : 0 < p) (hle : emin ≤ emax) {a b : ℚ}
    (ha : FormatValue p emin emax a) (hb : FormatValue p emin emax b)
    (hs : Rat.abs (a + b) < 2 ^ emin) : FormatValue p emin emax (a + b) := by
  obtain ⟨za, hza⟩ := formatValue_gridMultiple ha
  obtain ⟨zb, hzb⟩ := formatValue_gridMultiple hb
  have e : a + b = ((za + zb : ℤ) : ℚ) * 2 ^ (emin - ((p : ℤ) - 1)) := by
    rw [hza, hzb, Rat.intCast_add]; grind
  refine ⟨za + zb, emin, Int.le_refl _, hle, ?_, e⟩
  rw [e, abs_mul, abs_two_pow, abs_intCast] at hs
  have e2 : (2 : ℚ) ^ emin = ((2 ^ (p - 1) : ℕ) : ℚ) * 2 ^ (emin - ((p : ℤ) - 1)) := by
    rw [← two_pow_natCast, ← two_pow_add]; congr 1; omega
  rw [e2] at hs
  have hlt : (za + zb).natAbs < 2 ^ (p - 1) := by
    refine Nat.lt_of_not_le fun hge => ?_
    have hge' : ((2 ^ (p - 1) : ℕ) : ℚ) ≤ (((za + zb).natAbs : ℕ) : ℚ) := by exact_mod_cast hge
    have := Rat.mul_le_mul_of_nonneg_right hge' (Rat.le_of_lt (two_pow_pos (emin - ((p : ℤ) - 1))))
    grind
  have : 2 ^ (p - 1) ≤ 2 ^ p := Nat.pow_le_pow_right (by decide) (by omega)
  omega

/-- Above the subnormal range, rounding to nearest even errs by at most half a unit in the last
place: `|rne(a) − a| ≤ 2^(−p) · 2^⌊log₂ a⌋`. -/
theorem rneMag_error_ufp {a : ℚ} (ha : (2 : ℚ) ^ emin ≤ a) :
    Rat.abs (rneMag p emin a - a) ≤ 2 ^ (-(p : ℤ)) * 2 ^ floorLog2 a := by
  have hpos : 0 < a := by have := two_pow_pos emin; grind
  have hfl := floorLog2_spec hpos
  have he : emin ≤ floorLog2 a := by
    have := two_pow_lt_iff.mp (show (2 : ℚ) ^ emin < 2 ^ (floorLog2 a + 1) by grind); omega
  have hg : rneGrid p emin a = floorLog2 a - ((p : ℤ) - 1) := by
    rw [rneGrid_def]; congr 1; omega
  have h1 := roundNearestEven_error (a / 2 ^ rneGrid p emin a)
  unfold rneMag
  rw [abs_sub_comm, abs_sub_mul_two_pow]
  generalize Rat.abs (a / 2 ^ rneGrid p emin a - roundNearestEven (a / 2 ^ rneGrid p emin a)) = d at *
  have e : (2 : ℚ) ^ rneGrid p emin a = 2 * (2 ^ (-(p : ℤ)) * 2 ^ floorLog2 a) := by
    rw [hg, ← two_pow_add, show floorLog2 a - ((p : ℤ) - 1) = -(p : ℤ) + floorLog2 a + 1 by omega,
      two_pow_succ]
    grind
  rw [e]
  have hX : 0 ≤ (2 : ℚ) ^ (-(p : ℤ)) * 2 ^ floorLog2 a :=
    Rat.mul_nonneg (Rat.le_of_lt (two_pow_pos _)) (Rat.le_of_lt (two_pow_pos _))
  have := Rat.mul_le_mul_of_nonneg_right h1 hX
  generalize (2 : ℚ) ^ (-(p : ℤ)) * 2 ^ floorLog2 a = X at *
  grind

/-- `|rne(q) − q| ≤ 2^(−p) ufp(q)` for `|q| ≥ 2^emin`. -/
theorem rneU_error_ufp {q : ℚ} (hq : (2 : ℚ) ^ emin ≤ Rat.abs q) :
    Rat.abs (rneU p emin q - q) ≤ 2 ^ (-(p : ℤ)) * ufp q := by
  have hne : q ≠ 0 := fun h => by
    subst h; rw [abs_zero] at hq; have := two_pow_pos emin; grind
  have hu : ufp q = 2 ^ floorLog2 (Rat.abs q) := by unfold ufp; rw [if_neg hne]
  rw [hu]
  unfold rneU
  split
  · rename_i hneg
    rw [abs_of_neg hneg] at hq ⊢
    have e : -rneMag p emin (-q) - q = -(rneMag p emin (-q) - -q) := by grind
    rw [e, abs_neg]
    exact rneMag_error_ufp hq
  · rename_i hnn
    have hq0 : 0 ≤ q := by grind
    rw [abs_of_nonneg hq0] at hq ⊢
    exact rneMag_error_ufp hq

/-- **IEEE round to nearest even meets Jeannerod and Rump's hypotheses**, with `u = 2^(−p)`. -/
theorem roundRNE_jrAdd (hp : 0 < p) (hle : emin ≤ emax) :
    JRAdd (FormatValue p emin emax) (roundRNE p emin emax) (2 ^ (-(p : ℤ))) := by
  refine ⟨roundRNE_nearest hp hle, fun a b v ha hb h => ?_⟩
  by_cases hs : Rat.abs (a + b) < 2 ^ emin
  · left
    have hf := formatValue_add_small hp hle ha hb hs
    rw [roundRNE_of_formatValue hp hf] at h
    exact (Option.some.inj h).symm
  · right
    have hs' : (2 : ℚ) ^ emin ≤ Rat.abs (a + b) := Rat.not_lt.mp hs
    have hlt := abs_lt_of_roundRNE hp hle h
    obtain ⟨rfl, _⟩ := roundRNE_eq_some.mp h
    have hpos : 0 < Rat.abs (a + b) := by have := two_pow_pos emin; grind
    have hne : a + b ≠ 0 := fun h0 => by rw [h0, abs_zero] at hpos; exact Rat.lt_irrefl hpos
    have hu : ufp (a + b) = 2 ^ floorLog2 (Rat.abs (a + b)) := by unfold ufp; rw [if_neg hne]
    have hfl := floorLog2_spec hpos
    have he1 : emin ≤ floorLog2 (Rat.abs (a + b)) := by
      have := two_pow_lt_iff.mp (show (2 : ℚ) ^ emin < 2 ^ (floorLog2 (Rat.abs (a + b)) + 1) by grind)
      omega
    have he2 : floorLog2 (Rat.abs (a + b)) ≤ emax := by
      have := two_pow_lt_iff.mp
        (show (2 : ℚ) ^ floorLog2 (Rat.abs (a + b)) < 2 ^ (emax + 1) by grind)
      omega
    refine ⟨rneU_error_ufp hs', ?_, ?_⟩
    · rw [hu]; exact formatValue_two_pow hp he1 he2
    · rw [hu]; exact (formatValue_two_pow hp he1 he2).neg

/-- A product that is a value of the format, or at least `2^emin` in magnitude, is rounded within
`2^(−p)` relative error: no underflow. -/
theorem roundRNE_error_normal (hp : 0 < p) {z v : ℚ}
    (hz : (2 : ℚ) ^ emin ≤ Rat.abs z ∨ FormatValue p emin emax z)
    (h : roundRNE p emin emax z = some v) : Rat.abs (v - z) ≤ 2 ^ (-(p : ℤ)) * Rat.abs z := by
  rcases hz with hz | hz
  · obtain ⟨rfl, _⟩ := roundRNE_eq_some.mp h
    exact Rat.le_trans (rneU_error_ufp hz)
      (Rat.mul_le_mul_of_nonneg_left (ufp_le_abs z) (Rat.le_of_lt (two_pow_pos _)))
  · rw [roundRNE_of_formatValue hp hz] at h
    cases Option.some.inj h
    rw [show z - z = 0 by grind, abs_zero]
    exact Rat.mul_nonneg (Rat.le_of_lt (two_pow_pos _)) (abs_nonneg z)

/-- **Native dot products in IEEE arithmetic** (Jeannerod and Rump, Theorem 4.2): when no product
underflows, `|fl(x · y) − x · y| ≤ k 2^(−p) Σ|xᵢyᵢ|` for every `k`. -/
theorem nativeDot_error_jr_rne (hp : 0 < p) (hle : emin ≤ emax) {x y : List ℚ}
    (hz : ∀ z ∈ List.zipWith (· * ·) x y, (2 : ℚ) ^ emin ≤ Rat.abs z ∨ FormatValue p emin emax z)
    {v : ℚ} (h : nativeDot (roundRNE p emin emax) x y = some v) :
    Rat.abs (v - dot x y) ≤
      (List.zipWith (· * ·) x y).length * 2 ^ (-(p : ℤ)) *
        ((List.zipWith (· * ·) x y).map Rat.abs).sum :=
  nativeDot_error_jr (Rat.le_of_lt (two_pow_pos _)) (roundRNE_jrAdd hp hle)
    (fun z hz' _ hr => roundRNE_error_normal hp (hz z hz') hr) h

/-- **Native dot products in IEEE arithmetic, with underflow**:
`(k u + (k − 1) u²) Σ|xᵢyᵢ| + k (1 + (k − 1) u) 2^(emin − p)` with `u = 2^(−p)`. -/
theorem nativeDot_error_jr_rne_underflow (hp : 0 < p) (hle : emin ≤ emax) {x y : List ℚ} {v : ℚ}
    (h : nativeDot (roundRNE p emin emax) x y = some v) :
    Rat.abs (v - dot x y) ≤
      ((List.zipWith (· * ·) x y).length * 2 ^ (-(p : ℤ)) +
          (((List.zipWith (· * ·) x y).length : ℚ) - 1) * 2 ^ (-(p : ℤ)) * 2 ^ (-(p : ℤ))) *
          ((List.zipWith (· * ·) x y).map Rat.abs).sum +
        (List.zipWith (· * ·) x y).length *
          (1 + (((List.zipWith (· * ·) x y).length : ℚ) - 1) * 2 ^ (-(p : ℤ))) * 2 ^ (emin - p) :=
  nativeDot_error_jr_underflow (Rat.le_of_lt (two_pow_pos _)) (roundRNE_jrAdd hp hle)
    roundRNE_within h

end IEEE

/-- **Binary64 native dot products** (Jeannerod and Rump): `k 2^-53 Σ|xᵢyᵢ|` when no product is
below `2^-1022` (unless it is a binary64 value, zero included). -/
theorem nativeDot_error_jr_rne64 {x y : List ℚ}
    (hz : ∀ z ∈ List.zipWith (· * ·) x y, (2 : ℚ) ^ (-1022 : ℤ) ≤ Rat.abs z ∨ Binary64Value z)
    {v : ℚ} (h : nativeDot rne64 x y = some v) :
    Rat.abs (v - dot x y) ≤
      (List.zipWith (· * ·) x y).length * 2 ^ (-53 : ℤ) *
        ((List.zipWith (· * ·) x y).map Rat.abs).sum :=
  nativeDot_error_jr_rne (p := 53) (emax := 1023) (by decide) (by decide) hz h

/-- **Binary32 native dot products** (Jeannerod and Rump): `k 2^-24 Σ|xᵢyᵢ|` when no product is
below `2^-126` (unless it is a binary32 value). -/
theorem nativeDot_error_jr_rne32 {x y : List ℚ}
    (hz : ∀ z ∈ List.zipWith (· * ·) x y, (2 : ℚ) ^ (-126 : ℤ) ≤ Rat.abs z ∨ Binary32Value z)
    {v : ℚ} (h : nativeDot rne32Q x y = some v) :
    Rat.abs (v - dot x y) ≤
      (List.zipWith (· * ·) x y).length * 2 ^ (-24 : ℤ) *
        ((List.zipWith (· * ·) x y).map Rat.abs).sum :=
  nativeDot_error_jr_rne (p := 24) (emax := 127) (by decide) (by decide) hz h

/-! ## Ozaki-I's recombination: Jeannerod and Rump -/

/-- **Ozaki-I with a floating-point recombination** (Jeannerod and Rump, Proposition 3.1). When the
`n = s(s+1)/2` scaled slice products are values of the working format (true on the Tensor Core in
binary32 for grids in range, `OzakiTC.exactTerm_finiteValue32`) and are added left to right with a
rounding that meets `JRAdd`, the result is within `(n − 1) u Σ|tⱼ|` of their exact sum, with no
underflow term and no condition on `n`; the slicing adds the entrywise bound. -/
theorem ozaki1_error_jr {mult : MatrixMultiplier} {R : ℚ → Prop} {rnd : ℚ → Option ℚ} {u : ℚ}
    {b bound s : ℕ} (hmult : mult.ExactOn b bound) (hu : 0 ≤ u) (hJ : JRAdd R rnd u)
    {x y : List ℚ} (hlen : x.length = y.length) (hbound : x.length * (2 ^ b * 2 ^ b) ≤ bound)
    (hterms : ∀ t ∈ exactTerms b s x y, R t) {v : ℚ}
    (hv : ozaki1 mult (addOfRound rnd) b s x y = some v) :
    Rat.abs (v - dot x y) ≤
      (((trianglePairs s).length - 1 : ℕ) : ℚ) * u * ((exactTerms b s x y).map Rat.abs).sum +
        ((s + 1 : ℕ) : ℚ) * capSum (2 ^ (splitExp b x + splitExp b y - s * (b + 1))) x y := by
  rw [ozaki1_eq_sumWith hmult _ s hlen hbound] at hv
  have h1 := sumWith_error_jr hu hJ hterms hv
  have hlenT : (exactTerms b s x y).length = (trianglePairs s).length := by simp [exactTerms]
  rw [hlenT] at h1
  have h2 := exactTerms_error_sharp b s x y
  have htri : Rat.abs (v - dot x y) ≤ Rat.abs (v - (exactTerms b s x y).sum) +
      Rat.abs (dot x y - (exactTerms b s x y).sum) := by
    have := abs_add_le (v - (exactTerms b s x y).sum) ((exactTerms b s x y).sum - dot x y)
    rw [abs_sub_comm ((exactTerms b s x y).sum) (dot x y)] at this
    have h : v - (exactTerms b s x y).sum + ((exactTerms b s x y).sum - dot x y) = v - dot x y := by
      grind
    rwa [h] at this
  grind

/-- `ozaki1_error_jr` with the terms bounded as in `ozaki1_error`:
`(n − 1) u n k 2^(E+F) + (s + 1) Σᵢ min(2|xᵢyᵢ|, 2^(E+F−s(b+1)))`. -/
theorem ozaki1_error_jr_normwise {mult : MatrixMultiplier} {R : ℚ → Prop} {rnd : ℚ → Option ℚ} {u : ℚ}
    {b bound s : ℕ} (hmult : mult.ExactOn b bound) (hu : 0 ≤ u) (hJ : JRAdd R rnd u)
    {x y : List ℚ} (hlen : x.length = y.length) (hbound : x.length * (2 ^ b * 2 ^ b) ≤ bound)
    (hterms : ∀ t ∈ exactTerms b s x y, R t) {v : ℚ}
    (hv : ozaki1 mult (addOfRound rnd) b s x y = some v) :
    Rat.abs (v - dot x y) ≤
      (((trianglePairs s).length - 1 : ℕ) : ℚ) * u *
          ((trianglePairs s).length * (x.length * 2 ^ (splitExp b x + splitExp b y))) +
        ((s + 1 : ℕ) : ℚ) * capSum (2 ^ (splitExp b x + splitExp b y - s * (b + 1))) x y := by
  have h := ozaki1_error_jr hmult hu hJ hlen hbound hterms hv
  have hT : ((exactTerms b s x y).map Rat.abs).sum ≤
      (trianglePairs s).length * (x.length * 2 ^ (splitExp b x + splitExp b y)) := by
    unfold exactTerms
    rw [List.map_map]
    exact sum_le_length_mul (fun p hp => abs_exactTerm_le b s x y hp)
  have := Rat.mul_le_mul_of_nonneg_left hT
    (Rat.mul_nonneg (show (0 : ℚ) ≤ (((trianglePairs s).length - 1 : ℕ) : ℚ) from Rat.natCast_nonneg) hu)
  grind

end Ozaki
