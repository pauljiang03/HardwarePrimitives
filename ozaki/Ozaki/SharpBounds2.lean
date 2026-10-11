import Ozaki.SharpBounds

/-! # More error bounds: different slice counts, and any order of summation

Two generalizations of the bounds of `Ozaki.SharpBounds`.

* **Different slice counts per matrix** (`dot_eq_exactTermsRect_add`, `exactTermsRect_error`,
  `exactTermsRect_error_uniform`). Abdelfattah, Dongarra, Fasi, Mikaitis and Tisseur, *Analysis of
  floating-point matrix multiplication computed via integer arithmetic* (arXiv:2506.11277, v3
  2026, §4), let the two factors have different slice counts. Here `x` has `sx` slices and `y`
  has `sy`, and the slice products kept are those with `t < sx`, `u < sy` and `t + u < m`: the
  triangle of Ozaki-I is `sx = sy = m = s`, the full rectangle `m = sx + sy`. The error identity
  generalizes `dot_eq_exactTerms_add`: slice `t` of `x` meets the residual of `y` after
  `min sy (m − t)` slices. Every term is bounded as before, and uniformly the error is at most
  `(sx + 1) k 2^(E + F − c(b+1))` with `c = min(sx, sy, m)`, which is `exactTerms_error` for the
  triangle (`exactTermsRect_triangle`). The splitting is ours (round to nearest on grids
  recomputed from what is left), not their fixed-point truncation, so the statement is in our
  terms: the shape is theirs, the constants ours.
* **Jeannerod and Rump in any order** (`sumTree_error_jr`, `dotTree_error_jr`). Jeannerod and
  Rump, *Improved error bounds for inner products in floating-point arithmetic* (SIAM J. Matrix
  Anal. Appl. 34(2), 2013, Proposition 3.1 and Theorem 4.2), state their bounds for any order of
  evaluation; `Ozaki.SharpBounds` proves them left to right. Here a sum is evaluated along any
  binary tree (`SumTree`) whose leaves are any permutation of the terms: summing floating-point
  numbers loses at most `(n − 1) u Σ|tᵢ|`, and a dot product whose products are rounded within
  `u |xᵢyᵢ|` at most `k u Σ|xᵢyᵢ|`, with no condition on `n u` or `k u`. The induction combines two
  subtrees of `n₁ ≥ n₂` leaves with a case split on whether the smaller subtree's magnitude is at
  most `u n₂` times the larger's (`jr_merge`).
* **Ozaki-II with an inexact CRT accumulation** (`reduceApprox_eq`, `ozaki2Approx_error`,
  `ozaki2FP64_error`). Uchino, Ozaki and Imamura (arXiv:2602.02549) accumulate the CRT sum
  `Σ wⱼ rⱼ` in floating point, not exactly. If an accumulator is within `ε` of the exact sum and
  `2 k 2^(2P) + 2ε < M`, the reduction modulo `M` (`Ŝ − M · rne(Ŝ / M)`) still finds the right
  multiple of `M`, and the reconstructed product is within `ε`; the error bound of Ozaki-II gains
  `ε 2^(−s)` twice (before and through the final rounding). For the plain left-to-right binary64
  accumulation `ε = n 2^-53 2^(b+1) Σ|wⱼ|` by Jeannerod and Rump (`crtAccFP64_error`). Their
  implementation splits the large weights to keep products exact; any accumulator with a proved `ε`
  plugs into `ozaki2Approx_error`, but theirs is not modelled here. -/

local notation "ℕ" => Nat
local notation "ℤ" => Int
local notation "ℚ" => Rat

namespace Ozaki

/-! ## Different slice counts per matrix -/

/-- The slice pairs kept with `sx` slices of `x`, `sy` slices of `y` and `t + u < m`, by `t`. -/
def rectPairs (sx sy m : ℕ) : List (ℕ × ℕ) :=
  (List.range sx).flatMap fun t => (List.range (min sy (m - t))).map fun u => (t, u)

theorem mem_rectPairs {sx sy m t u : ℕ} :
    (t, u) ∈ rectPairs sx sy m ↔ t < sx ∧ u < sy ∧ t + u < m := by
  simp only [rectPairs, List.mem_flatMap, List.mem_range, List.mem_map, Prod.mk.injEq]
  constructor
  · rintro ⟨t', ht', u', hu', rfl, rfl⟩; omega
  · intro h; exact ⟨t, h.1, u, by omega, rfl, rfl⟩

/-- The exact terms with `sx` slices of `x`, `sy` slices of `y` and `t + u < m`. -/
def exactTermsRect (b sx sy m : ℕ) (x y : List ℚ) : List ℚ :=
  (rectPairs sx sy m).map (exactTerm (split b sx x).1 (split b sy y).1)

theorem sum_flatMap_map {α β : Type} (l : List α) (g : α → List β) (F : β → ℚ) :
    ((l.flatMap g).map F).sum = (l.map fun a => ((g a).map F).sum).sum := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    rw [List.flatMap_cons, List.map_append, sum_append_q, ih]
    simp only [List.map_cons, List.sum_cons]

/-- Adding over `rectPairs` is adding, for each `t < sx`, over `u < min sy (m − t)`. -/
theorem sum_rectPairs (sx sy m : ℕ) (f : ℕ → ℕ → ℚ) :
    ((rectPairs sx sy m).map fun p => f p.1 p.2).sum =
      ((List.range sx).map fun t => ((List.range (min sy (m - t))).map fun u => f t u).sum).sum := by
  unfold rectPairs
  rw [sum_flatMap_map]
  congr 1
  apply List.map_congr_left
  intro t _
  rw [List.map_map]
  rfl

/-- **Error identity with different slice counts.** `x · y` is the sum of the kept terms, plus the
residual of `x` after `sx` slices against `y`, plus each slice `t` of `x` against the residual of
`y` after `min sy (m − t)` slices. -/
theorem dot_eq_exactTermsRect_add (b sx sy m : ℕ) (x y : List ℚ) :
    dot x y = (exactTermsRect b sx sy m x y).sum + dot (split b sx x).2 y +
      ((List.range sx).map fun t => 2 ^ ((split b sx x).1.getD t default).grid *
        dot (ofInts ((split b sx x).1.getD t default).coeffs)
          (split b (min sy (m - t)) y).2).sum := by
  have hx := split_dot b sx x y
  rw [sum_map_eq_range_getD, (split_length b sx x).1] at hx
  rw [hx]
  have hterm : ∀ t ∈ List.range sx,
      2 ^ ((split b sx x).1.getD t default).grid *
        dot (ofInts ((split b sx x).1.getD t default).coeffs) y =
      ((List.range (min sy (m - t))).map fun u =>
          exactTerm (split b sx x).1 (split b sy y).1 (t, u)).sum +
        2 ^ ((split b sx x).1.getD t default).grid *
          dot (ofInts ((split b sx x).1.getD t default).coeffs) (split b (min sy (m - t)) y).2 := by
    intro t _
    generalize hsl : (split b sx x).1.getD t default = sl
    have hy := split_dot b (min sy (m - t)) y (ofInts sl.coeffs)
    rw [sum_map_eq_range_getD, (split_length b (min sy (m - t)) y).1] at hy
    rw [dot_comm, hy, dot_comm (split b (min sy (m - t)) y).2, Rat.mul_add, ← sum_map_mul_left]
    congr 1
    congr 1
    apply List.map_congr_left
    intro u hu
    have hul := List.mem_range.mp hu
    rw [split_prefix b sy (min sy (m - t)) y (Nat.min_le_left _ _), getD_take _ hul, dot_comm,
      dot_ofInts, exactTerm, hsl, dotZ_comm, two_pow_add]
    grind
  rw [List.map_congr_left hterm, sum_map_add]
  unfold exactTermsRect
  rw [sum_rectPairs sx sy m (fun t u => exactTerm (split b sx x).1 (split b sy y).1 (t, u))]
  grind

/-- Slice `t` of `x` against a residual of `y` after `j` slices: at most
`k 2^(E + F − (t + j)(b+1))`. -/
theorem abs_slice_residual_le (b sx j : ℕ) (x y : List ℚ) {t : ℕ} (ht : t < sx) :
    Rat.abs (2 ^ ((split b sx x).1.getD t default).grid *
        dot (ofInts ((split b sx x).1.getD t default).coeffs) (split b j y).2) ≤
      x.length * 2 ^ (splitExp b x + splitExp b y - ((t + j : ℕ) : ℤ) * (b + 1)) := by
  have hk : (0 : ℚ) ≤ x.length := Rat.natCast_nonneg
  have hmem := getD_mem (l := (split b sx x).1) (t := t) (by rw [(split_length b sx x).1]; exact ht)
  generalize hsl : (split b sx x).1.getD t default = sl at hmem
  have hgrid := split_grid_le b sx x t sl (by
    rw [← hsl, List.getD_eq_getElem?_getD,
      List.getElem?_eq_getElem (by rw [(split_length b sx x).1]; exact ht)]; rfl)
  have hc : ∀ a ∈ ofInts sl.coeffs, Rat.abs a ≤ (2 : ℚ) ^ (b : ℤ) := by
    intro a ha
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp ha
    rw [two_pow_natCast]
    exact abs_intCast_le (split_coeff_bound b sx x sl hmem q hq)
  have hd := abs_dot_le _ _ _ _ hc (split_residual_le b j y)
    (Rat.le_of_lt (two_pow_pos _)) (Rat.le_of_lt (two_pow_pos _))
  rw [ofInts_length, (split_length b sx x).2.1 sl hmem, ← two_pow_add] at hd
  rw [abs_mul, abs_two_pow]
  have hm := Rat.mul_le_mul_of_nonneg_left hd (Rat.le_of_lt (two_pow_pos sl.grid))
  refine Rat.le_trans hm ?_
  have hexp : sl.grid + ((b : ℤ) + (splitExp b y - (j : ℤ) * (b + 1))) ≤
      splitExp b x + splitExp b y - ((t + j : ℕ) : ℤ) * (b + 1) := by
    have hc : ((t + j : ℕ) : ℤ) = (t : ℤ) + j := by omega
    have : ((t + j : ℕ) : ℤ) * (b + 1) = (t : ℤ) * (b + 1) + (j : ℤ) * (b + 1) := by
      rw [hc]; exact Int.add_mul _ _ _
    omega
  have := two_pow_le hexp
  rw [two_pow_add] at this
  have := Rat.mul_le_mul_of_nonneg_left this hk
  grind

/-- **Slicing error with different slice counts.** With `sx` slices of `x`, `sy` of `y` and the
pairs `t + u < m`, `|x · y − Σ terms| ≤ k (2^(E + F − sx(b+1)) + Σ_{t < sx}
2^(E + F − (t + min(sy, m − t))(b+1)))`. -/
theorem exactTermsRect_error (b sx sy m : ℕ) (x y : List ℚ) :
    Rat.abs (dot x y - (exactTermsRect b sx sy m x y).sum) ≤
      x.length * (2 ^ (splitExp b x + splitExp b y - sx * (b + 1)) +
        ((List.range sx).map fun t => (2 : ℚ) ^ (splitExp b x + splitExp b y -
          ((t + min sy (m - t) : ℕ) : ℤ) * (b + 1))).sum) := by
  rw [dot_eq_exactTermsRect_add b sx sy m x y]
  have hk : (0 : ℚ) ≤ x.length := Rat.natCast_nonneg
  have h1 : Rat.abs (dot (split b sx x).2 y) ≤
      x.length * 2 ^ (splitExp b x + splitExp b y - sx * (b + 1)) := by
    have := abs_dot_le (split b sx x).2 y _ _ (split_residual_le b sx x)
      (abs_le_two_pow_splitExp b y) (Rat.le_of_lt (two_pow_pos _)) (Rat.le_of_lt (two_pow_pos _))
    rw [(split_length b sx x).2.2, ← two_pow_add] at this
    have he : splitExp b x - sx * (b + 1) + splitExp b y = splitExp b x + splitExp b y -
      sx * (b + 1) := by omega
    rwa [he] at this
  generalize hF : (fun t => 2 ^ ((split b sx x).1.getD t default).grid *
      dot (ofInts ((split b sx x).1.getD t default).coeffs) (split b (min sy (m - t)) y).2) = F
  have h3 : ((List.range sx).map fun t => Rat.abs (F t)).sum ≤
      ((List.range sx).map fun t => (x.length : ℚ) * 2 ^ (splitExp b x + splitExp b y -
        ((t + min sy (m - t) : ℕ) : ℤ) * (b + 1))).sum := by
    apply sum_le_sum
    intro t ht
    rw [← hF]
    exact abs_slice_residual_le b sx (min sy (m - t)) x y (List.mem_range.mp ht)
  rw [sum_map_mul_left] at h3
  have h4 := abs_sum_le (List.range sx) F
  have h5 := abs_add_le (dot (split b sx x).2 y) ((List.range sx).map F).sum
  have e : (exactTermsRect b sx sy m x y).sum + dot (split b sx x).2 y +
      ((List.range sx).map F).sum - (exactTermsRect b sx sy m x y).sum =
      dot (split b sx x).2 y + ((List.range sx).map F).sum := by grind
  rw [e, Rat.mul_add]
  grind

/-- **Slicing error with different slice counts, uniformly**: at most
`(sx + 1) k 2^(E + F − c(b+1))` with `c = min(sx, sy, m)`. -/
theorem exactTermsRect_error_uniform (b sx sy m : ℕ) (x y : List ℚ) :
    Rat.abs (dot x y - (exactTermsRect b sx sy m x y).sum) ≤
      ((sx + 1 : ℕ) : ℚ) * x.length *
        2 ^ (splitExp b x + splitExp b y - (min (min sx sy) m : ℕ) * (b + 1)) := by
  refine Rat.le_trans (exactTermsRect_error b sx sy m x y) ?_
  generalize hB : (2 : ℚ) ^ (splitExp b x + splitExp b y - (min (min sx sy) m : ℕ) * (b + 1)) = B
  have hk : (0 : ℚ) ≤ x.length := Rat.natCast_nonneg
  have hmul : ∀ c : ℕ, min (min sx sy) m ≤ c →
      (2 : ℚ) ^ (splitExp b x + splitExp b y - (c : ℤ) * (b + 1)) ≤ B := by
    intro c hc
    rw [← hB]
    apply two_pow_le
    have : ((min (min sx sy) m : ℕ) : ℤ) * (b + 1) ≤ (c : ℤ) * (b + 1) :=
      Int.mul_le_mul_of_nonneg_right (by omega) (by omega)
    exact Int.sub_le_sub_left this _
  have h1 := hmul sx (by omega)
  have h2 : ((List.range sx).map fun t => (2 : ℚ) ^ (splitExp b x + splitExp b y -
      ((t + min sy (m - t) : ℕ) : ℤ) * (b + 1))).sum ≤ (List.range sx).length * B :=
    sum_le_length_mul fun t _ => hmul _ (by omega)
  rw [List.length_range] at h2
  have := Rat.mul_le_mul_of_nonneg_left (show 2 ^ (splitExp b x + splitExp b y - sx * (b + 1)) +
    ((List.range sx).map fun t => (2 : ℚ) ^ (splitExp b x + splitExp b y -
      ((t + min sy (m - t) : ℕ) : ℤ) * (b + 1))).sum ≤ B + sx * B by grind) hk
  refine Rat.le_trans this ?_
  rw [natCast_succ]
  grind

/-- The triangle is the case `sx = sy = m = s`: the same terms, so the same sum, as
`exactTerms`. -/
theorem exactTermsRect_triangle (b s : ℕ) (x y : List ℚ) :
    (exactTermsRect b s s s x y).sum = (exactTerms b s x y).sum := by
  unfold exactTermsRect exactTerms
  rw [sum_rectPairs s s s (fun t u => exactTerm (split b s x).1 (split b s y).1 (t, u)),
    sum_trianglePairs s (fun t u => exactTerm (split b s x).1 (split b s y).1 (t, u))]
  congr 1
  apply List.map_congr_left
  intro t ht
  rw [show min s (s - t) = s - t by omega]

/-! ## Jeannerod and Rump in any order -/

/-- A sum `Σ tᵢ` evaluated along a binary tree: leaves are terms, a node adds its subtrees. -/
inductive SumTree where
  | leaf (t : ℚ)
  | node (l r : SumTree)
  deriving Repr

namespace SumTree

/-- The terms at the leaves, left to right. -/
def leaves : SumTree → List ℚ
  | leaf t => [t]
  | node l r => l.leaves ++ r.leaves

/-- Evaluation with `leafVal` at the leaves and `rnd` after every addition. -/
def evalWith (leafVal : ℚ → Option ℚ) (rnd : ℚ → Option ℚ) : SumTree → Option ℚ
  | leaf t => leafVal t
  | node l r =>
    (l.evalWith leafVal rnd).bind fun a => (r.evalWith leafVal rnd).bind fun b => rnd (a + b)

theorem leaves_length_pos : ∀ T : SumTree, 0 < T.leaves.length
  | leaf _ => by simp [leaves]
  | node l r => by simp only [leaves, List.length_append]; have := leaves_length_pos l; omega

end SumTree

/-- Sums of rationals are invariant under permutation. -/
theorem sum_perm_q {l₁ l₂ : List ℚ} (h : l₁.Perm l₂) : l₁.sum = l₂.sum := by
  induction h with
  | nil => rfl
  | cons a _ ih => simp only [List.sum_cons, ih]
  | swap a b l => simp only [List.sum_cons]; grind
  | trans _ _ ih₁ ih₂ => rw [ih₁, ih₂]

section JRTree

variable {R : ℚ → Prop} {rnd : ℚ → Option ℚ} {u : ℚ}

/-- **Adding two computed sums** (the induction step of Jeannerod and Rump's Proposition 3.1 and
Theorem 4.2 for any order). If `a₁, a₂ ∈ R` with `|aᵢ| ≤ (1 + nᵢ u) Sᵢ`, `1 ≤ n₂ ≤ n₁`, the
rounding error of `a₁ + a₂` is at most `u (n₂ S₁ + n₁ S₂)`. Either `S₂ ≤ u n₂ S₁` and the error is
at most `|a₂|`, or the error is at most `u · ufp(a₁ + a₂)` and, with `±ufp` representable, at most
`|a₁ + a₂| − ufp(a₁ + a₂)`, which is small enough when `ufp` exceeds the target. -/
theorem jr_merge (hu : 0 ≤ u) (hJ : JRAdd R rnd u) {a₁ a₂ S₁ S₂ v : ℚ} {n₁ n₂ : ℕ}
    (hn₂ : 1 ≤ n₂) (h21 : n₂ ≤ n₁) (ha₁ : R a₁) (ha₂ : R a₂) (hS₁ : 0 ≤ S₁) (hS₂ : 0 ≤ S₂)
    (hb₁ : Rat.abs a₁ ≤ (1 + n₁ * u) * S₁) (hb₂ : Rat.abs a₂ ≤ (1 + n₂ * u) * S₂)
    (hv : rnd (a₁ + a₂) = some v) :
    Rat.abs (v - (a₁ + a₂)) ≤ u * (n₂ * S₁ + n₁ * S₂) := by
  have hc1 : (1 : ℚ) ≤ n₂ := by exact_mod_cast hn₂
  have hca : (n₂ : ℚ) ≤ n₁ := by exact_mod_cast h21
  generalize (n₁ : ℚ) = a at hb₁ hca ⊢
  generalize (n₂ : ℚ) = c at hb₂ hc1 hca ⊢
  have huS₂ : 0 ≤ u * S₂ := Rat.mul_nonneg hu hS₂
  have huS₁ : 0 ≤ u * S₁ := Rat.mul_nonneg hu hS₁
  have hT : 0 ≤ u * (c * S₁ + a * S₂) :=
    Rat.mul_nonneg hu (by
      have := Rat.mul_nonneg (show (0 : ℚ) ≤ c by grind) hS₁
      have := Rat.mul_nonneg (show (0 : ℚ) ≤ a by grind) hS₂
      grind)
  by_cases hsmall : S₂ ≤ u * c * S₁
  · -- the error is at most `|a₂|`
    have h1 := hJ.err_le_right ha₁ hv
    have h2 : c * u * S₂ ≤ a * u * S₂ := by
      have := Rat.mul_le_mul_of_nonneg_right hca huS₂
      grind
    have e1 : (1 + c * u) * S₂ = S₂ + c * u * S₂ := by grind
    have e2 : u * (c * S₁ + a * S₂) = u * c * S₁ + a * u * S₂ := by grind
    grind
  · have hlt : u * c * S₁ < S₂ := Rat.not_le.mp hsmall
    rcases hJ.2 a₁ a₂ v ha₁ ha₂ hv with rfl | ⟨h1, hR1, hR2⟩
    · rw [show a₁ + a₂ - (a₁ + a₂) = 0 by grind, abs_zero]; exact hT
    · by_cases hu2 : ufp (a₁ + a₂) ≤ c * S₁ + a * S₂
      · exact Rat.le_trans h1 (Rat.mul_le_mul_of_nonneg_left hu2 hu)
      · have hgt : c * S₁ + a * S₂ < ufp (a₁ + a₂) := Rat.not_le.mp hu2
        -- `±ufp(σ)` is in `R`, at distance `|σ| − ufp(σ)` from `σ = a₁ + a₂`
        have hcomp : Rat.abs (v - (a₁ + a₂)) ≤ Rat.abs (a₁ + a₂) - ufp (a₁ + a₂) := by
          have hu0 := ufp_le_abs (a₁ + a₂)
          by_cases hsg : 0 ≤ a₁ + a₂
          · have := (hJ.1 _ v hv).2 _ hR1
            rw [abs_of_nonneg hsg] at hu0
            rw [abs_sub_comm (a₁ + a₂) v,
              abs_of_nonneg (show 0 ≤ a₁ + a₂ - ufp (a₁ + a₂) by grind)] at this
            rw [abs_of_nonneg hsg]; exact this
          · have hneg : a₁ + a₂ < 0 := Rat.not_le.mp hsg
            have := (hJ.1 _ v hv).2 _ hR2
            rw [abs_of_neg hneg] at hu0
            have e : a₁ + a₂ - -ufp (a₁ + a₂) = -(-(a₁ + a₂) - ufp (a₁ + a₂)) := by grind
            rw [abs_sub_comm (a₁ + a₂) v, e, abs_neg,
              abs_of_nonneg (show 0 ≤ -(a₁ + a₂) - ufp (a₁ + a₂) by grind)] at this
            rw [abs_of_neg hneg]; grind
        have hσ : Rat.abs (a₁ + a₂) ≤ (1 + a * u) * S₁ + (1 + c * u) * S₂ :=
          Rat.le_trans (abs_add_le a₁ a₂) (by grind)
        -- `D = (1 + u) T − (1 + a u) S₁ − (1 + c u) S₂ ≥ 0`, with `X = u (a − c) S₁ ≤ (a − 1) S₂`
        have hX : u * (a - c) * S₁ ≤ (a - 1) * S₂ := by
          have hac : 0 ≤ a - c := by grind
          have h1' : (a - c) * (u * c * S₁) ≤ (a - c) * S₂ :=
            Rat.mul_le_mul_of_nonneg_left (Rat.le_of_lt hlt) hac
          have h2' : (a - c) * S₂ ≤ c * ((a - 1) * S₂) := by
            have : 0 ≤ a * (c - 1) * S₂ :=
              Rat.mul_nonneg (Rat.mul_nonneg (by grind) (by grind)) hS₂
            grind
          have h3' : c * (u * (a - c) * S₁) ≤ c * ((a - 1) * S₂) := by
            have e : c * (u * (a - c) * S₁) = (a - c) * (u * c * S₁) := by grind
            rw [e]; exact Rat.le_trans h1' h2'
          exact Rat.le_of_mul_le_mul_left h3' (by grind)
        have hY : 0 ≤ u * (a - c) * S₂ :=
          Rat.mul_nonneg (Rat.mul_nonneg hu (by grind)) hS₂
        have hc1S : 0 ≤ (c - 1) * S₁ := Rat.mul_nonneg (by grind) hS₁
        have eD : (1 + u) * (c * S₁ + a * S₂) - (1 + a * u) * S₁ - (1 + c * u) * S₂ =
            (c - 1) * S₁ + (a - 1) * S₂ + u * (a - c) * S₂ - u * (a - c) * S₁ := by grind
        have eT : u * (c * S₁ + a * S₂) = (1 + u) * (c * S₁ + a * S₂) - (c * S₁ + a * S₂) := by
          grind
        grind

/-- `jr_merge` in either order of the subtree sizes. -/
theorem jr_merge' (hu : 0 ≤ u) (hJ : JRAdd R rnd u) {a₁ a₂ S₁ S₂ v : ℚ} {n₁ n₂ : ℕ}
    (hn₁ : 1 ≤ n₁) (hn₂ : 1 ≤ n₂) (ha₁ : R a₁) (ha₂ : R a₂) (hS₁ : 0 ≤ S₁) (hS₂ : 0 ≤ S₂)
    (hb₁ : Rat.abs a₁ ≤ (1 + n₁ * u) * S₁) (hb₂ : Rat.abs a₂ ≤ (1 + n₂ * u) * S₂)
    (hv : rnd (a₁ + a₂) = some v) :
    Rat.abs (v - (a₁ + a₂)) ≤ u * (n₂ * S₁ + n₁ * S₂) := by
  by_cases h : n₂ ≤ n₁
  · exact jr_merge hu hJ hn₂ h ha₁ ha₂ hS₁ hS₂ hb₁ hb₂ hv
  · rw [Rat.add_comm a₁ a₂] at hv ⊢
    have := jr_merge hu hJ hn₁ (by omega) ha₂ ha₁ hS₂ hS₁ hb₂ hb₁ hv
    grind

/-- **Summing floating-point numbers along any tree** (Jeannerod and Rump, Proposition 3.1):
`|fl(Σ tᵢ) − Σ tᵢ| ≤ (n − 1) u Σ|tᵢ|` for `n` values of `R` added in any order, with no condition
on `n u`. -/
theorem sumTree_jr (hu : 0 ≤ u) (hJ : JRAdd R rnd u) :
    ∀ (T : SumTree) (v : ℚ), (∀ t ∈ T.leaves, R t) → T.evalWith some rnd = some v →
      R v ∧ Rat.abs (v - T.leaves.sum) ≤
        ((T.leaves.length : ℚ) - 1) * u * (T.leaves.map Rat.abs).sum
  | .leaf t, v, hR, hv => by
    simp only [SumTree.evalWith, Option.some.injEq] at hv
    subst hv
    refine ⟨hR _ (by simp [SumTree.leaves]), ?_⟩
    simp only [SumTree.leaves, List.sum_cons, List.sum_nil, List.length_cons, List.length_nil,
      List.map_cons, List.map_nil]
    rw [show t - (t + 0) = 0 by grind, abs_zero, show ((0 + 1 : ℕ) : ℚ) = 1 from rfl]
    grind
  | .node l r, v, hR, hv => by
    simp only [SumTree.evalWith] at hv
    cases hl : l.evalWith some rnd with
    | none => simp [hl] at hv
    | some a₁ =>
      cases hr : r.evalWith some rnd with
      | none => simp [hl, hr] at hv
      | some a₂ =>
        simp only [hl, hr, Option.bind_some] at hv
        have hRl : ∀ t ∈ l.leaves, R t := fun t ht => hR t (by simp [SumTree.leaves, ht])
        have hRr : ∀ t ∈ r.leaves, R t := fun t ht => hR t (by simp [SumTree.leaves, ht])
        obtain ⟨ha₁, he₁⟩ := sumTree_jr hu hJ l a₁ hRl hl
        obtain ⟨ha₂, he₂⟩ := sumTree_jr hu hJ r a₂ hRr hr
        refine ⟨(hJ.1 _ v hv).1, ?_⟩
        have hn₁ := SumTree.leaves_length_pos l
        have hn₂ := SumTree.leaves_length_pos r
        generalize hS₁ : (l.leaves.map Rat.abs).sum = S₁ at he₁
        generalize hS₂ : (r.leaves.map Rat.abs).sum = S₂ at he₂
        have hS₁0 : 0 ≤ S₁ := by rw [← hS₁]; exact sum_nonneg fun t _ => abs_nonneg t
        have hS₂0 : 0 ≤ S₂ := by rw [← hS₂]; exact sum_nonneg fun t _ => abs_nonneg t
        have hs₁ : Rat.abs l.leaves.sum ≤ S₁ := by
          rw [← hS₁]; have := abs_sum_le l.leaves id; simpa only [List.map_id, id] using this
        have hs₂ : Rat.abs r.leaves.sum ≤ S₂ := by
          rw [← hS₂]; have := abs_sum_le r.leaves id; simpa only [List.map_id, id] using this
        have hn₁' : (1 : ℚ) ≤ l.leaves.length := by exact_mod_cast hn₁
        have hn₂' : (1 : ℚ) ≤ r.leaves.length := by exact_mod_cast hn₂
        have hb (a s S n : ℚ) (hs : Rat.abs s ≤ S) (he : Rat.abs (a - s) ≤ (n - 1) * u * S)
            (hS : 0 ≤ S) : Rat.abs a ≤ (1 + n * u) * S := by
          have := abs_add_le (a - s) s
          rw [show a - s + s = a by grind] at this
          have : 0 ≤ u * S := Rat.mul_nonneg hu hS
          have e : (1 + n * u) * S = S + (n - 1) * u * S + u * S := by grind
          grind
        have hb₁ := hb a₁ l.leaves.sum S₁ l.leaves.length hs₁ he₁ hS₁0
        have hb₂ := hb a₂ r.leaves.sum S₂ r.leaves.length hs₂ he₂ hS₂0
        have hm := jr_merge' hu hJ hn₁ hn₂ ha₁ ha₂ hS₁0 hS₂0 hb₁ hb₂ hv
        simp only [SumTree.leaves, List.length_append, List.map_append]
        rw [sum_append_q, sum_append_q, hS₁, hS₂, Rat.natCast_add]
        have t1 := abs_add_le (v - (a₁ + a₂)) (a₁ - l.leaves.sum)
        have t2 := abs_add_le (v - (a₁ + a₂) + (a₁ - l.leaves.sum)) (a₂ - r.leaves.sum)
        rw [show v - (a₁ + a₂) + (a₁ - l.leaves.sum) + (a₂ - r.leaves.sum) =
          v - (l.leaves.sum + r.leaves.sum) by grind] at t2
        have e : ((l.leaves.length : ℚ) + r.leaves.length - 1) * u * (S₁ + S₂) =
            u * (r.leaves.length * S₁ + l.leaves.length * S₂) +
              ((l.leaves.length : ℚ) - 1) * u * S₁ + ((r.leaves.length : ℚ) - 1) * u * S₂ := by
          grind
        grind


/-- **A dot product along any tree** (Jeannerod and Rump, Theorem 4.2): the leaves are the exact
products `zᵢ`, each rounded within `u |zᵢ|` (no underflow), and the rounded products are added
in any order; the result is within `k u Σ|zᵢ|` of `Σ zᵢ`, for every `k`. -/
theorem dotTree_jr (hu : 0 ≤ u) (hJ : JRAdd R rnd u) :
    ∀ (T : SumTree) (v : ℚ),
      (∀ z ∈ T.leaves, ∀ p, rnd z = some p → Rat.abs (p - z) ≤ u * Rat.abs z) →
      T.evalWith rnd rnd = some v →
      R v ∧ Rat.abs (v - T.leaves.sum) ≤ (T.leaves.length : ℚ) * u * (T.leaves.map Rat.abs).sum
  | .leaf z, v, hz, hv => by
    simp only [SumTree.evalWith] at hv
    refine ⟨(hJ.1 z v hv).1, ?_⟩
    have := hz z (by simp [SumTree.leaves]) v hv
    simp only [SumTree.leaves, List.sum_cons, List.sum_nil, List.length_cons, List.length_nil,
      List.map_cons, List.map_nil]
    rw [show z + 0 = z by grind, show ((0 + 1 : ℕ) : ℚ) = 1 from rfl]
    grind
  | .node l r, v, hz, hv => by
    simp only [SumTree.evalWith] at hv
    cases hl : l.evalWith rnd rnd with
    | none => simp [hl] at hv
    | some a₁ =>
      cases hr : r.evalWith rnd rnd with
      | none => simp [hl, hr] at hv
      | some a₂ =>
        simp only [hl, hr, Option.bind_some] at hv
        have hzl : ∀ z ∈ l.leaves, ∀ p, rnd z = some p → Rat.abs (p - z) ≤ u * Rat.abs z :=
          fun z h => hz z (by simp [SumTree.leaves, h])
        have hzr : ∀ z ∈ r.leaves, ∀ p, rnd z = some p → Rat.abs (p - z) ≤ u * Rat.abs z :=
          fun z h => hz z (by simp [SumTree.leaves, h])
        obtain ⟨ha₁, he₁⟩ := dotTree_jr hu hJ l a₁ hzl hl
        obtain ⟨ha₂, he₂⟩ := dotTree_jr hu hJ r a₂ hzr hr
        refine ⟨(hJ.1 _ v hv).1, ?_⟩
        have hn₁ := SumTree.leaves_length_pos l
        have hn₂ := SumTree.leaves_length_pos r
        generalize hS₁ : (l.leaves.map Rat.abs).sum = S₁ at he₁
        generalize hS₂ : (r.leaves.map Rat.abs).sum = S₂ at he₂
        have hS₁0 : 0 ≤ S₁ := by rw [← hS₁]; exact sum_nonneg fun t _ => abs_nonneg t
        have hS₂0 : 0 ≤ S₂ := by rw [← hS₂]; exact sum_nonneg fun t _ => abs_nonneg t
        have hs₁ : Rat.abs l.leaves.sum ≤ S₁ := by
          rw [← hS₁]; have := abs_sum_le l.leaves id; simpa only [List.map_id, id] using this
        have hs₂ : Rat.abs r.leaves.sum ≤ S₂ := by
          rw [← hS₂]; have := abs_sum_le r.leaves id; simpa only [List.map_id, id] using this
        have hb (a s S n : ℚ) (hs : Rat.abs s ≤ S) (he : Rat.abs (a - s) ≤ n * u * S) :
            Rat.abs a ≤ (1 + n * u) * S := by
          have := abs_add_le (a - s) s
          rw [show a - s + s = a by grind] at this
          have e : (1 + n * u) * S = S + n * u * S := by grind
          grind
        have hb₁ := hb a₁ l.leaves.sum S₁ l.leaves.length hs₁ he₁
        have hb₂ := hb a₂ r.leaves.sum S₂ r.leaves.length hs₂ he₂
        have hm := jr_merge' hu hJ hn₁ hn₂ ha₁ ha₂ hS₁0 hS₂0 hb₁ hb₂ hv
        simp only [SumTree.leaves, List.length_append, List.map_append]
        rw [sum_append_q, sum_append_q, hS₁, hS₂, Rat.natCast_add]
        have t1 := abs_add_le (v - (a₁ + a₂)) (a₁ - l.leaves.sum)
        have t2 := abs_add_le (v - (a₁ + a₂) + (a₁ - l.leaves.sum)) (a₂ - r.leaves.sum)
        rw [show v - (a₁ + a₂) + (a₁ - l.leaves.sum) + (a₂ - r.leaves.sum) =
          v - (l.leaves.sum + r.leaves.sum) by grind] at t2
        have e : ((l.leaves.length : ℚ) + r.leaves.length) * u * (S₁ + S₂) =
            u * (r.leaves.length * S₁ + l.leaves.length * S₂) +
              (l.leaves.length : ℚ) * u * S₁ + (r.leaves.length : ℚ) * u * S₂ := by
          grind
        grind

/-- **Summation in any order**: for any tree whose leaves are a permutation of `ts ⊆ R`,
`|fl(Σ tᵢ) − Σ tᵢ| ≤ (n − 1) u Σ|tᵢ|`. -/
theorem sumTree_error_jr (hu : 0 ≤ u) (hJ : JRAdd R rnd u) {T : SumTree} {ts : List ℚ}
    (hp : T.leaves.Perm ts) (hts : ∀ t ∈ ts, R t) {v : ℚ} (hv : T.evalWith some rnd = some v) :
    Rat.abs (v - ts.sum) ≤ ((ts.length : ℚ) - 1) * u * (ts.map Rat.abs).sum := by
  have := (sumTree_jr hu hJ T v (fun t ht => hts t (hp.mem_iff.mp ht)) hv).2
  rwa [sum_perm_q hp, sum_perm_q (hp.map Rat.abs), hp.length_eq] at this

/-- **The dot product in any order**: for any tree whose leaves are a permutation of the
products `xᵢyᵢ`, each rounded within `u |xᵢyᵢ|`, `|fl(x · y) − x · y| ≤ k u Σ|xᵢyᵢ|`. -/
theorem dotTree_error_jr (hu : 0 ≤ u) (hJ : JRAdd R rnd u) {T : SumTree} {x y : List ℚ}
    (hp : T.leaves.Perm (List.zipWith (· * ·) x y))
    (hz : ∀ z ∈ List.zipWith (· * ·) x y, ∀ p, rnd z = some p → Rat.abs (p - z) ≤ u * Rat.abs z)
    {v : ℚ} (hv : T.evalWith rnd rnd = some v) :
    Rat.abs (v - dot x y) ≤
      (List.zipWith (· * ·) x y).length * u * ((List.zipWith (· * ·) x y).map Rat.abs).sum := by
  have := (dotTree_jr hu hJ T v (fun z hz' => hz z (hp.mem_iff.mp hz')) hv).2
  rwa [sum_perm_q hp, sum_perm_q (hp.map Rat.abs), hp.length_eq] at this

end JRTree

section IEEETree

variable {p : ℕ} {emin emax : ℤ}

/-- **IEEE summation in any order** (Jeannerod and Rump, Proposition 3.1): `(n − 1) 2^(−p) Σ|tᵢ|`
for floating-point numbers added along any tree, underflow allowed. -/
theorem sumTree_error_jr_rne (hp : 0 < p) (hle : emin ≤ emax) {T : SumTree} {ts : List ℚ}
    (hperm : T.leaves.Perm ts) (hts : ∀ t ∈ ts, FormatValue p emin emax t) {v : ℚ}
    (hv : T.evalWith some (roundRNE p emin emax) = some v) :
    Rat.abs (v - ts.sum) ≤ ((ts.length : ℚ) - 1) * 2 ^ (-(p : ℤ)) * (ts.map Rat.abs).sum :=
  sumTree_error_jr (Rat.le_of_lt (two_pow_pos _)) (roundRNE_jrAdd hp hle) hperm hts hv

/-- **IEEE dot products in any order** (Jeannerod and Rump, Theorem 4.2): when no product
underflows, `k 2^(−p) Σ|xᵢyᵢ|` for the rounded products added along any tree. -/
theorem dotTree_error_jr_rne (hp : 0 < p) (hle : emin ≤ emax) {T : SumTree} {x y : List ℚ}
    (hperm : T.leaves.Perm (List.zipWith (· * ·) x y))
    (hz : ∀ z ∈ List.zipWith (· * ·) x y, (2 : ℚ) ^ emin ≤ Rat.abs z ∨ FormatValue p emin emax z)
    {v : ℚ} (hv : T.evalWith (roundRNE p emin emax) (roundRNE p emin emax) = some v) :
    Rat.abs (v - dot x y) ≤
      (List.zipWith (· * ·) x y).length * 2 ^ (-(p : ℤ)) *
        ((List.zipWith (· * ·) x y).map Rat.abs).sum :=
  dotTree_error_jr (Rat.le_of_lt (two_pow_pos _)) (roundRNE_jrAdd hp hle) hperm
    (fun z hz' _ hr => roundRNE_error_normal hp (hz z hz') hr) hv

end IEEETree

/-! ## Ozaki-II with an inexact CRT accumulation -/

/-- The reduction of an approximate CRT sum `Ŝ ≈ Σ wⱼ rⱼ` modulo `M`: `Ŝ − M · rne(Ŝ / M)`. -/
def reduceApprox (M : ℕ) (S : ℚ) : ℚ := S - M * roundNearestEven (S / M)

/-- **The reduction is robust to an inexact sum.** If `Ŝ` is within `ε` of `q M + c` and
`2|c| + 2ε < M`, the reduction finds the multiple `q` and returns `c` within `ε`. -/
theorem reduceApprox_eq {M : ℕ} (hM : 0 < M) {q c : ℤ} {S ε : ℚ}
    (hS : Rat.abs (S - ((q : ℚ) * M + c)) ≤ ε) (hmargin : 2 * Rat.abs (c : ℚ) + 2 * ε < M) :
    roundNearestEven (S / M) = q ∧ Rat.abs (reduceApprox M S - c) ≤ ε := by
  have hMq : (0 : ℚ) < M := by exact_mod_cast hM
  have hMne : (M : ℚ) ≠ 0 := Rat.ne_of_gt hMq
  -- `|S − q M| ≤ |c| + ε < M / 2`
  have h1 : Rat.abs (S - q * M) ≤ Rat.abs (c : ℚ) + ε := by
    have := abs_add_le (S - ((q : ℚ) * M + c)) (c : ℚ)
    rw [show S - ((q : ℚ) * M + c) + c = S - q * M by grind] at this
    grind
  have h2 : 2 * Rat.abs (S - q * M) < M := by grind
  -- `|S / M − q| < 1 / 2`
  have ht : (S / M - q) * M = S - q * M := by
    have hdm : S / M * M = S := Rat.div_mul_cancel hMne
    grind
  have h3 : 2 * Rat.abs (S / M - q) < 1 := by
    have e : Rat.abs (S / M - q) * M = Rat.abs (S - q * M) := by
      rw [← ht, abs_mul, abs_of_nonneg (Rat.le_of_lt hMq)]
    have h4 : 2 * Rat.abs (S / M - q) * M < 1 * M := by
      rw [Rat.one_mul, Rat.mul_assoc, e]; exact h2
    exact Rat.lt_of_mul_lt_mul_right h4 (Rat.le_of_lt hMq)
  have hn := roundNearestEven_nearest (S / M) q
  have h5 : Rat.abs ((roundNearestEven (S / M) : ℚ) - q) < 1 := by
    have := abs_add_le ((roundNearestEven (S / M) : ℚ) - S / M) (S / M - q)
    rw [show (roundNearestEven (S / M) : ℚ) - S / M + (S / M - q) =
      (roundNearestEven (S / M) : ℚ) - q by grind, abs_sub_comm _ (S / M)] at this
    grind
  have hq : roundNearestEven (S / M) = q := by
    rw [← Rat.intCast_sub, abs_intCast] at h5
    have : (roundNearestEven (S / M) - q).natAbs < 1 := by exact_mod_cast h5
    omega
  refine ⟨hq, ?_⟩
  unfold reduceApprox
  rw [hq, show S - (M : ℚ) * q - c = S - ((q : ℚ) * M + c) by grind]
  exact hS

/-- **Ozaki-II with an approximate CRT accumulation**: the residue products are exact on the
engine, `Σ wⱼ rⱼ` is computed by `acc` (for instance in floating point, `none` on overflow), and
the reduction is `reduceApprox`. -/
def ozaki2Approx (eng : Engine) (round : ℚ → Option ℚ) (acc : List ℤ → List ℤ → Option ℚ)
    (B : CRTBasis) (P : ℕ) (x y : List ℚ) : Option ℚ := do
  let a := scaleTrunc (scaleShift P x) x
  let c := scaleTrunc (scaleShift P y) y
  let rs ← B.moduli.mapM fun m => residueProduct eng m a c
  let S ← acc B.weights rs
  round (reduceApprox B.modulus S * 2 ^ (-(scaleShift P x + scaleShift P y)))

/-- The values `mapM` returns come from the list. -/
theorem mem_of_mapM {α β : Type} {f : α → Option β} :
    ∀ {l : List α} {r : List β}, l.mapM f = some r → ∀ y ∈ r, ∃ x ∈ l, f x = some y
  | [], r, h => by
    simp only [List.mapM_nil, pure, Option.some.injEq] at h; subst h; simp
  | x :: l, r, h => by
    rw [List.mapM_cons] at h
    cases hx : f x with
    | none => simp [hx] at h
    | some b =>
      cases hl : l.mapM f with
      | none => simp [hx, hl] at h
      | some bs =>
        simp only [hx, hl, Option.bind_eq_bind, Option.bind_some, pure, Option.some.injEq] at h
        subst h
        intro y hy
        rcases List.mem_cons.mp hy with rfl | hy
        · exact ⟨x, List.mem_cons_self, hx⟩
        · obtain ⟨x', hx', hf⟩ := mem_of_mapM hl y hy
          exact ⟨x', List.mem_cons_of_mem _ hx', hf⟩

theorem mapM_length {α β : Type} {f : α → Option β} :
    ∀ {l : List α} {r : List β}, l.mapM f = some r → r.length = l.length
  | [], r, h => by simp only [List.mapM_nil, pure, Option.some.injEq] at h; subst h; rfl
  | x :: l, r, h => by
    rw [List.mapM_cons] at h
    cases hx : f x with
    | none => simp [hx] at h
    | some b =>
      cases hl : l.mapM f with
      | none => simp [hx, hl] at h
      | some bs =>
        simp only [hx, hl, Option.bind_eq_bind, Option.bind_some, pure, Option.some.injEq] at h
        subst h
        simp [mapM_length hl]

/-- A residue product is in `[0, m)`. -/
theorem residueProduct_range {eng : Engine} {m : ℕ} (hm : 0 < m) {a c : List ℤ} {r : ℤ}
    (h : residueProduct eng m a c = some r) : 0 ≤ r ∧ r < m := by
  unfold residueProduct at h
  cases hv : eng (a.map fun z => symMod z m) (c.map fun z => symMod z m) with
  | none => simp [hv] at h
  | some v =>
    cases hz : toInt? v with
    | none => simp [hv, hz] at h
    | some z =>
      simp only [hv, hz, Option.bind_eq_bind, Option.bind_some, pure, Option.some.injEq] at h
      subst h
      exact ⟨Int.emod_nonneg z (by omega), Int.emod_lt_of_pos z (by omega)⟩

/-- **The error of Ozaki-II with an inexact CRT accumulation.** If the accumulator is within `ε`
of `Σ wⱼ rⱼ` and `2 k 2^(2P) + 2ε < M`, the reduction recovers the product of the truncated inputs
within `ε`, and the result is within `u (|C| + ε 2^(−s)) + η + ε 2^(−s)` plus the truncation bound
of `x · y`, where `C = 2^(−s) (a · c)` and `s = sₓ + s_y`. The exact case is `ε = 0`. -/
theorem ozaki2Approx_error {eng : Engine} {b budget : ℕ} (heng : eng.ExactOn b budget)
    {round : ℚ → Option ℚ} {u η : ℚ} (hu : 0 ≤ u) (hround : RoundWithin round u η)
    {B : CRTBasis} (hB : B.Valid) (hmb : ∀ m ∈ B.moduli, m ≤ 2 ^ (b + 1))
    {acc : List ℤ → List ℤ → Option ℚ} {ε : ℚ}
    (hacc : ∀ rs : List ℤ, rs.length = B.weights.length → (∀ r ∈ rs, 0 ≤ r ∧ r < 2 ^ (b + 1)) →
      ∀ S, acc B.weights rs = some S → Rat.abs (S - (dotZ B.weights rs : ℚ)) ≤ ε)
    (P : ℕ) {x y : List ℚ} (hlen : x.length = y.length)
    (hbudget : x.length * (2 ^ b * 2 ^ b) ≤ budget)
    (hrange : 2 * x.length * (2 ^ P * 2 ^ P) < B.modulus)
    (hmargin : 2 * ((x.length * (2 ^ P * 2 ^ P) : ℕ) : ℚ) + 2 * ε < B.modulus) {v : ℚ}
    (hv : ozaki2Approx eng round acc B P x y = some v) :
    Rat.abs (v - dot x y) ≤
      u * (Rat.abs ((dotZ (scaleTrunc (scaleShift P x) x) (scaleTrunc (scaleShift P y) y) : ℚ) *
          2 ^ (-(scaleShift P x + scaleShift P y))) + ε * 2 ^ (-(scaleShift P x + scaleShift P y))) +
        η + ε * 2 ^ (-(scaleShift P x + scaleShift P y)) +
      (List.zipWith (fun a b => 2 ^ (-scaleShift P x) * Rat.abs b +
          2 ^ (-(scaleShift P x + scaleShift P y)) *
            Rat.abs (truncInt (a * 2 ^ scaleShift P x) : ℚ)) x y).sum := by
  have hM : 0 < B.modulus := by omega
  -- the exact reconstruction, from `ozaki2_eq` with the identity rounding
  have hexact := ozaki2_eq heng some hB hmb P hlen hbudget hrange
  unfold ozaki2 at hexact
  unfold ozaki2Approx at hv
  dsimp only at hexact hv
  generalize ha : scaleTrunc (scaleShift P x) x = a at hexact hv ⊢
  generalize hc : scaleTrunc (scaleShift P y) y = c at hexact hv ⊢
  generalize hs : scaleShift P x + scaleShift P y = sh at hexact hv ⊢
  cases hrs : B.moduli.mapM (fun m => residueProduct eng m a c) with
  | none => rw [hrs] at hv; simp at hv
  | some rs =>
    rw [hrs] at hv hexact
    simp only [Option.bind_eq_bind, Option.bind_some, Option.some.injEq] at hv hexact
    cases hS' : acc B.weights rs with
    | none => rw [hS'] at hv; simp at hv
    | some Sacc =>
    rw [hS', Option.bind_some] at hv
    have hrsR : ∀ r ∈ rs, 0 ≤ r ∧ r < 2 ^ (b + 1) := by
      intro r hr
      obtain ⟨m, hm, hmr⟩ := mem_of_mapM hrs r hr
      have := residueProduct_range (hB.2.1 m hm) hmr
      have hmb' : (m : ℤ) ≤ 2 ^ (b + 1) := by exact_mod_cast hmb m hm
      omega
    have hrsl : rs.length = B.weights.length := by rw [mapM_length hrs, hB.1]
    have hcrt : crt B rs = dotZ a c := by
      have h2 := two_pow_ne_zero (-sh)
      have : (crt B rs : ℚ) = dotZ a c := by
        have := congrArg (· * (2 : ℚ) ^ sh) hexact
        rw [Rat.mul_assoc, Rat.mul_assoc, two_pow_neg_mul, Rat.mul_one, Rat.mul_one] at this
        exact this
      exact_mod_cast this
    -- `Σ wⱼ rⱼ = q M + a · c`
    obtain ⟨q, hq⟩ := symMod_dvd (dotZ B.weights rs) B.modulus
    have hS : (dotZ B.weights rs : ℚ) = (q : ℚ) * B.modulus + (dotZ a c : ℤ) := by
      have : dotZ B.weights rs = q * B.modulus + dotZ a c := by
        unfold crt at hcrt; rw [← hcrt]; rw [Int.mul_comm]; omega
      rw [this]; push_cast; rfl
    have hab : ((dotZ a c).natAbs : ℚ) ≤ ((x.length * (2 ^ P * 2 ^ P) : ℕ) : ℚ) := by
      have : (dotZ a c).natAbs ≤ x.length * (2 ^ P * 2 ^ P) := by
        refine Nat.le_trans (natAbs_dotZ_le a c) ?_
        have hla : a.length = x.length := by rw [← ha, scaleTrunc_length]
        rw [← hla]
        exact dotAbs_le a c _ _ (by rw [← ha]; exact scaleTrunc_bound P x)
          (by rw [← hc]; exact scaleTrunc_bound P y)
      exact_mod_cast this
    have hred := reduceApprox_eq hM (q := q) (c := dotZ a c) (S := Sacc) (ε := ε)
      (by rw [← hS]; exact hacc rs hrsl hrsR Sacc hS')
      (by rw [abs_intCast]; grind)
    obtain ⟨_, hĉ⟩ := hred
    generalize hC' : reduceApprox B.modulus Sacc = ĉ at hv hĉ
    -- the three errors: rounding, reduction, truncation
    have hp := two_pow_pos (-sh)
    have hd : Rat.abs (ĉ * 2 ^ (-sh) - (dotZ a c : ℚ) * 2 ^ (-sh)) ≤ ε * 2 ^ (-sh) := by
      rw [show ĉ * 2 ^ (-sh) - (dotZ a c : ℚ) * 2 ^ (-sh) = (ĉ - dotZ a c) * 2 ^ (-sh) by grind,
        abs_mul, abs_two_pow]
      exact Rat.mul_le_mul_of_nonneg_right hĉ (Rat.le_of_lt hp)
    have hr := hround _ v hv
    have ht := truncProduct_error (scaleShift P x) (scaleShift P y) x y hlen
    rw [ha, hc, hs] at ht
    have hC'abs : Rat.abs (ĉ * 2 ^ (-sh)) ≤
        Rat.abs ((dotZ a c : ℚ) * 2 ^ (-sh)) + ε * 2 ^ (-sh) := by
      have := abs_add_le (ĉ * 2 ^ (-sh) - (dotZ a c : ℚ) * 2 ^ (-sh)) ((dotZ a c : ℚ) * 2 ^ (-sh))
      rw [show ĉ * 2 ^ (-sh) - (dotZ a c : ℚ) * 2 ^ (-sh) + (dotZ a c : ℚ) * 2 ^ (-sh) =
        ĉ * 2 ^ (-sh) by grind] at this
      grind
    have hu' := Rat.mul_le_mul_of_nonneg_left hC'abs hu
    have e1 := abs_add_le (v - ĉ * 2 ^ (-sh)) (ĉ * 2 ^ (-sh) - (dotZ a c : ℚ) * 2 ^ (-sh))
    have e2 := abs_add_le (v - ĉ * 2 ^ (-sh) + (ĉ * 2 ^ (-sh) - (dotZ a c : ℚ) * 2 ^ (-sh)))
      ((dotZ a c : ℚ) * 2 ^ (-sh) - dot x y)
    rw [show v - ĉ * 2 ^ (-sh) + (ĉ * 2 ^ (-sh) - (dotZ a c : ℚ) * 2 ^ (-sh)) +
      ((dotZ a c : ℚ) * 2 ^ (-sh) - dot x y) = v - dot x y by grind] at e2
    rw [abs_sub_comm ((dotZ a c : ℚ) * 2 ^ (-sh)) (dot x y),
      show (dotZ a c : ℚ) * 2 ^ (-sh) = 2 ^ (-sh) * (dotZ a c : ℚ) by grind] at e2
    grind

/-- The CRT sum `Σ wⱼ rⱼ` accumulated in binary64, left to right, each product rounded. -/
def crtAccFP64 (ws rs : List ℤ) : Option ℚ := nativeDot rne64 (ofInts ws) (ofInts rs)

theorem mem_zipWith_ofInts : ∀ (ws rs : List ℤ),
    ∀ z : ℚ, z ∈ List.zipWith (· * ·) (ofInts ws) (ofInts rs) → ∃ n : ℤ, z = (n : ℚ)
  | [], _, z, hz => by simp [ofInts] at hz
  | _ :: _, [], z, hz => by simp [ofInts] at hz
  | w :: ws, r :: rs, z, hz => by
    simp only [ofInts, List.map_cons, List.zipWith_cons_cons, List.mem_cons] at hz
    rcases hz with rfl | hz
    · exact ⟨w * r, (Rat.intCast_mul w r).symm⟩
    · exact mem_zipWith_ofInts ws rs z hz

theorem sum_abs_zipWith_ofInts_le {M : ℚ} (hM : 0 ≤ M) : ∀ (ws rs : List ℤ),
    (∀ r ∈ rs, Rat.abs (r : ℚ) ≤ M) →
    ((List.zipWith (· * ·) (ofInts ws) (ofInts rs)).map Rat.abs).sum ≤
      M * (ws.map fun w : ℤ => Rat.abs (w : ℚ)).sum
  | [], _, _ => by simp [ofInts]
  | w :: ws, [], _ => by
    simp only [ofInts, List.map_cons, List.map_nil, List.zipWith_nil_right, List.sum_nil]
    have := sum_nonneg (l := ws) (f := fun w : ℤ => Rat.abs (w : ℚ)) fun _ _ => abs_nonneg _
    have := abs_nonneg (w : ℚ)
    exact Rat.mul_nonneg hM (by grind)
  | w :: ws, r :: rs, h => by
    simp only [ofInts, List.map_cons, List.zipWith_cons_cons, List.sum_cons]
    have ih := sum_abs_zipWith_ofInts_le hM ws rs (fun r' hr' => h r' (List.mem_cons_of_mem _ hr'))
    simp only [ofInts] at ih
    have hr := h r List.mem_cons_self
    have h1 : Rat.abs ((w : ℚ) * r) ≤ M * Rat.abs (w : ℚ) := by
      rw [abs_mul]
      have := Rat.mul_le_mul_of_nonneg_left hr (abs_nonneg (w : ℚ))
      grind
    grind

/-- **The binary64 CRT accumulation's error** (Jeannerod and Rump): for residues in
`[0, 2^(b+1))`, the left-to-right binary64 sum of the products `wⱼ rⱼ` is within
`n 2^-53 2^(b+1) Σ|wⱼ|`, `n` the number of weights. Products of integers never underflow: a nonzero
one is at least `1`. -/
theorem crtAccFP64_error {b : ℕ} {ws rs : List ℤ} (hr : ∀ r ∈ rs, 0 ≤ r ∧ r < 2 ^ (b + 1))
    {S : ℚ} (h : crtAccFP64 ws rs = some S) :
    Rat.abs (S - (dotZ ws rs : ℚ)) ≤
      ws.length * 2 ^ (-53 : ℤ) * (2 ^ (b + 1 : ℤ) * (ws.map fun w : ℤ => Rat.abs (w : ℚ)).sum) := by
  have hz : ∀ z ∈ List.zipWith (· * ·) (ofInts ws) (ofInts rs),
      (2 : ℚ) ^ (-1022 : ℤ) ≤ Rat.abs z ∨ Binary64Value z := by
    intro z hz
    obtain ⟨n, rfl⟩ := mem_zipWith_ofInts ws rs z hz
    by_cases hn : n = 0
    · subst hn
      exact Or.inr ⟨0, 0, by decide, by decide, by decide, by simp⟩
    · left
      rw [abs_intCast]
      have h1 : (1 : ℚ) ≤ ((n.natAbs : ℕ) : ℚ) := by
        have : 1 ≤ n.natAbs := by omega
        exact_mod_cast this
      exact Rat.le_trans (by decide +kernel) h1
  have hjr := nativeDot_error_jr_rne64 hz h
  rw [dot_ofInts] at hjr
  refine Rat.le_trans hjr ?_
  have hl : ((List.zipWith (· * ·) (ofInts ws) (ofInts rs)).length : ℚ) ≤ ws.length := by
    have : (List.zipWith (· * ·) (ofInts ws) (ofInts rs)).length ≤ ws.length := by
      simp only [List.length_zipWith, ofInts_length]; exact Nat.min_le_left _ _
    exact_mod_cast this
  have hM : ∀ r ∈ rs, Rat.abs (r : ℚ) ≤ 2 ^ (b + 1 : ℤ) := by
    intro r hmem
    obtain ⟨h0, h1⟩ := hr r hmem
    have h2 : ((r.natAbs : ℕ) : ℤ) < ((2 ^ (b + 1) : ℕ) : ℤ) := by
      rw [Int.natAbs_of_nonneg h0]; push_cast; exact h1
    have h3 : r.natAbs < 2 ^ (b + 1) := by exact_mod_cast h2
    rw [abs_intCast, show ((b : ℤ) + 1) = ((b + 1 : ℕ) : ℤ) by omega, two_pow_natCast]
    exact_mod_cast Nat.le_of_lt h3
  have hs := sum_abs_zipWith_ofInts_le (Rat.le_of_lt (two_pow_pos _)) ws rs hM
  have hsn : 0 ≤ ((List.zipWith (· * ·) (ofInts ws) (ofInts rs)).map Rat.abs).sum :=
    sum_nonneg fun _ _ => abs_nonneg _
  have hu := two_pow_pos (-53 : ℤ)
  have h1 := Rat.mul_le_mul_of_nonneg_right hl (Rat.le_of_lt hu)
  have h2 := Rat.mul_le_mul_of_nonneg_right h1 hsn
  have h3 := Rat.mul_le_mul_of_nonneg_left hs
    (Rat.mul_nonneg (Rat.natCast_nonneg) (Rat.le_of_lt hu) : (0 : ℚ) ≤ ws.length * 2 ^ (-53 : ℤ))
  grind

/-- **Ozaki-II with the CRT sum accumulated in binary64**: with `ε = n 2^-53 2^(b+1) Σ|wⱼ|` from
`crtAccFP64_error`, `ozaki2Approx_error` applies whenever `2 k 2^(2P) + 2ε < M`. -/
theorem ozaki2FP64_error {eng : Engine} {b budget : ℕ} (heng : eng.ExactOn b budget)
    {round : ℚ → Option ℚ} {u η : ℚ} (hu : 0 ≤ u) (hround : RoundWithin round u η)
    {B : CRTBasis} (hB : B.Valid) (hmb : ∀ m ∈ B.moduli, m ≤ 2 ^ (b + 1))
    (P : ℕ) {x y : List ℚ} (hlen : x.length = y.length)
    (hbudget : x.length * (2 ^ b * 2 ^ b) ≤ budget)
    (hrange : 2 * x.length * (2 ^ P * 2 ^ P) < B.modulus)
    (hmargin : 2 * ((x.length * (2 ^ P * 2 ^ P) : ℕ) : ℚ) +
      2 * (B.weights.length * 2 ^ (-53 : ℤ) *
        (2 ^ (b + 1 : ℤ) * (B.weights.map fun w : ℤ => Rat.abs (w : ℚ)).sum)) < B.modulus) {v : ℚ}
    (hv : ozaki2Approx eng round crtAccFP64 B P x y = some v) :
    Rat.abs (v - dot x y) ≤
      u * (Rat.abs ((dotZ (scaleTrunc (scaleShift P x) x) (scaleTrunc (scaleShift P y) y) : ℚ) *
          2 ^ (-(scaleShift P x + scaleShift P y))) +
        (B.weights.length * 2 ^ (-53 : ℤ) *
          (2 ^ (b + 1 : ℤ) * (B.weights.map fun w : ℤ => Rat.abs (w : ℚ)).sum)) *
          2 ^ (-(scaleShift P x + scaleShift P y))) + η +
        (B.weights.length * 2 ^ (-53 : ℤ) *
          (2 ^ (b + 1 : ℤ) * (B.weights.map fun w : ℤ => Rat.abs (w : ℚ)).sum)) *
          2 ^ (-(scaleShift P x + scaleShift P y)) +
      (List.zipWith (fun a b => 2 ^ (-scaleShift P x) * Rat.abs b +
          2 ^ (-(scaleShift P x + scaleShift P y)) *
            Rat.abs (truncInt (a * 2 ^ scaleShift P x) : ℚ)) x y).sum :=
  ozaki2Approx_error heng hu hround hB hmb (fun _ _ hr _ h => crtAccFP64_error hr h) P hlen
    hbudget hrange hmargin hv

end Ozaki
