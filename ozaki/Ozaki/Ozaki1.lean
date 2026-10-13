import Ozaki.Split
import Ozaki.Summation

/-! # Ozaki-I: slice products and recombination

One output entry `x · y` (row `x` of `A`, column `y` of `B`) is computed as follows.

1. Split `x` and `y` into `s` slices of `b`-bit integers (`Ozaki.Split`).
2. Multiply slice `t` of `x` with slice `u` of `y` on a low-precision matrix multiplier for every
   pair with `t + u < s`: `s (s + 1) / 2` products on the matrix multiplier.
3. Scale each product by `2^(gₜ + hᵤ)` and add the scaled products in working precision, smallest
   first.

The matrix multiplier is abstract here (`MatrixMultiplier`): any function that returns an integer
dot product. The hardware libraries supply matrix multipliers built from the NVIDIA Tensor Core
model (`OzakiTC`) and the AMD matrix-core model (`OzakiMC`), and prove them exact on slices
(`MatrixMultiplier.ExactOn`).

Main results:

* `ozaki1_eq_sumWith`: with an exact matrix multiplier, Ozaki-I adds exactly the scaled exact slice
  products;
* `dot_eq_exactTerms_add`: the exact error identity
  `x · y − Σ_{t+u<s} 2^(gₜ+hᵤ) qₜ·pᵤ = r · y + Σₜ 2^gₜ (qₜ · r'ₛ₋ₜ)`, where `r` is the residual of
  `x` after `s` slices and `r'ₖ` the residual of `y` after `k` slices;
* `exactTerms_error`: `|x · y − Σ terms| ≤ (s + 1) · k · 2^(E + F − s(b+1))`;
* `exactTerms_error_normwise`: the same bound is at most
  `4 (s + 1) · k · max|x| · max|y| · 2^(−s(b+1))`;
* `ozaki1_error`: with additions of relative error `u` and absolute error `η`, the computed result
  is within `((1 + u)^n − 1) n k 2^(E+F) + n (1 + u)^n η + (s + 1) k 2^(E+F−s(b+1))` of `x · y`,
  with `n = s (s + 1) / 2`.

The Z3 model rescales each slice product with a binary32 multiplication, which it asserts to be
exact (`[S3.2]`); here the rescaling is the exact product by a power of two, so the two agree
whenever that assertion holds. -/

local notation "ℕ" => Nat
local notation "ℤ" => Int
local notation "ℚ" => Rat

namespace Ozaki

/-! ## Matrix multipliers -/

/-- A low-precision matrix multiplier seen from one output entry: it evaluates an integer dot
product `Σ xᵢ yᵢ`, returning its value or failing. -/
abbrev MatrixMultiplier := List ℤ → List ℤ → Option ℚ

/-- The matrix multiplier returns `Σ xᵢ yᵢ` exactly on equally long vectors whose entries have
magnitude at most `2^b` and whose products have total magnitude at most `bound`, the exactness
bound. -/
def MatrixMultiplier.ExactOn (mult : MatrixMultiplier) (b bound : ℕ) : Prop :=
  ∀ x y : List ℤ, x.length = y.length → (∀ a ∈ x, a.natAbs ≤ 2 ^ b) →
    (∀ a ∈ y, a.natAbs ≤ 2 ^ b) → dotAbs x y ≤ bound → mult x y = some (dotZ x y)

/-- The ideal matrix multiplier: exact integer arithmetic. -/
def exactMultiplier : MatrixMultiplier := fun x y => some (dotZ x y)

theorem exactMultiplier_exactOn (b bound : ℕ) : exactMultiplier.ExactOn b bound :=
  fun _ _ _ _ _ _ => rfl

/-! ## Slice pairs -/

/-- The pairs `(t, u)` with `t + u < s`, by anti-diagonal from the largest `t + u` down and with
`t` ascending within each: the order in which the Z3 model adds the scaled products (smallest
first). -/
def trianglePairs (s : ℕ) : List (ℕ × ℕ) :=
  (List.range s).reverse.flatMap fun d => (List.range (d + 1)).map fun t => (t, d - t)

theorem trianglePairs_succ (s : ℕ) :
    trianglePairs (s + 1) = (List.range (s + 1)).map (fun t => (t, s - t)) ++ trianglePairs s := by
  simp only [trianglePairs, List.range_succ, List.reverse_append, List.reverse_singleton,
    List.singleton_append, List.flatMap_cons]

theorem mem_trianglePairs {s t u : ℕ} : (t, u) ∈ trianglePairs s ↔ t + u < s := by
  simp only [trianglePairs, List.mem_flatMap, List.mem_reverse, List.mem_range, List.mem_map,
    Prod.mk.injEq]
  constructor
  · rintro ⟨d, hd, t', ht', rfl, rfl⟩; omega
  · intro h; exact ⟨t + u, h, t, by omega, rfl, by omega⟩

/-- There are `s (s + 1) / 2` pairs. -/
theorem trianglePairs_length (s : ℕ) : 2 * (trianglePairs s).length = s * (s + 1) := by
  induction s with
  | zero => rfl
  | succ s ih =>
    rw [trianglePairs_succ, List.length_append, List.length_map, List.length_range]
    grind

/-- Adding over the anti-diagonals is adding, for each `t`, over `u < s − t`. -/
theorem sum_trianglePairs (s : ℕ) (f : ℕ → ℕ → ℚ) :
    ((trianglePairs s).map fun p => f p.1 p.2).sum =
      ((List.range s).map fun t => ((List.range (s - t)).map fun u => f t u).sum).sum := by
  induction s with
  | zero => rfl
  | succ s ih =>
    rw [trianglePairs_succ, List.map_append, sum_append_q, ih, List.map_map]
    have hsplit : ∀ t ∈ List.range (s + 1),
        ((List.range (s + 1 - t)).map fun u => f t u).sum =
          ((List.range (s - t)).map fun u => f t u).sum + f t (s - t) := by
      intro t ht
      have ht' := List.mem_range.mp ht
      rw [show s + 1 - t = (s - t) + 1 by omega, List.range_succ, List.map_append,
        sum_append_q]
      simp <;> grind
    rw [List.map_congr_left hsplit, sum_map_add, List.range_succ, List.map_append, sum_append_q]
    simp only [Function.comp_def, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
      Nat.sub_self]
    grind

/-! ## The scheme -/

/-- The term of the slice pair `(t, u)`: the slice product of the matrix multiplier, scaled by
`2^(gₜ + hᵤ)`. -/
def pairTerm (mult : MatrixMultiplier) (sx sy : List Slice) (p : ℕ × ℕ) : Option ℚ :=
  (mult (sx.getD p.1 default).coeffs (sy.getD p.2 default).coeffs).map
    fun v => 2 ^ ((sx.getD p.1 default).grid + (sy.getD p.2 default).grid) * v

/-- The exact term of the slice pair `(t, u)`: `2^(gₜ + hᵤ) · (qₜ · pᵤ)`. -/
def exactTerm (sx sy : List Slice) (p : ℕ × ℕ) : ℚ :=
  2 ^ ((sx.getD p.1 default).grid + (sy.getD p.2 default).grid) *
    dotZ (sx.getD p.1 default).coeffs (sy.getD p.2 default).coeffs

/-- The exact terms of Ozaki-I with `s` slices of `b` bits, in the order of `trianglePairs`. -/
def exactTerms (b s : ℕ) (x y : List ℚ) : List ℚ :=
  (trianglePairs s).map (exactTerm (split b s x).1 (split b s y).1)

/-- **Ozaki-I** for one output entry `x · y`: `s` slices of `b` bits, the `s (s + 1) / 2` slice
products with `t + u < s` on the matrix multiplier, then left-to-right summation with `add`. -/
def ozaki1 (mult : MatrixMultiplier) (add : ℚ → ℚ → Option ℚ) (b s : ℕ) (x y : List ℚ) : Option ℚ :=
  ((trianglePairs s).mapM (pairTerm mult (split b s x).1 (split b s y).1)).bind (sumWith add 0)

/-- `mapM` of a function that always succeeds. -/
theorem mapM_eq_some_map {l : List α} {f : α → Option β} {g : α → β}
    (h : ∀ a ∈ l, f a = some (g a)) : l.mapM f = some (l.map g) := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    simp only [List.mapM_cons, h a (by simp), Option.pure_def, Option.bind_eq_bind,
      Option.bind_some, List.map_cons]
    rw [ih (fun b hb => h b (by simp [hb]))]
    rfl

theorem getD_mem {l : List α} [Inhabited α] {t : ℕ} (h : t < l.length) : l.getD t default ∈ l := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h]
  exact List.getElem_mem h

/-- Every call of Ozaki-I to the matrix multiplier multiplies two slices whose coefficients are
`b`-bit integers. -/
theorem pairTerm_exact {mult : MatrixMultiplier} {b bound s : ℕ} (hmult : mult.ExactOn b bound)
    {x y : List ℚ} (hlen : x.length = y.length) (hbound : x.length * (2 ^ b * 2 ^ b) ≤ bound)
    {p : ℕ × ℕ} (hp : p ∈ trianglePairs s) :
    pairTerm mult (split b s x).1 (split b s y).1 p =
      some (exactTerm (split b s x).1 (split b s y).1 p) := by
  obtain ⟨t, u⟩ := p
  have htu := mem_trianglePairs.mp hp
  obtain ⟨hlx, hcx, _⟩ := split_length b s x
  obtain ⟨hly, hcy, _⟩ := split_length b s y
  have hmx := getD_mem (l := (split b s x).1) (t := t) (by omega)
  have hmy := getD_mem (l := (split b s y).1) (t := u) (by omega)
  have hl1 := hcx _ hmx
  have hl2 := hcy _ hmy
  unfold pairTerm exactTerm
  rw [hmult _ _ (by rw [hl1, hl2, hlen]) (split_coeff_bound b s x _ hmx)
    (split_coeff_bound b s y _ hmy)]
  · rfl
  · refine Nat.le_trans (dotAbs_le _ _ _ _ (split_coeff_bound b s x _ hmx)
      (split_coeff_bound b s y _ hmy)) ?_
    rw [hl1]; exact hbound

/-- **Exact calls to the matrix multiplier.** With a matrix multiplier exact on `b`-bit slices,
Ozaki-I adds exactly the scaled exact slice products. -/
theorem ozaki1_eq_sumWith {mult : MatrixMultiplier} {b bound : ℕ} (hmult : mult.ExactOn b bound)
    (add : ℚ → ℚ → Option ℚ) (s : ℕ) {x y : List ℚ} (hlen : x.length = y.length)
    (hbound : x.length * (2 ^ b * 2 ^ b) ≤ bound) :
    ozaki1 mult add b s x y = sumWith add 0 (exactTerms b s x y) := by
  unfold ozaki1 exactTerms
  rw [mapM_eq_some_map (fun p hp => pairTerm_exact hmult hlen hbound hp)]
  rfl

/-! ## The exact error identity -/

theorem sum_map_eq_range_getD [Inhabited α] (l : List α) (F : α → ℚ) :
    (l.map F).sum = ((List.range l.length).map fun t => F (l.getD t default)).sum := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    rw [List.length_cons, List.range_succ_eq_map]
    simp only [List.map_cons, List.map_map, List.sum_cons, List.getD_cons_zero]
    rw [ih]
    congr 1

theorem getD_take [Inhabited α] (l : List α) {n u : ℕ} (h : u < n) :
    (l.take n).getD u default = l.getD u default := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_take_of_lt h]

/-- **Error identity.** `x · y` is the sum of the exact terms, plus the residual of `x` against
`y`, plus each slice of `x` against the residual of `y` after the slices it was paired with. -/
theorem dot_eq_exactTerms_add (b s : ℕ) (x y : List ℚ) :
    dot x y = (exactTerms b s x y).sum + dot (split b s x).2 y +
      ((List.range s).map fun t => 2 ^ ((split b s x).1.getD t default).grid *
        dot (ofInts ((split b s x).1.getD t default).coeffs) (split b (s - t) y).2).sum := by
  have hx := split_dot b s x y
  rw [sum_map_eq_range_getD, (split_length b s x).1] at hx
  rw [hx]
  have hterm : ∀ t ∈ List.range s,
      2 ^ ((split b s x).1.getD t default).grid *
        dot (ofInts ((split b s x).1.getD t default).coeffs) y =
      ((List.range (s - t)).map fun u => exactTerm (split b s x).1 (split b s y).1 (t, u)).sum +
        2 ^ ((split b s x).1.getD t default).grid *
          dot (ofInts ((split b s x).1.getD t default).coeffs) (split b (s - t) y).2 := by
    intro t ht
    have htl := List.mem_range.mp ht
    generalize hsl : (split b s x).1.getD t default = sl
    have hy := split_dot b (s - t) y (ofInts sl.coeffs)
    rw [sum_map_eq_range_getD, (split_length b (s - t) y).1] at hy
    rw [dot_comm, hy, dot_comm (split b (s - t) y).2, Rat.mul_add, ← sum_map_mul_left]
    congr 1
    congr 1
    apply List.map_congr_left
    intro u hu
    have hul := List.mem_range.mp hu
    rw [split_prefix b s (s - t) y (by omega), getD_take _ hul, dot_comm, dot_ofInts,
      exactTerm, hsl, dotZ_comm, two_pow_add]
    grind
  rw [List.map_congr_left hterm, sum_map_add]
  unfold exactTerms
  rw [sum_trianglePairs s (fun t u => exactTerm (split b s x).1 (split b s y).1 (t, u))]
  grind

/-! ## Bounds -/

/-- **Slicing error.** `|x · y − Σ terms| ≤ (s + 1) · k · 2^(E + F − s(b+1))`, with `E` and `F` the
exponents of `x` and `y`. -/
theorem exactTerms_error (b s : ℕ) (x y : List ℚ) :
    Rat.abs (dot x y - (exactTerms b s x y).sum) ≤
      ((s + 1 : ℕ) : ℚ) * x.length * 2 ^ (splitExp b x + splitExp b y - s * (b + 1)) := by
  rw [dot_eq_exactTerms_add b s x y]
  generalize hB : (2 : ℚ) ^ (splitExp b x + splitExp b y - s * (b + 1)) = B
  have hBpos : 0 < B := by rw [← hB]; exact two_pow_pos _
  have hk : (0 : ℚ) ≤ x.length := Rat.natCast_nonneg
  -- the residual of `x` against `y`
  have h1 : Rat.abs (dot (split b s x).2 y) ≤ x.length * B := by
    have := abs_dot_le (split b s x).2 y _ _ (split_residual_le b s x)
      (abs_le_two_pow_splitExp b y) (Rat.le_of_lt (two_pow_pos _)) (Rat.le_of_lt (two_pow_pos _))
    rw [(split_length b s x).2.2, ← two_pow_add] at this
    rw [← hB]
    have he : splitExp b x - s * (b + 1) + splitExp b y = splitExp b x + splitExp b y -
      s * (b + 1) := by omega
    rwa [he] at this
  -- each slice of `x` against a residual of `y`
  have h2 : ∀ t ∈ List.range s, Rat.abs (2 ^ ((split b s x).1.getD t default).grid *
      dot (ofInts ((split b s x).1.getD t default).coeffs) (split b (s - t) y).2) ≤
        x.length * B := by
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
    have hd := abs_dot_le _ _ _ _ hc (split_residual_le b (s - t) y)
      (Rat.le_of_lt (two_pow_pos _)) (Rat.le_of_lt (two_pow_pos _))
    rw [ofInts_length, (split_length b s x).2.1 sl hmem, ← two_pow_add] at hd
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

/-- **Slicing error, normwise.** For nonzero `x` and `y`,
`|x · y − Σ terms| ≤ 4 (s + 1) · k · max|x| · max|y| · 2^(−s(b+1))`. -/
theorem exactTerms_error_normwise (b s : ℕ) {x y : List ℚ} (hx : maxAbs x ≠ 0) (hy : maxAbs y ≠ 0) :
    Rat.abs (dot x y - (exactTerms b s x y).sum) ≤
      4 * ((s + 1 : ℕ) : ℚ) * x.length * maxAbs x * maxAbs y * 2 ^ (-((s * (b + 1) : ℕ) : ℤ)) := by
  refine Rat.le_trans (exactTerms_error b s x y) ?_
  obtain ⟨_, hEx, _⟩ := splitExp_spec b hx
  obtain ⟨_, hEy, _⟩ := splitExp_spec b hy
  have h2x : (2 : ℚ) ^ splitExp b x < 2 * maxAbs x := by
    have : (2 : ℚ) ^ splitExp b x = 2 ^ (splitExp b x - 1) * 2 := by
      rw [← two_pow_succ]; congr 1; omega
    grind
  have h2y : (2 : ℚ) ^ splitExp b y < 2 * maxAbs y := by
    have : (2 : ℚ) ^ splitExp b y = 2 ^ (splitExp b y - 1) * 2 := by
      rw [← two_pow_succ]; congr 1; omega
    grind
  have hsplit : (2 : ℚ) ^ (splitExp b x + splitExp b y - s * (b + 1)) =
      2 ^ splitExp b x * 2 ^ splitExp b y * 2 ^ (-((s * (b + 1) : ℕ) : ℤ)) := by
    rw [← two_pow_add, ← two_pow_add]; congr 1
  rw [hsplit]
  have hP := two_pow_pos (-((s * (b + 1) : ℕ) : ℤ))
  have hk : (0 : ℚ) ≤ ((s + 1 : ℕ) : ℚ) * x.length :=
    Rat.mul_nonneg Rat.natCast_nonneg Rat.natCast_nonneg
  have hxy : (2 : ℚ) ^ splitExp b x * 2 ^ splitExp b y ≤ (2 * maxAbs x) * (2 * maxAbs y) :=
    mul_le_mul_abs (by rw [abs_two_pow]; exact Rat.le_of_lt h2x)
      (by rw [abs_two_pow]; exact Rat.le_of_lt h2y) |> fun h => by
        rwa [abs_mul, abs_two_pow, abs_two_pow] at h
  have := Rat.mul_le_mul_of_nonneg_right hxy (Rat.le_of_lt hP)
  have := Rat.mul_le_mul_of_nonneg_left this hk
  grind

/-- Every exact term is at most `k · 2^(E + F)`. -/
theorem abs_exactTerm_le (b s : ℕ) (x y : List ℚ) {p : ℕ × ℕ}
    (hp : p ∈ trianglePairs s) :
    Rat.abs (exactTerm (split b s x).1 (split b s y).1 p) ≤
      x.length * 2 ^ (splitExp b x + splitExp b y) := by
  obtain ⟨t, u⟩ := p
  have htu := mem_trianglePairs.mp hp
  obtain ⟨hlx, hcx, _⟩ := split_length b s x
  obtain ⟨hly, hcy, _⟩ := split_length b s y
  have hmx := getD_mem (l := (split b s x).1) (t := t) (by omega)
  have hmy := getD_mem (l := (split b s y).1) (t := u) (by omega)
  generalize hsx : (split b s x).1.getD t default = sx at hmx
  generalize hsy : (split b s y).1.getD u default = sy at hmy
  have hgx := split_grid_le b s x t sx (by
    rw [← hsx, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega)]; rfl)
  have hgy := split_grid_le b s y u sy (by
    rw [← hsy, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega)]; rfl)
  unfold exactTerm
  simp only [hsx, hsy]
  rw [abs_mul, abs_two_pow, abs_intCast]
  have hd := natAbs_dotZ_le sx.coeffs sy.coeffs
  have hb := dotAbs_le sx.coeffs sy.coeffs _ _ (split_coeff_bound b s x sx hmx)
    (split_coeff_bound b s y sy hmy)
  rw [hcx sx hmx] at hb
  have hq : (((dotZ sx.coeffs sy.coeffs).natAbs : ℕ) : ℚ) ≤ x.length * (2 ^ (b : ℤ) * 2 ^ (b : ℤ)) := by
    rw [two_pow_natCast, ← Rat.natCast_mul, ← Rat.natCast_mul]
    exact Rat.natCast_le_natCast.mpr (Nat.le_trans hd hb)
  have hm := Rat.mul_le_mul_of_nonneg_left hq (Rat.le_of_lt (two_pow_pos (sx.grid + sy.grid)))
  refine Rat.le_trans hm ?_
  have hexp : sx.grid + sy.grid + (b + b) ≤ splitExp b x + splitExp b y := by
    have : (0 : ℤ) ≤ (t : ℤ) * (b + 1) := Int.mul_nonneg (by omega) (by omega)
    have : (0 : ℤ) ≤ (u : ℤ) * (b + 1) := Int.mul_nonneg (by omega) (by omega)
    omega
  have := two_pow_le hexp
  rw [two_pow_add, two_pow_add (b : ℤ)] at this
  have := Rat.mul_le_mul_of_nonneg_left this (show (0 : ℚ) ≤ x.length from Rat.natCast_nonneg)
  grind

/-- **Ozaki-I error.** With a matrix multiplier exact on `b`-bit slices and additions of relative
error `u` and absolute error `η`, the result is within
`((1 + u)^n − 1) n k 2^(E+F) + n (1 + u)^n η + (s + 1) k 2^(E+F−s(b+1))` of `x · y`. -/
theorem ozaki1_error {mult : MatrixMultiplier} {add : ℚ → ℚ → Option ℚ} {b bound s : ℕ} {u η : ℚ}
    (hmult : mult.ExactOn b bound) (hu : 0 ≤ u) (hη : 0 ≤ η) (hadd : AddWithin add u η)
    {x y : List ℚ} (hlen : x.length = y.length) (hbound : x.length * (2 ^ b * 2 ^ b) ≤ bound)
    {v : ℚ} (hv : ozaki1 mult add b s x y = some v) :
    Rat.abs (v - dot x y) ≤
      ((1 + u) ^ (trianglePairs s).length - 1) *
          ((trianglePairs s).length * (x.length * 2 ^ (splitExp b x + splitExp b y))) +
        (trianglePairs s).length * (1 + u) ^ (trianglePairs s).length * η +
        ((s + 1 : ℕ) : ℚ) * x.length * 2 ^ (splitExp b x + splitExp b y - s * (b + 1)) := by
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
    have : (1 : ℚ) ≤ (1 + u) ^ (trianglePairs s).length := by
      clear hr hT hlenT
      induction (trianglePairs s).length with
      | zero => simp
      | succ n ih =>
        rw [Rat.pow_succ]
        have := Rat.mul_le_mul_of_nonneg_left (show (1 : ℚ) ≤ 1 + u by grind)
          (show (0 : ℚ) ≤ (1 + u) ^ n by grind)
        grind
    grind
  have hT' := Rat.mul_le_mul_of_nonneg_left hT hpow
  have hs := exactTerms_error b s x y
  have htri : Rat.abs (v - dot x y) ≤ Rat.abs (v - (exactTerms b s x y).sum) +
      Rat.abs (dot x y - (exactTerms b s x y).sum) := by
    have := abs_add_le (v - (exactTerms b s x y).sum) ((exactTerms b s x y).sum - dot x y)
    rw [abs_sub_comm ((exactTerms b s x y).sum) (dot x y)] at this
    have h : v - (exactTerms b s x y).sum + ((exactTerms b s x y).sum - dot x y) = v - dot x y := by
      grind
    rwa [h] at this
  grind

/-- With exact additions, Ozaki-I returns the exact sum of its terms, within the slicing error. -/
theorem ozaki1_exactAdd {mult : MatrixMultiplier} {b bound s : ℕ} (hmult : mult.ExactOn b bound)
    {x y : List ℚ} (hlen : x.length = y.length) (hbound : x.length * (2 ^ b * 2 ^ b) ≤ bound) :
    ozaki1 mult exactAdd b s x y = some (exactTerms b s x y).sum := by
  rw [ozaki1_eq_sumWith hmult exactAdd s hlen hbound, sumWith_exactAdd]
  congr 1; grind

/-! ## Matrices -/

/-- Columns of a matrix given by its rows. -/
def transpose : List (List ℚ) → List (List ℚ)
  | [] => []
  | [r] => r.map fun a => [a]
  | r :: rs => List.zipWith List.cons r (transpose rs)

/-- `C = AB` entrywise with Ozaki-I; `A` by rows, `B` by rows. -/
def ozaki1Gemm (mult : MatrixMultiplier) (add : ℚ → ℚ → Option ℚ) (b s : ℕ) (A B : List (List ℚ)) :
    Option (List (List ℚ)) :=
  A.mapM fun x => (transpose B).mapM fun y => ozaki1 mult add b s x y

end Ozaki
