import Ozaki.Rounding

/-! # Ozaki-I: error-free slicing

Ozaki, Ogita, Oishi and Rump (2012) split a row `x` of `A` (or a column `y` of `B`) into slices of
small integers on decreasing power-of-two grids:

  `x = Σₜ 2^gₜ · qₜ + r`,  `qₜ` integer vectors with `|qₜ,ᵢ| ≤ 2^b`.

Slice `t` rounds what the previous slices left to the nearest multiple of `2^gₜ`, ties to even,
where `gₜ = Eₜ − b` and `Eₜ = ⌈log₂ max|·|⌉` of what is left. On binary32 inputs this is exactly
what the σ-trick `fl(fl(a + σ) − σ)` computes (`OzakiTC.Split32`). Each slice therefore keeps `b`
bits below the leading bit of its row, and what it leaves is at most half its grid step, so every
slice gains `b + 1` bits:

* `split_dot`: the split is exact, as a statement about every dot product `x · y`;
* `split_coeff_bound`: every coefficient has magnitude at most `2^b`;
* `split_grid_le`: the `t`-th grid is at most `2^(E − b − t(b+1))`;
* `split_residual_le`: every residual entry is at most `2^(E − s(b+1))`;
* `splitExp_spec`: `E` is `⌈log₂ max|x|⌉` for a nonzero `x`, and bounds every `|xᵢ|`.

A zero vector has zero slices; its grids continue the sequence `gₜ₊₁ = gₜ − (b + 1)` so that the
grid bounds hold for every vector. -/

local notation "ℕ" => Nat
local notation "ℤ" => Int
local notation "ℚ" => Rat

namespace Ozaki

/-- One slice: integer coefficients `q` on the grid `2^grid`; it is worth `q · 2^grid`. -/
structure Slice where
  grid : ℤ
  coeffs : List ℤ
  deriving Repr, DecidableEq, Inhabited

/-- Grid of the next slice: `2^(E − b)` with `E = ⌈log₂ max|x|⌉`; for a zero vector, the grid
continues `b + 1` below the previous one. -/
def sliceGrid (b : ℕ) (prev : ℤ) (x : List ℚ) : ℤ :=
  if maxAbs x = 0 then prev - (b + 1) else ceilLog2 (maxAbs x) - b

/-- Coefficients `qᵢ = rne(xᵢ / 2^g)`. -/
def sliceCoeffs (g : ℤ) (x : List ℚ) : List ℤ := x.map fun a => roundNearestEven (a / 2 ^ g)

/-- What a slice leaves: `xᵢ − qᵢ · 2^g`. -/
def sliceRest (g : ℤ) (x : List ℚ) : List ℚ :=
  x.map fun a => a - (roundNearestEven (a / 2 ^ g) : ℚ) * 2 ^ g

/-- `s` slices of `b` bits and the residual; `prev` is the grid a zero vector continues from. -/
def splitFrom (b : ℕ) : ℕ → ℤ → List ℚ → List Slice × List ℚ
  | 0, _, x => ([], x)
  | s + 1, prev, x =>
    let g := sliceGrid b prev x
    let r := splitFrom b s g (sliceRest g x)
    (⟨g, sliceCoeffs g x⟩ :: r.1, r.2)

/-- `split b s x`: `s` slices of `b`-bit integers, and the residual. -/
def split (b s : ℕ) (x : List ℚ) : List Slice × List ℚ := splitFrom b s b x

/-- The exponent `E` of a split: `E = ⌈log₂ max|x|⌉` for a nonzero vector. -/
def splitExp (b : ℕ) (x : List ℚ) : ℤ := sliceGrid b b x + b

/-! ## One slice -/

theorem sliceCoeffs_length (g : ℤ) (x : List ℚ) : (sliceCoeffs g x).length = x.length := by
  simp [sliceCoeffs]

theorem sliceRest_length (g : ℤ) (x : List ℚ) : (sliceRest g x).length = x.length := by
  simp [sliceRest]

/-- One slice is exact: `x · y = 2^g (q · y) + (x − 2^g q) · y`. -/
theorem dot_slice (g : ℤ) (x y : List ℚ) :
    dot x y = 2 ^ g * dot (ofInts (sliceCoeffs g x)) y + dot (sliceRest g x) y := by
  induction x generalizing y with
  | nil => simp [sliceCoeffs, sliceRest] <;> grind
  | cons a x ih =>
    cases y with
    | nil => simp [sliceCoeffs, sliceRest] <;> grind
    | cons c y =>
      have h := ih y
      simp only [sliceCoeffs, sliceRest, List.map_cons, ofInts_cons, dot_cons] at h ⊢
      rw [h]
      grind

/-- Every entry is bounded by `2^E`, the exponent of its slice. -/
theorem abs_le_two_pow_sliceGrid (b : ℕ) (prev : ℤ) (x : List ℚ) :
    ∀ a ∈ x, Rat.abs a ≤ 2 ^ (sliceGrid b prev x + b) := by
  intro a ha
  unfold sliceGrid
  split
  · rename_i h
    rw [eq_zero_of_maxAbs h a ha, abs_zero]
    exact Rat.le_of_lt (two_pow_pos _)
  · rename_i h
    have hpos : 0 < maxAbs x := by have := maxAbs_nonneg x; grind
    have hE := (ceilLog2_spec hpos).2
    have : ceilLog2 (maxAbs x) - (b : ℤ) + b = ceilLog2 (maxAbs x) := by omega
    rw [this]
    exact Rat.le_trans (abs_le_maxAbs ha) hE

/-- Every coefficient of a slice has magnitude at most `2^b`. -/
theorem sliceCoeffs_bound (b : ℕ) (prev : ℤ) (x : List ℚ) :
    ∀ q ∈ sliceCoeffs (sliceGrid b prev x) x, q.natAbs ≤ 2 ^ b := by
  intro q hq
  obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hq
  apply natAbs_roundNearestEven_le
  have hg := two_pow_pos (sliceGrid b prev x)
  have hA := abs_le_two_pow_sliceGrid b prev x a ha
  rw [abs_div_two_pow, div_le_iff hg, ← two_pow_natCast, ← two_pow_add]
  have : (b : ℤ) + sliceGrid b prev x = sliceGrid b prev x + b := by omega
  rw [this]
  exact hA

/-- What a slice leaves is at most half its grid step. -/
theorem sliceRest_bound (g : ℤ) (x : List ℚ) : ∀ a ∈ sliceRest g x, Rat.abs a ≤ 2 ^ (g - 1) := by
  intro a ha
  obtain ⟨c, _, rfl⟩ := List.mem_map.mp ha
  have hg := two_pow_pos g
  have he := roundNearestEven_error (c / 2 ^ g)
  have hc : c / 2 ^ g * 2 ^ g = c := Rat.div_mul_cancel (two_pow_ne_zero g)
  have heq : c - (roundNearestEven (c / 2 ^ g) : ℚ) * 2 ^ g =
      (c / 2 ^ g - roundNearestEven (c / 2 ^ g)) * 2 ^ g := by grind
  rw [heq, abs_mul_two_pow]
  have hhalf : (2 : ℚ) ^ (g - 1) * 2 = 2 ^ g := by rw [← two_pow_succ]; congr 1; omega
  have := Rat.mul_le_mul_of_nonneg_right he (Rat.le_of_lt hg)
  grind

/-- The next grid is at least `b + 1` below the current one. -/
theorem sliceGrid_rest_le (b : ℕ) (g : ℤ) (x : List ℚ) :
    sliceGrid b g (sliceRest g x) ≤ g - (b + 1) := by
  unfold sliceGrid
  split
  · exact Int.le_refl _
  · rename_i h
    have hpos : 0 < maxAbs (sliceRest g x) := by have := maxAbs_nonneg (sliceRest g x); grind
    have hm := maxAbs_le (Rat.le_of_lt (two_pow_pos (g - 1))) (sliceRest_bound g x)
    have := (ceilLog2_le_iff hpos (g - 1)).mpr hm
    omega

/-! ## The split -/

theorem splitFrom_length (b s : ℕ) (prev : ℤ) (x : List ℚ) :
    (splitFrom b s prev x).1.length = s ∧
    (∀ sl ∈ (splitFrom b s prev x).1, sl.coeffs.length = x.length) ∧
    (splitFrom b s prev x).2.length = x.length := by
  induction s generalizing prev x with
  | zero => simp [splitFrom]
  | succ s ih =>
    obtain ⟨h1, h2, h3⟩ := ih (sliceGrid b prev x) (sliceRest (sliceGrid b prev x) x)
    refine ⟨by simp [splitFrom, h1], ?_, by simp [splitFrom, h3, sliceRest_length]⟩
    intro sl hsl
    simp only [splitFrom, List.mem_cons] at hsl
    rcases hsl with rfl | hsl
    · exact sliceCoeffs_length _ _
    · rw [h2 sl hsl, sliceRest_length]

/-- **The split is exact.** For every `y`, `x · y = Σₜ 2^gₜ (qₜ · y) + r · y`. -/
theorem splitFrom_dot (b s : ℕ) (prev : ℤ) (x y : List ℚ) :
    dot x y = ((splitFrom b s prev x).1.map fun sl => 2 ^ sl.grid * dot (ofInts sl.coeffs) y).sum +
      dot (splitFrom b s prev x).2 y := by
  induction s generalizing prev x with
  | zero => simp [splitFrom] <;> grind
  | succ s ih =>
    simp only [splitFrom, List.map_cons, List.sum_cons]
    rw [dot_slice (sliceGrid b prev x) x y, ih (sliceGrid b prev x) (sliceRest (sliceGrid b prev x) x)]
    grind

/-- Every coefficient has magnitude at most `2^b`. -/
theorem splitFrom_coeff_bound (b s : ℕ) (prev : ℤ) (x : List ℚ) :
    ∀ sl ∈ (splitFrom b s prev x).1, ∀ q ∈ sl.coeffs, q.natAbs ≤ 2 ^ b := by
  induction s generalizing prev x with
  | zero => simp [splitFrom]
  | succ s ih =>
    simp only [splitFrom, List.mem_cons, forall_eq_or_imp]
    exact ⟨sliceCoeffs_bound b prev x, ih _ _⟩

/-- The first grid is `sliceGrid b prev x`, and the `t`-th is at least `t (b + 1)` below it. -/
theorem splitFrom_grid_le (b s : ℕ) (prev : ℤ) (x : List ℚ) :
    ∀ (t : ℕ) (sl : Slice), (splitFrom b s prev x).1[t]? = some sl →
      sl.grid ≤ sliceGrid b prev x - (t : ℤ) * (b + 1) := by
  induction s generalizing prev x with
  | zero => simp [splitFrom]
  | succ s ih =>
    intro t sl h
    cases t with
    | zero =>
      simp only [splitFrom, List.getElem?_cons_zero, Option.some.injEq] at h
      subst h; simp
    | succ t =>
      simp only [splitFrom, List.getElem?_cons_succ] at h
      have h1 := ih _ _ t sl h
      have h2 := sliceGrid_rest_le b (sliceGrid b prev x) x
      push_cast
      have : (t : ℤ) * (b + 1) + (b + 1) = ((t : ℤ) + 1) * (b + 1) := by
        rw [Int.add_mul, Int.one_mul]
      omega

/-- Every residual entry is at most `2^(E − s(b+1))`, with `E = sliceGrid b prev x + b`. -/
theorem splitFrom_residual_le (b s : ℕ) (prev : ℤ) (x : List ℚ) :
    ∀ a ∈ (splitFrom b s prev x).2, Rat.abs a ≤ 2 ^ (sliceGrid b prev x + b - s * (b + 1)) := by
  induction s generalizing prev x with
  | zero =>
    intro a ha
    simp only [splitFrom] at ha
    have he : sliceGrid b prev x + (b : ℤ) - ((0 : ℕ) : ℤ) * (b + 1) = sliceGrid b prev x + b := by
      omega
    rw [he]
    exact abs_le_two_pow_sliceGrid b prev x a ha
  | succ s ih =>
    intro a ha
    simp only [splitFrom] at ha
    have h1 := ih _ _ a ha
    have h2 := sliceGrid_rest_le b (sliceGrid b prev x) x
    refine Rat.le_trans h1 (two_pow_le ?_)
    push_cast
    have : ((s : ℤ) + 1) * (b + 1) = (s : ℤ) * (b + 1) + (b + 1) := by
      rw [Int.add_mul, Int.one_mul]
    omega

/-- A split into fewer slices is a prefix: the residual after `s` slices is the remaining
slices plus the final residual. -/
theorem splitFrom_prefix (b s n : ℕ) (prev : ℤ) (x : List ℚ) (hn : n ≤ s) :
    (splitFrom b n prev x).1 = (splitFrom b s prev x).1.take n := by
  induction n generalizing s prev x with
  | zero => simp [splitFrom]
  | succ n ih =>
    cases s with
    | zero => omega
    | succ s =>
      simp only [splitFrom, List.take_succ_cons]
      rw [ih s _ _ (by omega)]

/-! ## The exponent of a split -/

theorem split_eq (b s : ℕ) (x : List ℚ) : split b s x = splitFrom b s b x := rfl

/-- `E = ⌈log₂ max|x|⌉` for a nonzero vector: `2^(E−1) < max|x| ≤ 2^E`. -/
theorem splitExp_spec (b : ℕ) {x : List ℚ} (hx : maxAbs x ≠ 0) :
    splitExp b x = ceilLog2 (maxAbs x) ∧
      (2 : ℚ) ^ (splitExp b x - 1) < maxAbs x ∧ maxAbs x ≤ 2 ^ splitExp b x := by
  have hE : splitExp b x = ceilLog2 (maxAbs x) := by
    unfold splitExp sliceGrid; rw [if_neg hx]; omega
  have hpos : 0 < maxAbs x := by have := maxAbs_nonneg x; grind
  rw [hE]
  exact ⟨rfl, ceilLog2_spec hpos⟩

theorem abs_le_two_pow_splitExp (b : ℕ) (x : List ℚ) :
    ∀ a ∈ x, Rat.abs a ≤ 2 ^ splitExp b x := abs_le_two_pow_sliceGrid b b x

theorem split_dot (b s : ℕ) (x y : List ℚ) :
    dot x y = ((split b s x).1.map fun sl => 2 ^ sl.grid * dot (ofInts sl.coeffs) y).sum +
      dot (split b s x).2 y := splitFrom_dot b s b x y

theorem split_coeff_bound (b s : ℕ) (x : List ℚ) :
    ∀ sl ∈ (split b s x).1, ∀ q ∈ sl.coeffs, q.natAbs ≤ 2 ^ b := splitFrom_coeff_bound b s b x

theorem split_grid_le (b s : ℕ) (x : List ℚ) :
    ∀ (t : ℕ) (sl : Slice), (split b s x).1[t]? = some sl →
      sl.grid + b ≤ splitExp b x - (t : ℤ) * (b + 1) := by
  intro t sl h
  have := splitFrom_grid_le b s b x t sl h
  unfold splitExp; omega

theorem split_residual_le (b s : ℕ) (x : List ℚ) :
    ∀ a ∈ (split b s x).2, Rat.abs a ≤ 2 ^ (splitExp b x - s * (b + 1)) :=
  splitFrom_residual_le b s b x

theorem split_length (b s : ℕ) (x : List ℚ) :
    (split b s x).1.length = s ∧ (∀ sl ∈ (split b s x).1, sl.coeffs.length = x.length) ∧
      (split b s x).2.length = x.length := splitFrom_length b s b x

theorem split_prefix (b s n : ℕ) (x : List ℚ) (hn : n ≤ s) :
    (split b n x).1 = (split b s x).1.take n := splitFrom_prefix b s n b x hn

end Ozaki
