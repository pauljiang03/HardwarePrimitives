import Ozaki.SharpBounds2
import Ozaki.Width

/-! # Accumulation by levels (Abdelfattah et al., §4.4)

Abdelfattah, Dongarra, Fasi, Mikaitis and Tisseur, *Analysis of floating-point matrix
multiplication computed via integer arithmetic* (arXiv:2506.11277, v3, §4.4), accumulate the exact
integer slice products of Ozaki-I in floating point in **levels**: consecutive diagonals
`t + u = d` whose scaled products, all integer multiples of one power of two, fit together in the
floating-point significand are added with no rounding error in any order, and rounding happens
only when the level sums are added. With `ψ` levels their bound is `γ_{ψ−1}` instead of
`γ_{s(s+1)/2 − 1}` (their (4.9), (4.19)); their (4.21)–(4.22) count how many diagonals fit in a
level (`Q ≤ ⌊(p − T − 1)/t⌋`, `3` for INT8 slices of `t = 7` bits, INT32 outputs and binary64).

Here:

* **Exact levels** (`LevelExact`, `sumTree_exact`). Terms that are integer multiples of `2^G`
  whose magnitudes total less than `2^(p+G)`, with `2^G` in the format's range, add up exactly
  along any binary tree in IEEE round to nearest even with `p` bits: every partial sum is a
  multiple of `2^G` below `2^(p+G)`, hence a format value (`formatValue_of_grid`). This is the
  carry argument of §4.4 without the bookkeeping of spare carry locations: it bounds the partial
  sums by the sum of the magnitudes.
* **Accumulation by levels** (`levelAcc`, `levelAcc_error`). Each level is added exactly along
  its own tree, and the `ψ` level sums are added left to right: the error is at most
  `(ψ − 1) 2^(−p) Σⱼ |Lⱼ|`, by Jeannerod and Rump (`sumWith_error_jr`). Their (4.9) states
  `Ĉ = (1 + Θ) ∘ C̃` with `|θ| ≤ γ_{ψ−1}`; the standard summation bound, which is what is proved
  here, is relative to `Σⱼ |Lⱼ|` (equal to `|C̃|` only when the level sums share a sign), with the
  sharper constant `(ψ − 1) u` and no condition on `ψ u`.
* **Ozaki-I accumulated by levels** (`ozaki1Levels_error`): for any partition of the exact slice
  products into levels that pass the check (`levelOKB`, decidable at run time from the grids and
  magnitudes), the result is within `(ψ − 1) 2^(−p) Σⱼ |Lⱼ|` plus the slicing bound of `x · y`.
* **How many diagonals fit** (`level_exact_of_diagonals`). For a regular slicing, where the
  products of diagonal `d` are multiples of `2^(G₀ − dτ)` and total at most
  `(d + 1) K 2^(G₀ − dτ)` (`K` bounds one integer slice product, `τ` is the slice width), a level
  of diagonals `D₀ … D₁` is exact when `Σ_{d=D₀}^{D₁} (d + 1) K 2^((D₁ − d)τ) < 2^p`.
  Abdelfattah et al.'s configuration (INT8 slices of `7` bits, INT32 outputs, binary64) fits three
  diagonals per level up to diagonal `253` (`fits_int8_binary64`; they state `255`); four do not
  (`not_fits_int8_binary64_four`). With `11`-bit fp16 slices on a Tensor Core (`τ = 12`) and
  products of up to `k 2^22` with `k = 1024`, two diagonals fit up to diagonal `510`
  (`fits_fp16_binary64`) and three do not (`not_fits_fp16_binary64_three`): six slices take three
  levels, so two rounded additions instead of twenty.

Our splitting adapts each slice's grid to what is left (`Ozaki.Split`), so its grids are at least,
not exactly, `b + 1` bits apart: the a priori count applies when they are regular, and otherwise
the run-time check decides the levels. The bounds are in our terms; the spare-carry recursion
(4.21)–(4.22) is replaced by the cruder but sufficient condition on the sum of magnitudes. -/

local notation "ℕ" => Nat
local notation "ℤ" => Int
local notation "ℚ" => Rat

namespace Ozaki

/-! ## Grid multiples and exact sums -/

theorem gridMultiple_zero (G : ℤ) : GridMultiple G 0 := ⟨0, by simp⟩

theorem gridMultiple_add {G : ℤ} {a b : ℚ} (ha : GridMultiple G a) (hb : GridMultiple G b) :
    GridMultiple G (a + b) := by
  obtain ⟨z, rfl⟩ := ha
  obtain ⟨w, rfl⟩ := hb
  exact ⟨z + w, by rw [Rat.intCast_add, Rat.add_mul]⟩

/-- A multiple of `2^g` is a multiple of every finer grid `2^G`, `G ≤ g`. -/
theorem gridMultiple_mono {G g : ℤ} (hGg : G ≤ g) {a : ℚ} (ha : GridMultiple g a) :
    GridMultiple G a := by
  obtain ⟨z, rfl⟩ := ha
  refine ⟨z * (2 ^ (g - G).toNat : ℕ), ?_⟩
  rw [two_pow_eq_natCast_mul hGg, Rat.intCast_mul, Rat.intCast_natCast, Rat.mul_assoc]

theorem le_of_eq_q {a b : ℚ} (h : a = b) : a ≤ b := h ▸ Rat.le_refl

theorem abs_listSum_le : ∀ ts : List ℚ, Rat.abs ts.sum ≤ (ts.map Rat.abs).sum
  | [] => by simp
  | t :: ts => by
    simp only [List.sum_cons, List.map_cons]
    have := abs_add_le t ts.sum
    have := abs_listSum_le ts
    grind

/-- **Grid multiples below `2^(p+G)` are format values** when the grid is in the format's range. -/
theorem formatValue_of_grid {p : ℕ} {emin emax G : ℤ} {v : ℚ} (hg : GridMultiple G v)
    (hv : Rat.abs v < 2 ^ ((p : ℤ) + G)) (h1 : emin ≤ G + ((p : ℤ) - 1))
    (h2 : G + ((p : ℤ) - 1) ≤ emax) : FormatValue p emin emax v := by
  obtain ⟨z, rfl⟩ := hg
  refine ⟨z, G + ((p : ℤ) - 1), h1, h2, ?_, ?_⟩
  · rw [abs_mul_two_pow, two_pow_add, abs_intCast] at hv
    have h3 : ((z.natAbs : ℕ) : ℚ) < 2 ^ (p : ℤ) :=
      Rat.lt_of_mul_lt_mul_right hv (Rat.le_of_lt (two_pow_pos G))
    rw [two_pow_natCast] at h3
    exact_mod_cast h3
  · rw [show G + ((p : ℤ) - 1) - ((p : ℤ) - 1) = G by omega]

/-! ## Exact levels -/

/-- **A level that adds up exactly**: integer multiples of `2^G` whose magnitudes total less than
`2^(p+G)`, with the grid in the range of the format of `p` bits and exponents `emin … emax`. -/
def LevelExact (p : ℕ) (emin emax G : ℤ) (ts : List ℚ) : Prop :=
  (∀ t ∈ ts, GridMultiple G t) ∧ (ts.map Rat.abs).sum < 2 ^ ((p : ℤ) + G) ∧
    emin ≤ G + ((p : ℤ) - 1) ∧ G + ((p : ℤ) - 1) ≤ emax

theorem LevelExact.sum_formatValue {p : ℕ} {emin emax G : ℤ} {ts : List ℚ}
    (h : LevelExact p emin emax G ts) : FormatValue p emin emax ts.sum :=
  formatValue_of_grid (gridMultiple_sum h.1)
    (lt_of_le_of_lt' (abs_listSum_le ts) h.2.1) h.2.2.1 h.2.2.2

theorem LevelExact.mono {p : ℕ} {emin emax G : ℤ} {ts us : List ℚ}
    (h : LevelExact p emin emax G (ts ++ us)) :
    LevelExact p emin emax G ts ∧ LevelExact p emin emax G us := by
  obtain ⟨hg, hs, h1, h2⟩ := h
  rw [sum_map_append] at hs
  have hts := sum_nonneg (l := ts) (f := Rat.abs) fun a _ => abs_nonneg a
  have hus := sum_nonneg (l := us) (f := Rat.abs) fun a _ => abs_nonneg a
  exact ⟨⟨fun t ht => hg t (List.mem_append_left _ ht), by grind, h1, h2⟩,
    ⟨fun t ht => hg t (List.mem_append_right _ ht), by grind, h1, h2⟩⟩

/-- **An exact level adds up exactly along any tree**: every partial sum is a format value, so
every rounded addition is exact. -/
theorem sumTree_exact {p : ℕ} {emin emax G : ℤ} (hp : 0 < p) :
    ∀ T : SumTree, LevelExact p emin emax G T.leaves →
      T.evalWith some (roundRNE p emin emax) = some T.leaves.sum
  | .leaf t, _ => by simp [SumTree.evalWith, SumTree.leaves, Rat.add_zero]
  | .node l r, hL => by
    have hL' : LevelExact p emin emax G (l.leaves ++ r.leaves) := hL
    obtain ⟨hl, hr⟩ := hL'.mono
    have ef : (SumTree.node l r).leaves.sum = l.leaves.sum + r.leaves.sum := by
      simp only [SumTree.leaves, List.sum_append]
    simp only [SumTree.evalWith, sumTree_exact hp l hl, sumTree_exact hp r hr, Option.bind_some]
    rw [ef, ← List.sum_append]
    exact roundRNE_of_formatValue hp hL'.sum_formatValue

/-- The check of a level, decidable at run time: every term is an integer multiple of `2^G`, the
magnitudes total less than `2^(p+G)`, and the grid is in range. -/
def levelOKB (p : ℕ) (emin emax G : ℤ) (ts : List ℚ) : Bool :=
  ts.all (fun t => (t / 2 ^ G).den == 1) && decide ((ts.map Rat.abs).sum < 2 ^ ((p : ℤ) + G)) &&
    decide (emin ≤ G + ((p : ℤ) - 1)) && decide (G + ((p : ℤ) - 1) ≤ emax)

theorem levelOKB_spec {p : ℕ} {emin emax G : ℤ} {ts : List ℚ} (h : levelOKB p emin emax G ts = true) :
    LevelExact p emin emax G ts := by
  simp only [levelOKB, Bool.and_eq_true, List.all_eq_true, beq_iff_eq, decide_eq_true_eq] at h
  obtain ⟨⟨⟨hg, hs⟩, h1⟩, h2⟩ := h
  refine ⟨fun t ht => ⟨(t / 2 ^ G).num, ?_⟩, hs, h1, h2⟩
  have hden := hg t ht
  have hz : ((t / 2 ^ G).num : ℚ) = t / 2 ^ G :=
    Rat.ext Rat.ofInt_num (by rw [hden]; exact Rat.ofInt_den)
  rw [hz, Rat.div_mul_cancel (two_pow_ne_zero G)]

/-! ## Accumulation by levels -/

/-- **Accumulation by levels**: each level added along its own tree, then the level sums added
left to right with `rnd`. -/
def levelAcc (rnd : ℚ → Option ℚ) (levels : List SumTree) : Option ℚ :=
  (levels.mapM fun (T : SumTree) => T.evalWith some rnd).bind (sumWith (addOfRound rnd) 0)

theorem sum_flatMap_leaves :
    ∀ levels : List SumTree,
      (levels.flatMap SumTree.leaves).sum = (levels.map fun T => T.leaves.sum).sum
  | [] => rfl
  | T :: Ts => by
    rw [List.flatMap_cons, List.sum_append, List.map_cons, List.sum_cons, sum_flatMap_leaves Ts]

/-- **The error of accumulation by levels.** With `ψ` exact levels, the result is within
`(ψ − 1) 2^(−p) Σⱼ |Lⱼ|` of the exact sum of all the terms. -/
theorem levelAcc_error {p : ℕ} {emin emax : ℤ} (hp : 0 < p) (hle : emin ≤ emax)
    {levels : List SumTree} (hlev : ∀ T ∈ levels, ∃ G, LevelExact p emin emax G T.leaves)
    {v : ℚ} (hv : levelAcc (roundRNE p emin emax) levels = some v) :
    Rat.abs (v - (levels.flatMap SumTree.leaves).sum) ≤
      ((levels.length - 1 : ℕ) : ℚ) * 2 ^ (-(p : ℤ)) *
        (levels.map fun T => Rat.abs T.leaves.sum).sum := by
  have hmap : levels.mapM (fun (T : SumTree) => T.evalWith some (roundRNE p emin emax)) =
      some (levels.map fun T => T.leaves.sum) :=
    mapM_eq_some_map fun T hT => by
      obtain ⟨G, hG⟩ := hlev T hT
      exact sumTree_exact hp T hG
  unfold levelAcc at hv
  rw [hmap, Option.bind_some] at hv
  have hR : ∀ L ∈ levels.map (fun T => T.leaves.sum), FormatValue p emin emax L := by
    intro L hL
    obtain ⟨T, hT, rfl⟩ := List.mem_map.mp hL
    obtain ⟨G, hG⟩ := hlev T hT
    exact hG.sum_formatValue
  have h := sumWith_error_jr (Rat.le_of_lt (two_pow_pos _)) (roundRNE_jrAdd hp hle) hR hv
  rw [sum_flatMap_leaves, List.length_map, List.map_map] at *
  exact h

/-! ## Ozaki-I accumulated by levels -/

/-- **Ozaki-I with its slice products accumulated by levels.** For any partition of the exact
slice products into levels that add up exactly, the result is within `(ψ − 1) 2^(−p) Σⱼ |Lⱼ|`
plus the slicing bound of `x · y`. -/
theorem ozaki1Levels_error {p : ℕ} {emin emax : ℤ} (hp : 0 < p) (hle : emin ≤ emax) (b s : ℕ)
    {x y : List ℚ} {levels : List SumTree}
    (hperm : (levels.flatMap SumTree.leaves).Perm (exactTerms b s x y))
    (hlev : ∀ T ∈ levels, ∃ G, LevelExact p emin emax G T.leaves)
    {v : ℚ} (hv : levelAcc (roundRNE p emin emax) levels = some v) :
    Rat.abs (v - dot x y) ≤
      ((levels.length - 1 : ℕ) : ℚ) * 2 ^ (-(p : ℤ)) *
          (levels.map fun T => Rat.abs T.leaves.sum).sum +
        ((s + 1 : ℕ) : ℚ) * x.length * 2 ^ (splitExp b x + splitExp b y - s * (b + 1)) := by
  have h1 := levelAcc_error hp hle hlev hv
  rw [sum_perm_q hperm] at h1
  have h2 := exactTerms_error b s x y
  have := abs_add_le (v - (exactTerms b s x y).sum) ((exactTerms b s x y).sum - dot x y)
  rw [show v - (exactTerms b s x y).sum + ((exactTerms b s x y).sum - dot x y) = v - dot x y by
    grind, abs_sub_comm ((exactTerms b s x y).sum)] at this
  grind

/-- The level sums total at most the sum of the magnitudes of the terms. -/
theorem levelSums_le (levels : List SumTree) :
    (levels.map fun T => Rat.abs T.leaves.sum).sum ≤
      ((levels.flatMap SumTree.leaves).map Rat.abs).sum := by
  induction levels with
  | nil => simp
  | cons T Ts ih =>
    simp only [List.map_cons, List.sum_cons, List.flatMap_cons, sum_map_append]
    have := abs_listSum_le T.leaves
    grind

/-! ## How many diagonals fit in a level -/

/-- **A level of consecutive diagonals adds up exactly** when the slicing is regular: the terms of
diagonal `d` are multiples of `2^(G₀ − dτ)` and total at most `(d + 1) K 2^(G₀ − dτ)`, and
`Σ_{d=D₀}^{D₁} (d + 1) K 2^((D₁ − d)τ) < 2^p`. -/
theorem level_exact_of_diagonals {p : ℕ} {emin emax G0 : ℤ} {τ K D0 n : ℕ} (diags : ℕ → List ℚ)
    (hg : ∀ d ∈ List.range' D0 n, ∀ t ∈ diags d, GridMultiple (G0 - (d : ℤ) * τ) t)
    (hb : ∀ d ∈ List.range' D0 n,
      ((diags d).map Rat.abs).sum ≤ ((d + 1 : ℕ) : ℚ) * K * 2 ^ (G0 - (d : ℤ) * τ))
    (hfit : ((List.range' D0 n).map fun d =>
        (((d + 1) * K * 2 ^ ((D0 + n - 1 - d) * τ) : ℕ) : ℚ)).sum < 2 ^ (p : ℤ))
    (h1 : emin ≤ G0 - ((D0 + n - 1 : ℕ) : ℤ) * τ + ((p : ℤ) - 1))
    (h2 : G0 - ((D0 + n - 1 : ℕ) : ℤ) * τ + ((p : ℤ) - 1) ≤ emax) :
    LevelExact p emin emax (G0 - ((D0 + n - 1 : ℕ) : ℤ) * τ) ((List.range' D0 n).flatMap diags) := by
  refine ⟨?_, ?_, h1, h2⟩
  · intro t ht
    obtain ⟨d, hd, htd⟩ := List.mem_flatMap.mp ht
    have hdle : d ≤ D0 + n - 1 := by
      have := List.mem_range'_1.mp hd; omega
    refine gridMultiple_mono ?_ (hg d hd t htd)
    have : (d : ℤ) * τ ≤ ((D0 + n - 1 : ℕ) : ℤ) * τ :=
      Int.mul_le_mul_of_nonneg_right (by exact_mod_cast hdle) (by omega)
    omega
  · -- each diagonal, measured on the grid of the last one
    have key : ∀ d ∈ List.range' D0 n,
        ((diags d).map Rat.abs).sum ≤
          (((d + 1) * K * 2 ^ ((D0 + n - 1 - d) * τ) : ℕ) : ℚ) *
            2 ^ (G0 - ((D0 + n - 1 : ℕ) : ℤ) * τ) := by
      intro d hd
      have hdle : d ≤ D0 + n - 1 := by
        have := List.mem_range'_1.mp hd; omega
      refine Rat.le_trans (hb d hd) (le_of_eq_q ?_)
      have e : G0 - (d : ℤ) * τ =
          (((D0 + n - 1 - d) * τ : ℕ) : ℤ) + (G0 - ((D0 + n - 1 : ℕ) : ℤ) * τ) := by
        obtain ⟨m, hm⟩ : ∃ m, D0 + n - 1 = m + d := ⟨D0 + n - 1 - d, by omega⟩
        rw [hm, show m + d - d = m by omega]
        push_cast
        grind
      rw [e, two_pow_add, two_pow_natCast]
      push_cast
      grind
    have hsum : (((List.range' D0 n).flatMap diags).map Rat.abs).sum =
        ((List.range' D0 n).map fun d => ((diags d).map Rat.abs).sum).sum := by
      induction (List.range' D0 n) with
      | nil => rfl
      | cons d ds ih => rw [List.flatMap_cons, sum_map_append, List.map_cons, List.sum_cons, ih]
    rw [hsum, two_pow_add]
    refine lt_of_le_of_lt' (sum_le_sum key) ?_
    rw [sum_map_mul_right]
    exact Rat.mul_lt_mul_of_pos_right hfit (two_pow_pos _)

/-- The check `Σ_{d=D₀}^{D₀+n−1} (d + 1) K 2^((D₀ + n − 1 − d)τ) < 2^p` on natural numbers. -/
def diagFits (p K τ D0 n : ℕ) : Bool :=
  decide (((List.range' D0 n).map fun d => (d + 1) * K * 2 ^ ((D0 + n - 1 - d) * τ)).sum < 2 ^ p)

theorem diagFits_spec {p K τ D0 n : ℕ} (h : diagFits p K τ D0 n = true) :
    ((List.range' D0 n).map fun d =>
        (((d + 1) * K * 2 ^ ((D0 + n - 1 - d) * τ) : ℕ) : ℚ)).sum < 2 ^ (p : ℤ) := by
  simp only [diagFits, decide_eq_true_eq] at h
  rw [two_pow_natCast]
  have : (((List.range' D0 n).map fun d => (d + 1) * K * 2 ^ ((D0 + n - 1 - d) * τ)).sum : ℚ) =
      ((List.range' D0 n).map fun d => (((d + 1) * K * 2 ^ ((D0 + n - 1 - d) * τ) : ℕ) : ℚ)).sum := by
    induction (List.range' D0 n) with
    | nil => rfl
    | cons d ds ih => rw [List.map_cons, List.sum_cons, Rat.natCast_add, ih, List.map_cons, List.sum_cons]
  rw [← this]
  exact_mod_cast h

/-- Abdelfattah et al.'s configuration (INT8 slices of `t = 7` bits, INT32 outputs of `2^31`,
binary64): three diagonals fit in a level for every level ending at diagonal `253` or below. -/
theorem fits_int8_binary64 : ∀ D1 ∈ List.range 252, diagFits 53 (2 ^ 31) 7 D1 3 = true := by
  decide +kernel

/-- ... and four diagonals do not, from the level starting at diagonal `1` on. -/
theorem not_fits_int8_binary64_four : diagFits 53 (2 ^ 31) 7 1 4 = false := by decide +kernel

/-- `11`-bit fp16 slices on a Tensor Core (`τ = 12`), products of up to `k 2^22` with
`k = 1024`, binary64: two diagonals fit in a level up to diagonal `510`. -/
theorem fits_fp16_binary64 : ∀ D1 ∈ List.range 510, diagFits 53 (2 ^ 32) 12 D1 2 = true := by
  decide +kernel

theorem not_fits_fp16_binary64_three : diagFits 53 (2 ^ 32) 12 0 3 = false := by decide +kernel

end Ozaki
