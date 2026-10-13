import OzakiTC

/-! # Every schedule is exact when the positive and negative products are each small

The usual exactness condition for a chain of integer block FMAs is `Σ|aᵢbᵢ| ≤ 2^24`. On the Tensor
Core model a chain is exact when every running value at a block boundary stays within `2^24`
(`Ozaki.TC.runBlocks_cancel`). Every running value of every order and grouping of the products is
the sum of a sub-list, which lies between `−N` and `P`, the totals of the negative and of the
positive products. So `P < 2^24` and `N < 2^24` make every schedule exact
(`runBlocks_exact_of_posneg`) and all schedules agree (`schedules_agree_of_posneg`); for
sign-balanced data this allows up to twice the usual total magnitude. -/

open TensorCore
open Ozaki
open Ozaki.TC

namespace MMAlgebra.TC


/-- The positive part of a value. -/
def posPart (x : ℚ) : ℚ := if 0 ≤ x then x else 0

/-- The magnitude of the negative part of a value. -/
def negPart (x : ℚ) : ℚ := if 0 ≤ x then 0 else -x

/-- `P`: the total of the positive products. -/
def wordPos (p : Model) (ps : List (p.Word × p.Word)) : ℚ :=
  (ps.map fun q => posPart (wordValue p q.1 * wordValue p q.2)).sum

/-- `N`: the total magnitude of the negative products. -/
def wordNeg (p : Model) (ps : List (p.Word × p.Word)) : ℚ :=
  (ps.map fun q => negPart (wordValue p q.1 * wordValue p q.2)).sum

theorem abs_lt_of_bounds {x c : ℚ} (h1 : -c < x) (h2 : x < c) : Rat.abs x < c := by
  rw [abs_def]; split <;> grind

theorem posPart_nonneg (x : ℚ) : 0 ≤ posPart x := by unfold posPart; split <;> grind
theorem negPart_nonneg (x : ℚ) : 0 ≤ negPart x := by unfold negPart; split <;> grind
theorem le_posPart (x : ℚ) : x ≤ posPart x := by unfold posPart; split <;> grind
theorem neg_negPart_le (x : ℚ) : -negPart x ≤ x := by unfold negPart; split <;> grind

/-- Every sub-list's sum lies in `[−N, P]` of the whole list. -/
theorem sublist_bounds (p : Model) {l L : List (p.Word × p.Word)} (h : l.Sublist L) :
    -wordNeg p L ≤ wordProducts p l ∧ wordProducts p l ≤ wordPos p L := by
  induction h with
  | slnil => simp [wordNeg, wordPos, wordProducts]
  | cons a _ ih =>
    obtain ⟨h1, h2⟩ := ih
    simp only [wordNeg, wordPos, List.map_cons, List.sum_cons] at h1 h2 ⊢
    have := posPart_nonneg (wordValue p a.1 * wordValue p a.2)
    have := negPart_nonneg (wordValue p a.1 * wordValue p a.2)
    constructor <;> grind
  | cons_cons a _ ih =>
    obtain ⟨h1, h2⟩ := ih
    simp only [wordNeg, wordPos, wordProducts, List.map_cons, List.sum_cons] at h1 h2 ⊢
    have := le_posPart (wordValue p a.1 * wordValue p a.2)
    have := neg_negPart_le (wordValue p a.1 * wordValue p a.2)
    constructor <;> grind

theorem wordPos_perm (p : Model) {xs ys : List (p.Word × p.Word)} (h : xs.Perm ys) :
    wordPos p xs = wordPos p ys := by unfold wordPos; exact sum_perm_q (h.map _)

theorem wordNeg_perm (p : Model) {xs ys : List (p.Word × p.Word)} (h : xs.Perm ys) :
    wordNeg p xs = wordNeg p ys := by unfold wordNeg; exact sum_perm_q (h.map _)

/-- **Schedule-free exactness.** Blocks of `b`-bit integer operands (`2b ≤ F`) chained from `0`
return the exact sum whenever the positive products total less than `2^24` and the negative
products too, in whatever order and grouping the products are presented. -/
theorem runBlocks_exact_of_posneg {p : Model} {b : ℕ} (hp : IntExact p b)
    (blocks : List (List (p.Word × p.Word)))
    (hg : ∀ g ∈ blocks, g.length = p.nfma ∧ ∀ q ∈ g, IntWord p b q.1 ∧ IntWord p b q.2)
    (hP : wordPos p blocks.flatten < 2 ^ (24 : ℤ)) (hN : wordNeg p blocks.flatten < 2 ^ (24 : ℤ)) :
    ∃ ts, runBlocks p 0 blocks = .ok ts ∧ runValue 0 ts = wordProducts p blocks.flatten := by
  have hz : value32 (0 : F32) = some ((0 : ℤ) : ℚ) := by decide +kernel
  have hpre : ∀ j < blocks.length,
      Rat.abs (((0 : ℤ) : ℚ) + wordProducts p (blocks.take j).flatten) < 2 ^ (24 : ℤ) := by
    intro j _
    have hsub : (blocks.take j).flatten.Sublist blocks.flatten := by
      have he : blocks.flatten = (blocks.take j).flatten ++ (blocks.drop j).flatten := by
        rw [← List.flatten_append, List.take_append_drop]
      rw [he]; exact List.sublist_append_left _ _
    obtain ⟨h1, h2⟩ := sublist_bounds p hsub
    rw [Rat.intCast_zero, Rat.zero_add]
    exact abs_lt_of_bounds (by grind) (by grind)
  have htot : Rat.abs (((0 : ℤ) : ℚ) + wordProducts p blocks.flatten) ≤ 2 ^ (24 : ℤ) := by
    obtain ⟨h1, h2⟩ := sublist_bounds p (List.Sublist.refl blocks.flatten)
    rw [Rat.intCast_zero, Rat.zero_add]
    exact Rat.le_of_lt (abs_lt_of_bounds (by grind) (by grind))
  obtain ⟨ts, hts, hv⟩ := runBlocks_cancel hp blocks 0 0 hz hg (chainOK_of_prefixes p blocks _ hpre htot)
  exact ⟨ts, hts, by rw [hv, Rat.intCast_zero, Rat.zero_add]⟩

/-- **Any two schedules agree.** Two orders and groupings of the same products, both satisfying the
conditions, return the same exact value. -/
theorem schedules_agree_of_posneg {p : Model} {b : ℕ} (hp : IntExact p b)
    (b₁ b₂ : List (List (p.Word × p.Word))) (hperm : b₁.flatten.Perm b₂.flatten)
    (hg₁ : ∀ g ∈ b₁, g.length = p.nfma ∧ ∀ q ∈ g, IntWord p b q.1 ∧ IntWord p b q.2)
    (hg₂ : ∀ g ∈ b₂, g.length = p.nfma ∧ ∀ q ∈ g, IntWord p b q.1 ∧ IntWord p b q.2)
    (hP : wordPos p b₁.flatten < 2 ^ (24 : ℤ)) (hN : wordNeg p b₁.flatten < 2 ^ (24 : ℤ)) :
    ∃ ts₁ ts₂, runBlocks p 0 b₁ = .ok ts₁ ∧ runBlocks p 0 b₂ = .ok ts₂ ∧
      runValue 0 ts₁ = runValue 0 ts₂ := by
  obtain ⟨ts₁, h₁, v₁⟩ := runBlocks_exact_of_posneg hp b₁ hg₁ hP hN
  obtain ⟨ts₂, h₂, v₂⟩ := runBlocks_exact_of_posneg hp b₂ hg₂
    (by rw [← wordPos_perm p hperm]; exact hP) (by rw [← wordNeg_perm p hperm]; exact hN)
  refine ⟨ts₁, ts₂, h₁, h₂, ?_⟩
  rw [v₁, v₂]; unfold wordProducts; exact sum_perm_q (hperm.map _)

end MMAlgebra.TC
