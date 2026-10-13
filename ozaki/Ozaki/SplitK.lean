import Ozaki.Ozaki1

/-! # Long dot products: split-K

An engine is exact only while the products of one call total at most its budget (`2^24` for a
binary32 output), which limits a dot product of `b`-bit slices to `k · 2^(2b) ≤ 2^24` terms: four
with `11`-bit slices. Real GEMMs have `k` in the thousands. Split-K removes the limit: cut both
vectors into chunks of `m` terms with `m · 2^(2b)` within the budget, run the engine on every chunk,
and add the chunk results, which are integers, exactly.

* `chunksOf m l`: `l` cut into chunks of `m` (the last may be shorter);
* `chunked m eng`: the split-K engine;
* `chunked_exactOn`: if `mult` is exact on `b`-bit vectors within its budget and `m · 2^(2b)` fits
  the budget, the split-K engine is exact on `b`-bit vectors of every length, whatever their total.

With it every theorem of the schemes holds for dot products of any length: take the budget
`k · 2^(2b)`. -/

local notation "ℕ" => Nat
local notation "ℤ" => Int
local notation "ℚ" => Rat

namespace Ozaki

/-- Chunks of `m`, with fuel `n`. -/
def chunksAux (m : ℕ) : ℕ → List α → List (List α)
  | 0, _ => []
  | _ + 1, [] => []
  | n + 1, a :: l => (a :: l).take m :: chunksAux m n ((a :: l).drop m)

/-- `l` cut into chunks of `m` terms; the last chunk may be shorter. -/
def chunksOf (m : ℕ) (l : List α) : List (List α) := chunksAux m l.length l

theorem dotZ_append {a c : List ℤ} (b d : List ℤ) (h : a.length = c.length) :
    dotZ (a ++ b) (c ++ d) = dotZ a c + dotZ b d := by
  induction a generalizing c with
  | nil =>
    cases c with
    | nil => simp [dotZ]
    | cons _ _ => simp at h
  | cons x a ih =>
    cases c with
    | nil => simp at h
    | cons z c =>
      simp only [List.cons_append, dotZ_cons, List.length_cons] at h ⊢
      rw [ih (by omega)]; omega

/-- The chunks of two equally long vectors pair up: equal lengths, at most `m` terms, entries
from the vectors, and the chunk products add up to the whole product. -/
theorem chunksAux_pairs {m : ℕ} (hm : 0 < m) :
    ∀ (n : ℕ) (x y : List ℤ), x.length = y.length → x.length ≤ n →
      (∀ p ∈ (chunksAux m n x).zip (chunksAux m n y),
        p.1.length = p.2.length ∧ p.1.length ≤ m ∧ (∀ a ∈ p.1, a ∈ x) ∧ (∀ a ∈ p.2, a ∈ y)) ∧
      (((chunksAux m n x).zip (chunksAux m n y)).map fun p => dotZ p.1 p.2).sum = dotZ x y
  | 0, x, y, hlen, hn => by
    have hx : x = [] := List.eq_nil_of_length_eq_zero (by omega)
    have hy : y = [] := List.eq_nil_of_length_eq_zero (by omega)
    subst hx hy; simp [chunksAux, dotZ]
  | n + 1, [], y, hlen, _ => by
    have hy : y = [] := List.eq_nil_of_length_eq_zero (by simp at hlen; omega)
    subst hy; simp [chunksAux, dotZ]
  | n + 1, a :: x, [], hlen, _ => by simp at hlen
  | n + 1, a :: x, c :: y, hlen, hn => by
    have hl : (a :: x).length = (c :: y).length := hlen
    have hdl : ((a :: x).drop m).length = ((c :: y).drop m).length := by simp [hl]
    have hdn : ((a :: x).drop m).length ≤ n := by simp at hn ⊢; omega
    obtain ⟨hpairs, hsum⟩ := chunksAux_pairs hm n _ _ hdl hdn
    have htl : ((a :: x).take m).length = ((c :: y).take m).length := by simp [hl]
    refine ⟨?_, ?_⟩
    · intro p hp
      simp only [chunksAux, List.zip_cons_cons, List.mem_cons] at hp
      rcases hp with rfl | hp
      · refine ⟨htl, by simp; omega, fun z hz => List.mem_of_mem_take hz,
          fun z hz => List.mem_of_mem_take hz⟩
      · obtain ⟨h1, h2, h3, h4⟩ := hpairs p hp
        exact ⟨h1, h2, fun z hz => List.mem_of_mem_drop (h3 z hz),
          fun z hz => List.mem_of_mem_drop (h4 z hz)⟩
    · simp only [chunksAux, List.zip_cons_cons, List.map_cons, List.sum_cons]
      rw [hsum, ← dotZ_append _ _ htl, List.take_append_drop, List.take_append_drop]

theorem dotAbs_append {a c : List ℤ} (b d : List ℤ) (h : a.length = c.length) :
    dotAbs (a ++ b) (c ++ d) = dotAbs a c + dotAbs b d := by
  induction a generalizing c with
  | nil =>
    cases c with
    | nil => simp [dotAbs]
    | cons _ _ => simp at h
  | cons x a ih =>
    cases c with
    | nil => simp at h
    | cons z c =>
      simp only [List.cons_append, dotAbs_cons, List.length_cons] at h ⊢
      rw [ih (by omega)]; omega

/-- The magnitudes of the chunk products add up to those of the whole product. -/
theorem chunksAux_dotAbs {m : ℕ} (hm : 0 < m) :
    ∀ (n : ℕ) (x y : List ℤ), x.length = y.length → x.length ≤ n →
      (((chunksAux m n x).zip (chunksAux m n y)).map fun p => dotAbs p.1 p.2).sum = dotAbs x y
  | 0, x, y, hlen, hn => by
    have hx : x = [] := List.eq_nil_of_length_eq_zero (by omega)
    have hy : y = [] := List.eq_nil_of_length_eq_zero (by omega)
    subst hx hy; simp [chunksAux, dotAbs]
  | n + 1, [], y, hlen, _ => by
    have hy : y = [] := List.eq_nil_of_length_eq_zero (by simp at hlen; omega)
    subst hy; simp [chunksAux, dotAbs]
  | n + 1, a :: x, [], hlen, _ => by simp at hlen
  | n + 1, a :: x, c :: y, hlen, hn => by
    have hl : (a :: x).length = (c :: y).length := hlen
    have hdl : ((a :: x).drop m).length = ((c :: y).drop m).length := by simp [hl]
    have hdn : ((a :: x).drop m).length ≤ n := by simp at hn ⊢; omega
    have htl : ((a :: x).take m).length = ((c :: y).take m).length := by simp [hl]
    simp only [chunksAux, List.zip_cons_cons, List.map_cons, List.sum_cons]
    rw [chunksAux_dotAbs hm n _ _ hdl hdn, ← dotAbs_append _ _ htl, List.take_append_drop,
      List.take_append_drop]

/-- **Split-K.** Cut both vectors into chunks of `m`, run the engine on every chunk pair, and add
the chunk results exactly. -/
def chunked (m : ℕ) (mult : MatrixMultiplier) : MatrixMultiplier := fun x y =>
  (((chunksOf m x).zip (chunksOf m y)).mapM fun p => mult p.1 p.2).map List.sum

theorem intCast_sum_map (l : List α) (f : α → ℤ) :
    (((l.map f).sum : ℤ) : ℚ) = (l.map fun a => (f a : ℚ)).sum := by
  induction l with
  | nil => simp
  | cons a l ih => simp only [List.map_cons, List.sum_cons, Rat.intCast_add, ih]

/-- **Split-K is exact for every length.** If `mult` is exact on `b`-bit vectors whose products
total at most `bound`, and `m · 2^(2b) ≤ budget`, the split-K engine with chunks of `m` is exact
on `b`-bit vectors of any length, with no budget at all. -/
theorem chunked_exactOn {mult : MatrixMultiplier} {b bound m : ℕ} (hmult : mult.ExactOn b bound)
    (hm : 0 < m) (hmb : m * (2 ^ b * 2 ^ b) ≤ bound) (B : ℕ) : (chunked m mult).ExactOn b B := by
  intro x y hlen hx hy _
  unfold chunked chunksOf
  rw [hlen]
  have hlen' : x.length = y.length := hlen
  obtain ⟨hpairs, hsum⟩ := chunksAux_pairs hm y.length x y hlen (by omega)
  rw [mapM_eq_some_map (g := fun p : List ℤ × List ℤ => ((dotZ p.1 p.2 : ℤ) : ℚ))]
  · rw [Option.map_some, ← intCast_sum_map, hsum]
    rfl
  · intro p hp
    obtain ⟨h1, h2, h3, h4⟩ := hpairs p hp
    apply hmult _ _ h1 (fun a ha => hx a (h3 a ha)) (fun a ha => hy a (h4 a ha))
    refine Nat.le_trans (dotAbs_le _ _ _ _ (fun a ha => hx a (h3 a ha))
      (fun a ha => hy a (h4 a ha))) ?_
    exact Nat.le_trans (Nat.mul_le_mul_right _ h2) hmb

/-- The budget the scheme theorems ask for is met by any split-K engine: take `k · 2^(2b)`. -/
theorem chunked_exactOn_self {mult : MatrixMultiplier} {b bound m : ℕ} (hmult : mult.ExactOn b bound)
    (hm : 0 < m) (hmb : m * (2 ^ b * 2 ^ b) ≤ bound) (x : List ℚ) :
    (chunked m mult).ExactOn b (x.length * (2 ^ b * 2 ^ b)) :=
  chunked_exactOn hmult hm hmb _

/-- Chunk length for `b`-bit slices on an engine with budget `2^24`: `2^(24 − 2b)` products total at
most `2^24` (four for `11`-bit slices, `256` for `8`-bit). -/
def chunkLen (b : ℕ) : ℕ := 2 ^ (24 - 2 * b)

theorem chunkLen_pos (b : ℕ) : 0 < chunkLen b := Nat.two_pow_pos _

theorem chunkLen_exactnessBound {b : ℕ} (hb : 2 * b ≤ 24) : chunkLen b * (2 ^ b * 2 ^ b) ≤ 2 ^ 24 := by
  unfold chunkLen
  rw [← Nat.pow_add, ← Nat.pow_add]
  apply Nat.le_of_eq; congr 1; omega

end Ozaki
