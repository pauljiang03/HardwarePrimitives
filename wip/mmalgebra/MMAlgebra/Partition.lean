/-! # Ordered partitions are determined by their pairwise patterns

A chain schedule from the zero accumulator is a list of blocks, each a list of slots holding a
product index or nothing. Its **ordered partition** (`Chain.nf`) is the list of its nonempty
blocks, each as the sorted list of its products: the normal form of a chain in the rigid algebra.
For two products `x` and `y`, the **pattern** of a chain (`pattern`) is what its nonempty blocks
hold of them, in order: `x` and `y` together, `x` before `y`, or `y` before `x`.

`nf_eq_of_patterns` is the combinatorial step of completeness for chains: two chains over the same
products, each product once, whose patterns agree on every pair of products have the same ordered
partition. An ordered partition is a total preorder ("`x` is not after `y`"), and a total preorder
is determined by how it orders each pair. The proof peels off the first nonempty blocks: a product
of the first block of one chain that is missing from the first block of the other would be ordered
after a product of that block in one chain and before it in the other. Hardware-independent. -/

local notation "ℕ" => Nat

namespace MMAlgebra

/-- A chain schedule from the zero accumulator: blocks of slots, each slot a product index or
empty. -/
abbrev Chain := List (List (Option ℕ))

/-- The products of a block. -/
def blockLeaves (B : List (Option ℕ)) : List ℕ := B.filterMap id

/-- The products of a chain, in order. -/
def Chain.leaves (σ : Chain) : List ℕ := (σ.map blockLeaves).flatten

/-- The ordered partition of a chain: its nonempty blocks in order, each as the sorted list of its
products. -/
def Chain.nf (σ : Chain) : List (List ℕ) :=
  (σ.map fun B => (blockLeaves B).mergeSort).filter fun l => !l.isEmpty

/-- What a block holds of two products `x` and `y`. -/
inductive PairKind | none | fst | snd | both
  deriving DecidableEq, Repr

def pairKind (x y : ℕ) (B : List (Option ℕ)) : PairKind :=
  if some x ∈ B then (if some y ∈ B then .both else .fst)
  else (if some y ∈ B then .snd else .none)

/-- The pattern of `x` and `y` in a chain: the kinds of its blocks that hold either. -/
def pattern (x y : ℕ) (σ : Chain) : List PairKind :=
  (σ.map (pairKind x y)).filter fun k => decide (k ≠ .none)

theorem mem_blockLeaves {i : ℕ} {B : List (Option ℕ)} : i ∈ blockLeaves B ↔ some i ∈ B := by
  simp [blockLeaves]

theorem leaves_cons (B : List (Option ℕ)) (σ : Chain) :
    Chain.leaves (B :: σ) = blockLeaves B ++ σ.leaves := by
  simp [Chain.leaves]

theorem nf_cons (B : List (Option ℕ)) (σ : Chain) :
    Chain.nf (B :: σ) = if blockLeaves B = [] then σ.nf else (blockLeaves B).mergeSort :: σ.nf := by
  unfold Chain.nf
  simp only [List.map_cons, List.filter_cons]
  by_cases h : blockLeaves B = []
  · simp [h]
  · have : ((blockLeaves B).mergeSort).isEmpty = false := by
      cases hs : (blockLeaves B).mergeSort with
      | nil =>
        have := (List.mergeSort_perm (blockLeaves B) (fun a b => decide (a ≤ b))).length_eq
        rw [hs, List.length_nil] at this; exact absurd (List.length_eq_zero_iff.mp this.symm) h
      | cons _ _ => rfl
    simp [h, this]

theorem pattern_cons (x y : ℕ) (B : List (Option ℕ)) (σ : Chain) :
    pattern x y (B :: σ) =
      if pairKind x y B = .none then pattern x y σ else pairKind x y B :: pattern x y σ := by
  unfold pattern
  simp only [List.map_cons, List.filter_cons]
  by_cases h : pairKind x y B = .none <;> simp [h]

theorem pairKind_none {x y : ℕ} {B : List (Option ℕ)} (hx : some x ∉ B) (hy : some y ∉ B) :
    pairKind x y B = .none := by
  simp [pairKind, hx, hy]

/-- Two lists of products without repetitions and with the same members sort to the same list. -/
theorem mergeSort_eq_of_mem {l₁ l₂ : List ℕ} (d₁ : l₁.Nodup) (d₂ : l₂.Nodup)
    (h : ∀ i, i ∈ l₁ ↔ i ∈ l₂) : l₁.mergeSort = l₂.mergeSort := by
  have hp : l₁.Perm l₂ := (List.perm_ext_iff_of_nodup d₁ d₂).mpr h
  have hp' : l₁.mergeSort.Perm l₂.mergeSort :=
    (List.mergeSort_perm _ _).trans (hp.trans (List.mergeSort_perm _ _).symm)
  apply List.Perm.eq_of_pairwise (le := fun a b => decide (a ≤ b)) _ _ _ hp'
  · intro a b _ _ h1 h2; simp at h1 h2; omega
  · exact List.pairwise_mergeSort (by intro a b c h1 h2; simp at *; omega)
      (by intro a b; simp; omega) _
  · exact List.pairwise_mergeSort (by intro a b c h1 h2; simp at *; omega)
      (by intro a b; simp; omega) _

/-- The conditions of the combinatorial lemma: both chains hold each product once and hold the
same products, and every pair of distinct products has the same pattern in both. -/
structure SamePatterns (σ τ : Chain) : Prop where
  nodup₁ : σ.leaves.Nodup
  nodup₂ : τ.leaves.Nodup
  leaves : ∀ i, i ∈ σ.leaves ↔ i ∈ τ.leaves
  pat : ∀ x y, x ∈ σ.leaves → y ∈ σ.leaves → x ≠ y → pattern x y σ = pattern x y τ

theorem SamePatterns.symm {σ τ : Chain} (h : SamePatterns σ τ) : SamePatterns τ σ :=
  ⟨h.nodup₂, h.nodup₁, fun i => (h.leaves i).symm,
    fun x y hx hy hxy => (h.pat x y ((h.leaves x).mpr hx) ((h.leaves y).mpr hy) hxy).symm⟩

/-- A leading block without products can be dropped. -/
theorem SamePatterns.drop_empty {B : List (Option ℕ)} {σ τ : Chain} (hB : blockLeaves B = [])
    (h : SamePatterns (B :: σ) τ) : SamePatterns σ τ := by
  have hl : Chain.leaves (B :: σ) = σ.leaves := by rw [leaves_cons, hB]; rfl
  have hk : ∀ x y, pairKind x y B = .none := by
    intro x y
    have hx : some x ∉ B := by intro hm; have := mem_blockLeaves.mpr hm; rw [hB] at this; simp at this
    have hy : some y ∉ B := by intro hm; have := mem_blockLeaves.mpr hm; rw [hB] at this; simp at this
    exact pairKind_none hx hy
  refine ⟨by rw [← hl]; exact h.nodup₁, h.nodup₂, fun i => by rw [← hl]; exact h.leaves i, ?_⟩
  intro x y hx hy hxy
  have := h.pat x y (by rw [hl]; exact hx) (by rw [hl]; exact hy) hxy
  rw [pattern_cons, if_pos (hk x y)] at this
  exact this

theorem nil_leaves_nf {σ : Chain} (h : σ.leaves = []) : σ.nf = [] := by
  induction σ with
  | nil => rfl
  | cons B σ ih =>
    rw [leaves_cons, List.append_eq_nil_iff] at h
    rw [nf_cons, if_pos h.1]; exact ih h.2

/-- The first block's products agree. -/
theorem first_block_mem {B C : List (Option ℕ)} {σ τ : Chain}
    (h : SamePatterns (B :: σ) (C :: τ)) (hC : blockLeaves C ≠ []) :
    ∀ i, i ∈ blockLeaves B → i ∈ blockLeaves C := by
  intro i hi
  apply Classical.byContradiction
  intro hni
  obtain ⟨j, hj⟩ := List.exists_mem_of_ne_nil _ hC
  have hjτ : j ∈ Chain.leaves (C :: τ) := by rw [leaves_cons]; exact List.mem_append_left _ hj
  have hjσ := (h.leaves j).mpr hjτ
  have hiσ : i ∈ Chain.leaves (B :: σ) := by rw [leaves_cons]; exact List.mem_append_left _ hi
  have hij : i ≠ j := by intro e; subst e; exact hni hj
  have hp := h.pat i j hiσ hjσ hij
  rw [pattern_cons, pattern_cons] at hp
  have hkB : pairKind i j B = .fst ∨ pairKind i j B = .both := by
    have := mem_blockLeaves.mp hi
    unfold pairKind; rw [if_pos this]; split <;> simp
  have hkC : pairKind i j C = .snd := by
    have h1 : some i ∉ C := fun hm => hni (mem_blockLeaves.mpr hm)
    have h2 := mem_blockLeaves.mp hj
    unfold pairKind; rw [if_neg h1, if_pos h2]
  rw [hkC] at hp
  rcases hkB with hk | hk <;> rw [hk] at hp <;> simp at hp

theorem nodup_tail {B : List (Option ℕ)} {σ : Chain} (h : (Chain.leaves (B :: σ)).Nodup) :
    σ.leaves.Nodup ∧ (blockLeaves B).Nodup ∧ ∀ i, i ∈ blockLeaves B → i ∉ σ.leaves := by
  rw [leaves_cons, List.nodup_append] at h
  exact ⟨h.2.1, h.1, fun i hi hs => h.2.2 i hi i hs rfl⟩

/-- After equal first blocks, the rest of the chains satisfy the conditions again. -/
theorem SamePatterns.tail {B C : List (Option ℕ)} {σ τ : Chain}
    (h : SamePatterns (B :: σ) (C :: τ)) (hBC : ∀ i, i ∈ blockLeaves B ↔ i ∈ blockLeaves C) :
    SamePatterns σ τ := by
  obtain ⟨n₁, d₁, o₁⟩ := nodup_tail h.nodup₁
  obtain ⟨n₂, d₂, o₂⟩ := nodup_tail h.nodup₂
  have memσ : ∀ i, i ∈ σ.leaves ↔ i ∈ Chain.leaves (B :: σ) ∧ i ∉ blockLeaves B := by
    intro i; rw [leaves_cons, List.mem_append]
    constructor
    · intro hi; exact ⟨Or.inr hi, fun hb => o₁ i hb hi⟩
    · rintro ⟨hi | hi, hn⟩
      · exact absurd hi hn
      · exact hi
  have memτ : ∀ i, i ∈ τ.leaves ↔ i ∈ Chain.leaves (C :: τ) ∧ i ∉ blockLeaves C := by
    intro i; rw [leaves_cons, List.mem_append]
    constructor
    · intro hi; exact ⟨Or.inr hi, fun hb => o₂ i hb hi⟩
    · rintro ⟨hi | hi, hn⟩
      · exact absurd hi hn
      · exact hi
  refine ⟨n₁, n₂, ?_, ?_⟩
  · intro i
    rw [memσ, memτ, h.leaves i, hBC i]
  · intro x y hx hy hxy
    have hx' := (memσ x).mp hx
    have hy' := (memσ y).mp hy
    have hp := h.pat x y hx'.1 hy'.1 hxy
    have hxB : some x ∉ B := fun hm => hx'.2 (mem_blockLeaves.mpr hm)
    have hyB : some y ∉ B := fun hm => hy'.2 (mem_blockLeaves.mpr hm)
    have hxC : some x ∉ C := fun hm => hx'.2 ((hBC x).mpr (mem_blockLeaves.mpr hm))
    have hyC : some y ∉ C := fun hm => hy'.2 ((hBC y).mpr (mem_blockLeaves.mpr hm))
    rw [pattern_cons, pattern_cons, if_pos (pairKind_none hxB hyB),
      if_pos (pairKind_none hxC hyC)] at hp
    exact hp

/-- **Ordered partitions are determined by pairwise patterns.** Two chains that hold each product
once, hold the same products, and agree on the pattern of every pair of distinct products have the
same ordered partition. -/
theorem nf_eq_of_patterns : ∀ (n : ℕ) (σ τ : Chain), σ.length + τ.length ≤ n →
    SamePatterns σ τ → σ.nf = τ.nf
  | 0, σ, τ, hn, h => by
    have h1 : σ = [] := List.length_eq_zero_iff.mp (by omega)
    have h2 : τ = [] := List.length_eq_zero_iff.mp (by omega)
    subst h1; subst h2; rfl
  | n + 1, [], τ, _, h => by
    have : τ.leaves = [] := by
      apply List.eq_nil_iff_forall_not_mem.mpr
      intro i hi
      have := (h.leaves i).mpr hi
      simp [Chain.leaves] at this
    rw [nil_leaves_nf this]; rfl
  | n + 1, B :: σ, [], _, h => by
    have : Chain.leaves (B :: σ) = [] := by
      apply List.eq_nil_iff_forall_not_mem.mpr
      intro i hi
      have := (h.leaves i).mp hi
      simp [Chain.leaves] at this
    rw [nil_leaves_nf this]; rfl
  | n + 1, B :: σ, C :: τ, hn, h => by
    by_cases hB : blockLeaves B = []
    · rw [nf_cons, if_pos hB]
      exact nf_eq_of_patterns n σ (C :: τ) (by simp at hn ⊢; omega) (h.drop_empty hB)
    · by_cases hC : blockLeaves C = []
      · rw [nf_cons C, if_pos hC]
        exact (nf_eq_of_patterns n τ (B :: σ) (by simp at hn ⊢; omega)
          (h.symm.drop_empty hC)).symm
      · have h1 := first_block_mem h hC
        have h2 := first_block_mem h.symm hB
        have hBC : ∀ i, i ∈ blockLeaves B ↔ i ∈ blockLeaves C := fun i => ⟨h1 i, h2 i⟩
        rw [nf_cons, nf_cons C, if_neg hB, if_neg hC,
          mergeSort_eq_of_mem (nodup_tail h.nodup₁).2.1 (nodup_tail h.nodup₂).2.1 hBC,
          nf_eq_of_patterns n σ τ (by simp at hn ⊢; omega) (h.tail hBC)]

/-- **Distinct ordered partitions differ on a pair.** Two chains that hold each product once and
hold the same products, with different ordered partitions, have different patterns on some pair of
distinct products. -/
theorem exists_pattern_ne {σ τ : Chain} (n₁ : σ.leaves.Nodup) (n₂ : τ.leaves.Nodup)
    (hl : ∀ i, i ∈ σ.leaves ↔ i ∈ τ.leaves) (hne : σ.nf ≠ τ.nf) :
    ∃ x y, x ∈ σ.leaves ∧ y ∈ σ.leaves ∧ x ≠ y ∧ pattern x y σ ≠ pattern x y τ := by
  apply Classical.byContradiction
  intro hno
  apply hne
  refine nf_eq_of_patterns _ σ τ (Nat.le_refl _) ⟨n₁, n₂, hl, ?_⟩
  intro x y hx hy hxy
  apply Classical.byContradiction
  intro hp
  exact hno ⟨x, y, hx, hy, hxy, hp⟩

end MMAlgebra
