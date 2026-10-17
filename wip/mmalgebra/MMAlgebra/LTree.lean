/-! # Labeled trees are determined by their restrictions to three leaves

The normal forms of the reduction algebras are rooted trees whose leaves are product indices, each
once, and whose internal nodes have at least two children, in no order: on CDNA 1 a node is one
correctly rounded sum of its children, on CDNA 2 a binary32 addition, and on the rigid models a
block FMA or an addition, with the accumulator child of a block marked. `LTree N E` is such a tree
with a label in `N` on every internal node and a label in `E` on every edge to a child.

**Restriction** to a set `S` of leaves (`LTree.restrict`) removes the other leaves, removes the
nodes left without leaves, and replaces a node left with one child by that child (its edge label
to the parent is the parent's edge to the replaced node). A tree is **canonical** (`Canon`) when
every node has at least two children, listed by increasing smallest leaf.

`eq_of_restrict3` is the combinatorial step of completeness for trees and terms: two canonical trees
on the same leaves, each leaf once, that agree after restriction to every set of at most three of
their leaves are equal. For unlabeled trees this is the classical fact that a rooted tree is
determined by its rooted triplets. The proof compares the roots: if the roots split the leaves
differently, some leaves `x`, `y` lie in one child of one root and in different children of the
other, and with a leaf `z` outside that child the restrictions to `{x, y, z}` differ; if the roots
agree on the split but not on a label, the restrictions to two leaves in different children differ;
otherwise two children with the same leaves differ, and induction applies to them.
Hardware-independent. -/

local notation "ℕ" => Nat

namespace MMAlgebra

/-- A rooted tree with product indices at the leaves, a label in `N` on every internal node, and a
label in `E` on every edge to a child. -/
inductive LTree (N E : Type) where
  | leaf (i : ℕ)
  | node (l : N) (cs : List (E × LTree N E))

namespace LTree

variable {N E : Type}

mutual
/-- The leaves of a tree, in order. -/
def leaves : LTree N E → List ℕ
  | .leaf i => [i]
  | .node _ cs => kidsLeaves cs
/-- The leaves of a list of children. -/
def kidsLeaves : List (E × LTree N E) → List ℕ
  | [] => []
  | (_, t) :: cs => leaves t ++ kidsLeaves cs
end

theorem kidsLeaves_eq (cs : List (E × LTree N E)) : kidsLeaves cs = (cs.map fun c => c.2.leaves).flatten := by
  induction cs with
  | nil => rfl
  | cons c cs ih => obtain ⟨e, t⟩ := c; simp [kidsLeaves, ih]

theorem leaves_node (l : N) (cs : List (E × LTree N E)) :
    (node l cs).leaves = (cs.map fun c => c.2.leaves).flatten := by
  simp only [leaves]; exact kidsLeaves_eq cs

theorem mem_leaves_node {x : ℕ} {l : N} {cs : List (E × LTree N E)} :
    x ∈ (node l cs).leaves ↔ ∃ c ∈ cs, x ∈ c.2.leaves := by
  rw [leaves_node, List.mem_flatten]
  constructor
  · rintro ⟨l', hl', hx⟩
    obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hl'
    exact ⟨c, hc, hx⟩
  · rintro ⟨c, hc, hx⟩
    exact ⟨_, List.mem_map.mpr ⟨c, hc, rfl⟩, hx⟩

/-- The smallest element of a list (`0` for the empty list). -/
def lmin : List ℕ → ℕ
  | [] => 0
  | x :: xs => xs.foldl min x

theorem foldl_min_le (xs : List ℕ) (a : ℕ) : xs.foldl min a ≤ a ∧ ∀ y ∈ xs, xs.foldl min a ≤ y := by
  induction xs generalizing a with
  | nil => simp
  | cons x xs ih =>
    simp only [List.foldl_cons, List.mem_cons]
    obtain ⟨h1, h2⟩ := ih (min a x)
    refine ⟨by omega, ?_⟩
    rintro y (rfl | hy)
    · omega
    · exact h2 y hy

theorem foldl_min_mem (xs : List ℕ) (a : ℕ) : xs.foldl min a = a ∨ xs.foldl min a ∈ xs := by
  induction xs generalizing a with
  | nil => simp
  | cons x xs ih =>
    simp only [List.foldl_cons, List.mem_cons]
    rcases ih (min a x) with h | h
    · rw [h]; by_cases hax : a ≤ x
      · left; omega
      · right; left; omega
    · right; right; exact h

theorem lmin_le {l : List ℕ} {y : ℕ} (hy : y ∈ l) : lmin l ≤ y := by
  cases l with
  | nil => simp at hy
  | cons x xs =>
    simp only [lmin]
    rcases List.mem_cons.mp hy with rfl | hy
    · exact (foldl_min_le xs y).1
    · exact (foldl_min_le xs x).2 y hy

theorem lmin_mem {l : List ℕ} (h : l ≠ []) : lmin l ∈ l := by
  cases l with
  | nil => exact absurd rfl h
  | cons x xs =>
    simp only [lmin]
    rcases foldl_min_mem xs x with h | h
    · rw [h]; simp
    · exact List.mem_cons_of_mem _ h

/-- The smallest leaf of a tree. -/
def key (t : LTree N E) : ℕ := lmin t.leaves

/-- Children listed by increasing smallest leaf. -/
def sortKids (cs : List (E × LTree N E)) : List (E × LTree N E) :=
  cs.mergeSort fun a b => decide (key a.2 ≤ key b.2)

/-- A node from a list of children: none for no child, the child itself for one, and a node with
the children sorted otherwise. -/
def mk (l : N) (cs : List (E × LTree N E)) : Option (LTree N E) :=
  match cs with
  | [] => none
  | [(_, t)] => some t
  | _ :: _ :: _ => some (node l (sortKids cs))

mutual
/-- Restriction to the leaves in `S`: `none` when no leaf is in `S`. -/
def restrict (S : ℕ → Bool) : LTree N E → Option (LTree N E)
  | .leaf i => if S i then some (.leaf i) else none
  | .node l cs => mk l (restrictKids S cs)
/-- The restrictions of the children that keep a leaf, with their edge labels. -/
def restrictKids (S : ℕ → Bool) : List (E × LTree N E) → List (E × LTree N E)
  | [] => []
  | (e, t) :: cs => match restrict S t with
    | none => restrictKids S cs
    | some t' => (e, t') :: restrictKids S cs
end

mutual
/-- Every node has at least two children, listed by strictly increasing smallest leaf. -/
def Canon : LTree N E → Prop
  | .leaf _ => True
  | .node _ cs => 2 ≤ cs.length ∧ (cs.map fun c => key c.2).Pairwise (· < ·) ∧ KidsCanon cs
/-- Every child is canonical. -/
def KidsCanon : List (E × LTree N E) → Prop
  | [] => True
  | (_, t) :: cs => Canon t ∧ KidsCanon cs
end

theorem kidsCanon_iff (cs : List (E × LTree N E)) : KidsCanon cs ↔ ∀ c ∈ cs, Canon c.2 := by
  induction cs with
  | nil => simp [KidsCanon]
  | cons c cs ih => obtain ⟨e, t⟩ := c; simp [KidsCanon, ih]

/-- The restriction to a set given as a list. -/
def restrictTo (s : List ℕ) (t : LTree N E) : Option (LTree N E) := t.restrict fun i => decide (i ∈ s)

/-! ## Leaves of restrictions -/

/-- The leaves of an optional tree. -/
def oleaves : Option (LTree N E) → List ℕ
  | none => []
  | some t => t.leaves

theorem sortKids_perm (cs : List (E × LTree N E)) : (sortKids cs).Perm cs :=
  List.mergeSort_perm _ _

theorem kidsLeaves_perm {cs ds : List (E × LTree N E)} (h : cs.Perm ds) :
    (kidsLeaves cs).Perm (kidsLeaves ds) := by
  rw [kidsLeaves_eq, kidsLeaves_eq]
  exact (h.map _).flatten

theorem oleaves_mk (l : N) (cs : List (E × LTree N E)) :
    (oleaves (mk l cs)).Perm (kidsLeaves cs) := by
  match cs with
  | [] => simp [mk, oleaves, kidsLeaves]
  | [(e, t)] => simp [mk, oleaves, kidsLeaves]
  | c₁ :: c₂ :: cs =>
    simp only [mk, oleaves, leaves]
    exact kidsLeaves_perm (sortKids_perm _)

mutual
/-- The leaves of a restriction are the leaves in `S`, up to order. -/
theorem oleaves_restrict (S : ℕ → Bool) : ∀ t : LTree N E,
    (oleaves (t.restrict S)).Perm (t.leaves.filter S)
  | .leaf i => by
    by_cases h : S i = true <;> simp [restrict, oleaves, leaves, h]
  | .node l cs => by
    simp only [restrict, leaves]
    exact (oleaves_mk l _).trans (kidsLeaves_restrictKids S cs)
theorem kidsLeaves_restrictKids (S : ℕ → Bool) : ∀ cs : List (E × LTree N E),
    (kidsLeaves (restrictKids S cs)).Perm ((kidsLeaves cs).filter S)
  | [] => by simp [restrictKids, kidsLeaves]
  | (e, t) :: cs => by
    have ih := kidsLeaves_restrictKids S cs
    have ht := oleaves_restrict S t
    simp only [restrictKids, kidsLeaves, List.filter_append]
    cases hr : restrict S t with
    | none =>
      rw [hr] at ht
      simp only [oleaves] at ht
      rw [List.nil_perm.mp ht, List.nil_append]
      exact ih
    | some t' =>
      rw [hr] at ht
      simp only [kidsLeaves, oleaves] at ht ⊢
      exact ht.append ih
end

theorem mem_oleaves_restrict {S : ℕ → Bool} {t : LTree N E} {x : ℕ} :
    x ∈ oleaves (t.restrict S) ↔ x ∈ t.leaves ∧ S x = true := by
  rw [(oleaves_restrict S t).mem_iff, List.mem_filter]

mutual
/-- A restriction keeps at least one leaf. -/
theorem restrict_ne_nil (S : ℕ → Bool) : ∀ (t t' : LTree N E), t.restrict S = some t' →
    t'.leaves ≠ []
  | .leaf i, t', h => by
    simp only [restrict] at h
    split at h
    · cases h; simp [leaves]
    · cases h
  | .node l cs, t', h => by
    simp only [restrict] at h
    unfold mk at h
    split at h
    · cases h
    · rename_i e t'' heq
      cases h
      exact restrictKids_ne_nil S cs e t' (by rw [heq]; simp)
    · rename_i c₁ c₂ cs' heq
      cases h
      obtain ⟨e₁, t₁⟩ := c₁
      have h1 := restrictKids_ne_nil S cs e₁ t₁ (by rw [heq]; simp)
      intro he
      have hp := kidsLeaves_perm (sortKids_perm ((e₁, t₁) :: c₂ :: cs'))
      simp only [leaves] at he
      rw [heq] at he
      rw [he] at hp
      have := List.nil_perm.mp hp
      simp only [kidsLeaves, List.append_eq_nil_iff] at this
      exact h1 this.1
theorem restrictKids_ne_nil (S : ℕ → Bool) : ∀ (cs : List (E × LTree N E)) (e : E) (t' : LTree N E),
    (e, t') ∈ restrictKids S cs → t'.leaves ≠ []
  | [], e, t', h => by simp [restrictKids] at h
  | (e₀, t) :: cs, e, t', h => by
    simp only [restrictKids] at h
    cases hr : restrict S t with
    | none => rw [hr] at h; exact restrictKids_ne_nil S cs e t' h
    | some t'' =>
      rw [hr] at h
      rcases List.mem_cons.mp h with h | h
      · cases h; exact restrict_ne_nil S t t' hr
      · exact restrictKids_ne_nil S cs e t' h
end

theorem restrict_eq_none {S : ℕ → Bool} {t : LTree N E} (h : ∀ x ∈ t.leaves, S x = false) :
    t.restrict S = none := by
  cases hr : t.restrict S with
  | none => rfl
  | some t' =>
    exfalso
    have hl := oleaves_restrict S t
    rw [hr] at hl
    simp only [oleaves] at hl
    have : t.leaves.filter S = [] := by
      apply List.filter_eq_nil_iff.mpr
      intro x hx; simp [h x hx]
    rw [this] at hl
    exact restrict_ne_nil S t t' hr (List.perm_nil.mp hl)

/-! ## Sizes and canonical trees -/

mutual
/-- The number of nodes and leaves. -/
def size : LTree N E → ℕ
  | .leaf _ => 1
  | .node _ cs => 1 + kidsSize cs
def kidsSize : List (E × LTree N E) → ℕ
  | [] => 0
  | (_, t) :: cs => size t + kidsSize cs
end

theorem size_le_kidsSize {c : E × LTree N E} : ∀ {cs : List (E × LTree N E)}, c ∈ cs →
    c.2.size ≤ kidsSize cs
  | [], h => by simp at h
  | (e, t) :: cs, h => by
    simp only [kidsSize]
    rcases List.mem_cons.mp h with rfl | h
    · show t.size ≤ t.size + kidsSize cs; omega
    · have := size_le_kidsSize h; omega

theorem size_lt_of_mem {l : N} {cs : List (E × LTree N E)} {c : E × LTree N E} (h : c ∈ cs) :
    c.2.size < (node l cs).size := by
  have := size_le_kidsSize h
  simp only [size]; omega

theorem canon_node {l : N} {cs : List (E × LTree N E)} (h : Canon (node l cs)) :
    2 ≤ cs.length ∧ (cs.map fun c => key c.2).Pairwise (· < ·) ∧ ∀ c ∈ cs, Canon c.2 := by
  simp only [Canon] at h
  exact ⟨h.1, h.2.1, (kidsCanon_iff cs).mp h.2.2⟩

theorem canon_leaves_ne_nil : ∀ (n : ℕ) (t : LTree N E), t.size ≤ n → Canon t → t.leaves ≠ []
  | _, .leaf i, _, _ => by simp [leaves]
  | 0, .node l cs, hs, _ => by simp [size] at hs
  | n + 1, .node l cs, hs, h => by
    obtain ⟨hlen, _, hk⟩ := canon_node h
    obtain ⟨c, cs', rfl⟩ : ∃ c cs', cs = c :: cs' := by
      cases cs with
      | nil => simp at hlen
      | cons c cs' => exact ⟨c, cs', rfl⟩
    have hc := canon_leaves_ne_nil n c.2
      (by have := size_lt_of_mem (l := l) (List.mem_cons_self (a := c) (l := cs')); omega)
      (hk c (by simp))
    intro he
    rw [leaves_node] at he
    simp only [List.map_cons, List.flatten_cons, List.append_eq_nil_iff] at he
    exact hc he.1

/-- A canonical node has two distinct leaves in different children. -/
theorem canon_two_kids {l : N} {cs : List (E × LTree N E)} (h : Canon (node l cs)) :
    ∃ c₁ ∈ cs, ∃ c₂ ∈ cs, c₁ ≠ c₂ ∧ c₁.2.leaves ≠ [] ∧ c₂.2.leaves ≠ [] := by
  obtain ⟨hlen, hsort, hk⟩ := canon_node h
  match cs, hlen, hsort, hk with
  | c₁ :: c₂ :: cs', _, hsort, hk =>
    refine ⟨c₁, by simp, c₂, by simp, ?_, canon_leaves_ne_nil _ _ (Nat.le_refl _) (hk c₁ (by simp)),
      canon_leaves_ne_nil _ _ (Nat.le_refl _) (hk c₂ (by simp))⟩
    intro he
    subst he
    simp only [List.map_cons, List.pairwise_cons, List.mem_cons, List.mem_map] at hsort
    have := hsort.1 (key c₁.2) (Or.inl rfl)
    omega

/-! ## Restriction lemmas -/

theorem mem_restrictKids {S : ℕ → Bool} {e : E} {t' : LTree N E} :
    ∀ {cs : List (E × LTree N E)},
      (e, t') ∈ restrictKids S cs ↔ ∃ t, (e, t) ∈ cs ∧ t.restrict S = some t'
  | [] => by simp [restrictKids]
  | (e₀, t₀) :: cs => by
    simp only [restrictKids]
    cases hr : restrict S t₀ with
    | none =>
      rw [mem_restrictKids]
      constructor
      · rintro ⟨t, ht, h⟩; exact ⟨t, List.mem_cons_of_mem _ ht, h⟩
      · rintro ⟨t, ht, h⟩
        rcases List.mem_cons.mp ht with he | ht
        · cases he; rw [hr] at h; cases h
        · exact ⟨t, ht, h⟩
    | some t₁ =>
      constructor
      · intro hm
        rcases List.mem_cons.mp hm with he | hm
        · cases he
          exact ⟨t₀, by simp, hr⟩
        · obtain ⟨t, ht, h⟩ := mem_restrictKids.mp hm
          exact ⟨t, List.mem_cons_of_mem _ ht, h⟩
      · rintro ⟨t, ht, h⟩
        rcases List.mem_cons.mp ht with he | ht
        · cases he; rw [hr] at h; cases h; exact List.mem_cons_self
        · exact List.mem_cons_of_mem _ (mem_restrictKids.mpr ⟨t, ht, h⟩)

theorem restrictKids_nil {S : ℕ → Bool} :
    ∀ {cs : List (E × LTree N E)}, (∀ c ∈ cs, ∀ x ∈ c.2.leaves, S x = false) → restrictKids S cs = []
  | [], _ => rfl
  | (e, t) :: cs, h => by
    simp only [restrictKids]
    rw [restrict_eq_none (h (e, t) (by simp))]
    exact restrictKids_nil (fun c hc => h c (by simp [hc]))

theorem restrictKids_append (S : ℕ → Bool) :
    ∀ (cs ds : List (E × LTree N E)), restrictKids S (cs ++ ds) = restrictKids S cs ++ restrictKids S ds
  | [], ds => rfl
  | (e, t) :: cs, ds => by
    simp only [List.cons_append, restrictKids]
    cases restrict S t <;> simp [restrictKids_append S cs ds]

theorem kidsLeaves_append (cs ds : List (E × LTree N E)) :
    kidsLeaves (cs ++ ds) = kidsLeaves cs ++ kidsLeaves ds := by
  rw [kidsLeaves_eq, kidsLeaves_eq, kidsLeaves_eq]; simp

/-- When every leaf in `S` lies in one child, the restriction of the node is that of the child. -/
theorem restrict_node_sub {S : ℕ → Bool} {l : N} {cs : List (E × LTree N E)}
    (hn : (node l cs).leaves.Nodup) {c : E × LTree N E} (hc : c ∈ cs)
    (hS : ∀ x ∈ (node l cs).leaves, S x = true → x ∈ c.2.leaves) :
    (node l cs).restrict S = c.2.restrict S := by
  obtain ⟨pre, post, rfl⟩ := List.append_of_mem hc
  simp only [leaves, kidsLeaves_append, kidsLeaves] at hn hS
  have hn1 := List.nodup_append.mp hn
  have hn2 := List.nodup_append.mp hn1.2.1
  have hpre : ∀ c' ∈ pre, ∀ x ∈ c'.2.leaves, S x = false := by
    intro c' hc' x hx
    apply Classical.byContradiction
    intro hSx
    have hSx' : S x = true := by simpa using hSx
    have hxl : x ∈ kidsLeaves pre := by
      rw [kidsLeaves_eq]; exact List.mem_flatten.mpr ⟨_, List.mem_map.mpr ⟨c', hc', rfl⟩, hx⟩
    have := hS x (List.mem_append_left _ hxl) hSx'
    exact hn1.2.2 x hxl x (List.mem_append_left _ this) rfl
  have hpost : ∀ c' ∈ post, ∀ x ∈ c'.2.leaves, S x = false := by
    intro c' hc' x hx
    apply Classical.byContradiction
    intro hSx
    have hSx' : S x = true := by simpa using hSx
    have hxl : x ∈ kidsLeaves post := by
      rw [kidsLeaves_eq]; exact List.mem_flatten.mpr ⟨_, List.mem_map.mpr ⟨c', hc', rfl⟩, hx⟩
    have := hS x (List.mem_append_right _ (List.mem_append_right _ hxl)) hSx'
    exact hn2.2.2 x this x hxl rfl
  simp only [restrict, restrictKids_append, restrictKids_nil hpre, List.nil_append]
  obtain ⟨e, t⟩ := c
  simp only [restrictKids, restrictKids_nil hpost]
  cases restrict S t <;> rfl

theorem restrict_congr {S S' : ℕ → Bool} : ∀ (n : ℕ) (t : LTree N E), t.size ≤ n →
    (∀ x ∈ t.leaves, S x = S' x) → t.restrict S = t.restrict S'
  | _, .leaf i, _, h => by simp only [restrict, h i (by simp [leaves])]
  | 0, .node l cs, hs, _ => by simp [size] at hs
  | n + 1, .node l cs, hs, h => by
    simp only [restrict]
    congr 1
    have : ∀ ds : List (E × LTree N E), (∀ d ∈ ds, d ∈ cs) → restrictKids S ds = restrictKids S' ds := by
      intro ds hds
      induction ds with
      | nil => rfl
      | cons d ds ih =>
        obtain ⟨e, t⟩ := d
        have hd := hds (e, t) (by simp)
        have ht := restrict_congr n t (by have := size_lt_of_mem (l := l) hd; simp only at this; omega)
          (fun x hx => h x (mem_leaves_node.mpr ⟨(e, t), hd, hx⟩))
        simp only [restrictKids, ht]
        rw [ih (fun d' hd' => hds d' (by simp [hd']))]
    exact this cs (fun _ h => h)

theorem two_le_length {α : Type} {l : List α} {a b : α} (ha : a ∈ l) (hb : b ∈ l) (hab : a ≠ b) :
    2 ≤ l.length := by
  match l with
  | [] => simp at ha
  | [u] => simp at ha hb; subst ha; subst hb; exact absurd rfl hab
  | _ :: _ :: _ => simp

/-- When two different children keep leaves, the restriction is a node with the same label and the
sorted restricted children. -/
theorem restrict_node_two {S : ℕ → Bool} {l : N} {cs : List (E × LTree N E)}
    {c₁ c₂ : E × LTree N E} (h₁ : c₁ ∈ cs) (h₂ : c₂ ∈ cs) {x y : ℕ} (hx : x ∈ c₁.2.leaves)
    (hy : y ∈ c₂.2.leaves) (hSx : S x = true) (hSy : S y = true) (hxy : x ∉ c₂.2.leaves) :
    (node l cs).restrict S = some (node l (sortKids (restrictKids S cs))) := by
  obtain ⟨e₁, t₁⟩ := c₁
  obtain ⟨e₂, t₂⟩ := c₂
  have hr₁ := (mem_oleaves_restrict (S := S) (t := t₁)).mpr ⟨hx, hSx⟩
  have hr₂ := (mem_oleaves_restrict (S := S) (t := t₂)).mpr ⟨hy, hSy⟩
  cases hq₁ : t₁.restrict S with
  | none => rw [hq₁] at hr₁; simp [oleaves] at hr₁
  | some u₁ =>
    cases hq₂ : t₂.restrict S with
    | none => rw [hq₂] at hr₂; simp [oleaves] at hr₂
    | some u₂ =>
      have m₁ : (e₁, u₁) ∈ restrictKids S cs := mem_restrictKids.mpr ⟨t₁, h₁, hq₁⟩
      have m₂ : (e₂, u₂) ∈ restrictKids S cs := mem_restrictKids.mpr ⟨t₂, h₂, hq₂⟩
      have hne : (e₁, u₁) ≠ (e₂, u₂) := by
        intro he
        cases he
        rw [hq₁] at hr₁
        have := (mem_oleaves_restrict (S := S) (t := t₂)).mp (by rw [hq₂]; exact hr₁)
        exact hxy this.1
      have hlen := two_le_length m₁ m₂ hne
      simp only [restrict]
      unfold mk
      split
      · rename_i heq; rw [heq] at hlen; simp at hlen
      · rename_i heq; rw [heq] at hlen; simp at hlen
      · rename_i c₁' c₂' rest heq; rw [heq]

/-! ## Observations of a restricted root -/

/-- The label of the root, if it is a node. -/
def rlabel : Option (LTree N E) → Option N
  | some (.node l _) => some l
  | _ => none

/-- The label of the edge from the root to the child that holds `x`. -/
def edgeTo (x : ℕ) : Option (LTree N E) → Option E
  | some (.node _ cs) => (cs.find? fun c => decide (x ∈ c.2.leaves)).map Prod.fst
  | _ => none

/-- `x` and `y` lie in one child of the root. -/
def together (x y : ℕ) : Option (LTree N E) → Prop
  | some (.node _ cs) => ∃ c ∈ cs, x ∈ c.2.leaves ∧ y ∈ c.2.leaves
  | _ => False

theorem find?_map_fst {α β : Type} (p : α × β → Bool) {e : α} :
    ∀ {cs : List (α × β)}, (∃ c ∈ cs, p c = true) → (∀ c ∈ cs, p c = true → c.1 = e) →
      (cs.find? p).map Prod.fst = some e
  | [], h, _ => by simp at h
  | c :: cs, h, h' => by
    simp only [List.find?_cons]
    cases hc : p c with
    | true => simp [h' c (by simp) hc]
    | false =>
      simp only
      apply find?_map_fst p
      · obtain ⟨c', hc', hp⟩ := h
        rcases List.mem_cons.mp hc' with rfl | hc'
        · rw [hc] at hp; cases hp
        · exact ⟨c', hc', hp⟩
      · intro c' hc' hp; exact h' c' (List.mem_cons_of_mem _ hc') hp

theorem together_restrict {S : ℕ → Bool} {l : N} {cs : List (E × LTree N E)} {x y : ℕ}
    (h : (node l cs).restrict S = some (node l (sortKids (restrictKids S cs)))) :
    together x y ((node l cs).restrict S) ↔
      ∃ c ∈ cs, x ∈ c.2.leaves ∧ y ∈ c.2.leaves ∧ S x = true ∧ S y = true := by
  rw [h]
  simp only [together]
  constructor
  · rintro ⟨⟨e, t'⟩, hc, hx, hy⟩
    obtain ⟨t, ht, hr⟩ := mem_restrictKids.mp ((sortKids_perm _).subset hc)
    have hx' := (mem_oleaves_restrict (S := S) (t := t)).mp (by rw [hr]; exact hx)
    have hy' := (mem_oleaves_restrict (S := S) (t := t)).mp (by rw [hr]; exact hy)
    exact ⟨(e, t), ht, hx'.1, hy'.1, hx'.2, hy'.2⟩
  · rintro ⟨⟨e, t⟩, ht, hx, hy, hSx, hSy⟩
    have hx' := (mem_oleaves_restrict (S := S) (t := t)).mpr ⟨hx, hSx⟩
    have hy' := (mem_oleaves_restrict (S := S) (t := t)).mpr ⟨hy, hSy⟩
    cases hr : t.restrict S with
    | none => rw [hr] at hx'; simp [oleaves] at hx'
    | some t' =>
      rw [hr] at hx' hy'
      exact ⟨(e, t'), (sortKids_perm _).symm.subset (mem_restrictKids.mpr ⟨t, ht, hr⟩), hx', hy'⟩

theorem edgeTo_restrict {S : ℕ → Bool} {l : N} {cs : List (E × LTree N E)} {x : ℕ}
    (hn : (node l cs).leaves.Nodup)
    (h : (node l cs).restrict S = some (node l (sortKids (restrictKids S cs))))
    {c : E × LTree N E} (hc : c ∈ cs) (hx : x ∈ c.2.leaves) (hSx : S x = true) :
    edgeTo x ((node l cs).restrict S) = some c.1 := by
  rw [h]
  simp only [edgeTo]
  apply find?_map_fst
  · obtain ⟨e, t⟩ := c
    have hx' := (mem_oleaves_restrict (S := S) (t := t)).mpr ⟨hx, hSx⟩
    cases hr : t.restrict S with
    | none => rw [hr] at hx'; simp [oleaves] at hx'
    | some t' =>
      rw [hr] at hx'
      exact ⟨(e, t'), (sortKids_perm _).symm.subset (mem_restrictKids.mpr ⟨t, hc, hr⟩),
        by simpa [oleaves] using hx'⟩
  · rintro ⟨e', t'⟩ hm hp
    obtain ⟨t, ht, hr⟩ := mem_restrictKids.mp ((sortKids_perm _).subset hm)
    have hx' := (mem_oleaves_restrict (S := S) (t := t)).mp (by rw [hr]; simpa [oleaves] using hp)
    -- `x` lies in a single child
    simp only [leaves, kidsLeaves_eq] at hn
    obtain ⟨e₀, t₀⟩ := c
    apply Classical.byContradiction
    intro hne
    have hdiff : (e', t) ≠ (e₀, t₀) := by intro he; cases he; exact hne rfl
    obtain ⟨pre, post, rfl⟩ := List.append_of_mem hc
    simp only [List.map_append, List.map_cons, List.flatten_append, List.flatten_cons] at hn
    rcases List.mem_append.mp ht with ht | ht
    · have h1 := List.nodup_append.mp hn
      exact h1.2.2 x (List.mem_flatten.mpr ⟨_, List.mem_map.mpr ⟨_, ht, rfl⟩, hx'.1⟩) x
        (List.mem_append_left _ hx) rfl
    · rcases List.mem_cons.mp ht with he | ht
      · exact hdiff he
      · have h1 := (List.nodup_append.mp (List.nodup_append.mp hn).2.1)
        exact h1.2.2 x hx x (List.mem_flatten.mpr ⟨_, List.mem_map.mpr ⟨_, ht, rfl⟩, hx'.1⟩) rfl

/-! ## The theorem -/

theorem kids_disjoint : ∀ {cs : List (E × LTree N E)}, (kidsLeaves cs).Nodup →
    ∀ {c₁ c₂ : E × LTree N E}, c₁ ∈ cs → c₂ ∈ cs → c₁ ≠ c₂ → ∀ x ∈ c₁.2.leaves, x ∉ c₂.2.leaves
  | [], _, _, _, h₁, _, _, _, _ => by simp at h₁
  | c :: cs, hn, c₁, c₂, h₁, h₂, hne, x, hx => by
    obtain ⟨e, t⟩ := c
    simp only [kidsLeaves] at hn
    have hn' := List.nodup_append.mp hn
    have hin : ∀ {c'}, c' ∈ cs → ∀ {y}, y ∈ c'.2.leaves → y ∈ kidsLeaves cs := by
      intro c' hc' y hy
      rw [kidsLeaves_eq]; exact List.mem_flatten.mpr ⟨_, List.mem_map.mpr ⟨c', hc', rfl⟩, hy⟩
    rcases List.mem_cons.mp h₁ with rfl | h₁ <;> rcases List.mem_cons.mp h₂ with rfl | h₂
    · exact absurd rfl hne
    · intro hx2; exact hn'.2.2 x hx x (hin h₂ hx2) rfl
    · intro hx2; exact hn'.2.2 x hx2 x (hin h₁ hx) rfl
    · exact kids_disjoint hn'.2.1 h₁ h₂ hne x hx

theorem nodup_kids {l : N} {cs : List (E × LTree N E)} (h : (node l cs).leaves.Nodup) :
    (kidsLeaves cs).Nodup := by simpa [leaves] using h

theorem nodup_of_kid {l : N} {cs : List (E × LTree N E)} (h : (node l cs).leaves.Nodup)
    {c : E × LTree N E} (hc : c ∈ cs) : c.2.leaves.Nodup := by
  rw [leaves_node] at h
  exact (List.sublist_flatten_of_mem (List.mem_map.mpr ⟨c, hc, rfl⟩)).nodup h

theorem pairwise_nodup {cs : List (E × LTree N E)} (h : (cs.map fun c => key c.2).Pairwise (· < ·)) :
    cs.Nodup := by
  rw [List.pairwise_map] at h
  exact h.imp fun {a b} hab => by intro he; subst he; omega

/-- **A canonical tree is determined by its restrictions to three leaves.** Two canonical trees on
the same leaves, each leaf once, whose restrictions to every set of at most three leaves agree, are
equal. -/
theorem eq_of_restrict3 : ∀ (n : ℕ) (T₁ T₂ : LTree N E), T₁.size ≤ n → Canon T₁ → Canon T₂ →
    T₁.leaves.Nodup → T₂.leaves.Nodup → (∀ x, x ∈ T₁.leaves ↔ x ∈ T₂.leaves) →
    (∀ s : List ℕ, s.length ≤ 3 → restrictTo s T₁ = restrictTo s T₂) → T₁ = T₂
  | _, .leaf i, .leaf j, _, _, _, _, _, hl, _ => by
    have := (hl i).mp (by simp [leaves]); simp [leaves] at this; rw [this]
  | _, .leaf i, .node l cs, _, _, h₂, _, n₂, hl, _ => by
    exfalso
    obtain ⟨c₁, hc₁, c₂, hc₂, hne, hl₁, hl₂⟩ := canon_two_kids h₂
    obtain ⟨x, hx⟩ := List.exists_mem_of_ne_nil _ hl₁
    obtain ⟨y, hy⟩ := List.exists_mem_of_ne_nil _ hl₂
    have hxl := (hl x).mpr (mem_leaves_node.mpr ⟨c₁, hc₁, hx⟩)
    have hyl := (hl y).mpr (mem_leaves_node.mpr ⟨c₂, hc₂, hy⟩)
    simp [leaves] at hxl hyl
    exact kids_disjoint (nodup_kids n₂) hc₁ hc₂ hne x hx (by rw [hxl, ← hyl]; exact hy)
  | _, .node l cs, .leaf i, _, h₁, _, n₁, _, hl, _ => by
    exfalso
    obtain ⟨c₁, hc₁, c₂, hc₂, hne, hl₁, hl₂⟩ := canon_two_kids h₁
    obtain ⟨x, hx⟩ := List.exists_mem_of_ne_nil _ hl₁
    obtain ⟨y, hy⟩ := List.exists_mem_of_ne_nil _ hl₂
    have hxl := (hl x).mp (mem_leaves_node.mpr ⟨c₁, hc₁, hx⟩)
    have hyl := (hl y).mp (mem_leaves_node.mpr ⟨c₂, hc₂, hy⟩)
    simp [leaves] at hxl hyl
    exact kids_disjoint (nodup_kids n₁) hc₁ hc₂ hne x hx (by rw [hxl, ← hyl]; exact hy)
  | 0, .node l₁ cs₁, .node l₂ cs₂, hs, _, _, _, _, _, _ => by simp [size] at hs
  | n + 1, .node l₁ cs₁, .node l₂ cs₂, hs, h₁, h₂, n₁, n₂, hl, H => by
    obtain ⟨_, hsort₁, hk₁⟩ := canon_node h₁
    obtain ⟨_, hsort₂, hk₂⟩ := canon_node h₂
    have d₁ : ∀ {c₁ c₂ : E × LTree N E}, c₁ ∈ cs₁ → c₂ ∈ cs₁ → c₁ ≠ c₂ →
        ∀ x ∈ c₁.2.leaves, x ∉ c₂.2.leaves :=
      fun h₁ h₂ hne => kids_disjoint (nodup_kids n₁) h₁ h₂ hne
    have d₂ : ∀ {c₁ c₂ : E × LTree N E}, c₁ ∈ cs₂ → c₂ ∈ cs₂ → c₁ ≠ c₂ →
        ∀ x ∈ c₁.2.leaves, x ∉ c₂.2.leaves :=
      fun h₁ h₂ hne => kids_disjoint (nodup_kids n₂) h₁ h₂ hne
    -- every leaf lies in a child
    have kid₁ : ∀ x, x ∈ (node l₁ cs₁).leaves → ∃ c ∈ cs₁, x ∈ c.2.leaves :=
      fun x hx => mem_leaves_node.mp hx
    have kid₂ : ∀ x, x ∈ (node l₁ cs₁).leaves → ∃ c ∈ cs₂, x ∈ c.2.leaves :=
      fun x hx => mem_leaves_node.mp ((hl x).mp hx)
    have inL₁ : ∀ {c : E × LTree N E} {x : ℕ}, c ∈ cs₁ → x ∈ c.2.leaves → x ∈ (node l₁ cs₁).leaves :=
      fun hc hx => mem_leaves_node.mpr ⟨_, hc, hx⟩
    have inL₂ : ∀ {c : E × LTree N E} {x : ℕ}, c ∈ cs₂ → x ∈ c.2.leaves → x ∈ (node l₁ cs₁).leaves :=
      fun {_ x} hc hx => (hl x).mpr (mem_leaves_node.mpr ⟨_, hc, hx⟩)
    -- a leaf in another child of the first root
    have other : ∀ c ∈ cs₁, ∃ c' ∈ cs₁, c' ≠ c ∧ ∃ z, z ∈ c'.2.leaves := by
      intro c hc
      obtain ⟨c₁, hc₁, c₂, hc₂, hne, hl₁, hl₂⟩ := canon_two_kids h₁
      by_cases h : c₁ = c
      · subst h
        exact ⟨c₂, hc₂, Ne.symm hne, List.exists_mem_of_ne_nil _ hl₂⟩
      · exact ⟨c₁, hc₁, h, List.exists_mem_of_ne_nil _ hl₁⟩
    -- step 1: the roots split the leaves the same way
    have split : ∀ x y, (∃ c ∈ cs₁, x ∈ c.2.leaves ∧ y ∈ c.2.leaves) ↔
        (∃ c ∈ cs₂, x ∈ c.2.leaves ∧ y ∈ c.2.leaves) := by
      intro x y
      constructor
      · rintro ⟨c, hc, hx, hy⟩
        apply Classical.byContradiction
        intro hno
        obtain ⟨c', hc', hne', z, hz⟩ := other c hc
        let s := [x, y, z]
        have hS : ∀ w ∈ s, (fun i => decide (i ∈ s)) w = true := by intro w hw; simpa using hw
        have r₁ := restrict_node_two (l := l₁) (S := fun i => decide (i ∈ s)) hc hc' hx hz
          (hS x (by simp [s])) (hS z (by simp [s])) (d₁ hc hc' (Ne.symm hne') x hx)
        obtain ⟨a, ha, hxa⟩ := kid₂ x (inL₁ hc hx)
        obtain ⟨b, hb, hyb⟩ := kid₂ y (inL₁ hc hy)
        have hxb : x ∉ b.2.leaves := fun h => hno ⟨b, hb, h, hyb⟩
        have r₂ := restrict_node_two (l := l₂) (S := fun i => decide (i ∈ s)) ha hb hxa hyb
          (hS x (by simp [s])) (hS y (by simp [s])) hxb
        have e := H s (by simp [s])
        have t₁ : together x y (restrictTo s (node l₁ cs₁)) :=
          (together_restrict r₁).mpr ⟨c, hc, hx, hy, hS x (by simp [s]), hS y (by simp [s])⟩
        unfold restrictTo at e t₁
        rw [e] at t₁
        obtain ⟨c'', hc'', hx'', hy'', _, _⟩ := (together_restrict r₂).mp t₁
        exact hno ⟨c'', hc'', hx'', hy''⟩
      · rintro ⟨c, hc, hx, hy⟩
        apply Classical.byContradiction
        intro hno
        obtain ⟨a, ha, hxa⟩ := kid₁ x (inL₂ hc hx)
        obtain ⟨b, hb, hyb⟩ := kid₁ y (inL₂ hc hy)
        have hxb : x ∉ b.2.leaves := fun h => hno ⟨b, hb, h, hyb⟩
        have hab : a ≠ b := by intro he; subst he; exact hxb hxa
        -- a leaf of the second root outside `c`
        obtain ⟨c₁, hc₁, c₂, hc₂, hne, hl₁, hl₂⟩ := canon_two_kids h₂
        obtain ⟨c', hc', hne', z, hz⟩ : ∃ c' ∈ cs₂, c' ≠ c ∧ ∃ z, z ∈ c'.2.leaves := by
          by_cases h : c₁ = c
          · subst h; exact ⟨c₂, hc₂, Ne.symm hne, List.exists_mem_of_ne_nil _ hl₂⟩
          · exact ⟨c₁, hc₁, h, List.exists_mem_of_ne_nil _ hl₁⟩
        let s := [x, y, z]
        have hS : ∀ w ∈ s, (fun i => decide (i ∈ s)) w = true := by intro w hw; simpa using hw
        have r₂ := restrict_node_two (l := l₂) (S := fun i => decide (i ∈ s)) hc hc' hx hz
          (hS x (by simp [s])) (hS z (by simp [s])) (d₂ hc hc' (Ne.symm hne') x hx)
        have r₁ := restrict_node_two (l := l₁) (S := fun i => decide (i ∈ s)) ha hb hxa hyb
          (hS x (by simp [s])) (hS y (by simp [s])) hxb
        have e := H s (by simp [s])
        have t₂ : together x y (restrictTo s (node l₂ cs₂)) :=
          (together_restrict r₂).mpr ⟨c, hc, hx, hy, hS x (by simp [s]), hS y (by simp [s])⟩
        unfold restrictTo at e t₂
        rw [← e] at t₂
        obtain ⟨c'', hc'', hx'', hy'', _, _⟩ := (together_restrict r₁).mp t₂
        exact hno ⟨c'', hc'', hx'', hy''⟩
    -- two leaves in different children of the first root are in different children of the second
    have apart₂ : ∀ {c c' : E × LTree N E}, c ∈ cs₁ → c' ∈ cs₁ → c ≠ c' → ∀ {x y : ℕ}, x ∈ c.2.leaves →
        y ∈ c'.2.leaves → ¬ ∃ d ∈ cs₂, x ∈ d.2.leaves ∧ y ∈ d.2.leaves := by
      intro c c' hc hc' hne x y hx hy hd
      obtain ⟨c'', hc'', hx'', hy''⟩ := (split x y).mpr hd
      by_cases h : c'' = c
      · subst h; exact d₁ hc' hc'' (Ne.symm hne) y hy hy''
      · exact d₁ hc hc'' (Ne.symm h) x hx hx''
    -- the restriction to two leaves in different children
    have pair : ∀ {c c' : E × LTree N E}, c ∈ cs₁ → c' ∈ cs₁ → c ≠ c' → ∀ {x y : ℕ}, x ∈ c.2.leaves →
        y ∈ c'.2.leaves → ∃ a ∈ cs₂, x ∈ a.2.leaves ∧
          (node l₁ cs₁).restrict (fun i => decide (i ∈ [x, y])) =
            some (node l₁ (sortKids (restrictKids (fun i => decide (i ∈ [x, y])) cs₁))) ∧
          (node l₂ cs₂).restrict (fun i => decide (i ∈ [x, y])) =
            some (node l₂ (sortKids (restrictKids (fun i => decide (i ∈ [x, y])) cs₂))) := by
      intro c c' hc hc' hne x y hx hy
      obtain ⟨a, ha, hxa⟩ := kid₂ x (inL₁ hc hx)
      obtain ⟨b, hb, hyb⟩ := kid₂ y (inL₁ hc' hy)
      have hxb : x ∉ b.2.leaves := fun h => apart₂ hc hc' hne hx hy ⟨b, hb, h, hyb⟩
      refine ⟨a, ha, hxa, ?_, ?_⟩
      · exact restrict_node_two hc hc' hx hy (by simp) (by simp) (d₁ hc hc' hne x hx)
      · exact restrict_node_two ha hb hxa hyb (by simp) (by simp) hxb
    -- step 2: the root labels agree
    have hlab : l₁ = l₂ := by
      obtain ⟨c₁, hc₁, c₂, hc₂, hne, hl₁, hl₂⟩ := canon_two_kids h₁
      obtain ⟨x, hx⟩ := List.exists_mem_of_ne_nil _ hl₁
      obtain ⟨y, hy⟩ := List.exists_mem_of_ne_nil _ hl₂
      obtain ⟨_, _, _, r₁, r₂⟩ := pair hc₁ hc₂ hne hx hy
      have e := H [x, y] (by simp)
      unfold restrictTo at e
      rw [r₁, r₂] at e
      have e' := Option.some.inj e
      injection e' with h _
    -- step 3: matching children are equal
    have match_kid : ∀ c ∈ cs₁, ∀ x ∈ c.2.leaves, ∀ d ∈ cs₂, x ∈ d.2.leaves → d = c := by
      intro c hc x hx d hd hxd
      obtain ⟨c', hc', hne', y, hy⟩ := other c hc
      obtain ⟨a, ha, hxa, r₁, r₂⟩ := pair hc hc' (Ne.symm hne') hx hy
      have had : a = d := by
        apply Classical.byContradiction; intro h; exact d₂ ha hd h x hxa hxd
      subst had
      -- edge labels
      have e := H [x, y] (by simp)
      unfold restrictTo at e
      have ed₁ := edgeTo_restrict (x := x) n₁ r₁ hc hx (by simp)
      have ed₂ := edgeTo_restrict (x := x) n₂ r₂ ha hxa (by simp)
      rw [e, ed₂] at ed₁
      have hedge : a.1 = c.1 := Option.some.inj ed₁
      -- the same leaves
      have hleaves : ∀ y, y ∈ c.2.leaves ↔ y ∈ a.2.leaves := by
        intro y
        constructor
        · intro hy'
          obtain ⟨d', hd', hxd', hyd'⟩ := (split x y).mp ⟨c, hc, hx, hy'⟩
          have : d' = a := by
            apply Classical.byContradiction; intro h; exact d₂ hd' ha h x hxd' hxa
          subst this; exact hyd'
        · intro hy'
          obtain ⟨c'', hc'', hxc'', hyc''⟩ := (split x y).mpr ⟨a, ha, hxa, hy'⟩
          have : c'' = c := by
            apply Classical.byContradiction; intro h; exact d₁ hc'' hc h x hxc'' hx
          subst this; exact hyc''
      -- the same restrictions
      have hres : ∀ s : List ℕ, s.length ≤ 3 → restrictTo s c.2 = restrictTo s a.2 := by
        intro s hs
        let s' := s.filter fun i => decide (i ∈ c.2.leaves)
        have hs' : s'.length ≤ 3 := Nat.le_trans (List.length_filter_le _ _) hs
        have e' := H s' hs'
        unfold restrictTo at e' ⊢
        have c₁ : c.2.restrict (fun i => decide (i ∈ s)) = c.2.restrict (fun i => decide (i ∈ s')) :=
          restrict_congr _ _ (Nat.le_refl _) (fun w hw => by simp [s', hw])
        have c₂ : a.2.restrict (fun i => decide (i ∈ s)) = a.2.restrict (fun i => decide (i ∈ s')) :=
          restrict_congr _ _ (Nat.le_refl _) (fun w hw => by simp [s', (hleaves w).mpr hw])
        rw [c₁, c₂, ← restrict_node_sub n₁ hc (fun w _ hw => by simp [s'] at hw; exact hw.2),
          ← restrict_node_sub n₂ ha (fun w _ hw => by simp [s'] at hw; exact (hleaves w).mp hw.2)]
        exact e'
      have hsub := eq_of_restrict3 n c.2 a.2
        (by have := size_lt_of_mem (l := l₁) hc; omega) (hk₁ c hc) (hk₂ a ha)
        (nodup_of_kid n₁ hc) (nodup_of_kid n₂ ha) hleaves hres
      obtain ⟨e₁, t₁⟩ := c
      obtain ⟨e₂, t₂⟩ := a
      simp only at hedge hsub
      rw [hedge, hsub]
    -- step 4: the children lists agree
    have sub₁ : ∀ c ∈ cs₁, c ∈ cs₂ := by
      intro c hc
      obtain ⟨x, hx⟩ := List.exists_mem_of_ne_nil _ (canon_leaves_ne_nil _ _ (Nat.le_refl _) (hk₁ c hc))
      obtain ⟨d, hd, hxd⟩ := kid₂ x (inL₁ hc hx)
      rw [← match_kid c hc x hx d hd hxd]; exact hd
    have sub₂ : ∀ d ∈ cs₂, d ∈ cs₁ := by
      intro d hd
      obtain ⟨x, hx⟩ := List.exists_mem_of_ne_nil _ (canon_leaves_ne_nil _ _ (Nat.le_refl _) (hk₂ d hd))
      obtain ⟨c, hc, hxc⟩ := kid₁ x (inL₂ hd hx)
      rw [match_kid c hc x hxc d hd hx]; exact hc
    have hperm : cs₁.Perm cs₂ :=
      (List.perm_ext_iff_of_nodup (pairwise_nodup hsort₁) (pairwise_nodup hsort₂)).mpr
        fun c => ⟨sub₁ c, sub₂ c⟩
    have heq : cs₁ = cs₂ := by
      apply List.Perm.eq_of_pairwise (le := fun a b => key a.2 < key b.2) _ _ _ hperm
      · intro a b _ _ h h'; omega
      · exact List.pairwise_map.mp hsort₁
      · exact List.pairwise_map.mp hsort₂
    rw [hlab, heq]

/-- **Distinct canonical trees differ on at most three leaves.** Two different canonical trees on
the same leaves, each leaf once, have different restrictions to some list of at most three of their
leaves, without repetition. -/
theorem exists_restrict3_ne {T₁ T₂ : LTree N E} (h₁ : Canon T₁) (h₂ : Canon T₂)
    (n₁ : T₁.leaves.Nodup) (n₂ : T₂.leaves.Nodup) (hl : ∀ x, x ∈ T₁.leaves ↔ x ∈ T₂.leaves)
    (hne : T₁ ≠ T₂) :
    ∃ s : List ℕ, s.length ≤ 3 ∧ s.Nodup ∧ (∀ x ∈ s, x ∈ T₁.leaves) ∧
      restrictTo s T₁ ≠ restrictTo s T₂ := by
  apply Classical.byContradiction
  intro hno
  apply hne
  refine eq_of_restrict3 _ T₁ T₂ (Nat.le_refl _) h₁ h₂ n₁ n₂ hl ?_
  intro s hs
  let s' := T₁.leaves.filter fun i => decide (i ∈ s)
  have hn' : s'.Nodup := (List.filter_sublist).nodup n₁
  have hlen : s'.length ≤ 3 :=
    Nat.le_trans (List.Nodup.length_le_of_subset hn' (fun x hx => by simp [s'] at hx; exact hx.2)) hs
  have hsub : ∀ x ∈ s', x ∈ T₁.leaves := fun x hx => by simp [s'] at hx; exact hx.1
  have e : restrictTo s' T₁ = restrictTo s' T₂ := by
    apply Classical.byContradiction; intro h; exact hno ⟨s', hlen, hn', hsub, h⟩
  unfold restrictTo at e ⊢
  rw [restrict_congr (S' := fun i => decide (i ∈ s')) _ T₁ (Nat.le_refl _) (fun w hw => by simp [s', hw]),
    restrict_congr (S' := fun i => decide (i ∈ s')) _ T₂ (Nat.le_refl _)
      (fun w hw => by simp [s', (hl w).mpr hw])]
  exact e

end LTree

end MMAlgebra
