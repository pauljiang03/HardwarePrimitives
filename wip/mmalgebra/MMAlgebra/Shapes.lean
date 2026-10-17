import MMAlgebra.LTree

/-! # Canonical trees on at most three leaves

A canonical tree (every node with at least two children, listed by increasing smallest leaf) on
the leaves `a < b < c` has one of four shapes: a node with three leaf children (`shape3`'s first
case), or a node whose children are a node on two of the leaves and the third leaf, in the three
ways of choosing the pair; on `a < b` it is a node with two leaf children (`shape2`), and on `a` it
is the leaf (`shape1`). With finitely many labels these are finitely many trees, so the base
witnesses of completeness are a finite table per architecture. Hardware-independent. -/

local notation "ℕ" => Nat

namespace MMAlgebra.LTree

variable {N E : Type}

theorem length_leaves_node (l : N) (cs : List (E × LTree N E)) :
    (node l cs).leaves.length = (cs.map fun c => c.2.leaves.length).sum := by
  rw [leaves_node, List.length_flatten, List.map_map]; rfl

theorem canon_kid_pos {l : N} {cs : List (E × LTree N E)} (h : Canon (node l cs)) :
    ∀ c ∈ cs, 1 ≤ c.2.leaves.length := by
  intro c hc
  have := canon_leaves_ne_nil _ _ (Nat.le_refl _) ((canon_node h).2.2 c hc)
  cases hq : c.2.leaves with
  | nil => exact absurd hq this
  | cons _ _ => simp

theorem sum_ge_length {cs : List (E × LTree N E)} (h : ∀ c ∈ cs, 1 ≤ c.2.leaves.length) :
    cs.length ≤ (cs.map fun c => c.2.leaves.length).sum := by
  induction cs with
  | nil => simp
  | cons c cs ih =>
    simp only [List.length_cons, List.map_cons, List.sum_cons]
    have := h c (by simp)
    have := ih (fun c' hc' => h c' (by simp [hc']))
    omega

theorem canon_node_len {l : N} {cs : List (E × LTree N E)} (h : Canon (node l cs)) :
    2 ≤ (node l cs).leaves.length := by
  rw [length_leaves_node]
  exact Nat.le_trans (canon_node h).1 (sum_ge_length (canon_kid_pos h))

theorem leaf_of_len_one {U : LTree N E} (hc : Canon U) (h : U.leaves.length = 1) :
    ∃ i, U = leaf i := by
  cases U with
  | leaf i => exact ⟨i, rfl⟩
  | node l cs => have := canon_node_len hc; omega

theorem key_leaf (i : ℕ) : key (leaf i : LTree N E) = i := by simp [key, leaves, lmin]

theorem length_of_mem_iff {l : List ℕ} (hn : l.Nodup) {s : List ℕ} (hs : s.Nodup)
    (h : ∀ x, x ∈ l ↔ x ∈ s) : l.length = s.length :=
  ((List.perm_ext_iff_of_nodup hn hs).mpr h).length_eq

/-- A canonical tree on one leaf is that leaf. -/
theorem shape1 {U : LTree N E} {a : ℕ} (hc : Canon U) (hn : U.leaves.Nodup)
    (hl : ∀ x, x ∈ U.leaves ↔ x = a) : U = leaf a := by
  have hlen := length_of_mem_iff hn (s := [a]) (by simp) (fun x => by simp [hl x])
  obtain ⟨i, rfl⟩ := leaf_of_len_one hc (by simpa using hlen)
  have := (hl i).mp (by simp [leaves])
  rw [this]

/-- A canonical tree on two leaves `a < b` is a node with the two leaves as children. -/
theorem shape2 {U : LTree N E} {a b : ℕ} (hab : a < b) (hc : Canon U) (hn : U.leaves.Nodup)
    (hl : ∀ x, x ∈ U.leaves ↔ x = a ∨ x = b) :
    ∃ l e₁ e₂, U = node l [(e₁, leaf a), (e₂, leaf b)] := by
  have hlen : U.leaves.length = 2 :=
    length_of_mem_iff hn (s := [a, b]) (by simp; omega) (fun x => by simp [hl x])
  cases U with
  | leaf i => simp [leaves] at hlen
  | node l cs =>
    have hpos := canon_kid_pos hc
    obtain ⟨hk2, hsort, hkc⟩ := canon_node hc
    rw [length_leaves_node] at hlen
    match cs, hk2, hsort, hkc, hpos, hlen with
    | [c₁, c₂], _, hsort, hkc, hpos, hlen =>
      simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil] at hlen
      have h1 := hpos c₁ (by simp)
      have h2 := hpos c₂ (by simp)
      obtain ⟨u, hu⟩ := leaf_of_len_one (hkc c₁ (by simp)) (by omega)
      obtain ⟨v, hv⟩ := leaf_of_len_one (hkc c₂ (by simp)) (by omega)
      obtain ⟨e₁, t₁⟩ := c₁
      obtain ⟨e₂, t₂⟩ := c₂
      simp only at hu hv
      subst hu; subst hv
      simp only [List.map_cons, List.map_nil, key_leaf] at hsort
      have hsort : u < v := List.rel_of_pairwise_cons hsort (by simp)
      have mu := (hl u).mp (mem_leaves_node.mpr ⟨(e₁, leaf u), by simp, by simp [leaves]⟩)
      have mv := (hl v).mp (mem_leaves_node.mpr ⟨(e₂, leaf v), by simp, by simp [leaves]⟩)
      have ma := (hl a).mpr (Or.inl rfl)
      have mb := (hl b).mpr (Or.inr rfl)
      rw [mem_leaves_node] at ma mb
      simp [leaves] at ma mb
      have : u = a := by omega
      have : v = b := by omega
      subst_vars
      exact ⟨l, e₁, e₂, rfl⟩
    | c₁ :: c₂ :: c₃ :: cs, _, _, _, hpos, hlen =>
      simp only [List.map_cons, List.sum_cons] at hlen
      have := hpos c₁ (by simp)
      have := hpos c₂ (by simp)
      have := hpos c₃ (by simp)
      omega

/-- A list of two distinct leaves, as its minimum and maximum. -/
theorem two_leaves {l : List ℕ} (hn : l.Nodup) (h : l.length = 2) :
    ∃ v w, v < w ∧ ∀ x, x ∈ l ↔ x = v ∨ x = w := by
  match l, hn, h with
  | [p, q], hn, _ =>
    have hpq : p ≠ q := by simpa using hn
    rcases Nat.lt_or_gt_of_ne hpq with h | h
    · exact ⟨p, q, h, by simp⟩
    · exact ⟨q, p, h, by intro x; simp; omega⟩

/-- A canonical tree on three leaves `a < b < c` has one of four shapes: the three leaves as
children, or a node on `{a, b}`, `{a, c}` or `{b, c}` beside the third leaf. -/
theorem shape3 {U : LTree N E} {a b c : ℕ} (hab : a < b) (hbc : b < c) (hc : Canon U)
    (hn : U.leaves.Nodup) (hl : ∀ x, x ∈ U.leaves ↔ x = a ∨ x = b ∨ x = c) :
    (∃ l e₁ e₂ e₃, U = node l [(e₁, leaf a), (e₂, leaf b), (e₃, leaf c)]) ∨
    (∃ l e₁ e₂ l' f₁ f₂, U = node l [(e₁, node l' [(f₁, leaf a), (f₂, leaf b)]), (e₂, leaf c)]) ∨
    (∃ l e₁ e₂ l' f₁ f₂, U = node l [(e₁, node l' [(f₁, leaf a), (f₂, leaf c)]), (e₂, leaf b)]) ∨
    (∃ l e₁ e₂ l' f₁ f₂, U = node l [(e₁, leaf a), (e₂, node l' [(f₁, leaf b), (f₂, leaf c)])]) := by
  have hlen : U.leaves.length = 3 :=
    length_of_mem_iff hn (s := [a, b, c]) (by simp; omega) (fun x => by simp [hl x])
  cases U with
  | leaf i => simp [leaves] at hlen
  | node l cs =>
    have hpos := canon_kid_pos hc
    obtain ⟨hk2, hsort, hkc⟩ := canon_node hc
    have hlen' := hlen
    rw [length_leaves_node] at hlen
    have mem : ∀ x, (x = a ∨ x = b ∨ x = c) ↔ ∃ c' ∈ cs, x ∈ c'.2.leaves := fun x => by
      rw [← hl x, mem_leaves_node]
    match cs, hk2, hsort, hkc, hpos, hlen, mem with
    | [c₁, c₂, c₃], _, hsort, hkc, hpos, hlen, mem =>
      simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil] at hlen
      have h1 := hpos c₁ (by simp)
      have h2 := hpos c₂ (by simp)
      have h3 := hpos c₃ (by simp)
      obtain ⟨u, hu⟩ := leaf_of_len_one (hkc c₁ (by simp)) (by omega)
      obtain ⟨v, hv⟩ := leaf_of_len_one (hkc c₂ (by simp)) (by omega)
      obtain ⟨w, hw⟩ := leaf_of_len_one (hkc c₃ (by simp)) (by omega)
      obtain ⟨e₁, t₁⟩ := c₁
      obtain ⟨e₂, t₂⟩ := c₂
      obtain ⟨e₃, t₃⟩ := c₃
      simp only at hu hv hw
      subst hu; subst hv; subst hw
      simp only [List.map_cons, List.map_nil, key_leaf] at hsort
      have s1 : u < v := List.rel_of_pairwise_cons hsort (by simp)
      have s2 : v < w := List.rel_of_pairwise_cons (List.Pairwise.of_cons hsort) (by simp)
      have ma := (mem a).mp (Or.inl rfl)
      have mb := (mem b).mp (Or.inr (Or.inl rfl))
      have mc := (mem c).mp (Or.inr (Or.inr rfl))
      have mu := (mem u).mpr ⟨_, List.mem_cons_self, by simp [leaves]⟩
      simp [leaves] at ma mb mc mu
      have : u = a := by omega
      have : v = b := by omega
      have : w = c := by omega
      subst_vars
      exact Or.inl ⟨l, e₁, e₂, e₃, rfl⟩
    | [c₁, c₂], _, hsort, hkc, hpos, hlen, mem =>
      simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil] at hlen
      have h1 := hpos c₁ (by simp)
      have h2 := hpos c₂ (by simp)
      have hn' := hn
      rw [leaves_node] at hn'
      simp only [List.map_cons, List.map_nil, List.flatten_cons, List.flatten_nil,
        List.append_nil] at hn'
      have n1 := (List.nodup_append.mp hn').1
      have n2 := (List.nodup_append.mp hn').2.1
      obtain ⟨e₁, t₁⟩ := c₁
      obtain ⟨e₂, t₂⟩ := c₂
      simp only at h1 h2 hlen n1 n2
      simp only [List.map_cons, List.map_nil] at hsort
      have s1 : key t₁ < key t₂ := List.rel_of_pairwise_cons hsort (by simp)
      have ma := (mem a).mp (Or.inl rfl)
      have mb := (mem b).mp (Or.inr (Or.inl rfl))
      have mc := (mem c).mp (Or.inr (Or.inr rfl))
      simp only [List.mem_cons, List.mem_nil_iff, or_false, exists_eq_or_imp, exists_eq_left]
        at ma mb mc
      rcases (by omega : t₁.leaves.length = 1 ∧ t₂.leaves.length = 2 ∨
          t₁.leaves.length = 2 ∧ t₂.leaves.length = 1) with ⟨l1, l2⟩ | ⟨l1, l2⟩
      · obtain ⟨u, rfl⟩ := leaf_of_len_one (hkc (e₁, t₁) (by simp)) l1
        obtain ⟨v, w, hvw, hm⟩ := two_leaves n2 l2
        obtain ⟨l', f₁, f₂, rfl⟩ := shape2 hvw (hkc (e₂, t₂) (by simp)) n2 hm
        simp only [key_leaf] at s1
        have hk : key (node l' [(f₁, leaf v), (f₂, leaf w)] : LTree N E) = v := by
          simp [key, leaves, kidsLeaves, lmin]; omega
        rw [hk] at s1
        have mu := (mem u).mpr ⟨_, List.mem_cons_self, by simp [leaves]⟩
        have mv := (mem v).mpr ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, (hm v).mpr (Or.inl rfl)⟩
        have mw := (mem w).mpr ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, (hm w).mpr (Or.inr rfl)⟩
        simp [leaves, kidsLeaves] at ma mb mc
        have : u = a := by omega
        have : v = b := by omega
        have : w = c := by omega
        subst_vars
        exact Or.inr (Or.inr (Or.inr ⟨l, e₁, e₂, l', f₁, f₂, rfl⟩))
      · obtain ⟨u, rfl⟩ := leaf_of_len_one (hkc (e₂, t₂) (by simp)) l2
        obtain ⟨v, w, hvw, hm⟩ := two_leaves n1 l1
        obtain ⟨l', f₁, f₂, rfl⟩ := shape2 hvw (hkc (e₁, t₁) (by simp)) n1 hm
        simp only [key_leaf] at s1
        have hk : key (node l' [(f₁, leaf v), (f₂, leaf w)] : LTree N E) = v := by
          simp [key, leaves, kidsLeaves, lmin]; omega
        rw [hk] at s1
        have mu := (mem u).mpr ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, by simp [leaves]⟩
        have mv := (mem v).mpr ⟨_, List.mem_cons_self, (hm v).mpr (Or.inl rfl)⟩
        have mw := (mem w).mpr ⟨_, List.mem_cons_self, (hm w).mpr (Or.inr rfl)⟩
        simp [leaves, kidsLeaves] at ma mb mc
        have : v = a := by omega
        subst_vars
        rcases (by omega : (w = b ∧ u = c) ∨ (u = b ∧ w = c)) with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · subst h1; subst h2
          exact Or.inr (Or.inl ⟨l, e₁, e₂, l', f₁, f₂, rfl⟩)
        · subst h1; subst h2
          exact Or.inr (Or.inr (Or.inl ⟨l, e₁, e₂, l', f₁, f₂, rfl⟩))
    | c₁ :: c₂ :: c₃ :: c₄ :: cs, _, _, _, hpos, hlen, _ =>
      simp only [List.map_cons, List.sum_cons] at hlen
      have := hpos c₁ (by simp)
      have := hpos c₂ (by simp)
      have := hpos c₃ (by simp)
      have := hpos c₄ (by simp)
      omega

/-! ## Relabeling leaves and finite codes -/

mutual
/-- Relabel the leaves. -/
def mapLeaves (g : ℕ → ℕ) : LTree N E → LTree N E
  | .leaf i => .leaf (g i)
  | .node l cs => .node l (mapKids g cs)
def mapKids (g : ℕ → ℕ) : List (E × LTree N E) → List (E × LTree N E)
  | [] => []
  | (e, t) :: cs => (e, mapLeaves g t) :: mapKids g cs
end

/-- A canonical tree on two leaves: a node label and two edge labels. -/
def realize2 (κ : N × E × E) (a b : ℕ) : LTree N E := node κ.1 [(κ.2.1, leaf a), (κ.2.2, leaf b)]

/-- The four shapes of a canonical tree on three leaves `a < b < c`, with their labels. -/
inductive Shape3 (N E : Type) where
  | fan (l : N) (e₁ e₂ e₃ : E)
  | ab (l : N) (e₁ e₂ : E) (l' : N) (f₁ f₂ : E)
  | ac (l : N) (e₁ e₂ : E) (l' : N) (f₁ f₂ : E)
  | bc (l : N) (e₁ e₂ : E) (l' : N) (f₁ f₂ : E)
  deriving DecidableEq, Repr

/-- The tree of a shape on the leaves `a < b < c`. -/
def Shape3.realize : Shape3 N E → ℕ → ℕ → ℕ → LTree N E
  | .fan l e₁ e₂ e₃, a, b, c => node l [(e₁, leaf a), (e₂, leaf b), (e₃, leaf c)]
  | .ab l e₁ e₂ l' f₁ f₂, a, b, c => node l [(e₁, node l' [(f₁, leaf a), (f₂, leaf b)]), (e₂, leaf c)]
  | .ac l e₁ e₂ l' f₁ f₂, a, b, c => node l [(e₁, node l' [(f₁, leaf a), (f₂, leaf c)]), (e₂, leaf b)]
  | .bc l e₁ e₂ l' f₁ f₂, a, b, c => node l [(e₁, leaf a), (e₂, node l' [(f₁, leaf b), (f₂, leaf c)])]

/-- The relabeling `0 ↦ a, 1 ↦ b, 2 ↦ c`. -/
def lab3 (a b c : ℕ) : ℕ → ℕ := fun j => if j = 0 then a else if j = 1 then b else c

theorem realize2_lab (κ : N × E × E) (a b : ℕ) :
    realize2 κ a b = mapLeaves (lab3 a b b) (realize2 κ 0 1) := rfl

theorem realize3_lab (κ : Shape3 N E) (a b c : ℕ) :
    κ.realize a b c = mapLeaves (lab3 a b c) (κ.realize 0 1 2) := by
  cases κ <;> rfl

/-- **Canonical trees on three leaves, as codes.** -/
theorem shape3_code {U : LTree N E} {a b c : ℕ} (hab : a < b) (hbc : b < c) (hc : Canon U)
    (hn : U.leaves.Nodup) (hl : ∀ x, x ∈ U.leaves ↔ x = a ∨ x = b ∨ x = c) :
    ∃ κ : Shape3 N E, U = κ.realize a b c := by
  rcases shape3 hab hbc hc hn hl with ⟨l, e₁, e₂, e₃, h⟩ | ⟨l, e₁, e₂, l', f₁, f₂, h⟩ |
    ⟨l, e₁, e₂, l', f₁, f₂, h⟩ | ⟨l, e₁, e₂, l', f₁, f₂, h⟩
  · exact ⟨.fan l e₁ e₂ e₃, h⟩
  · exact ⟨.ab l e₁ e₂ l' f₁ f₂, h⟩
  · exact ⟨.ac l e₁ e₂ l' f₁ f₂, h⟩
  · exact ⟨.bc l e₁ e₂ l' f₁ f₂, h⟩

/-- **Canonical trees on two leaves, as codes.** -/
theorem shape2_code {U : LTree N E} {a b : ℕ} (hab : a < b) (hc : Canon U) (hn : U.leaves.Nodup)
    (hl : ∀ x, x ∈ U.leaves ↔ x = a ∨ x = b) : ∃ κ : N × E × E, U = realize2 κ a b := by
  obtain ⟨l, e₁, e₂, h⟩ := shape2 hab hc hn hl
  exact ⟨(l, e₁, e₂), h⟩

/-- A list of distinct naturals of length at most three, sorted. -/
theorem small_support {l : List ℕ} (hn : l.Nodup) (hlen : l.length ≤ 3) (hne : l ≠ []) :
    (∃ a, ∀ x, x ∈ l ↔ x = a) ∨ (∃ a b, a < b ∧ ∀ x, x ∈ l ↔ x = a ∨ x = b) ∨
      (∃ a b c, a < b ∧ b < c ∧ ∀ x, x ∈ l ↔ x = a ∨ x = b ∨ x = c) := by
  match l, hn, hlen, hne with
  | [a], _, _, _ => exact Or.inl ⟨a, by simp⟩
  | [a, b], hn, _, _ =>
    have : a ≠ b := by simpa using hn
    right; left
    rcases Nat.lt_or_gt_of_ne this with h | h
    · exact ⟨a, b, h, by simp⟩
    · exact ⟨b, a, h, by intro x; simp; omega⟩
  | [a, b, c], hn, _, _ =>
    simp at hn
    right; right
    rcases Nat.lt_or_gt_of_ne hn.1.1 with h1 | h1 <;> rcases Nat.lt_or_gt_of_ne hn.1.2 with h2 | h2 <;>
      rcases Nat.lt_or_gt_of_ne hn.2 with h3 | h3
    all_goals first
      | exact ⟨a, b, c, by omega, by omega, by intro x; simp⟩
      | exact ⟨a, c, b, by omega, by omega, by intro x; simp; omega⟩
      | exact ⟨b, a, c, by omega, by omega, by intro x; simp; omega⟩
      | exact ⟨b, c, a, by omega, by omega, by intro x; simp; omega⟩
      | exact ⟨c, a, b, by omega, by omega, by intro x; simp; omega⟩
      | exact ⟨c, b, a, by omega, by omega, by intro x; simp; omega⟩
      | omega

end MMAlgebra.LTree
