import MMAlgebra.Term
import MMAlgebra.LTree
import MMAlgebra.ChainComplete

/-! # Completeness for terms on any matrix multiplier

The normal form of a reduction term is a labeled tree (`nfL`): a block FMA is a node labeled
`blk` whose children are its accumulator subterm (edge `cE`) and its products (edges `pE`), an
addition is a node labeled `add` with two children (edges `aE`), a subterm without products
disappears, and a node left with one child is that child. With every label equal, this is the
rooted tree of correctly rounded sums of CDNA 1; with the labels of the rigid algebra it is the
normal form of the Tensor Cores, CDNA 3 and SFMA.

* `nfL_restrict`: the normal form of a term restricted to a support is the restriction of its
  normal form;
* `nfL_canon`: normal forms are canonical trees;
* `term_complete`: if a machine evaluates every term as a function `evO` of its normal form
  (soundness of the laws) and inputs on at most three products separate any two normal forms over
  them (base witnesses), then two terms over the same products, each product once, with different
  normal forms give different outputs on some input that is `z` outside three products.

The step from a term to its supports of at most three products is `LTree.exists_restrict3_ne`.
Hardware-independent. Terms are evaluated from the zero accumulator (`c = 0`, so `init` is the
zero accumulator too). -/

local notation "ℕ" => Nat

namespace MMAlgebra

open LTree

variable {α β N E : Type}

/-! ## Restriction of terms -/

/-- Empty every slot outside `S`. -/
def Term.restrict (S : ℕ → Bool) : Term → Term
  | .zero => .zero
  | .init => .init
  | .hole => .hole
  | .blk t I => .blk (t.restrict S) (I.map (·.filter S))
  | .add t u => .add (t.restrict S) (u.restrict S)

/-- **Restriction.** On an input that is `z` outside `S`, a term evaluates as its restriction. -/
theorem eval_mask {m : Machine α β} {z : α} (hz : SlotZero m z) (S : ℕ → Bool) (p : ℕ → α)
    (c h : β) : ∀ t : Term, eval m (mask z S p) c h t = eval m p c h (t.restrict S)
  | .zero => rfl
  | .init => rfl
  | .hole => rfl
  | .blk t I => by
    simp only [eval, Term.restrict, eval_mask hz S p c h t]
    cases eval m p c h (t.restrict S) with
    | none => rfl
    | some d =>
      simp only [Option.bind_some]
      apply hz
      simp only [List.map_map]
      apply List.map_congr_left
      intro o _
      cases o with
      | none => rfl
      | some i => by_cases hi : S i = true <;> simp [mask, Option.filter, hi]
  | .add t u => by simp only [eval, Term.restrict, eval_mask hz S p c h t, eval_mask hz S p c h u]

theorem termWF_restrict {K : ℕ} (S : ℕ → Bool) : ∀ {t : Term}, TermWF K t → TermWF K (t.restrict S)
  | .zero, _ => trivial
  | .init, _ => trivial
  | .hole, h => h
  | .blk t I, h => ⟨termWF_restrict S h.1, by simp [h.2]⟩
  | .add t u, h => ⟨termWF_restrict S h.1, termWF_restrict S h.2⟩

theorem blockLeaves_restrict (S : ℕ → Bool) (I : List (Option ℕ)) :
    blockLeaves (I.map (·.filter S)) = (blockLeaves I).filter S := by
  unfold blockLeaves
  induction I with
  | nil => rfl
  | cons o I ih =>
    cases o with
    | none => simpa using ih
    | some i =>
      by_cases hi : S i = true
      · simp [Option.filter, hi] at ih ⊢; exact ih
      · simp [Option.filter, hi] at ih ⊢; exact ih

theorem leaves_restrict (S : ℕ → Bool) : ∀ t : Term, (t.restrict S).leaves = t.leaves.filter S
  | .zero => rfl
  | .init => rfl
  | .hole => rfl
  | .blk t I => by
    simp only [Term.restrict, Term.leaves, List.filter_append, leaves_restrict S t]
    exact congrArg _ (blockLeaves_restrict S I)
  | .add t u => by simp only [Term.restrict, Term.leaves, List.filter_append, leaves_restrict S t,
      leaves_restrict S u]

/-! ## Normal forms as labeled trees -/

/-- The labels of a normal form: of block and addition nodes, and of the edges to a block's
accumulator, to its products, and to the operands of an addition. -/
structure Labels (N E : Type) where
  blk : N
  add : N
  cE : E
  pE : E
  aE : E

/-- A child for an optional subtree. -/
def optKid (e : E) : Option (LTree N E) → List (E × LTree N E)
  | none => []
  | some t => [(e, t)]

/-- The normal form of a term: `none` when it holds no product. -/
def nfL (L : Labels N E) : Term → Option (LTree N E)
  | .zero => none
  | .init => none
  | .hole => none
  | .blk t I => mk L.blk (optKid L.cE (nfL L t) ++ (blockLeaves I).map fun i => (L.pE, leaf i))
  | .add t u => mk L.add (optKid L.aE (nfL L t) ++ optKid L.aE (nfL L u))

theorem kidsLeaves_optKid (e : E) (o : Option (LTree N E)) : kidsLeaves (optKid e o) = oleaves o := by
  cases o <;> simp [optKid, kidsLeaves, oleaves]

theorem kidsLeaves_leafs (e : E) (l : List ℕ) :
    kidsLeaves (l.map fun i => ((e, leaf i) : E × LTree N E)) = l := by
  induction l with
  | nil => rfl
  | cons i l ih => simp [kidsLeaves, leaves, ih]

/-- The leaves of a normal form are the products of the term. -/
theorem oleaves_nfL (L : Labels N E) : ∀ t : Term, (oleaves (nfL L t)).Perm t.leaves
  | .zero => by simp [nfL, oleaves, Term.leaves]
  | .init => by simp [nfL, oleaves, Term.leaves]
  | .hole => by simp [nfL, oleaves, Term.leaves]
  | .blk t I => by
    simp only [nfL, Term.leaves]
    refine (oleaves_mk _ _).trans ?_
    rw [kidsLeaves_append, kidsLeaves_optKid, kidsLeaves_leafs]
    exact (oleaves_nfL L t).append (List.Perm.refl _)
  | .add t u => by
    simp only [nfL, Term.leaves]
    refine (oleaves_mk _ _).trans ?_
    rw [kidsLeaves_append, kidsLeaves_optKid, kidsLeaves_optKid]
    exact (oleaves_nfL L t).append (oleaves_nfL L u)

/-! ## Children with disjoint leaves -/

/-- Children whose leaves are nonempty and, together, without repetition. -/
def KidsOK (cs : List (E × LTree N E)) : Prop :=
  (kidsLeaves cs).Nodup ∧ ∀ c ∈ cs, c.2.leaves ≠ []

theorem keys_nodup : ∀ {cs : List (E × LTree N E)}, KidsOK cs → (cs.map fun c => key c.2).Nodup
  | [], _ => List.nodup_nil
  | (e, t) :: cs, ⟨hn, hne⟩ => by
    simp only [kidsLeaves] at hn
    have hn' := List.nodup_append.mp hn
    simp only [List.map_cons, List.nodup_cons]
    refine ⟨?_, keys_nodup ⟨hn'.2.1, fun c hc => hne c (by simp [hc])⟩⟩
    intro hk
    obtain ⟨c', hc', he⟩ := List.mem_map.mp hk
    have h1 : key t ∈ t.leaves := lmin_mem (hne (e, t) (by simp))
    have h2 : key c'.2 ∈ c'.2.leaves := lmin_mem (hne c' (by simp [hc']))
    rw [he] at h2
    have h3 : key t ∈ kidsLeaves cs := by
      rw [kidsLeaves_eq]; exact List.mem_flatten.mpr ⟨_, List.mem_map.mpr ⟨c', hc', rfl⟩, h2⟩
    exact hn'.2.2 _ h1 _ h3 rfl

theorem inj_of_nodup_map {γ δ : Type} {f : γ → δ} :
    ∀ {l : List γ}, (l.map f).Nodup → ∀ {a b : γ}, a ∈ l → b ∈ l → f a = f b → a = b
  | [], _, _, _, ha, _, _ => by simp at ha
  | x :: xs, hn, a, b, ha, hb, hab => by
    simp only [List.map_cons, List.nodup_cons] at hn
    rcases List.mem_cons.mp ha with ha1 | ha2
    · rcases List.mem_cons.mp hb with hb1 | hb2
      · rw [ha1, hb1]
      · rw [ha1] at hab
        exact absurd (hab ▸ List.mem_map.mpr ⟨b, hb2, rfl⟩) hn.1
    · rcases List.mem_cons.mp hb with hb1 | hb2
      · rw [hb1] at hab
        exact absurd (hab.symm ▸ List.mem_map.mpr ⟨a, ha2, rfl⟩) hn.1
      · exact inj_of_nodup_map hn.2 ha2 hb2 hab

theorem sortKids_eq_of_perm {cs ds : List (E × LTree N E)} (h : cs.Perm ds) (hk : KidsOK cs) :
    sortKids cs = sortKids ds := by
  have hp : (sortKids cs).Perm (sortKids ds) :=
    (sortKids_perm cs).trans (h.trans (sortKids_perm ds).symm)
  have hkn := keys_nodup hk
  apply List.Perm.eq_of_pairwise (le := fun a b => decide (key a.2 ≤ key b.2)) _ _ _ hp
  · intro a b ha _ hab hba
    simp at hab hba
    have hke : key a.2 = key b.2 := by omega
    have ha' := (sortKids_perm cs).subset ha
    have hb' : b ∈ cs := h.symm.subset ((sortKids_perm ds).subset (by assumption))
    exact inj_of_nodup_map hkn ha' hb' hke
  · exact List.pairwise_mergeSort (by intro a b c h1 h2; simp at *; omega)
      (by intro a b; simp; omega) _
  · exact List.pairwise_mergeSort (by intro a b c h1 h2; simp at *; omega)
      (by intro a b; simp; omega) _

theorem mk_perm (l : N) {cs ds : List (E × LTree N E)} (h : cs.Perm ds) (hk : KidsOK cs) :
    mk l cs = mk l ds := by
  match cs, ds, h with
  | [], ds, h => rw [List.nil_perm.mp h]
  | [c], ds, h => rw [List.perm_singleton.mp h.symm]
  | c₁ :: c₂ :: cs, ds, h =>
    match ds, h with
    | d₁ :: d₂ :: ds, h =>
      simp only [mk]
      rw [sortKids_eq_of_perm h hk]
    | [], h => exact absurd h.length_eq (by simp)
    | [_], h => exact absurd h.length_eq (by simp)

theorem restrictKids_eq_filterMap (S : ℕ → Bool) :
    ∀ cs : List (E × LTree N E),
      restrictKids S cs = cs.filterMap fun c => (c.2.restrict S).map fun t => (c.1, t)
  | [] => rfl
  | (e, t) :: cs => by
    simp only [restrictKids, List.filterMap_cons]
    cases restrict S t <;> simp [restrictKids_eq_filterMap S cs]

theorem restrictKids_perm (S : ℕ → Bool) {cs ds : List (E × LTree N E)} (h : cs.Perm ds) :
    (restrictKids S cs).Perm (restrictKids S ds) := by
  rw [restrictKids_eq_filterMap, restrictKids_eq_filterMap]
  exact h.filterMap _

theorem kidsOK_restrict (S : ℕ → Bool) {cs : List (E × LTree N E)} (hk : KidsOK cs) :
    KidsOK (restrictKids S cs) := by
  refine ⟨?_, ?_⟩
  · have := kidsLeaves_restrictKids S cs
    exact this.nodup_iff.mpr (List.filter_sublist.nodup hk.1)
  · rintro ⟨e, t'⟩ hm
    obtain ⟨t, _, hr⟩ := mem_restrictKids.mp hm
    exact restrict_ne_nil S t t' hr

theorem kidsOK_perm {cs ds : List (E × LTree N E)} (h : cs.Perm ds) (hk : KidsOK cs) : KidsOK ds :=
  ⟨(kidsLeaves_perm h).nodup_iff.mp hk.1, fun c hc => hk.2 c (h.symm.subset hc)⟩

/-- Restricting a node built by `mk` restricts its children. -/
theorem mk_restrict (S : ℕ → Bool) (l : N) {cs : List (E × LTree N E)} (hk : KidsOK cs) :
    (mk l cs).bind (restrict S) = mk l (restrictKids S cs) := by
  match cs with
  | [] => rfl
  | [(e, t)] =>
    simp only [mk, Option.bind_some, restrictKids]
    cases restrict S t <;> rfl
  | c₁ :: c₂ :: cs =>
    simp only [mk, Option.bind_some, restrict]
    exact mk_perm l (restrictKids_perm S (sortKids_perm _)) (kidsOK_restrict S (kidsOK_perm
      (sortKids_perm _).symm hk))

theorem restrictKids_append' (S : ℕ → Bool) (cs ds : List (E × LTree N E)) :
    restrictKids S (cs ++ ds) = restrictKids S cs ++ restrictKids S ds := restrictKids_append S cs ds

theorem restrictKids_optKid (S : ℕ → Bool) (e : E) (o : Option (LTree N E)) :
    restrictKids S (optKid e o) = optKid e (o.bind (restrict S)) := by
  cases o with
  | none => rfl
  | some t => simp only [optKid, restrictKids, Option.bind_some]; cases restrict S t <;> rfl

theorem restrictKids_leafs (S : ℕ → Bool) (e : E) (l : List ℕ) :
    restrictKids S (l.map fun i => ((e, leaf i) : E × LTree N E)) =
      (l.filter S).map fun i => (e, leaf i) := by
  induction l with
  | nil => rfl
  | cons i l ih =>
    by_cases hi : S i = true
    · simp [restrictKids, restrict, hi, ih]
    · simp [restrictKids, restrict, hi, ih]

theorem oleaves_ne_nil_of_some {o : Option (LTree N E)} {t : LTree N E} (h : o = some t)
    (hne : oleaves o ≠ []) : t.leaves ≠ [] := by subst h; exact hne

theorem kidsOK_of (cs : List (E × LTree N E)) (hn : (kidsLeaves cs).Nodup)
    (hne : ∀ c ∈ cs, c.2.leaves ≠ []) : KidsOK cs := ⟨hn, hne⟩

theorem mk_ne_nil (l : N) {cs : List (E × LTree N E)} (hne : ∀ c ∈ cs, c.2.leaves ≠ [])
    {u : LTree N E} (h : mk l cs = some u) : u.leaves ≠ [] := by
  match cs, hne, h with
  | [(e, t)], hne, h => simp only [mk, Option.some.injEq] at h; subst h; exact hne (e, t) (by simp)
  | c₁ :: c₂ :: cs, hne, h =>
    simp only [mk, Option.some.injEq] at h
    subst h
    intro he
    have hp := kidsLeaves_perm (sortKids_perm (c₁ :: c₂ :: cs))
    simp only [leaves] at he
    rw [he] at hp
    have := List.nil_perm.mp hp
    obtain ⟨e₁, t₁⟩ := c₁
    simp only [kidsLeaves, List.append_eq_nil_iff] at this
    exact hne (e₁, t₁) (by simp) this.1

theorem optKid_ne_nil {e : E} {o : Option (LTree N E)}
    (h : ∀ u, o = some u → u.leaves ≠ []) : ∀ c ∈ optKid e o, c.2.leaves ≠ [] := by
  cases o with
  | none => simp [optKid]
  | some u => simp only [optKid, List.mem_singleton]; rintro c rfl; exact h u rfl

theorem leafs_ne_nil (e : E) (l : List ℕ) :
    ∀ c ∈ (l.map fun i => ((e, leaf i) : E × LTree N E)), c.2.leaves ≠ [] := by
  intro c hc
  obtain ⟨i, _, rfl⟩ := List.mem_map.mp hc
  simp [leaves]

/-- A normal form has a leaf. -/
theorem nfL_ne_nil (L : Labels N E) : ∀ (t : Term) (u : LTree N E), nfL L t = some u → u.leaves ≠ []
  | .zero, u, h => by simp [nfL] at h
  | .init, u, h => by simp [nfL] at h
  | .hole, u, h => by simp [nfL] at h
  | .blk t I, u, h => by
    simp only [nfL] at h
    refine mk_ne_nil _ ?_ h
    intro c hc
    rcases List.mem_append.mp hc with hc | hc
    · exact optKid_ne_nil (nfL_ne_nil L t) c hc
    · exact leafs_ne_nil _ _ c hc
  | .add t₁ t₂, u, h => by
    simp only [nfL] at h
    refine mk_ne_nil _ ?_ h
    intro c hc
    rcases List.mem_append.mp hc with hc | hc
    · exact optKid_ne_nil (nfL_ne_nil L t₁) c hc
    · exact optKid_ne_nil (nfL_ne_nil L t₂) c hc

theorem blk_kids_ok (L : Labels N E) (t : Term) (I : List (Option ℕ))
    (hn : (Term.blk t I).leaves.Nodup) :
    KidsOK (optKid L.cE (nfL L t) ++ (blockLeaves I).map fun i => ((L.pE, leaf i) : E × LTree N E)) := by
  refine ⟨?_, ?_⟩
  · rw [kidsLeaves_append, kidsLeaves_optKid, kidsLeaves_leafs]
    exact ((oleaves_nfL L t).append (List.Perm.refl _)).nodup_iff.mpr hn
  · intro c hc
    rcases List.mem_append.mp hc with hc | hc
    · exact optKid_ne_nil (nfL_ne_nil L t) c hc
    · exact leafs_ne_nil _ _ c hc

theorem add_kids_ok (L : Labels N E) (t u : Term) (hn : (Term.add t u).leaves.Nodup) :
    KidsOK (optKid L.aE (nfL L t) ++ optKid L.aE (nfL L u)) := by
  refine ⟨?_, ?_⟩
  · rw [kidsLeaves_append, kidsLeaves_optKid, kidsLeaves_optKid]
    exact ((oleaves_nfL L t).append (oleaves_nfL L u)).nodup_iff.mpr hn
  · intro c hc
    rcases List.mem_append.mp hc with hc | hc
    · exact optKid_ne_nil (nfL_ne_nil L t) c hc
    · exact optKid_ne_nil (nfL_ne_nil L u) c hc

/-- **Normal forms commute with restriction.** -/
theorem nfL_restrict (L : Labels N E) (S : ℕ → Bool) :
    ∀ t : Term, t.leaves.Nodup → nfL L (t.restrict S) = (nfL L t).bind (restrict S)
  | .zero, _ => rfl
  | .init, _ => rfl
  | .hole, _ => rfl
  | .blk t I, hn => by
    have ht : t.leaves.Nodup := (List.nodup_append.mp hn).1
    simp only [Term.restrict, nfL]
    rw [mk_restrict S L.blk (blk_kids_ok L t I hn), restrictKids_append, restrictKids_optKid,
      restrictKids_leafs, nfL_restrict L S t ht, blockLeaves_restrict]
  | .add t u, hn => by
    have h1 : t.leaves.Nodup := (List.nodup_append.mp hn).1
    have h2 : u.leaves.Nodup := (List.nodup_append.mp hn).2.1
    simp only [Term.restrict, nfL]
    rw [mk_restrict S L.add (add_kids_ok L t u hn), restrictKids_append, restrictKids_optKid,
      restrictKids_optKid, nfL_restrict L S t h1, nfL_restrict L S u h2]

theorem mk_canon (l : N) {cs : List (E × LTree N E)} (hk : KidsOK cs) (hc : ∀ c ∈ cs, Canon c.2)
    {u : LTree N E} (h : mk l cs = some u) : Canon u := by
  match cs, hk, hc, h with
  | [(e, t)], _, hc, h => simp only [mk, Option.some.injEq] at h; subst h; exact hc (e, t) (by simp)
  | c₁ :: c₂ :: cs, hk, hc, h =>
    simp only [mk, Option.some.injEq] at h
    subst h
    simp only [Canon]
    refine ⟨?_, ?_, ?_⟩
    · rw [(sortKids_perm _).length_eq]; simp
    · have hs : (sortKids (c₁ :: c₂ :: cs)).Pairwise fun a b => decide (key a.2 ≤ key b.2) :=
        List.pairwise_mergeSort (by intro a b c h1 h2; simp at *; omega)
          (by intro a b; simp; omega) _
      have hd := keys_nodup (kidsOK_perm (sortKids_perm _).symm hk)
      rw [List.pairwise_map]
      rw [List.Nodup, List.pairwise_map] at hd
      exact (hs.and hd).imp fun {a b} ⟨h1, h2⟩ => by simp at h1; omega
    · rw [kidsCanon_iff]
      intro c hm
      exact hc c ((sortKids_perm _).subset hm)

theorem optKid_canon {e : E} {o : Option (LTree N E)} (h : ∀ u, o = some u → Canon u) :
    ∀ c ∈ optKid e o, Canon c.2 := by
  cases o with
  | none => simp [optKid]
  | some u => simp only [optKid, List.mem_singleton]; rintro c rfl; exact h u rfl

/-- **Normal forms are canonical.** -/
theorem nfL_canon (L : Labels N E) :
    ∀ t : Term, t.leaves.Nodup → ∀ u, nfL L t = some u → Canon u
  | .zero, _, u, h => by simp [nfL] at h
  | .init, _, u, h => by simp [nfL] at h
  | .hole, _, u, h => by simp [nfL] at h
  | .blk t I, hn, u, h => by
    have ht : t.leaves.Nodup := (List.nodup_append.mp hn).1
    simp only [nfL] at h
    refine mk_canon _ (blk_kids_ok L t I hn) ?_ h
    intro c hc
    rcases List.mem_append.mp hc with hc | hc
    · exact optKid_canon (nfL_canon L t ht) c hc
    · obtain ⟨i, _, rfl⟩ := List.mem_map.mp hc; simp [Canon]
  | .add t₁ t₂, hn, u, h => by
    have h1 : t₁.leaves.Nodup := (List.nodup_append.mp hn).1
    have h2 : t₂.leaves.Nodup := (List.nodup_append.mp hn).2.1
    simp only [nfL] at h
    refine mk_canon _ (add_kids_ok L t₁ t₂ hn) ?_ h
    intro c hc
    rcases List.mem_append.mp hc with hc | hc
    · exact optKid_canon (nfL_canon L t₁ h1) c hc
    · exact optKid_canon (nfL_canon L t₂ h2) c hc

theorem nfL_none_iff (L : Labels N E) (t : Term) : nfL L t = none ↔ t.leaves = [] := by
  have hp := oleaves_nfL L t
  constructor
  · intro h; rw [h] at hp; exact List.nil_perm.mp hp
  · intro h
    rw [h] at hp
    cases hq : nfL L t with
    | none => rfl
    | some u =>
      rw [hq] at hp
      exact absurd (List.perm_nil.mp hp) (nfL_ne_nil L t u hq)

/-! ## Completeness from soundness and base witnesses -/

/-- A normal-form function into canonical labeled trees: its leaves are the products of the term,
it commutes with restriction, and its trees are canonical. `nfL` is one for every choice of
labels. -/
structure NormalForm (N E : Type) where
  nf : Term → Option (LTree N E)
  leaves : ∀ t, (oleaves (nf t)).Perm t.leaves
  restrict : ∀ (S : ℕ → Bool) (t : Term), t.leaves.Nodup → nf (t.restrict S) = (nf t).bind (LTree.restrict S)
  canon : ∀ t, t.leaves.Nodup → ∀ u, nf t = some u → Canon u

/-- The normal form of a choice of labels. -/
def labelsNF (L : Labels N E) : NormalForm N E where
  nf := nfL L
  leaves := oleaves_nfL L
  restrict S t h := nfL_restrict L S t h
  canon := nfL_canon L

theorem NormalForm.none_iff (F : NormalForm N E) (t : Term) : F.nf t = none ↔ t.leaves = [] := by
  have hp := F.leaves t
  constructor
  · intro h; rw [h] at hp; exact List.nil_perm.mp hp
  · intro h
    rw [h] at hp
    cases hq : F.nf t with
    | none => rfl
    | some u =>
      exfalso
      rw [hq] at hp
      have hl : u.leaves = [] := List.perm_nil.mp hp
      have hc := F.canon t (by rw [h]; exact List.nodup_nil) u hq
      exact canon_leaves_ne_nil _ u (Nat.le_refl _) hc hl

/-- **Completeness for terms.** On a machine whose blocks read an empty slot as `z`, suppose that,
on admissible inputs, every term evaluates from the zero accumulator as a function `evO` of its
normal form (`sound`), and that any two terms over the same products, at most three, with different
normal forms are separated by some admissible input (`base`). Then two terms over the same products,
each product once, with different normal forms differ on an input that is `z` outside at most
three of the products. -/
theorem term_complete (F : NormalForm N E) {m : Machine α β} {K : ℕ} {z : α} (hz : SlotZero m z)
    (Adm : (ℕ → α) → Prop) (evO : (ℕ → α) → Option (LTree N E) → Option β)
    (sound : ∀ t : Term, TermWF K t → t.leaves.Nodup →
      ∀ p, Adm p → eval m p m.zero m.zero t = evO p (F.nf t))
    (base : ∀ t₁ t₂ : Term, TermWF K t₁ → TermWF K t₂ → t₁.leaves.Nodup → t₂.leaves.Nodup →
      t₁.leaves.length ≤ 3 → (∀ i, i ∈ t₁.leaves ↔ i ∈ t₂.leaves) → F.nf t₁ ≠ F.nf t₂ →
      ∃ p, Adm p ∧ evO p (F.nf t₁) ≠ evO p (F.nf t₂))
    (t₁ t₂ : Term) (hw₁ : TermWF K t₁) (hw₂ : TermWF K t₂) (n₁ : t₁.leaves.Nodup)
    (n₂ : t₂.leaves.Nodup) (hl : ∀ i, i ∈ t₁.leaves ↔ i ∈ t₂.leaves) (hne : F.nf t₁ ≠ F.nf t₂) :
    ∃ (s : List ℕ) (q : ℕ → α), s.length ≤ 3 ∧ (∀ i, i ∉ s → q i = z) ∧
      (∃ p, Adm p ∧ ∀ i, q i = z ∨ q i = p i) ∧
      eval m q m.zero m.zero t₁ ≠ eval m q m.zero m.zero t₂ := by
  obtain ⟨U₁, hU₁⟩ : ∃ U, F.nf t₁ = some U := by
    cases h : F.nf t₁ with
    | some U => exact ⟨U, rfl⟩
    | none =>
      exfalso
      have e₁ := (F.none_iff t₁).mp h
      have e₂ : t₂.leaves = [] := List.eq_nil_iff_forall_not_mem.mpr fun i hi => by
        have := (hl i).mpr hi; rw [e₁] at this; simp at this
      exact hne (by rw [h, (F.none_iff t₂).mpr e₂])
  obtain ⟨U₂, hU₂⟩ : ∃ U, F.nf t₂ = some U := by
    cases h : F.nf t₂ with
    | some U => exact ⟨U, rfl⟩
    | none =>
      exfalso
      have e₂ := (F.none_iff t₂).mp h
      have e₁ : t₁.leaves = [] := List.eq_nil_iff_forall_not_mem.mpr fun i hi => by
        have := (hl i).mp hi; rw [e₂] at this; simp at this
      exact hne (by rw [h, (F.none_iff t₁).mpr e₁])
  have p₁ : U₁.leaves.Perm t₁.leaves := by have := F.leaves t₁; rw [hU₁] at this; exact this
  have p₂ : U₂.leaves.Perm t₂.leaves := by have := F.leaves t₂; rw [hU₂] at this; exact this
  have hUne : U₁ ≠ U₂ := by intro h; exact hne (by rw [hU₁, hU₂, h])
  obtain ⟨s, hs, hsn, hsub, hres⟩ := exists_restrict3_ne (F.canon t₁ n₁ U₁ hU₁)
    (F.canon t₂ n₂ U₂ hU₂) (p₁.nodup_iff.mpr n₁) (p₂.nodup_iff.mpr n₂)
    (fun i => by rw [p₁.mem_iff, p₂.mem_iff]; exact hl i) hUne
  let S : ℕ → Bool := fun i => decide (i ∈ s)
  have r₁ := F.restrict S t₁ n₁
  have r₂ := F.restrict S t₂ n₂
  rw [hU₁, Option.bind_some] at r₁
  rw [hU₂, Option.bind_some] at r₂
  have hne' : F.nf (t₁.restrict S) ≠ F.nf (t₂.restrict S) := by
    rw [r₁, r₂]; exact hres
  have hl₁ := leaves_restrict S t₁
  have hl₂ := leaves_restrict S t₂
  have nr₁ : (t₁.restrict S).leaves.Nodup := by rw [hl₁]; exact List.filter_sublist.nodup n₁
  have nr₂ : (t₂.restrict S).leaves.Nodup := by rw [hl₂]; exact List.filter_sublist.nodup n₂
  have hlen : (t₁.restrict S).leaves.length ≤ 3 :=
    Nat.le_trans (List.Nodup.length_le_of_subset nr₁ (fun x hx => by
      rw [hl₁] at hx; simpa [S] using (List.mem_filter.mp hx).2)) hs
  have hl' : ∀ i, i ∈ (t₁.restrict S).leaves ↔ i ∈ (t₂.restrict S).leaves := by
    intro i; rw [hl₁, hl₂, List.mem_filter, List.mem_filter, hl i]
  obtain ⟨p, hadm, hp⟩ :=
    base _ _ (termWF_restrict S hw₁) (termWF_restrict S hw₂) nr₁ nr₂ hlen hl' hne'
  refine ⟨s, mask z S p, hs, fun i hi => by simp [mask, S, hi],
    ⟨p, hadm, fun i => by unfold mask; split <;> simp⟩, ?_⟩
  rw [eval_mask hz, eval_mask hz, sound _ (termWF_restrict S hw₁) nr₁ p hadm,
    sound _ (termWF_restrict S hw₂) nr₂ p hadm]
  exact hp

end MMAlgebra
