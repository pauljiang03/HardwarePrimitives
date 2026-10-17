import MMAlgebra.Rigid

/-! # The algebra of correctly rounded nodes

On CDNA 1 (fp16) a block FMA returns the binary32 value nearest to the exact sum of its accumulator
and its products, and a binary32 addition the value nearest to the exact sum of its operands. The
normal form of a term (`nfC`) is then an unlabeled rooted tree: every block and addition is a node
that rounds the exact sum of its children, a node left with one child is that child (an empty
block passes its accumulator through, and a one-product block from zero is the product, which is a
binary32 value), and children are unordered. In particular a one-product first block merges into
the next block, `[x] [J] = [x J]`, and `[x] ⊕ [y] = [x y]`.

`cr_sound`: on a machine with the laws of correctly rounded nodes (`CRAlg`), every term evaluates as
its normal form on admissible inputs. `cr_term_complete`: with inputs on three products that
separate the four trees on three leaves, two terms with different normal forms differ on some
input. Hardware-independent. -/

local notation "ℕ" => Nat
local notation "ℚ" => Rat

namespace MMAlgebra

open LTree

variable {α β : Type}

/-- The labels of the correctly rounded normal form: every node and edge alike. -/
def crLabels : Labels Unit Unit := ⟨(), (), (), (), ()⟩

/-- The normal form of correctly rounded nodes. -/
abbrev nfC : Term → Option (LTree Unit Unit) := nfL crLabels

/-- The laws of a matrix multiplier whose results round exact sums: `rnd` is the rounding, `good`
the words that it returns and that pass through an empty block, `G` a set of exact values closed
under addition on which `rnd` returns good words (on the models, the multiples of `2^-149`), and
`Adm` the admissible inputs (finite operands). Binary32 addition rounds the exact sum of its
operands, and a product is a binary32 value. -/
structure RoundLaws (m : Machine α β) where
  z : α
  slot : SlotZero m z
  rnd : ℚ → Option β
  good : β → Prop
  G : ℚ → Prop
  Adm : (ℕ → α) → Prop
  add : ∀ x y, m.add x y = rnd (m.val x + m.val y)
  rnd_val : ∀ w, good w → rnd (m.val w) = some w
  rnd_good : ∀ (x : ℚ) (w : β), G x → rnd x = some w → good w
  rnd_zero : rnd 0 = some m.zero
  zero_good : good m.zero
  G_add : ∀ x y : ℚ, G x → G y → G (x + y)
  G_zero : G 0
  G_good : ∀ w, good w → G (m.val w)
  G_pval : ∀ p, Adm p → ∀ i, G (m.pval (p i))
  /-- A product is a binary32 value: rounding it returns a word of that value. -/
  prod_exact : ∀ p, Adm p → ∀ i, ∃ w, rnd (m.pval (p i)) = some w ∧ m.val w = m.pval (p i)

/-- The laws of correctly rounded nodes: besides `RoundLaws`, a block with `K` slots rounds the
exact sum of its accumulator and its products. -/
structure CRAlg (m : Machine α β) (K : ℕ) extends RoundLaws m where
  block : ∀ p, Adm p → ∀ d (I : List (Option ℕ)), I.length = K → good d →
    m.block d (I.map (Option.map p)) = rnd (m.val d + m.slotVal (I.map (Option.map p)))

section Eval
variable (m : Machine α β) (rnd : ℚ → Option β) (p : ℕ → α)

mutual
/-- The value of a correctly rounded tree: a leaf is its product rounded, a node rounds the exact
sum of its children's values. -/
def evCR : LTree Unit Unit → Option β
  | .leaf i => rnd (m.pval (p i))
  | .node _ cs => (sumCR cs).bind rnd
/-- The exact sum of the values of the children, if each has one. -/
def sumCR : List (Unit × LTree Unit Unit) → Option ℚ
  | [] => some 0
  | (_, t) :: cs => (evCR t).bind fun w => (sumCR cs).map fun s => m.val w + s
end

/-- The value of an optional normal form: zero for none. -/
def evCRO (zero : β) : Option (LTree Unit Unit) → Option β
  | none => some zero
  | some U => evCR m rnd p U

end Eval

variable {m : Machine α β} {K : ℕ}

/-- The sum of children is a function of the multiset of children. -/
theorem sumCR_perm (rnd : ℚ → Option β) (p : ℕ → α) {cs ds : List (Unit × LTree Unit Unit)}
    (h : cs.Perm ds) : sumCR m rnd p cs = sumCR m rnd p ds := by
  induction h with
  | nil => rfl
  | cons c _ ih => obtain ⟨e, t⟩ := c; simp only [sumCR, ih]
  | swap c₁ c₂ l =>
    obtain ⟨e₁, t₁⟩ := c₁
    obtain ⟨e₂, t₂⟩ := c₂
    simp only [sumCR]
    cases evCR m rnd p t₁ <;> cases evCR m rnd p t₂ <;> cases sumCR m rnd p l <;> simp <;> grind
  | trans _ _ ih₁ ih₂ => rw [ih₁, ih₂]

theorem sumCR_append (rnd : ℚ → Option β) (p : ℕ → α) :
    ∀ cs ds : List (Unit × LTree Unit Unit),
      sumCR m rnd p (cs ++ ds) = (sumCR m rnd p cs).bind fun s =>
        (sumCR m rnd p ds).map fun s' => s + s'
  | [], ds => by simp [sumCR]; cases sumCR m rnd p ds <;> simp [Rat.zero_add]
  | (e, t) :: cs, ds => by
    simp only [List.cons_append, sumCR, sumCR_append rnd p cs ds]
    cases evCR m rnd p t <;> cases sumCR m rnd p cs <;> cases sumCR m rnd p ds <;> simp <;> grind

mutual
theorem evCR_good (A : RoundLaws m) (p : ℕ → α) (hp : A.Adm p) :
    ∀ (U : LTree Unit Unit) (w : β), evCR m A.rnd p U = some w → A.good w
  | .leaf i, w, h => A.rnd_good _ _ (A.G_pval p hp i) h
  | .node l cs, w, h => by
    simp only [evCR] at h
    cases hs : sumCR m A.rnd p cs with
    | none => rw [hs] at h; cases h
    | some s =>
      rw [hs] at h
      exact A.rnd_good _ _ (sumCR_G A p hp cs s hs) h
theorem sumCR_G (A : RoundLaws m) (p : ℕ → α) (hp : A.Adm p) :
    ∀ (cs : List (Unit × LTree Unit Unit)) (s : ℚ), sumCR m A.rnd p cs = some s → A.G s
  | [], s, h => by
    simp only [sumCR, Option.some.injEq] at h; subst h; exact A.G_zero
  | (e, t) :: cs, s, h => by
    simp only [sumCR] at h
    cases ht : evCR m A.rnd p t with
    | none => rw [ht] at h; cases h
    | some w =>
      rw [ht] at h
      cases hs' : sumCR m A.rnd p cs with
      | none => rw [hs'] at h; cases h
      | some s' =>
        rw [hs'] at h
        simp only [Option.bind_some, Option.map_some, Option.some.injEq] at h
        subst h
        exact A.G_add _ _ (A.G_good w (evCR_good A p hp t w ht)) (sumCR_G A p hp cs s' hs')
end

theorem sumCR_leafs (A : RoundLaws m) (p : ℕ → α) (hp : A.Adm p) (l : List ℕ) :
    sumCR m A.rnd p (l.map fun i => (((), leaf i) : Unit × LTree Unit Unit)) =
      some ((l.map fun i => m.pval (p i)).sum) := by
  induction l with
  | nil => rfl
  | cons i l ih =>
    obtain ⟨w, hw, hv⟩ := A.prod_exact p hp i
    simp only [List.map_cons, sumCR, evCR, hw, Option.bind_some, ih, Option.map_some,
      List.sum_cons, hv]

theorem slotVal_map (I : List (Option ℕ)) (p : ℕ → α) :
    m.slotVal (I.map (Option.map p)) = ((blockLeaves I).map fun i => m.pval (p i)).sum := by
  rw [slotVal_eq_leaves]; rfl

/-- **Soundness of the correctly rounded laws.** On admissible inputs every term with blocks of
`K` slots, each product once, evaluates from the zero accumulator as its normal form. -/
theorem cr_sound (A : CRAlg m K) (p : ℕ → α) (hp : A.Adm p) :
    ∀ t : Term, TermWF K t → t.leaves.Nodup → eval m p m.zero m.zero t = evCRO m A.rnd p m.zero (nfC t)
  | .zero, _, _ => rfl
  | .init, _, _ => rfl
  | .hole, hw, _ => absurd hw (by simp [TermWF])
  | .blk t I, hw, hn => by
    obtain ⟨hwt, hlen⟩ := hw
    have hnt : t.leaves.Nodup := (List.nodup_append.mp hn).1
    have ih : eval m p m.zero m.zero t = evCRO m A.rnd p m.zero (nfL crLabels t) :=
      cr_sound A p hp t hwt hnt
    have hblk : ∀ d, A.good d → m.block d (I.map (Option.map p)) =
        A.rnd (m.val d + ((blockLeaves I).map fun i => m.pval (p i)).sum) := by
      intro d hd; rw [A.block p hp d I hlen hd, slotVal_map]
    show (eval m p m.zero m.zero t).bind (fun d => m.block d (I.map (Option.map p))) =
      evCRO m A.rnd p m.zero (mk () (optKid () (nfL crLabels t) ++
        (blockLeaves I).map fun i => (((), leaf i) : Unit × LTree Unit Unit)))
    rw [ih]
    have hval0 : m.val m.zero = 0 := m.val_zero
    cases hq : nfL crLabels t with
    | none =>
      show (some m.zero).bind _ = evCRO m A.rnd p m.zero (mk () ([] ++ _))
      rw [Option.bind_some, hblk _ A.zero_good, hval0, Rat.zero_add, List.nil_append]
      generalize hb : blockLeaves I = bl
      match bl with
      | [] => simp only [List.map_nil, List.sum_nil]; exact A.rnd_zero
      | [i] =>
        show A.rnd (List.sum [m.pval (p i)]) = A.rnd (m.pval (p i))
        simp only [List.sum_cons, List.sum_nil, Rat.add_zero]
      | i :: j :: rest =>
        show A.rnd _ = (sumCR m A.rnd p (sortKids ((i :: j :: rest).map
          fun i => (((), leaf i) : Unit × LTree Unit Unit)))).bind A.rnd
        rw [sumCR_perm A.rnd p (sortKids_perm _), sumCR_leafs A.toRoundLaws p hp]
        rfl
    | some u =>
      show (evCR m A.rnd p u).bind _ = evCRO m A.rnd p m.zero (mk () ([((), u)] ++ _))
      rw [List.singleton_append]
      have hg := evCR_good A.toRoundLaws p hp u
      generalize hb : blockLeaves I = bl at hblk
      match bl with
      | [] =>
        show (evCR m A.rnd p u).bind _ = evCR m A.rnd p u
        cases h : evCR m A.rnd p u with
        | none => rfl
        | some d =>
          simp only [Option.bind_some]
          rw [hblk d (hg d h), List.map_nil, List.sum_nil, Rat.add_zero]
          exact A.rnd_val d (hg d h)
      | i :: rest =>
        show (evCR m A.rnd p u).bind _ = (sumCR m A.rnd p (sortKids (((), u) :: (i :: rest).map
          fun i => (((), leaf i) : Unit × LTree Unit Unit)))).bind A.rnd
        rw [sumCR_perm A.rnd p (sortKids_perm _)]
        simp only [sumCR]
        rw [sumCR_leafs A.toRoundLaws p hp]
        cases h : evCR m A.rnd p u with
        | none => rfl
        | some d =>
          simp only [Option.bind_some, Option.map_some]
          rw [hblk d (hg d h)]
  | .add t₁ t₂, hw, hn => by
    obtain ⟨hw₁, hw₂⟩ := hw
    have n₁ : t₁.leaves.Nodup := (List.nodup_append.mp hn).1
    have n₂ : t₂.leaves.Nodup := (List.nodup_append.mp hn).2.1
    have ih₁ : eval m p m.zero m.zero t₁ = evCRO m A.rnd p m.zero (nfL crLabels t₁) :=
      cr_sound A p hp t₁ hw₁ n₁
    have ih₂ : eval m p m.zero m.zero t₂ = evCRO m A.rnd p m.zero (nfL crLabels t₂) :=
      cr_sound A p hp t₂ hw₂ n₂
    show (eval m p m.zero m.zero t₁).bind (fun x => (eval m p m.zero m.zero t₂).bind
      fun y => m.add x y) = evCRO m A.rnd p m.zero (mk () (optKid () (nfL crLabels t₁) ++
        optKid () (nfL crLabels t₂)))
    rw [ih₁, ih₂]
    have hval0 : m.val m.zero = 0 := m.val_zero
    cases hq₁ : nfL crLabels t₁ with
    | none =>
      cases hq₂ : nfL crLabels t₂ with
      | none =>
        show (some m.zero).bind (fun x => (some m.zero).bind fun y => m.add x y) = some m.zero
        simp only [Option.bind_some]
        rw [A.add, hval0, Rat.add_zero]; exact A.rnd_zero
      | some V =>
        show (some m.zero).bind (fun x => (evCR m A.rnd p V).bind fun y => m.add x y) =
          evCR m A.rnd p V
        rw [Option.bind_some]
        have hg := evCR_good A.toRoundLaws p hp V
        cases h : evCR m A.rnd p V with
        | none => rfl
        | some y =>
          simp only [Option.bind_some]
          rw [A.add, hval0, Rat.zero_add]; exact A.rnd_val y (hg y h)
    | some U =>
      cases hq₂ : nfL crLabels t₂ with
      | none =>
        show (evCR m A.rnd p U).bind (fun x => (some m.zero).bind fun y => m.add x y) =
          evCR m A.rnd p U
        have hg := evCR_good A.toRoundLaws p hp U
        cases h : evCR m A.rnd p U with
        | none => rfl
        | some x =>
          simp only [Option.bind_some]
          rw [A.add, hval0, Rat.add_zero]; exact A.rnd_val x (hg x h)
      | some V =>
        show (evCR m A.rnd p U).bind (fun x => (evCR m A.rnd p V).bind fun y => m.add x y) =
          (sumCR m A.rnd p (sortKids [((), U), ((), V)])).bind A.rnd
        rw [sumCR_perm A.rnd p (sortKids_perm _)]
        simp only [sumCR]
        cases evCR m A.rnd p U <;> cases evCR m A.rnd p V <;> simp [A.add, Rat.add_zero]

/-! ## Relabeling and the base step -/

section Relabel
variable (m : Machine α β) (rnd : ℚ → Option β)

mutual
theorem evCR_mapLeaves (p : ℕ → α) (g : ℕ → ℕ) : ∀ T : LTree Unit Unit,
    evCR m rnd p (mapLeaves g T) = evCR m rnd (fun i => p (g i)) T
  | .leaf i => rfl
  | .node l cs => by simp only [mapLeaves, evCR, sumCR_mapKids p g cs]
theorem sumCR_mapKids (p : ℕ → α) (g : ℕ → ℕ) : ∀ cs : List (Unit × LTree Unit Unit),
    sumCR m rnd p (mapKids g cs) = sumCR m rnd (fun i => p (g i)) cs
  | [] => rfl
  | (e, t) :: cs => by simp only [mapKids, sumCR, evCR_mapLeaves p g t, sumCR_mapKids p g cs]
end

mutual
theorem evCR_congr {p q : ℕ → α} : ∀ T : LTree Unit Unit, (∀ i ∈ T.leaves, p i = q i) →
    evCR m rnd p T = evCR m rnd q T
  | .leaf i, h => by simp only [evCR, h i (by simp [leaves])]
  | .node l cs, h => by
    simp only [evCR, sumCR_congr cs (fun i hi => h i (by simpa [leaves] using hi))]
theorem sumCR_congr {p q : ℕ → α} : ∀ cs : List (Unit × LTree Unit Unit),
    (∀ i ∈ kidsLeaves cs, p i = q i) → sumCR m rnd p cs = sumCR m rnd q cs
  | [], _ => rfl
  | (e, t) :: cs, h => by
    simp only [sumCR, evCR_congr t (fun i hi => h i (by simp [kidsLeaves, hi])),
      sumCR_congr cs (fun i hi => h i (by simp [kidsLeaves, hi]))]
end

end Relabel

/-- The four trees on three leaves. -/
def codes3Unit : List (Shape3 Unit Unit) :=
  [.fan () () () (), .ab () () () () () (), .ac () () () () () (), .bc () () () () () ()]

theorem mem_codes3Unit (κ : Shape3 Unit Unit) : κ ∈ codes3Unit := by
  cases κ <;> simp [codes3Unit]

/-- **The base step for unlabeled trees.** If inputs on `{0, 1, 2}` separate the four trees on three
leaves, then any two terms over the same products, at most three, with different normal forms are
separated by an admissible input. -/
theorem unit_base (F : NormalForm Unit Unit) (A : RoundLaws m) (ins3 : List (ℕ → α)) (hadm : ∀ q ∈ ins3, ∀ g : ℕ → ℕ,
      A.Adm (fun x => q (g x)))
    (h3 : ∀ κ₁ κ₂ : Shape3 Unit Unit, κ₁ ≠ κ₂ →
      ∃ q ∈ ins3, evCR m A.rnd q (κ₁.realize 0 1 2) ≠ evCR m A.rnd q (κ₂.realize 0 1 2)) :
    ∀ t₁ t₂ : Term, TermWF K t₁ → TermWF K t₂ → t₁.leaves.Nodup → t₂.leaves.Nodup →
      t₁.leaves.length ≤ 3 → (∀ i, i ∈ t₁.leaves ↔ i ∈ t₂.leaves) → F.nf t₁ ≠ F.nf t₂ →
      ∃ p, A.Adm p ∧ evCRO m A.rnd p m.zero (F.nf t₁) ≠ evCRO m A.rnd p m.zero (F.nf t₂) := by
  intro t₁ t₂ _ _ n₁ n₂ hlen hl hne
  obtain ⟨U₁, hU₁⟩ : ∃ U, F.nf t₁ = some U := by
    cases h : F.nf t₁ with
    | some U => exact ⟨U, rfl⟩
    | none =>
      exfalso
      have e₁ := (F.none_iff t₁).mp h
      have e₂ : t₂.leaves = [] := List.eq_nil_iff_forall_not_mem.mpr fun i hi => by
        have := (hl i).mpr hi; rw [e₁] at this; simp at this
      exact hne (by rw [h]; exact ((F.none_iff t₂).mpr e₂).symm)
  obtain ⟨U₂, hU₂⟩ : ∃ U, F.nf t₂ = some U := by
    cases h : F.nf t₂ with
    | some U => exact ⟨U, rfl⟩
    | none =>
      exfalso
      have e₂ := (F.none_iff t₂).mp h
      have e₁ : t₁.leaves = [] := List.eq_nil_iff_forall_not_mem.mpr fun i hi => by
        have := (hl i).mp hi; rw [e₂] at this; simp at this
      exact hne (by rw [h]; exact (F.none_iff t₁).mpr e₁)
  have p₁ : U₁.leaves.Perm t₁.leaves := by have := F.leaves t₁; rw [hU₁] at this; exact this
  have p₂ : U₂.leaves.Perm t₂.leaves := by have := F.leaves t₂; rw [hU₂] at this; exact this
  have c₁ := F.canon t₁ n₁ U₁ hU₁
  have c₂ := F.canon t₂ n₂ U₂ hU₂
  have hUne : U₁ ≠ U₂ := by intro h; exact hne (by rw [hU₁, hU₂, h])
  have m₁ : ∀ x, x ∈ U₁.leaves ↔ x ∈ t₁.leaves := fun x => p₁.mem_iff
  have m₂ : ∀ x, x ∈ U₂.leaves ↔ x ∈ t₁.leaves := fun x => by rw [p₂.mem_iff, hl x]
  have hne' : t₁.leaves ≠ [] := by
    intro h; have := (F.none_iff t₁).mpr h; rw [hU₁] at this; cases this
  rcases small_support n₁ hlen hne' with ⟨a, ha⟩ | ⟨a, b, hab, ha⟩ | ⟨a, b, c, hab, hbc, ha⟩
  · exfalso; apply hUne
    rw [shape1 c₁ (p₁.nodup_iff.mpr n₁) (fun x => by rw [m₁, ha]),
      shape1 c₂ (p₂.nodup_iff.mpr n₂) (fun x => by rw [m₂, ha])]
  · exfalso
    obtain ⟨⟨_, _, _⟩, rfl⟩ := shape2_code hab c₁ (p₁.nodup_iff.mpr n₁) (fun x => by rw [m₁, ha])
    obtain ⟨⟨_, _, _⟩, rfl⟩ := shape2_code hab c₂ (p₂.nodup_iff.mpr n₂) (fun x => by rw [m₂, ha])
    exact hUne rfl
  · obtain ⟨κ₁, rfl⟩ := shape3_code hab hbc c₁ (p₁.nodup_iff.mpr n₁) (fun x => by rw [m₁, ha])
    obtain ⟨κ₂, rfl⟩ := shape3_code hab hbc c₂ (p₂.nodup_iff.mpr n₂) (fun x => by rw [m₂, ha])
    have hκ : κ₁ ≠ κ₂ := by intro h; subst h; exact hUne rfl
    obtain ⟨q, hq3, hq⟩ := h3 κ₁ κ₂ hκ
    let inv : ℕ → ℕ := fun x => if x = a then 0 else if x = b then 1 else 2
    refine ⟨fun x => q (inv x), hadm q hq3 inv, ?_⟩
    rw [hU₁, hU₂]
    simp only [evCRO]
    rw [realize3_lab κ₁ a b c, realize3_lab κ₂ a b c, evCR_mapLeaves, evCR_mapLeaves]
    have hc : ∀ κ : Shape3 Unit Unit, evCR m A.rnd (fun i => (fun x => q (inv x)) (lab3 a b c i))
        (κ.realize 0 1 2) = evCR m A.rnd q (κ.realize 0 1 2) := by
      intro κ
      apply evCR_congr
      intro i hi
      have hi' : i = 0 ∨ i = 1 ∨ i = 2 := by
        cases κ <;> simp [Shape3.realize, leaves, kidsLeaves] at hi <;> omega
      rcases hi' with rfl | rfl | rfl
      · simp [lab3, inv]
      · have e : lab3 a b c 1 = b := by simp [lab3]
        simp only [inv, e, if_neg (show b ≠ a by omega)]; simp
      · have e : lab3 a b c 2 = c := by simp [lab3]
        simp only [inv, e, if_neg (show c ≠ a by omega), if_neg (show c ≠ b by omega)]
    rw [hc, hc]; exact hq

/-- **Completeness for terms with correctly rounded nodes.** -/
theorem cr_term_complete (A : CRAlg m K) (ins3 : List (ℕ → α))
    (hadm : ∀ q ∈ ins3, ∀ g : ℕ → ℕ, A.Adm (fun x => q (g x)))
    (hnd3 : (codes3Unit.map fun κ => ins3.map fun q => evCR m A.rnd q (κ.realize 0 1 2)).Nodup)
    (t₁ t₂ : Term) (hw₁ : TermWF K t₁) (hw₂ : TermWF K t₂) (n₁ : t₁.leaves.Nodup)
    (n₂ : t₂.leaves.Nodup) (hl : ∀ i, i ∈ t₁.leaves ↔ i ∈ t₂.leaves) (hne : nfC t₁ ≠ nfC t₂) :
    ∃ (s : List ℕ) (q : ℕ → α), s.length ≤ 3 ∧ (∀ i, i ∉ s → q i = A.z) ∧
      (∃ p, A.Adm p ∧ ∀ i, q i = A.z ∨ q i = p i) ∧
      eval m q m.zero m.zero t₁ ≠ eval m q m.zero m.zero t₂ :=
  term_complete (labelsNF crLabels) A.slot A.Adm (evCRO m A.rnd · m.zero)
    (fun t hw hn p hp => cr_sound A p hp t hw hn)
    (unit_base (labelsNF crLabels) A.toRoundLaws ins3 hadm (by
      have := sep_of_table codes3Unit mem_codes3Unit (fun _ => true) ins3
        (fun κ q => evCR m A.rnd q (κ.realize 0 1 2)) (by rw [List.filter_eq_self.mpr (fun _ _ => rfl)]; exact hnd3)
      exact fun κ₁ κ₂ h => this κ₁ κ₂ rfl rfl h))
    t₁ t₂ hw₁ hw₂ n₁ n₂ hl hne

end MMAlgebra
