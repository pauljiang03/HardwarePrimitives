import MMAlgebra.Rounded

/-! # The algebra of binary summation trees

On CDNA 2 a block FMA adds its products in a fixed balanced tree of binary32 additions over its
slot positions, `fl{fl{p₁ + p₂} + fl{p₃ + p₄}}`, and then adds `c` in one more addition. The normal
form of a term (`nfP`) is the unordered binary tree of all these additions: a block is a node with
two children, its accumulator subterm and the pairwise tree of its slots (`pairTree`), an addition
is a node with its two operands, and empty slots and subterms without products disappear. So `c`
can be moved out of a block into a separate addition (`nfP_csplit`).

`pair_sound`: on a machine with the laws of `PairAlg` (a block rounds the sum of its accumulator and
the value of its pairwise tree, whose nodes round the sums of their children), every term evaluates
as its normal form on admissible inputs. `pair_term_complete`: with inputs on three products that
separate the trees on three leaves, two terms with different normal forms differ on some input.
Hardware-independent. -/

local notation "ℕ" => Nat
local notation "ℚ" => Rat

namespace MMAlgebra

open LTree

variable {α β : Type}

/-- The pairwise tree of a list of slots: the two halves summed recursively, as a CDNA 2 block adds
its products; empty slots disappear. `d` bounds the depth. -/
def pairTree : ℕ → List (Option ℕ) → Option (LTree Unit Unit)
  | _, [] => none
  | _, [o] => o.map leaf
  | 0, _ :: _ :: _ => none
  | d + 1, l@(_ :: _ :: _) =>
    mk () (optKid () (pairTree d (l.take (l.length / 2))) ++ optKid () (pairTree d (l.drop (l.length / 2))))

theorem blockLeaves_append (l₁ l₂ : List (Option ℕ)) :
    blockLeaves (l₁ ++ l₂) = blockLeaves l₁ ++ blockLeaves l₂ := by
  simp [blockLeaves]

theorem blockLeaves_take_drop (l : List (Option ℕ)) (n : ℕ) :
    blockLeaves l = blockLeaves (l.take n) ++ blockLeaves (l.drop n) := by
  rw [← blockLeaves_append, List.take_append_drop]

theorem pairTree_succ (d : ℕ) (l : List (Option ℕ)) (hl : 2 ≤ l.length) :
    pairTree (d + 1) l = mk () (optKid () (pairTree d (l.take (l.length / 2))) ++
      optKid () (pairTree d (l.drop (l.length / 2)))) := by
  match l, hl with
  | _ :: _ :: _, _ => rfl

theorem pairTree_split_nodup {l : List (Option ℕ)} (hn : (blockLeaves l).Nodup) (n : ℕ) :
    (blockLeaves (l.take n)).Nodup ∧ (blockLeaves (l.drop n)).Nodup ∧
      ∀ x ∈ blockLeaves (l.take n), x ∉ blockLeaves (l.drop n) := by
  rw [blockLeaves_take_drop l n] at hn
  exact ⟨(List.nodup_append.mp hn).1, (List.nodup_append.mp hn).2.1,
    fun x hx hy => (List.nodup_append.mp hn).2.2 x hx x hy rfl⟩

/-- The leaves of a pairwise tree are among the slots' products, without repetition, and nonempty
when the tree exists. -/
theorem pairTree_leaves : ∀ (d : ℕ) (l : List (Option ℕ)), (blockLeaves l).Nodup →
    (oleaves (pairTree d l)).Nodup ∧ (∀ x ∈ oleaves (pairTree d l), x ∈ blockLeaves l) ∧
      ∀ u, pairTree d l = some u → u.leaves ≠ []
  | _, [], _ => by simp [pairTree, oleaves]
  | d, [o], _ => by
    cases o with
    | none => cases d <;> simp [pairTree, oleaves]
    | some i => cases d <;> simp [pairTree, oleaves, leaves, blockLeaves]
  | 0, _ :: _ :: _, _ => by simp [pairTree, oleaves]
  | d + 1, a :: b :: r, hn => by
    rw [pairTree_succ d (a :: b :: r) (by simp)]
    generalize a :: b :: r = l at hn ⊢
    obtain ⟨n₁, n₂, hdisj⟩ := pairTree_split_nodup hn (l.length / 2)
    obtain ⟨a₁, b₁, c₁⟩ := pairTree_leaves d (l.take (l.length / 2)) n₁
    obtain ⟨a₂, b₂, c₂⟩ := pairTree_leaves d (l.drop (l.length / 2)) n₂
    have hne : ∀ c ∈ optKid () (pairTree d (l.take (l.length / 2))) ++
        optKid () (pairTree d (l.drop (l.length / 2))), c.2.leaves ≠ [] := by
      intro c hc
      rcases List.mem_append.mp hc with h | h
      · exact optKid_ne_nil c₁ c h
      · exact optKid_ne_nil c₂ c h
    have hp := oleaves_mk () (optKid () (pairTree d (l.take (l.length / 2))) ++
      optKid () (pairTree d (l.drop (l.length / 2))))
    rw [kidsLeaves_append, kidsLeaves_optKid, kidsLeaves_optKid] at hp
    refine ⟨hp.nodup_iff.mpr (List.nodup_append.mpr ⟨a₁, a₂, ?_⟩), ?_, ?_⟩
    · intro x hx y hy hxy; subst hxy; exact hdisj x (b₁ x hx) (b₂ x hy)
    · intro x hx
      rw [blockLeaves_take_drop l (l.length / 2)]
      rcases List.mem_append.mp (hp.mem_iff.mp hx) with h | h
      · exact List.mem_append_left _ (b₁ x h)
      · exact List.mem_append_right _ (b₂ x h)
    · intro u hu; exact mk_ne_nil () hne hu

/-- With enough depth, the leaves of a pairwise tree are the slots' products. -/
theorem pairTree_complete : ∀ (d : ℕ) (l : List (Option ℕ)), l.length ≤ d + 1 →
    (oleaves (pairTree d l)).Perm (blockLeaves l)
  | _, [], _ => by simp [pairTree, oleaves, blockLeaves]
  | d, [o], _ => by cases o <;> cases d <;> simp [pairTree, oleaves, leaves, blockLeaves]
  | 0, _ :: _ :: _, h => by simp at h
  | d + 1, a :: b :: r, h => by
    rw [pairTree_succ d (a :: b :: r) (by simp)]
    have h2 : 2 ≤ (a :: b :: r).length := by simp
    generalize a :: b :: r = l at h h2 ⊢
    refine (oleaves_mk () _).trans ?_
    rw [kidsLeaves_append, kidsLeaves_optKid, kidsLeaves_optKid,
      blockLeaves_take_drop l (l.length / 2)]
    exact (pairTree_complete d _ (by simp; omega)).append (pairTree_complete d _ (by simp; omega))

theorem pairTree_kidsOK {d : ℕ} {l : List (Option ℕ)} (hn : (blockLeaves l).Nodup) :
    KidsOK (optKid () (pairTree d (l.take (l.length / 2))) ++
      optKid () (pairTree d (l.drop (l.length / 2)))) := by
  obtain ⟨n₁, n₂, hdisj⟩ := pairTree_split_nodup hn (l.length / 2)
  obtain ⟨a₁, b₁, c₁⟩ := pairTree_leaves d (l.take (l.length / 2)) n₁
  obtain ⟨a₂, b₂, c₂⟩ := pairTree_leaves d (l.drop (l.length / 2)) n₂
  refine ⟨?_, ?_⟩
  · rw [kidsLeaves_append, kidsLeaves_optKid, kidsLeaves_optKid]
    refine List.nodup_append.mpr ⟨a₁, a₂, ?_⟩
    intro x hx y hy hxy; subst hxy; exact hdisj x (b₁ x hx) (b₂ x hy)
  · intro c hc
    rcases List.mem_append.mp hc with h | h
    · exact optKid_ne_nil c₁ c h
    · exact optKid_ne_nil c₂ c h

theorem pairTree_restrict (S : ℕ → Bool) : ∀ (d : ℕ) (l : List (Option ℕ)), (blockLeaves l).Nodup →
    pairTree d (l.map (·.filter S)) = (pairTree d l).bind (restrict S)
  | d, [], _ => by cases d <;> rfl
  | d, [o], _ => by
    cases o with
    | none => cases d <;> rfl
    | some i => by_cases hi : S i = true <;> cases d <;> simp [pairTree, Option.filter, restrict, hi]
  | 0, _ :: _ :: _, _ => rfl
  | d + 1, a :: b :: r, hn => by
    rw [pairTree_succ d ((a :: b :: r).map (·.filter S)) (by simp),
      pairTree_succ d (a :: b :: r) (by simp)]
    generalize a :: b :: r = l at hn ⊢
    obtain ⟨n₁, n₂, _⟩ := pairTree_split_nodup hn (l.length / 2)
    rw [mk_restrict S () (pairTree_kidsOK hn), restrictKids_append, restrictKids_optKid,
      restrictKids_optKid, ← pairTree_restrict S d _ n₁, ← pairTree_restrict S d _ n₂,
      List.length_map, List.map_take, List.map_drop]

theorem pairTree_canon : ∀ (d : ℕ) (l : List (Option ℕ)), (blockLeaves l).Nodup →
    ∀ u, pairTree d l = some u → Canon u
  | _, [], _, u, h => by simp [pairTree] at h
  | d, [o], _, u, h => by
    cases o with
    | none => cases d <;> simp [pairTree] at h
    | some i => cases d <;> simp [pairTree] at h <;> subst h <;> simp [Canon]
  | 0, _ :: _ :: _, _, u, h => by simp [pairTree] at h
  | d + 1, a :: b :: r, hn, u, h => by
    rw [pairTree_succ d (a :: b :: r) (by simp)] at h
    generalize a :: b :: r = l at hn h
    obtain ⟨n₁, n₂, _⟩ := pairTree_split_nodup hn (l.length / 2)
    refine mk_canon () (pairTree_kidsOK hn) ?_ h
    intro c hc
    rcases List.mem_append.mp hc with h | h
    · exact optKid_canon (pairTree_canon d _ n₁) c h
    · exact optKid_canon (pairTree_canon d _ n₂) c h

/-! ## The normal form -/

/-- The normal form of binary summation trees. -/
def nfP : Term → Option (LTree Unit Unit)
  | .zero => none
  | .init => none
  | .hole => none
  | .blk t I => mk () (optKid () (nfP t) ++ optKid () (pairTree I.length I))
  | .add t u => mk () (optKid () (nfP t) ++ optKid () (nfP u))

theorem nfP_leaves : ∀ t : Term, (oleaves (nfP t)).Perm t.leaves
  | .zero => by simp [nfP, oleaves, Term.leaves]
  | .init => by simp [nfP, oleaves, Term.leaves]
  | .hole => by simp [nfP, oleaves, Term.leaves]
  | .blk t I => by
    simp only [nfP, Term.leaves]
    refine (oleaves_mk _ _).trans ?_
    rw [kidsLeaves_append, kidsLeaves_optKid, kidsLeaves_optKid]
    exact (nfP_leaves t).append (pairTree_complete _ _ (by omega))
  | .add t u => by
    simp only [nfP, Term.leaves]
    refine (oleaves_mk _ _).trans ?_
    rw [kidsLeaves_append, kidsLeaves_optKid, kidsLeaves_optKid]
    exact (nfP_leaves t).append (nfP_leaves u)

theorem pairTree_ne_nil : ∀ (d : ℕ) (l : List (Option ℕ)) (u : LTree Unit Unit),
    pairTree d l = some u → u.leaves ≠ []
  | d, [], u, h => by cases d <;> simp [pairTree] at h
  | d, [o], u, h => by
    cases o with
    | none => cases d <;> simp [pairTree] at h
    | some i => cases d <;> simp [pairTree] at h <;> subst h <;> simp [leaves]
  | 0, _ :: _ :: _, u, h => by simp [pairTree] at h
  | d + 1, a :: b :: r, u, h => by
    rw [pairTree_succ d (a :: b :: r) (by simp)] at h
    refine mk_ne_nil () ?_ h
    intro c hc
    rcases List.mem_append.mp hc with hc | hc
    · exact optKid_ne_nil (pairTree_ne_nil d _) c hc
    · exact optKid_ne_nil (pairTree_ne_nil d _) c hc

theorem nfP_ne_nil : ∀ (t : Term) (u : LTree Unit Unit), nfP t = some u → u.leaves ≠ []
  | .zero, u, h => by simp [nfP] at h
  | .init, u, h => by simp [nfP] at h
  | .hole, u, h => by simp [nfP] at h
  | .blk t I, u, h => by
    simp only [nfP] at h
    refine mk_ne_nil _ ?_ h
    intro c hc
    rcases List.mem_append.mp hc with hc | hc
    · exact optKid_ne_nil (nfP_ne_nil t) c hc
    · exact optKid_ne_nil (pairTree_ne_nil _ _) c hc
  | .add t₁ t₂, u, h => by
    simp only [nfP] at h
    refine mk_ne_nil _ ?_ h
    intro c hc
    rcases List.mem_append.mp hc with hc | hc
    · exact optKid_ne_nil (nfP_ne_nil t₁) c hc
    · exact optKid_ne_nil (nfP_ne_nil t₂) c hc

theorem blkP_kids_ok (t : Term) (I : List (Option ℕ)) (hn : (Term.blk t I).leaves.Nodup) :
    KidsOK (optKid () (nfP t) ++ optKid () (pairTree I.length I)) := by
  refine ⟨?_, ?_⟩
  · rw [kidsLeaves_append, kidsLeaves_optKid, kidsLeaves_optKid]
    exact ((nfP_leaves t).append (pairTree_complete _ _ (by omega))).nodup_iff.mpr hn
  · intro c hc
    have hnI : (blockLeaves I).Nodup := (List.nodup_append.mp hn).2.1
    rcases List.mem_append.mp hc with hc | hc
    · exact optKid_ne_nil (nfP_ne_nil t) c hc
    · exact optKid_ne_nil (pairTree_ne_nil _ _) c hc

theorem addP_kids_ok (t u : Term) (hn : (Term.add t u).leaves.Nodup) :
    KidsOK (optKid () (nfP t) ++ optKid () (nfP u)) := by
  refine ⟨?_, ?_⟩
  · rw [kidsLeaves_append, kidsLeaves_optKid, kidsLeaves_optKid]
    exact ((nfP_leaves t).append (nfP_leaves u)).nodup_iff.mpr hn
  · intro c hc
    rcases List.mem_append.mp hc with hc | hc
    · exact optKid_ne_nil (nfP_ne_nil t) c hc
    · exact optKid_ne_nil (nfP_ne_nil u) c hc

theorem nfP_restrict (S : ℕ → Bool) :
    ∀ t : Term, t.leaves.Nodup → nfP (t.restrict S) = (nfP t).bind (restrict S)
  | .zero, _ => rfl
  | .init, _ => rfl
  | .hole, _ => rfl
  | .blk t I, hn => by
    have hnt : t.leaves.Nodup := (List.nodup_append.mp hn).1
    have hnI : (blockLeaves I).Nodup := (List.nodup_append.mp hn).2.1
    simp only [Term.restrict, nfP]
    rw [mk_restrict S () (blkP_kids_ok t I hn), restrictKids_append, restrictKids_optKid,
      restrictKids_optKid, nfP_restrict S t hnt, ← pairTree_restrict S _ I hnI, List.length_map]
  | .add t u, hn => by
    have h1 : t.leaves.Nodup := (List.nodup_append.mp hn).1
    have h2 : u.leaves.Nodup := (List.nodup_append.mp hn).2.1
    simp only [Term.restrict, nfP]
    rw [mk_restrict S () (addP_kids_ok t u hn), restrictKids_append, restrictKids_optKid,
      restrictKids_optKid, nfP_restrict S t h1, nfP_restrict S u h2]

theorem nfP_canon : ∀ t : Term, t.leaves.Nodup → ∀ u, nfP t = some u → Canon u
  | .zero, _, u, h => by simp [nfP] at h
  | .init, _, u, h => by simp [nfP] at h
  | .hole, _, u, h => by simp [nfP] at h
  | .blk t I, hn, u, h => by
    have hnt : t.leaves.Nodup := (List.nodup_append.mp hn).1
    have hnI : (blockLeaves I).Nodup := (List.nodup_append.mp hn).2.1
    simp only [nfP] at h
    refine mk_canon _ (blkP_kids_ok t I hn) ?_ h
    intro c hc
    rcases List.mem_append.mp hc with hc | hc
    · exact optKid_canon (nfP_canon t hnt) c hc
    · exact optKid_canon (pairTree_canon _ _ hnI) c hc
  | .add t₁ t₂, hn, u, h => by
    have h1 : t₁.leaves.Nodup := (List.nodup_append.mp hn).1
    have h2 : t₂.leaves.Nodup := (List.nodup_append.mp hn).2.1
    simp only [nfP] at h
    refine mk_canon _ (addP_kids_ok t₁ t₂ hn) ?_ h
    intro c hc
    rcases List.mem_append.mp hc with hc | hc
    · exact optKid_canon (nfP_canon t₁ h1) c hc
    · exact optKid_canon (nfP_canon t₂ h2) c hc

/-- The normal form of binary summation trees is a normal-form function. -/
def pairNF : NormalForm Unit Unit where
  nf := nfP
  leaves := nfP_leaves
  restrict S t h := nfP_restrict S t h
  canon := nfP_canon

theorem mk_single (o : Option (LTree Unit Unit)) : mk () (optKid () o) = o := by
  cases o <;> rfl

/-- **The `c`-split law in normal form**: a block's accumulator can be moved into a separate
addition, `blk(t, I) = t ⊕ blk(0, I)`. -/
theorem nfP_csplit (t : Term) (I : List (Option ℕ)) :
    nfP (.blk t I) = nfP (.add t (.blk .zero I)) := by
  show mk () (optKid () (nfP t) ++ optKid () (pairTree I.length I)) =
    mk () (optKid () (nfP t) ++ optKid () (mk () (optKid () none ++ optKid () (pairTree I.length I))))
  rw [show optKid () (none : Option (LTree Unit Unit)) = [] from rfl, List.nil_append, mk_single]

/-! ## Soundness -/

/-- The laws of binary summation trees: besides `RoundLaws`, a block with `K` slots rounds the sum
of its accumulator and the value of the pairwise tree of its slots. -/
structure PairAlg (m : Machine α β) (K : ℕ) extends RoundLaws m where
  block : ∀ p, Adm p → ∀ d (I : List (Option ℕ)), I.length = K → good d →
    m.block d (I.map (Option.map p)) =
      (evCRO m rnd p m.zero (pairTree I.length I)).bind fun w => rnd (m.val d + m.val w)

variable {m : Machine α β} {K : ℕ}

theorem evCRO_good (A : RoundLaws m) (p : ℕ → α) (hp : A.Adm p) :
    ∀ (o : Option (LTree Unit Unit)) (w : β), evCRO m A.rnd p m.zero o = some w → A.good w
  | none, w, h => by simp only [evCRO, Option.some.injEq] at h; subst h; exact A.zero_good
  | some U, w, h => evCR_good A p hp U w h

/-- **Soundness of the pairwise laws.** On admissible inputs every term with blocks of `K` slots,
each product once, evaluates from the zero accumulator as its normal form. -/
theorem pair_sound (A : PairAlg m K) (p : ℕ → α) (hp : A.Adm p) :
    ∀ t : Term, TermWF K t → t.leaves.Nodup → eval m p m.zero m.zero t = evCRO m A.rnd p m.zero (nfP t)
  | .zero, _, _ => rfl
  | .init, _, _ => rfl
  | .hole, hw, _ => absurd hw (by simp [TermWF])
  | .blk t I, hw, hn => by
    obtain ⟨hwt, hlen⟩ := hw
    have hnt : t.leaves.Nodup := (List.nodup_append.mp hn).1
    have ih : eval m p m.zero m.zero t = evCRO m A.rnd p m.zero (nfP t) := pair_sound A p hp t hwt hnt
    have hval0 : m.val m.zero = 0 := m.val_zero
    show (eval m p m.zero m.zero t).bind (fun d => m.block d (I.map (Option.map p))) =
      evCRO m A.rnd p m.zero (mk () (optKid () (nfP t) ++ optKid () (pairTree I.length I)))
    rw [ih]
    have hblk := A.block p hp
    have hgd := evCRO_good A.toRoundLaws p hp (nfP t)
    have hgw := evCRO_good A.toRoundLaws p hp (pairTree I.length I)
    cases hq : nfP t with
    | none =>
      cases hr : pairTree I.length I with
      | none =>
        show (some m.zero).bind _ = some m.zero
        rw [Option.bind_some, hblk m.zero I hlen A.zero_good, hr]
        show A.rnd (m.val m.zero + m.val m.zero) = some m.zero
        rw [hval0, Rat.add_zero]; exact A.rnd_zero
      | some V =>
        show (some m.zero).bind _ = evCR m A.rnd p V
        rw [Option.bind_some, hblk m.zero I hlen A.zero_good, hr]
        show (evCR m A.rnd p V).bind _ = evCR m A.rnd p V
        have hg := evCR_good A.toRoundLaws p hp V
        cases h : evCR m A.rnd p V with
        | none => rfl
        | some w =>
          simp only [Option.bind_some]
          rw [hval0, Rat.zero_add]; exact A.rnd_val w (hg w h)
    | some U =>
      have hgU := evCR_good A.toRoundLaws p hp U
      cases hr : pairTree I.length I with
      | none =>
        show (evCR m A.rnd p U).bind _ = evCR m A.rnd p U
        cases h : evCR m A.rnd p U with
        | none => rfl
        | some d =>
          simp only [Option.bind_some]
          rw [hblk d I hlen (hgU d h), hr]
          show A.rnd (m.val d + m.val m.zero) = some d
          rw [hval0, Rat.add_zero]; exact A.rnd_val d (hgU d h)
      | some V =>
        show (evCR m A.rnd p U).bind _ = (sumCR m A.rnd p (sortKids [((), U), ((), V)])).bind A.rnd
        rw [sumCR_perm A.rnd p (sortKids_perm _)]
        simp only [sumCR]
        cases h : evCR m A.rnd p U with
        | none => rfl
        | some d =>
          simp only [Option.bind_some]
          rw [hblk d I hlen (hgU d h), hr]
          show (evCR m A.rnd p V).bind _ = _
          cases evCR m A.rnd p V <;> simp [Rat.add_zero]
  | .add t₁ t₂, hw, hn => by
    obtain ⟨hw₁, hw₂⟩ := hw
    have n₁ : t₁.leaves.Nodup := (List.nodup_append.mp hn).1
    have n₂ : t₂.leaves.Nodup := (List.nodup_append.mp hn).2.1
    have ih₁ : eval m p m.zero m.zero t₁ = evCRO m A.rnd p m.zero (nfP t₁) := pair_sound A p hp t₁ hw₁ n₁
    have ih₂ : eval m p m.zero m.zero t₂ = evCRO m A.rnd p m.zero (nfP t₂) := pair_sound A p hp t₂ hw₂ n₂
    show (eval m p m.zero m.zero t₁).bind (fun x => (eval m p m.zero m.zero t₂).bind
      fun y => m.add x y) = evCRO m A.rnd p m.zero (mk () (optKid () (nfP t₁) ++ optKid () (nfP t₂)))
    rw [ih₁, ih₂]
    have hval0 : m.val m.zero = 0 := m.val_zero
    cases hq₁ : nfP t₁ with
    | none =>
      cases hq₂ : nfP t₂ with
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
      cases hq₂ : nfP t₂ with
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

/-- **Completeness for terms with binary summation trees.** -/
theorem pair_term_complete (A : PairAlg m K) (ins3 : List (ℕ → α))
    (hadm : ∀ q ∈ ins3, ∀ g : ℕ → ℕ, A.Adm (fun x => q (g x)))
    (hnd3 : (codes3Unit.map fun κ => ins3.map fun q => evCR m A.rnd q (κ.realize 0 1 2)).Nodup)
    (t₁ t₂ : Term) (hw₁ : TermWF K t₁) (hw₂ : TermWF K t₂) (n₁ : t₁.leaves.Nodup)
    (n₂ : t₂.leaves.Nodup) (hl : ∀ i, i ∈ t₁.leaves ↔ i ∈ t₂.leaves) (hne : nfP t₁ ≠ nfP t₂) :
    ∃ (s : List ℕ) (q : ℕ → α), s.length ≤ 3 ∧ (∀ i, i ∉ s → q i = A.z) ∧
      (∃ p, A.Adm p ∧ ∀ i, q i = A.z ∨ q i = p i) ∧
      eval m q m.zero m.zero t₁ ≠ eval m q m.zero m.zero t₂ :=
  term_complete pairNF A.slot A.Adm (evCRO m A.rnd · m.zero)
    (fun t hw hn p hp => pair_sound A p hp t hw hn)
    (unit_base pairNF A.toRoundLaws ins3 hadm (by
      have := sep_of_table codes3Unit mem_codes3Unit (fun _ => true) ins3
        (fun κ q => evCR m A.rnd q (κ.realize 0 1 2))
        (by rw [List.filter_eq_self.mpr (fun _ _ => rfl)]; exact hnd3)
      exact fun κ₁ κ₂ h => this κ₁ κ₂ rfl rfl h))
    t₁ t₂ hw₁ hw₂ n₁ n₂ hl hne

end MMAlgebra
