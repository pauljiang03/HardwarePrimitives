import MMAlgebra.TermComplete
import MMAlgebra.Shapes

/-! # The rigid algebra: normal forms of terms and their soundness

On the rigid matrix multipliers (the Tensor Cores, CDNA 3, SFMA) the normal form of a term
(`nfR`) is a labeled tree: a block FMA is a node labeled `true` whose children are its accumulator
subterm (edge `true`) and its products (leaves on edges `false`), an addition is a node labeled
`false` with two children, a subterm without products disappears, and a node left with one child is
that child (an empty block passes its accumulator through, a one-product block from zero is a leaf,
an addition of a zero is its other operand).

`evR` evaluates such a tree on a machine. `rigid_sound`: on a machine with the laws of a rigid
multiplier (`RigidAlg`: a block depends on its slots as a multiset, an empty block passes a good
value through, addition is commutative with `+0` as a unit on good values, and every result is
good), every term evaluates from the zero accumulator as its normal form: the laws are sound.
`nfR_valid`: normal forms satisfy the shape constraints `rvalid` (at most one accumulator child,
products are leaves, additions have two children). Hardware-independent. -/

local notation "ℕ" => Nat

namespace MMAlgebra

open LTree

variable {α β : Type}

/-- The labels of the rigid normal form: block nodes `true`, addition nodes `false`, accumulator
edges `true`, product and operand edges `false`. -/
def rigidLabels : Labels Bool Bool := ⟨true, false, true, false, false⟩

/-- The rigid normal form. -/
abbrev nfR : Term → Option (LTree Bool Bool) := nfL rigidLabels

/-- The products of a block node: its leaf children on product edges. -/
def prodKids : List (Bool × LTree Bool Bool) → List ℕ
  | [] => []
  | (false, .leaf i) :: cs => i :: prodKids cs
  | _ :: cs => prodKids cs

section Eval
variable (m : Machine α β) (K : ℕ) (p : ℕ → α)

mutual
/-- The value of a rigid normal form: a leaf is a one-product block from zero, a block node runs
one block FMA from the value of its accumulator child, an addition node adds its two children. -/
def evR : LTree Bool Bool → Option β
  | .leaf i => m.block m.zero (some (p i) :: List.replicate (K - 1) none)
  | .node true cs => (evC cs).bind fun d =>
      m.block d ((prodKids cs).map (fun i => some (p i)) ++
        List.replicate (K - (prodKids cs).length) none)
  | .node false cs => evA cs
/-- The value of the accumulator child, or zero. -/
def evC : List (Bool × LTree Bool Bool) → Option β
  | [] => some m.zero
  | (true, t) :: _ => evR t
  | (false, _) :: cs => evC cs
/-- The sum of two children. -/
def evA : List (Bool × LTree Bool Bool) → Option β
  | [(_, t₁), (_, t₂)] => (evR t₁).bind fun x => (evR t₂).bind fun y => m.add x y
  | _ => none
end

/-- The value of an optional normal form: zero for none. -/
def evRO : Option (LTree Bool Bool) → Option β
  | none => some m.zero
  | some U => evR m K p U

end Eval

/-- The laws of a rigid multiplier used for terms: those used for chains, a commutative addition
with `+0` as a unit on good values, and good results. -/
structure RigidAlg (m : Machine α β) (K : ℕ) extends RigidLaws m K where
  add_comm : ∀ x y, m.add x y = m.add y x
  add_zero : ∀ x, good x → m.add x m.zero = some x
  block_good : ∀ d ps o, m.block d ps = some o → good o
  add_good : ∀ x y o, m.add x y = some o → good o

variable {m : Machine α β} {K : ℕ}

theorem evR_good (A : RigidAlg m K) (p : ℕ → α) :
    ∀ (U : LTree Bool Bool) (o : β), evR m K p U = some o → A.good o
  | .leaf i, o, h => A.block_good _ _ _ h
  | .node true cs, o, h => by
    simp only [evR] at h
    cases hc : evC m K p cs with
    | none => rw [hc] at h; cases h
    | some d => rw [hc] at h; exact A.block_good _ _ _ h
  | .node false cs, o, h => by
    simp only [evR] at h
    match cs, h with
    | [(_, t₁), (_, t₂)], h =>
      simp only [evA] at h
      cases h1 : evR m K p t₁ with
      | none => rw [h1] at h; cases h
      | some x =>
        cases h2 : evR m K p t₂ with
        | none => rw [h1, h2] at h; cases h
        | some y => rw [h1, h2] at h; exact A.add_good _ _ _ h

theorem evRO_good (A : RigidAlg m K) (p : ℕ → α) :
    ∀ (o : Option (LTree Bool Bool)) (w : β), evRO m K p o = some w → A.good w
  | none, w, h => by simp only [evRO, Option.some.injEq] at h; subst h; exact A.zero_good
  | some U, w, h => evR_good A p U w h

/-! ## Children lists -/

theorem evC_eq (p : ℕ → α) : ∀ cs : List (Bool × LTree Bool Bool),
    evC m K p cs = match cs.filter (fun c => c.1) with
      | [] => some m.zero
      | c :: _ => evR m K p c.2
  | [] => rfl
  | (true, t) :: cs => by simp [evC]
  | (false, t) :: cs => by simp only [evC, List.filter_cons]; exact evC_eq p cs

theorem evC_perm (p : ℕ → α) {cs ds : List (Bool × LTree Bool Bool)} (h : cs.Perm ds)
    (h1 : (cs.filter fun c => c.1).length ≤ 1) : evC m K p cs = evC m K p ds := by
  rw [evC_eq, evC_eq]
  have hf := h.filter (fun c => c.1)
  generalize cs.filter (fun c => c.1) = F₁ at hf h1 ⊢
  generalize ds.filter (fun c => c.1) = F₂ at hf ⊢
  match F₁, F₂, hf, h1 with
  | [], [], _, _ => rfl
  | [a], [b], hf, _ => rw [List.perm_singleton.mp hf.symm]
  | [], _ :: _, hf, _ => exact absurd hf.length_eq (by simp)
  | _ :: _, [], hf, _ => exact absurd hf.length_eq (by simp)
  | _ :: _ :: _, _, _, h1 => simp at h1
  | [_], _ :: _ :: _, hf, _ => exact absurd hf.length_eq (by simp)

theorem prodKids_eq : ∀ cs : List (Bool × LTree Bool Bool),
    prodKids cs = cs.filterMap fun c => match c with
      | (false, .leaf i) => some i
      | _ => none
  | [] => rfl
  | (false, .leaf i) :: cs => by simp [prodKids, prodKids_eq cs]
  | (false, .node l ks) :: cs => by simp [prodKids, prodKids_eq cs]
  | (true, t) :: cs => by simp [prodKids, prodKids_eq cs]

theorem prodKids_perm {cs ds : List (Bool × LTree Bool Bool)} (h : cs.Perm ds) :
    (prodKids cs).Perm (prodKids ds) := by
  rw [prodKids_eq, prodKids_eq]; exact h.filterMap _

theorem prodKids_optKid_true (o : Option (LTree Bool Bool)) : prodKids (optKid true o) = [] := by
  cases o <;> rfl

theorem prodKids_append (cs ds : List (Bool × LTree Bool Bool)) :
    prodKids (cs ++ ds) = prodKids cs ++ prodKids ds := by
  rw [prodKids_eq, prodKids_eq, prodKids_eq, List.filterMap_append]

theorem prodKids_leafs (l : List ℕ) :
    prodKids (l.map fun i => ((false, leaf i) : Bool × LTree Bool Bool)) = l := by
  induction l with
  | nil => rfl
  | cons i l ih => simp [prodKids, ih]

theorem filter_fst_leafs (l : List ℕ) :
    (l.map fun i => ((false, leaf i) : Bool × LTree Bool Bool)).filter (fun c => c.1) = [] := by
  induction l with
  | nil => rfl
  | cons i l ih => simp [ih]

/-- A block's slots are a permutation of its products followed by empty slots. -/
theorem slots_perm (I : List (Option ℕ)) :
    I.Perm ((blockLeaves I).map some ++ List.replicate (I.length - (blockLeaves I).length) none) := by
  rw [List.perm_iff_count]
  intro o
  have h1 := count_none_blockLeaves I
  cases o with
  | none =>
    simp only [List.count_append, List.count_replicate]
    have : ((blockLeaves I).map some).count (none : Option ℕ) = 0 := by
      apply List.count_eq_zero.mpr; simp
    rw [this]; simp; omega
  | some i =>
    simp only [List.count_append, List.count_replicate]
    rw [count_blockLeaves]
    have : ((blockLeaves I).map some).count (some i) = (blockLeaves I).count i := by
      generalize blockLeaves I = l
      induction l with
      | nil => rfl
      | cons j l ih => by_cases hj : j = i <;> simp [hj, ih]
    rw [this]; simp

theorem two_perm {γ : Type} {a b : γ} {l : List γ} (h : l.Perm [a, b]) : l = [a, b] ∨ l = [b, a] := by
  have hl := h.length_eq
  match l, hl, h with
  | [x, y], _, h =>
    have hx : x ∈ [a, b] := h.subset (by simp)
    rcases List.mem_cons.mp hx with hxa | hxb
    · rw [hxa] at h
      have := List.perm_singleton.mp ((List.perm_cons a).mp h)
      left; rw [hxa, this]
    · have hxb' : x = b := by simpa using hxb
      rw [hxb'] at h
      have h' := h.trans (List.Perm.swap b a [])
      have := List.perm_singleton.mp ((List.perm_cons b).mp h')
      right; rw [hxb', this]

/-! ## Soundness -/

theorem evR_block_bind (A : RigidAlg m K) (o : Option β)
    (ho : ∀ w, o = some w → A.good w) :
    o.bind (fun d => m.block d (List.replicate K none)) = o := by
  cases o with
  | none => rfl
  | some d => simp only [Option.bind_some]; exact A.pass d (ho d rfl)

/-- **Soundness of the rigid laws.** Every term with blocks of `K` slots, each product once,
evaluates from the zero accumulator as its normal form. -/
theorem rigid_sound (A : RigidAlg m K) (p : ℕ → α) :
    ∀ t : Term, TermWF K t → t.leaves.Nodup → eval m p m.zero m.zero t = evRO m K p (nfR t)
  | .zero, _, _ => rfl
  | .init, _, _ => rfl
  | .hole, hw, _ => absurd hw (by simp [TermWF])
  | .blk t I, hw, hn => by
    obtain ⟨hwt, hlen⟩ := hw
    have hnt : t.leaves.Nodup := (List.nodup_append.mp hn).1
    have ih : eval m p m.zero m.zero t = evRO m K p (nfL rigidLabels t) := rigid_sound A p t hwt hnt
    have hslot := (slots_perm I).map (Option.map p)
    rw [hlen] at hslot
    simp only [List.map_append, List.map_map, List.map_replicate, Option.map_none] at hslot
    have hblk : ∀ d, m.block d (I.map (Option.map p)) =
        m.block d ((blockLeaves I).map (fun i => some (p i)) ++
          List.replicate (K - (blockLeaves I).length) none) := fun d => by
      rw [A.perm d hslot]; rfl
    show (eval m p m.zero m.zero t).bind (fun d => m.block d (I.map (Option.map p))) =
      evRO m K p (mk true (optKid true (nfL rigidLabels t) ++
        (blockLeaves I).map fun i => ((false, leaf i) : Bool × LTree Bool Bool)))
    rw [ih]
    simp only [hblk]
    generalize blockLeaves I = bl
    cases hq : nfL rigidLabels t with
    | none =>
      show (some m.zero).bind _ = evRO m K p (mk true ([] ++ _))
      rw [Option.bind_some, List.nil_append]
      match bl with
      | [] =>
        show m.block m.zero ([] ++ List.replicate (K - 0) none) = some m.zero
        rw [List.nil_append, Nat.sub_zero]
        exact A.pass _ A.zero_good
      | [i] => rfl
      | i :: j :: rest =>
        change m.block m.zero _ = (evC m K p (sortKids ((i :: j :: rest).map
          fun i => ((false, leaf i) : Bool × LTree Bool Bool)))).bind _
        have hc : evC m K p (sortKids ((i :: j :: rest).map
            fun i => ((false, leaf i) : Bool × LTree Bool Bool))) = some m.zero := by
          have hf := filter_fst_leafs (i :: j :: rest)
          rw [← evC_perm p (sortKids_perm _).symm (by rw [hf]; simp), evC_eq, hf]
        rw [hc, Option.bind_some]
        have hp := prodKids_perm (sortKids_perm ((i :: j :: rest).map
          fun i => ((false, leaf i) : Bool × LTree Bool Bool)))
        rw [prodKids_leafs] at hp
        rw [hp.length_eq]
        exact A.perm _ ((hp.map _).symm.append (List.Perm.refl _))
    | some u =>
      show (evR m K p u).bind _ = evRO m K p (mk true ([(true, u)] ++ _))
      rw [List.singleton_append]
      match bl with
      | [] =>
        show (evR m K p u).bind (fun d => m.block d ([] ++ List.replicate (K - 0) none)) = evR m K p u
        simp only [List.nil_append, Nat.sub_zero]
        exact evR_block_bind A _ (evR_good A p u)
      | i :: rest =>
        change (evR m K p u).bind _ = (evC m K p (sortKids ((true, u) :: (i :: rest).map
          fun i => ((false, leaf i) : Bool × LTree Bool Bool)))).bind _
        have hc : evC m K p (sortKids ((true, u) :: (i :: rest).map
            fun i => ((false, leaf i) : Bool × LTree Bool Bool))) = evR m K p u := by
          rw [← evC_perm p (sortKids_perm _).symm (by simp)]
          rfl
        rw [hc]
        have hp := prodKids_perm (sortKids_perm ((true, u) :: (i :: rest).map
          fun i => ((false, leaf i) : Bool × LTree Bool Bool)))
        have hp' : prodKids ((true, u) :: (i :: rest).map
            fun i => ((false, leaf i) : Bool × LTree Bool Bool)) = i :: rest := by
          show prodKids ((i :: rest).map fun i => ((false, leaf i) : Bool × LTree Bool Bool)) = _
          exact prodKids_leafs _
        rw [hp'] at hp
        congr 1
        funext d
        rw [hp.length_eq]
        exact A.perm _ ((hp.map _).symm.append (List.Perm.refl _))
  | .add t₁ t₂, hw, hn => by
    obtain ⟨hw₁, hw₂⟩ := hw
    have n₁ : t₁.leaves.Nodup := (List.nodup_append.mp hn).1
    have n₂ : t₂.leaves.Nodup := (List.nodup_append.mp hn).2.1
    have ih₁ : eval m p m.zero m.zero t₁ = evRO m K p (nfL rigidLabels t₁) := rigid_sound A p t₁ hw₁ n₁
    have ih₂ : eval m p m.zero m.zero t₂ = evRO m K p (nfL rigidLabels t₂) := rigid_sound A p t₂ hw₂ n₂
    show (eval m p m.zero m.zero t₁).bind (fun x => (eval m p m.zero m.zero t₂).bind
      fun y => m.add x y) = evRO m K p (mk false (optKid false (nfL rigidLabels t₁) ++
        optKid false (nfL rigidLabels t₂)))
    rw [ih₁, ih₂]
    cases hq₁ : nfL rigidLabels t₁ with
    | none =>
      cases hq₂ : nfL rigidLabels t₂ with
      | none =>
        show (some m.zero).bind (fun x => (some m.zero).bind fun y => m.add x y) = some m.zero
        exact A.add_zero _ A.zero_good
      | some V =>
        show (some m.zero).bind (fun x => (evR m K p V).bind fun y => m.add x y) = evR m K p V
        rw [Option.bind_some]
        have := evR_good A p V
        cases h : evR m K p V with
        | none => rfl
        | some y => simp only [Option.bind_some]; rw [A.add_comm]; exact A.add_zero y (this y h)
    | some U =>
      cases hq₂ : nfL rigidLabels t₂ with
      | none =>
        show (evR m K p U).bind (fun x => (some m.zero).bind fun y => m.add x y) = evR m K p U
        have := evR_good A p U
        cases h : evR m K p U with
        | none => rfl
        | some x => simp only [Option.bind_some]; exact A.add_zero x (this x h)
      | some V =>
        show (evR m K p U).bind (fun x => (evR m K p V).bind fun y => m.add x y) =
          evA m K p (sortKids [(false, U), (false, V)])
        rcases two_perm (sortKids_perm [(false, U), (false, V)]) with h | h <;> rw [h] <;>
          simp only [evA]
        cases evR m K p U <;> cases evR m K p V <;> simp [A.add_comm]

/-! ## Validity of normal forms -/

/-- Every child on a product edge is a leaf. -/
def kidsLeafProd (cs : List (Bool × LTree Bool Bool)) : Bool :=
  cs.all fun c => c.1 || match c.2 with
    | .leaf _ => true
    | .node _ _ => false

mutual
/-- The shape constraints of rigid normal forms: a block node has at most one accumulator child
and its products are leaves; an addition node has two children on operand edges. -/
def rvalid : LTree Bool Bool → Bool
  | .leaf _ => true
  | .node true cs => decide ((cs.filter fun c => c.1).length ≤ 1) && kidsLeafProd cs && rvalidKids cs
  | .node false cs => cs.length == 2 && cs.all (fun c => !c.1) && rvalidKids cs
/-- Every child is valid. -/
def rvalidKids : List (Bool × LTree Bool Bool) → Bool
  | [] => true
  | (_, t) :: cs => rvalid t && rvalidKids cs
end

theorem rvalidKids_eq : ∀ cs : List (Bool × LTree Bool Bool),
    rvalidKids cs = cs.all fun c => rvalid c.2
  | [] => rfl
  | (e, t) :: cs => by simp [rvalidKids, rvalidKids_eq cs]

theorem rvalidKids_perm {cs ds : List (Bool × LTree Bool Bool)} (h : cs.Perm ds) :
    rvalidKids cs = rvalidKids ds := by
  rw [rvalidKids_eq, rvalidKids_eq]
  apply Bool.eq_iff_iff.mpr
  simp only [List.all_eq_true]
  exact ⟨fun h' c hc => h' c (h.symm.subset hc), fun h' c hc => h' c (h.subset hc)⟩

theorem kidsLeafProd_perm {cs ds : List (Bool × LTree Bool Bool)} (h : cs.Perm ds) :
    kidsLeafProd cs = kidsLeafProd ds := by
  unfold kidsLeafProd
  apply Bool.eq_iff_iff.mpr
  simp only [List.all_eq_true]
  exact ⟨fun h' c hc => h' c (h.symm.subset hc), fun h' c hc => h' c (h.subset hc)⟩

/-- **Normal forms are valid.** -/
theorem nfR_valid : ∀ (t : Term) (U : LTree Bool Bool), nfL rigidLabels t = some U → rvalid U = true
  | .zero, U, h => by simp [nfL] at h
  | .init, U, h => by simp [nfL] at h
  | .hole, U, h => by simp [nfL] at h
  | .blk t I, U, h => by
    have ih := nfR_valid t
    change mk true (optKid true (nfL rigidLabels t) ++
      (blockLeaves I).map fun i => ((false, leaf i) : Bool × LTree Bool Bool)) = some U at h
    have hkids : ∀ c ∈ optKid true (nfL rigidLabels t) ++
        (blockLeaves I).map (fun i => ((false, leaf i) : Bool × LTree Bool Bool)),
        rvalid c.2 = true ∧ (c.1 = true ∨ ∃ i, c.2 = leaf i) := by
      intro c hc
      rcases List.mem_append.mp hc with hc | hc
      · cases hq : nfL rigidLabels t with
        | none => rw [hq] at hc; simp [optKid] at hc
        | some u =>
          rw [hq] at hc; simp only [optKid, List.mem_singleton] at hc; subst hc
          exact ⟨ih u hq, Or.inl rfl⟩
      · obtain ⟨i, _, rfl⟩ := List.mem_map.mp hc
        exact ⟨by simp [rvalid], Or.inr ⟨i, rfl⟩⟩
    have hf : ((optKid true (nfL rigidLabels t) ++
        (blockLeaves I).map fun i => ((false, leaf i) : Bool × LTree Bool Bool)).filter
          fun c => c.1).length ≤ 1 := by
      rw [List.filter_append, filter_fst_leafs]
      cases nfL rigidLabels t <;> simp [optKid]
    generalize optKid true (nfL rigidLabels t) ++
      (blockLeaves I).map (fun i => ((false, leaf i) : Bool × LTree Bool Bool)) = ks at h hkids hf
    match ks, h, hkids, hf with
    | [(e, w)], h, hkids, _ =>
      simp only [mk, Option.some.injEq] at h
      rw [← h]
      exact (hkids (e, w) (by simp)).1
    | k₁ :: k₂ :: ks, h, hkids, hf =>
      simp only [mk, Option.some.injEq] at h; subst h
      have hp := sortKids_perm (k₁ :: k₂ :: ks)
      simp only [rvalid, Bool.and_eq_true, decide_eq_true_eq]
      refine ⟨⟨?_, ?_⟩, ?_⟩
      · rw [(hp.filter _).length_eq]; exact hf
      · rw [kidsLeafProd_perm hp]
        unfold kidsLeafProd
        simp only [List.all_eq_true, Bool.or_eq_true]
        intro c hc
        rcases (hkids c hc).2 with h1 | ⟨i, h2⟩
        · exact Or.inl h1
        · right; rw [h2]
      · rw [rvalidKids_perm hp, rvalidKids_eq]
        simp only [List.all_eq_true]
        intro c hc; exact (hkids c hc).1
  | .add t₁ t₂, U, h => by
    have ih₁ := nfR_valid t₁
    have ih₂ := nfR_valid t₂
    change mk false (optKid false (nfL rigidLabels t₁) ++ optKid false (nfL rigidLabels t₂)) =
      some U at h
    cases hq₁ : nfL rigidLabels t₁ with
    | none =>
      cases hq₂ : nfL rigidLabels t₂ with
      | none => rw [hq₁, hq₂] at h; simp [optKid, mk] at h
      | some V => rw [hq₁, hq₂] at h; simp only [optKid, List.nil_append, mk, Option.some.injEq] at h
                  subst h; exact ih₂ V hq₂
    | some W =>
      cases hq₂ : nfL rigidLabels t₂ with
      | none => rw [hq₁, hq₂] at h; simp only [optKid, List.append_nil, mk, Option.some.injEq] at h
                subst h; exact ih₁ W hq₁
      | some V =>
        rw [hq₁, hq₂] at h
        simp only [optKid, List.singleton_append, mk, Option.some.injEq] at h
        subst h
        rcases two_perm (sortKids_perm [(false, W), (false, V)]) with h | h <;> rw [h] <;>
          simp [rvalid, rvalidKids, ih₁ W hq₁, ih₂ V hq₂]

/-! ## Block sizes of normal forms -/

mutual
/-- Every block node has at most `K` products: the normal form of a term whose blocks have `K`
slots. -/
def rfits (K : ℕ) : LTree Bool Bool → Bool
  | .leaf _ => true
  | .node true cs => decide ((prodKids cs).length ≤ K) && rfitsKids K cs
  | .node false cs => rfitsKids K cs
/-- Every child fits. -/
def rfitsKids (K : ℕ) : List (Bool × LTree Bool Bool) → Bool
  | [] => true
  | (_, t) :: cs => rfits K t && rfitsKids K cs
end

theorem rfitsKids_eq (K : ℕ) : ∀ cs : List (Bool × LTree Bool Bool),
    rfitsKids K cs = cs.all fun c => rfits K c.2
  | [] => rfl
  | (e, t) :: cs => by simp [rfitsKids, rfitsKids_eq K cs]

theorem rfitsKids_perm (K : ℕ) {cs ds : List (Bool × LTree Bool Bool)} (h : cs.Perm ds) :
    rfitsKids K cs = rfitsKids K ds := by
  rw [rfitsKids_eq, rfitsKids_eq]
  apply Bool.eq_iff_iff.mpr
  simp only [List.all_eq_true]
  exact ⟨fun h' c hc => h' c (h.symm.subset hc), fun h' c hc => h' c (h.subset hc)⟩

theorem length_blockLeaves_le (I : List (Option ℕ)) : (blockLeaves I).length ≤ I.length := by
  unfold blockLeaves; exact List.length_filterMap_le _ _

/-- **Normal forms of terms with `K`-slot blocks fit `K`.** -/
theorem nfR_fits (K : ℕ) : ∀ (t : Term) (U : LTree Bool Bool), TermWF K t →
    nfL rigidLabels t = some U → rfits K U = true
  | .zero, U, _, h => by simp [nfL] at h
  | .init, U, _, h => by simp [nfL] at h
  | .hole, U, _, h => by simp [nfL] at h
  | .blk t I, U, hw, h => by
    have ih := nfR_fits K t
    change mk true (optKid true (nfL rigidLabels t) ++
      (blockLeaves I).map fun i => ((false, leaf i) : Bool × LTree Bool Bool)) = some U at h
    have hkids : ∀ c ∈ optKid true (nfL rigidLabels t) ++
        (blockLeaves I).map (fun i => ((false, leaf i) : Bool × LTree Bool Bool)),
        rfits K c.2 = true := by
      intro c hc
      rcases List.mem_append.mp hc with hc | hc
      · cases hq : nfL rigidLabels t with
        | none => rw [hq] at hc; simp [optKid] at hc
        | some u =>
          rw [hq] at hc; simp only [optKid, List.mem_singleton] at hc; subst hc
          exact ih u hw.1 hq
      · obtain ⟨i, _, rfl⟩ := List.mem_map.mp hc
        simp [rfits]
    have hn : (prodKids (optKid true (nfL rigidLabels t) ++
        (blockLeaves I).map fun i => ((false, leaf i) : Bool × LTree Bool Bool))).length ≤ K := by
      rw [prodKids_append, prodKids_optKid_true, prodKids_leafs, List.nil_append, ← hw.2]
      exact length_blockLeaves_le I
    generalize optKid true (nfL rigidLabels t) ++
      (blockLeaves I).map (fun i => ((false, leaf i) : Bool × LTree Bool Bool)) = ks at h hkids hn
    match ks, h, hkids, hn with
    | [(e, w)], h, hkids, _ =>
      simp only [mk, Option.some.injEq] at h
      rw [← h]
      exact hkids (e, w) (by simp)
    | k₁ :: k₂ :: ks, h, hkids, hn =>
      simp only [mk, Option.some.injEq] at h; subst h
      have hp := sortKids_perm (k₁ :: k₂ :: ks)
      simp only [rfits, Bool.and_eq_true, decide_eq_true_eq]
      refine ⟨?_, ?_⟩
      · rw [(prodKids_perm hp).length_eq]; exact hn
      · rw [rfitsKids_perm K hp, rfitsKids_eq]
        simp only [List.all_eq_true]
        intro c hc; exact hkids c hc
  | .add t₁ t₂, U, hw, h => by
    have ih₁ := nfR_fits K t₁
    have ih₂ := nfR_fits K t₂
    change mk false (optKid false (nfL rigidLabels t₁) ++ optKid false (nfL rigidLabels t₂)) =
      some U at h
    cases hq₁ : nfL rigidLabels t₁ with
    | none =>
      cases hq₂ : nfL rigidLabels t₂ with
      | none => rw [hq₁, hq₂] at h; simp [optKid, mk] at h
      | some V => rw [hq₁, hq₂] at h; simp only [optKid, List.nil_append, mk, Option.some.injEq] at h
                  subst h; exact ih₂ V hw.2 hq₂
    | some W =>
      cases hq₂ : nfL rigidLabels t₂ with
      | none => rw [hq₁, hq₂] at h; simp only [optKid, List.append_nil, mk, Option.some.injEq] at h
                subst h; exact ih₁ W hw.1 hq₁
      | some V =>
        rw [hq₁, hq₂] at h
        simp only [optKid, List.singleton_append, mk, Option.some.injEq] at h
        subst h
        rcases two_perm (sortKids_perm [(false, W), (false, V)]) with h | h <;> rw [h] <;>
          simp [rfits, rfitsKids, ih₁ W hw.1 hq₁, ih₂ V hw.2 hq₂]

/-! ## Relabeling leaves -/

section Relabel
variable (m : Machine α β) (K : ℕ)

theorem prodKids_mapKids (g : ℕ → ℕ) : ∀ cs : List (Bool × LTree Bool Bool),
    prodKids (mapKids g cs) = (prodKids cs).map g
  | [] => rfl
  | (false, .leaf i) :: cs => by simp [mapKids, mapLeaves, prodKids, prodKids_mapKids g cs]
  | (false, .node l ks) :: cs => by simp [mapKids, mapLeaves, prodKids, prodKids_mapKids g cs]
  | (true, t) :: cs => by
    cases t <;> simp [mapKids, mapLeaves, prodKids, prodKids_mapKids g cs]

mutual
theorem evR_mapLeaves (p : ℕ → α) (g : ℕ → ℕ) : ∀ T : LTree Bool Bool,
    evR m K p (mapLeaves g T) = evR m K (fun i => p (g i)) T
  | .leaf i => rfl
  | .node true cs => by
    simp only [mapLeaves, evR, evC_mapKids p g cs, prodKids_mapKids, List.map_map, List.length_map]
    rfl
  | .node false cs => by simp only [mapLeaves, evR]; exact evA_mapKids p g cs
theorem evC_mapKids (p : ℕ → α) (g : ℕ → ℕ) : ∀ cs : List (Bool × LTree Bool Bool),
    evC m K p (mapKids g cs) = evC m K (fun i => p (g i)) cs
  | [] => rfl
  | (true, t) :: _ => by simp only [mapKids, evC]; exact evR_mapLeaves p g t
  | (false, _) :: cs => by simp only [mapKids, evC]; exact evC_mapKids p g cs
theorem evA_mapKids (p : ℕ → α) (g : ℕ → ℕ) : ∀ cs : List (Bool × LTree Bool Bool),
    evA m K p (mapKids g cs) = evA m K (fun i => p (g i)) cs
  | [] => rfl
  | [(e, t)] => rfl
  | [(e₁, t₁), (e₂, t₂)] => by
    simp only [mapKids, evA, evR_mapLeaves p g t₁, evR_mapLeaves p g t₂]
  | _ :: _ :: _ :: _ => rfl
end

mutual
theorem evR_congr {p q : ℕ → α} : ∀ T : LTree Bool Bool, (∀ i ∈ T.leaves, p i = q i) →
    evR m K p T = evR m K q T
  | .leaf i, h => by simp only [evR, h i (by simp [leaves])]
  | .node true cs, h => by
    have hc := evC_congr cs (fun i hi => h i (by simpa [leaves] using hi))
    have hp : (prodKids cs).map (fun i => some (p i)) = (prodKids cs).map (fun i => some (q i)) := by
      apply List.map_congr_left
      intro i hi
      have : i ∈ kidsLeaves cs := by
        rw [prodKids_eq] at hi
        obtain ⟨c, hc', he⟩ := List.mem_filterMap.mp hi
        rw [kidsLeaves_eq]
        refine List.mem_flatten.mpr ⟨c.2.leaves, List.mem_map.mpr ⟨c, hc', rfl⟩, ?_⟩
        obtain ⟨e, t⟩ := c
        cases e <;> cases t <;> simp at he
        subst he; simp [leaves]
      rw [h i (by simpa [leaves] using this)]
    simp only [evR, hc, hp]
  | .node false cs, h => by
    simp only [evR]; exact evA_congr cs (fun i hi => h i (by simpa [leaves] using hi))
theorem evC_congr {p q : ℕ → α} : ∀ cs : List (Bool × LTree Bool Bool),
    (∀ i ∈ kidsLeaves cs, p i = q i) → evC m K p cs = evC m K q cs
  | [], _ => rfl
  | (true, t) :: cs, h => by
    simp only [evC]; exact evR_congr t (fun i hi => h i (by simp [kidsLeaves, hi]))
  | (false, t) :: cs, h => by
    simp only [evC]; exact evC_congr cs (fun i hi => h i (by simp [kidsLeaves, hi]))
theorem evA_congr {p q : ℕ → α} : ∀ cs : List (Bool × LTree Bool Bool),
    (∀ i ∈ kidsLeaves cs, p i = q i) → evA m K p cs = evA m K q cs
  | [], _ => rfl
  | [(e, t)], _ => rfl
  | [(e₁, t₁), (e₂, t₂)], h => by
    simp only [evA, evR_congr t₁ (fun i hi => h i (by simp [kidsLeaves, hi])),
      evR_congr t₂ (fun i hi => h i (by simp [kidsLeaves, hi]))]
  | _ :: _ :: _ :: _, _ => rfl
end

end Relabel

theorem filter_fst_mapKids (g : ℕ → ℕ) : ∀ cs : List (Bool × LTree Bool Bool),
    ((mapKids g cs).filter fun c => c.1).length = (cs.filter fun c => c.1).length
  | [] => rfl
  | (e, t) :: cs => by cases e <;> simp [mapKids, filter_fst_mapKids g cs]

theorem kidsLeafProd_mapKids (g : ℕ → ℕ) : ∀ cs : List (Bool × LTree Bool Bool),
    kidsLeafProd (mapKids g cs) = kidsLeafProd cs
  | [] => rfl
  | (e, t) :: cs => by
    have := kidsLeafProd_mapKids g cs
    unfold kidsLeafProd at this ⊢
    cases t <;> simp [mapKids, mapLeaves, this]

theorem length_mapKids (g : ℕ → ℕ) : ∀ cs : List (Bool × LTree Bool Bool),
    (mapKids g cs).length = cs.length
  | [] => rfl
  | (e, t) :: cs => by simp [mapKids, length_mapKids g cs]

theorem all_fst_mapKids (g : ℕ → ℕ) : ∀ cs : List (Bool × LTree Bool Bool),
    (mapKids g cs).all (fun c => !c.1) = cs.all (fun c => !c.1)
  | [] => rfl
  | (e, t) :: cs => by simp [mapKids, all_fst_mapKids g cs]

mutual
theorem rvalid_mapLeaves (g : ℕ → ℕ) : ∀ T : LTree Bool Bool, rvalid (mapLeaves g T) = rvalid T
  | .leaf i => rfl
  | .node true cs => by
    simp only [mapLeaves, rvalid, rvalidKids_mapKids g cs, filter_fst_mapKids, kidsLeafProd_mapKids]
  | .node false cs => by
    simp only [mapLeaves, rvalid, rvalidKids_mapKids g cs, length_mapKids, all_fst_mapKids]
theorem rvalidKids_mapKids (g : ℕ → ℕ) : ∀ cs : List (Bool × LTree Bool Bool),
    rvalidKids (mapKids g cs) = rvalidKids cs
  | [] => rfl
  | (e, t) :: cs => by simp only [mapKids, rvalidKids, rvalid_mapLeaves g t, rvalidKids_mapKids g cs]
end

mutual
theorem rfits_mapLeaves (K : ℕ) (g : ℕ → ℕ) : ∀ T : LTree Bool Bool,
    rfits K (mapLeaves g T) = rfits K T
  | .leaf i => rfl
  | .node true cs => by
    simp only [mapLeaves, rfits, rfitsKids_mapKids K g cs, prodKids_mapKids, List.length_map]
  | .node false cs => by
    simp only [mapLeaves, rfits, rfitsKids_mapKids K g cs]
theorem rfitsKids_mapKids (K : ℕ) (g : ℕ → ℕ) : ∀ cs : List (Bool × LTree Bool Bool),
    rfitsKids K (mapKids g cs) = rfitsKids K cs
  | [] => rfl
  | (e, t) :: cs => by
    simp only [mapKids, rfitsKids, rfits_mapLeaves K g t, rfitsKids_mapKids K g cs]
end

/-! ## Base witnesses from fingerprint tables -/

/-- Every two-leaf code. -/
def codes2All : List (Bool × Bool × Bool) :=
  [false, true].flatMap fun l => [false, true].flatMap fun e₁ => [false, true].map fun e₂ => (l, e₁, e₂)

/-- Every three-leaf code. -/
def codes3All : List (Shape3 Bool Bool) :=
  let B := [false, true]
  (B.flatMap fun l => B.flatMap fun e₁ => B.flatMap fun e₂ => B.map fun e₃ => Shape3.fan l e₁ e₂ e₃) ++
  (B.flatMap fun l => B.flatMap fun e₁ => B.flatMap fun e₂ => B.flatMap fun l' => B.flatMap fun f₁ =>
    B.flatMap fun f₂ => [Shape3.ab l e₁ e₂ l' f₁ f₂, Shape3.ac l e₁ e₂ l' f₁ f₂, Shape3.bc l e₁ e₂ l' f₁ f₂])

theorem mem_codes2All (κ : Bool × Bool × Bool) : κ ∈ codes2All := by
  obtain ⟨l, e₁, e₂⟩ := κ
  cases l <;> cases e₁ <;> cases e₂ <;> decide

theorem mem_codes3All (κ : Shape3 Bool Bool) : κ ∈ codes3All := by
  cases κ with
  | fan l e₁ e₂ e₃ => cases l <;> cases e₁ <;> cases e₂ <;> cases e₃ <;> decide
  | ab l e₁ e₂ l' f₁ f₂ =>
    cases l <;> cases e₁ <;> cases e₂ <;> cases l' <;> cases f₁ <;> cases f₂ <;> decide
  | ac l e₁ e₂ l' f₁ f₂ =>
    cases l <;> cases e₁ <;> cases e₂ <;> cases l' <;> cases f₁ <;> cases f₂ <;> decide
  | bc l e₁ e₂ l' f₁ f₂ =>
    cases l <;> cases e₁ <;> cases e₂ <;> cases l' <;> cases f₁ <;> cases f₂ <;> decide

/-- Distinct fingerprints on a list of inputs separate any two codes of a table. -/
theorem sep_of_table {γ δ : Type} (codes : List γ) (hall : ∀ κ, κ ∈ codes) (valid : γ → Bool)
    (ins : List δ) (f : γ → δ → Option β)
    (hnd : ((codes.filter valid).map fun κ => ins.map (f κ)).Nodup) :
    ∀ κ₁ κ₂, valid κ₁ = true → valid κ₂ = true → κ₁ ≠ κ₂ → ∃ q ∈ ins, f κ₁ q ≠ f κ₂ q := by
  intro κ₁ κ₂ h₁ h₂ hne
  apply Classical.byContradiction
  intro hno
  have heq : ins.map (f κ₁) = ins.map (f κ₂) := by
    apply List.map_congr_left
    intro q hq
    apply Classical.byContradiction; intro h; exact hno ⟨q, hq, h⟩
  exact hne (inj_of_nodup_map hnd (List.mem_filter.mpr ⟨hall κ₁, h₁⟩)
    (List.mem_filter.mpr ⟨hall κ₂, h₂⟩) heq)

/-- **The rigid base step.** If inputs on `{0, 1}` separate the valid two-leaf normal forms and
inputs on `{0, 1, 2}` separate the valid three-leaf ones, then any two terms over the same products,
at most three, with different normal forms are separated by some input. -/
theorem rigid_base_fits (ins2 ins3 : List (ℕ → α))
    (h2 : ∀ κ₁ κ₂ : Bool × Bool × Bool, (rvalid (realize2 κ₁ 0 1) && rfits K (realize2 κ₁ 0 1)) = true →
      (rvalid (realize2 κ₂ 0 1) && rfits K (realize2 κ₂ 0 1)) = true → κ₁ ≠ κ₂ →
      ∃ q ∈ ins2, evR m K q (realize2 κ₁ 0 1) ≠ evR m K q (realize2 κ₂ 0 1))
    (h3 : ∀ κ₁ κ₂ : Shape3 Bool Bool, (rvalid (κ₁.realize 0 1 2) && rfits K (κ₁.realize 0 1 2)) = true →
      (rvalid (κ₂.realize 0 1 2) && rfits K (κ₂.realize 0 1 2)) = true → κ₁ ≠ κ₂ →
      ∃ q ∈ ins3, evR m K q (κ₁.realize 0 1 2) ≠ evR m K q (κ₂.realize 0 1 2)) :
    ∀ t₁ t₂ : Term, TermWF K t₁ → TermWF K t₂ → t₁.leaves.Nodup → t₂.leaves.Nodup →
      t₁.leaves.length ≤ 3 → (∀ i, i ∈ t₁.leaves ↔ i ∈ t₂.leaves) → nfL rigidLabels t₁ ≠ nfL rigidLabels t₂ →
      ∃ p, True ∧ evRO m K p (nfL rigidLabels t₁) ≠ evRO m K p (nfL rigidLabels t₂) := by
  intro t₁ t₂ hw₁ hw₂ n₁ n₂ hlen hl hne
  have F := labelsNF rigidLabels
  obtain ⟨U₁, hU₁⟩ : ∃ U, nfL rigidLabels t₁ = some U := by
    cases h : nfL rigidLabels t₁ with
    | some U => exact ⟨U, rfl⟩
    | none =>
      exfalso
      have e₁ := (nfL_none_iff rigidLabels t₁).mp h
      have e₂ : t₂.leaves = [] := List.eq_nil_iff_forall_not_mem.mpr fun i hi => by
        have := (hl i).mpr hi; rw [e₁] at this; simp at this
      exact hne (by rw [h]; exact ((nfL_none_iff rigidLabels t₂).mpr e₂).symm)
  obtain ⟨U₂, hU₂⟩ : ∃ U, nfL rigidLabels t₂ = some U := by
    cases h : nfL rigidLabels t₂ with
    | some U => exact ⟨U, rfl⟩
    | none =>
      exfalso
      have e₂ := (nfL_none_iff rigidLabels t₂).mp h
      have e₁ : t₁.leaves = [] := List.eq_nil_iff_forall_not_mem.mpr fun i hi => by
        have := (hl i).mp hi; rw [e₂] at this; simp at this
      exact hne (by rw [h]; exact (nfL_none_iff rigidLabels t₁).mpr e₁)
  have p₁ : U₁.leaves.Perm t₁.leaves := by have := oleaves_nfL rigidLabels t₁; rw [hU₁] at this; exact this
  have p₂ : U₂.leaves.Perm t₂.leaves := by have := oleaves_nfL rigidLabels t₂; rw [hU₂] at this; exact this
  have c₁ := nfL_canon rigidLabels t₁ n₁ U₁ hU₁
  have c₂ := nfL_canon rigidLabels t₂ n₂ U₂ hU₂
  have v₁ := nfR_valid t₁ U₁ hU₁
  have v₂ := nfR_valid t₂ U₂ hU₂
  have f₁ := nfR_fits K t₁ U₁ hw₁ hU₁
  have f₂ := nfR_fits K t₂ U₂ hw₂ hU₂
  have hUne : U₁ ≠ U₂ := by intro h; exact hne (by rw [hU₁, hU₂, h])
  have m₁ : ∀ x, x ∈ U₁.leaves ↔ x ∈ t₁.leaves := fun x => p₁.mem_iff
  have m₂ : ∀ x, x ∈ U₂.leaves ↔ x ∈ t₁.leaves := fun x => by rw [p₂.mem_iff, hl x]
  have hne' : t₁.leaves ≠ [] := by
    intro h; have := (nfL_none_iff rigidLabels t₁).mpr h; rw [hU₁] at this; cases this
  rcases small_support n₁ hlen hne' with ⟨a, ha⟩ | ⟨a, b, hab, ha⟩ | ⟨a, b, c, hab, hbc, ha⟩
  · exfalso; apply hUne
    rw [shape1 c₁ (p₁.nodup_iff.mpr n₁) (fun x => by rw [m₁, ha]),
      shape1 c₂ (p₂.nodup_iff.mpr n₂) (fun x => by rw [m₂, ha])]
  · obtain ⟨κ₁, rfl⟩ := shape2_code hab c₁ (p₁.nodup_iff.mpr n₁) (fun x => by rw [m₁, ha])
    obtain ⟨κ₂, rfl⟩ := shape2_code hab c₂ (p₂.nodup_iff.mpr n₂) (fun x => by rw [m₂, ha])
    have hκ : κ₁ ≠ κ₂ := by intro h; subst h; exact hUne rfl
    rw [realize2_lab κ₁ a b, rvalid_mapLeaves] at v₁
    rw [realize2_lab κ₂ a b, rvalid_mapLeaves] at v₂
    rw [realize2_lab κ₁ a b, rfits_mapLeaves] at f₁
    rw [realize2_lab κ₂ a b, rfits_mapLeaves] at f₂
    obtain ⟨q, _, hq⟩ := h2 κ₁ κ₂ (by rw [v₁, f₁]; rfl) (by rw [v₂, f₂]; rfl) hκ
    refine ⟨fun x => if x = a then q 0 else q 1, trivial, ?_⟩
    rw [hU₁, hU₂]
    simp only [evRO]
    rw [realize2_lab κ₁ a b, realize2_lab κ₂ a b, evR_mapLeaves, evR_mapLeaves]
    have hc : ∀ κ : Bool × Bool × Bool, evR m K (fun i => (fun x => if x = a then q 0 else q 1)
        (lab3 a b b i)) (realize2 κ 0 1) = evR m K q (realize2 κ 0 1) := by
      intro κ
      apply evR_congr
      intro i hi
      simp [realize2, leaves, kidsLeaves] at hi
      rcases hi with rfl | rfl
      · simp [lab3]
      · simp [lab3]; omega
    rw [hc, hc]; exact hq
  · obtain ⟨κ₁, rfl⟩ := shape3_code hab hbc c₁ (p₁.nodup_iff.mpr n₁) (fun x => by rw [m₁, ha])
    obtain ⟨κ₂, rfl⟩ := shape3_code hab hbc c₂ (p₂.nodup_iff.mpr n₂) (fun x => by rw [m₂, ha])
    have hκ : κ₁ ≠ κ₂ := by intro h; subst h; exact hUne rfl
    rw [realize3_lab κ₁ a b c, rvalid_mapLeaves] at v₁
    rw [realize3_lab κ₂ a b c, rvalid_mapLeaves] at v₂
    rw [realize3_lab κ₁ a b c, rfits_mapLeaves] at f₁
    rw [realize3_lab κ₂ a b c, rfits_mapLeaves] at f₂
    obtain ⟨q, _, hq⟩ := h3 κ₁ κ₂ (by rw [v₁, f₁]; rfl) (by rw [v₂, f₂]; rfl) hκ
    refine ⟨fun x => if x = a then q 0 else if x = b then q 1 else q 2, trivial, ?_⟩
    rw [hU₁, hU₂]
    simp only [evRO]
    rw [realize3_lab κ₁ a b c, realize3_lab κ₂ a b c, evR_mapLeaves, evR_mapLeaves]
    have hc : ∀ κ : Shape3 Bool Bool, evR m K (fun i =>
        (fun x => if x = a then q 0 else if x = b then q 1 else q 2) (lab3 a b c i))
        (κ.realize 0 1 2) = evR m K q (κ.realize 0 1 2) := by
      intro κ
      apply evR_congr
      intro i hi
      have hi' : i = 0 ∨ i = 1 ∨ i = 2 := by
        cases κ <;> simp [Shape3.realize, leaves, kidsLeaves] at hi <;> omega
      rcases hi' with rfl | rfl | rfl
      · simp [lab3]
      · simp [lab3]; omega
      · have e : lab3 a b c 2 = c := by simp [lab3]
        simp only [e, if_neg (show c ≠ a by omega), if_neg (show c ≠ b by omega)]
    rw [hc, hc]; exact hq

theorem rigid_base (ins2 ins3 : List (ℕ → α))
    (h2 : ∀ κ₁ κ₂ : Bool × Bool × Bool, rvalid (realize2 κ₁ 0 1) = true →
      rvalid (realize2 κ₂ 0 1) = true → κ₁ ≠ κ₂ →
      ∃ q ∈ ins2, evR m K q (realize2 κ₁ 0 1) ≠ evR m K q (realize2 κ₂ 0 1))
    (h3 : ∀ κ₁ κ₂ : Shape3 Bool Bool, rvalid (κ₁.realize 0 1 2) = true →
      rvalid (κ₂.realize 0 1 2) = true → κ₁ ≠ κ₂ →
      ∃ q ∈ ins3, evR m K q (κ₁.realize 0 1 2) ≠ evR m K q (κ₂.realize 0 1 2)) :
    ∀ t₁ t₂ : Term, TermWF K t₁ → TermWF K t₂ → t₁.leaves.Nodup → t₂.leaves.Nodup →
      t₁.leaves.length ≤ 3 → (∀ i, i ∈ t₁.leaves ↔ i ∈ t₂.leaves) → nfL rigidLabels t₁ ≠ nfL rigidLabels t₂ →
      ∃ p, True ∧ evRO m K p (nfL rigidLabels t₁) ≠ evRO m K p (nfL rigidLabels t₂) :=
  rigid_base_fits ins2 ins3
    (fun κ₁ κ₂ v₁ v₂ hκ => h2 κ₁ κ₂ (Bool.and_eq_true_iff.mp v₁).1 (Bool.and_eq_true_iff.mp v₂).1 hκ)
    (fun κ₁ κ₂ v₁ v₂ hκ => h3 κ₁ κ₂ (Bool.and_eq_true_iff.mp v₁).1 (Bool.and_eq_true_iff.mp v₂).1 hκ)

/-- **Completeness for terms on a rigid machine.** With the laws of a rigid multiplier and inputs
that separate the normal forms on two and three products, two terms over the same products, each
once, with different rigid normal forms differ on an input that is `z` outside at most three of the
products. -/
theorem rigid_term_complete (A : RigidAlg m K) (ins2 ins3 : List (ℕ → α))
    (hnd2 : ((codes2All.filter fun κ => rvalid (realize2 κ 0 1)).map
      fun κ => ins2.map fun q => evR m K q (realize2 κ 0 1)).Nodup)
    (hnd3 : ((codes3All.filter fun κ => rvalid (κ.realize 0 1 2)).map
      fun κ => ins3.map fun q => evR m K q (κ.realize 0 1 2)).Nodup)
    (t₁ t₂ : Term) (hw₁ : TermWF K t₁) (hw₂ : TermWF K t₂) (n₁ : t₁.leaves.Nodup)
    (n₂ : t₂.leaves.Nodup) (hl : ∀ i, i ∈ t₁.leaves ↔ i ∈ t₂.leaves) (hne : nfR t₁ ≠ nfR t₂) :
    ∃ (s : List ℕ) (q : ℕ → α), s.length ≤ 3 ∧ (∀ i, i ∉ s → q i = A.z) ∧
      eval m q m.zero m.zero t₁ ≠ eval m q m.zero m.zero t₂ := by
  obtain ⟨s, q, hs, hz, _, hq⟩ := term_complete (labelsNF rigidLabels) A.slot (fun _ => True) (evRO m K)
    (fun t hw hn p _ => rigid_sound A p t hw hn)
    (rigid_base ins2 ins3
      (sep_of_table codes2All mem_codes2All _ ins2 (fun κ q => evR m K q (realize2 κ 0 1)) hnd2)
      (sep_of_table codes3All mem_codes3All _ ins3 (fun κ q => evR m K q (κ.realize 0 1 2)) hnd3))
    t₁ t₂ hw₁ hw₂ n₁ n₂ hl hne
  exact ⟨s, q, hs, hz, hq⟩

/-- **Completeness for terms on a rigid machine, with small blocks.** As `rigid_term_complete`, with
fingerprint tables over the normal forms whose blocks fit `K` slots only (for `K < 3`). -/
theorem rigid_term_complete_fits (A : RigidAlg m K) (ins2 ins3 : List (ℕ → α))
    (hnd2 : ((codes2All.filter fun κ => rvalid (realize2 κ 0 1) && rfits K (realize2 κ 0 1)).map
      fun κ => ins2.map fun q => evR m K q (realize2 κ 0 1)).Nodup)
    (hnd3 : ((codes3All.filter fun κ => rvalid (κ.realize 0 1 2) && rfits K (κ.realize 0 1 2)).map
      fun κ => ins3.map fun q => evR m K q (κ.realize 0 1 2)).Nodup)
    (t₁ t₂ : Term) (hw₁ : TermWF K t₁) (hw₂ : TermWF K t₂) (n₁ : t₁.leaves.Nodup)
    (n₂ : t₂.leaves.Nodup) (hl : ∀ i, i ∈ t₁.leaves ↔ i ∈ t₂.leaves) (hne : nfR t₁ ≠ nfR t₂) :
    ∃ (s : List ℕ) (q : ℕ → α), s.length ≤ 3 ∧ (∀ i, i ∉ s → q i = A.z) ∧
      eval m q m.zero m.zero t₁ ≠ eval m q m.zero m.zero t₂ := by
  obtain ⟨s, q, hs, hz, _, hq⟩ := term_complete (labelsNF rigidLabels) A.slot (fun _ => True) (evRO m K)
    (fun t hw hn p _ => rigid_sound A p t hw hn)
    (rigid_base_fits ins2 ins3
      (sep_of_table codes2All mem_codes2All _ ins2 (fun κ q => evR m K q (realize2 κ 0 1)) hnd2)
      (sep_of_table codes3All mem_codes3All _ ins3 (fun κ q => evR m K q (κ.realize 0 1 2)) hnd3))
    t₁ t₂ hw₁ hw₂ n₁ n₂ hl hne
  exact ⟨s, q, hs, hz, hq⟩

end MMAlgebra
