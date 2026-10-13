import TensorCore

/-! # Laws of one block FMA on the Tensor Core model

Two laws of the reduction algebra that hold for every Tensor Core model (any FMA size, extra
alignment bits and minimum alignment exponent):

* `evalBlock_bits_perm`: a block FMA's output word depends on its products only as a multiset;
* `evalBlock_bits_zero`: a product with a zero operand can replace, or be replaced by, a zero pair
  `(0, 0)`, whatever its other finite operand: zero products are invisible.

Both are stated on `blockOut`, the output word of `evalBlock` or its error. -/

open TensorCore

namespace MMAlgebra.TC

/-! ## `mapM` over a permutation -/

/-- Relation between two optional lists: both fail, or both succeed with permuted results. -/
def PermOpt {β : Type} : Option (List β) → Option (List β) → Prop
  | none, none => True
  | some u, some v => u.Perm v
  | _, _ => False

theorem PermOpt.trans {β : Type} {o₁ o₂ o₃ : Option (List β)}
    (h₁ : PermOpt o₁ o₂) (h₂ : PermOpt o₂ o₃) : PermOpt o₁ o₃ := by
  cases o₁ <;> cases o₂ <;> cases o₃ <;> simp_all [PermOpt]
  exact h₁.trans h₂

theorem mapM_perm {α β : Type} (f : α → Option β) {xs ys : List α} (h : xs.Perm ys) :
    PermOpt (xs.mapM f) (ys.mapM f) := by
  induction h with
  | nil => simp [PermOpt]
  | @cons x l₁ l₂ _ ih =>
    simp only [List.mapM_cons]
    revert ih
    generalize List.mapM f l₁ = o₁
    generalize List.mapM f l₂ = o₂
    intro ih
    cases hx : f x <;> cases o₁ <;> cases o₂ <;> simp_all [PermOpt]
  | swap x y l =>
    simp only [List.mapM_cons]
    generalize List.mapM f l = o
    cases hx : f x <;> cases hy : f y <;> cases o <;> simp [PermOpt]
    exact List.Perm.swap _ _ _
  | trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂

/-! ## The accumulator of a block is a function of the multiset of its terms -/

theorem maxTermExp_perm {ts us : List DenormalizedProduct} (h : ts.Perm us) :
    maxTermExp ts = maxTermExp us := by
  unfold maxTermExp
  apply (h.filterMap _).foldl_eq'
  intro x _ y _ z
  cases z <;> simp <;> omega

theorem accumulator_perm (p : Model) (c : Decoded) {ps qs : List (Decoded × Decoded)}
    (h : ps.Perm qs) :
    (PreparedBlock.mk p ps c).accumulator = (PreparedBlock.mk p qs c).accumulator := by
  have ht : (PreparedBlock.mk p ps c).terms.Perm (PreparedBlock.mk p qs c).terms := by
    unfold PreparedBlock.terms
    exact List.Perm.cons _ (h.map _)
  have hg : (PreparedBlock.mk p ps c).alignGridExponent =
      (PreparedBlock.mk p qs c).alignGridExponent := by
    unfold PreparedBlock.alignGridExponent PreparedBlock.alignExp
    rw [maxTermExp_perm ht]
  unfold PreparedBlock.accumulator PreparedBlock.alignedBits
  rw [hg, sumZ_perm (ht.map _)]

/-- Output bits (or the error) of one block. -/
def blockOut {p : Model} (x : BlockInput p) : Except ModelError F32 :=
  (evalBlock x).map fun t => t.output.bits

theorem evalPrepared_bits_eq {b b' : PreparedBlock} (h : b.accumulator = b'.accumulator) :
    (evalPrepared b).map (fun t => t.output.bits) = (evalPrepared b').map (fun t => t.output.bits) := by
  unfold evalPrepared
  rw [h]
  split
  · rfl
  · split <;> rfl

theorem prepareProducts_perm (p : Model) {ps qs : List (p.Word × p.Word)} (h : ps.Perm qs) :
    PermOpt (prepareProducts p ps) (prepareProducts p qs) := by
  unfold prepareProducts
  exact mapM_perm _ h

/-- **Permutation law.** A Tensor Core block FMA depends on its products only as a multiset. -/
theorem evalBlock_bits_perm {p : Model} {ps qs : List (p.Word × p.Word)} (h : ps.Perm qs)
    (c : F32) : blockOut (p := p) ⟨ps, c⟩ = blockOut ⟨qs, c⟩ := by
  unfold blockOut evalBlock
  simp only [h.length_eq]
  split
  · rfl
  · unfold prepare
    simp only
    have hm := prepareProducts_perm p h
    cases hc : decode32 c with
    | none => simp
    | some dc =>
      revert hm
      cases prepareProducts p ps <;> cases prepareProducts p qs <;> simp [PermOpt]
      intro hperm
      exact evalPrepared_bits_eq (accumulator_perm p dc hperm)


/-! ## Zero products are invisible -/

/-- Pointwise relation between two lists (core Lean has no `Rel2`). -/
inductive Rel2 {α β : Type} (R : α → β → Prop) : List α → List β → Prop
  | nil : Rel2 R [] []
  | cons {x y l₁ l₂} : R x y → Rel2 R l₁ l₂ → Rel2 R (x :: l₁) (y :: l₂)

theorem Rel2.length_eq {α β : Type} {R : α → β → Prop} {l₁ : List α} {l₂ : List β}
    (h : Rel2 R l₁ l₂) : l₁.length = l₂.length := by
  induction h with
  | nil => rfl
  | cons _ _ ih => simp [ih]

theorem Rel2.map {α β γ δ : Type} {R : α → β → Prop} {S : γ → δ → Prop} (f : α → γ) (g : β → δ)
    (hfg : ∀ x y, R x y → S (f x) (g y)) {l₁ : List α} {l₂ : List β} (h : Rel2 R l₁ l₂) :
    Rel2 S (l₁.map f) (l₂.map g) := by
  induction h with
  | nil => exact .nil
  | cons hxy _ ih => exact .cons (hfg _ _ hxy) ih

theorem Rel2.same {α γ δ : Type} {S : γ → δ → Prop} (f : α → γ) (g : α → δ)
    (hfg : ∀ x, S (f x) (g x)) (l : List α) : Rel2 S (l.map f) (l.map g) := by
  induction l with
  | nil => exact .nil
  | cons x l ih => exact .cons (hfg x) ih

/-- A pair of finite words whose product is zero. -/
def ZeroPair (p : Model) (x : p.Word × p.Word) : Prop :=
  ∃ da db : Decoded, p.decode x.1 = some da ∧ p.decode x.2 = some db ∧
    da.significand * db.significand = 0

/-- Two decoded products agree, or both are zero. -/
def ProdRel (x y : Decoded × Decoded) : Prop :=
  x = y ∨ (x.1.significand * x.2.significand = 0 ∧ y.1.significand * y.2.significand = 0)

/-- Both fail, or both succeed with pointwise related results. -/
def RelOpt {β : Type} (R : β → β → Prop) : Option (List β) → Option (List β) → Prop
  | none, none => True
  | some u, some v => Rel2 R u v
  | _, _ => False

/-- One-element version of `RelOpt`. -/
def RelOpt1 {β : Type} (R : β → β → Prop) : Option β → Option β → Prop
  | none, none => True
  | some u, some v => R u v
  | _, _ => False

theorem mapM_rel {α β : Type} (f : α → Option β) (R : α → α → Prop) (S : β → β → Prop)
    (hf : ∀ x y, R x y → RelOpt1 S (f x) (f y)) {xs ys : List α} (h : Rel2 R xs ys) :
    RelOpt S (xs.mapM f) (ys.mapM f) := by
  induction h with
  | nil => exact Rel2.nil
  | @cons x y l₁ l₂ hxy _ ih =>
    simp only [List.mapM_cons]
    revert ih
    generalize List.mapM f l₁ = o₁
    generalize List.mapM f l₂ = o₂
    intro ih
    have hxy' := hf x y hxy
    revert hxy'
    cases f x <;> cases f y <;> cases o₁ <;> cases o₂ <;> simp_all [RelOpt, RelOpt1]
    intro h
    exact Rel2.cons h ih

theorem prepareProducts_rel (p : Model) {ps qs : List (p.Word × p.Word)}
    (h : Rel2 (fun x y => x = y ∨ (ZeroPair p x ∧ ZeroPair p y)) ps qs) :
    RelOpt ProdRel (prepareProducts p ps) (prepareProducts p qs) := by
  unfold prepareProducts
  apply mapM_rel _ _ _ _ h
  intro x y hxy
  rcases hxy with rfl | ⟨⟨da, db, ha, hb, hz⟩, ⟨ea, eb, ha', hb', hz'⟩⟩
  · cases hx : p.decode x.1 <;> cases hy : p.decode x.2 <;> simp [RelOpt1, ProdRel, hx, hy]
  · simp [RelOpt1, ProdRel, ha, hb, ha', hb', hz, hz']

theorem denormalizedMul_significand (a b : Decoded) :
    (denormalizedMul a b).significand = a.significand * b.significand := rfl

theorem zero_term_value (t : DenormalizedProduct) (h : t.significand = 0) : t.value = 0 := by
  simp [DenormalizedProduct.value, h]

theorem accumulator_rel (p : Model) (c : Decoded) {ds es : List (Decoded × Decoded)}
    (h : Rel2 ProdRel ds es) :
    (PreparedBlock.mk p ds c).accumulator = (PreparedBlock.mk p es c).accumulator := by
  have hterms : Rel2 (fun t u : DenormalizedProduct => t = u ∨
      (t.significand = 0 ∧ u.significand = 0))
      (PreparedBlock.mk p ds c).terms (PreparedBlock.mk p es c).terms := by
    unfold PreparedBlock.terms
    refine Rel2.cons (Or.inl rfl) ?_
    refine Rel2.map _ _ ?_ h
    intro x y hxy
    rcases hxy with rfl | ⟨hx, hy⟩
    · exact Or.inl rfl
    · exact Or.inr ⟨by rw [denormalizedMul_significand]; exact hx, by rw [denormalizedMul_significand]; exact hy⟩
  have hfm : ∀ {ts us : List DenormalizedProduct}, Rel2 (fun t u : DenormalizedProduct =>
      t = u ∨ (t.significand = 0 ∧ u.significand = 0)) ts us →
      ts.filterMap (fun t => if t.significand = 0 then none else some t.exponent) =
      us.filterMap (fun t => if t.significand = 0 then none else some t.exponent) := by
    intro ts us hr
    induction hr with
    | nil => rfl
    | @cons t u l₁ l₂ htu _ ih =>
      rcases htu with rfl | ⟨ht, hu⟩
      · simp only [List.filterMap_cons, ih]
      · simp [ht, hu, ih]
  have hval : ∀ {ts us : List DenormalizedProduct} (g : ℤ), Rel2 (fun t u : DenormalizedProduct =>
      t = u ∨ (t.significand = 0 ∧ u.significand = 0)) ts us →
      ts.map (fun t => truncBits t.value g) = us.map (fun t => truncBits t.value g) := by
    intro ts us g hr
    induction hr with
    | nil => rfl
    | @cons t u l₁ l₂ htu _ ih =>
      rcases htu with rfl | ⟨ht, hu⟩
      · simp only [List.map_cons, ih]
      · simp only [List.map_cons, ih, zero_term_value t ht, zero_term_value u hu]
  have hg : (PreparedBlock.mk p ds c).alignGridExponent =
      (PreparedBlock.mk p es c).alignGridExponent := by
    unfold PreparedBlock.alignGridExponent PreparedBlock.alignExp maxTermExp
    rw [hfm hterms]
  unfold PreparedBlock.accumulator PreparedBlock.alignedBits
  rw [hg, hval _ hterms]

/-- **Zero law.** Slots that hold the same pair, or zero products of finite words, give the same
block output. -/
theorem evalBlock_bits_zero {p : Model} {ps qs : List (p.Word × p.Word)}
    (h : Rel2 (fun x y => x = y ∨ (ZeroPair p x ∧ ZeroPair p y)) ps qs) (c : F32) :
    blockOut (p := p) ⟨ps, c⟩ = blockOut ⟨qs, c⟩ := by
  unfold blockOut evalBlock
  simp only [h.length_eq]
  split
  · rfl
  · unfold prepare
    simp only
    have hm := prepareProducts_rel p h
    cases hc : decode32 c with
    | none => simp
    | some dc =>
      revert hm
      cases prepareProducts p ps <;> cases prepareProducts p qs <;> simp [RelOpt]
      intro hrel
      exact evalPrepared_bits_eq (accumulator_rel p dc hrel)

end MMAlgebra.TC
