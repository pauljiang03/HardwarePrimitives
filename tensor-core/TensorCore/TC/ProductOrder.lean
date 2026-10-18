import TensorCore.TC.Block
import TensorCore.Numerics.Sum

/-! # The order of the products

A block FMA aligns every term to the largest exponent and adds the truncated terms exactly, so
its output depends on the products only as a multiset. -/

namespace TensorCore

theorem maxTermExp_perm {ts us : List DenormalizedProduct} (h : ts.Perm us) :
    maxTermExp ts = maxTermExp us := by
  unfold maxTermExp
  apply List.Perm.foldl_eq' (h.filterMap _)
  intro x _ y _ z
  cases z <;> simp only [Option.some.injEq] <;> omega

/-- Two optional results that both fail, or both succeed with permuted lists. -/
def PermOption {α : Type} : Option (List α) → Option (List α) → Prop
  | none, none => True
  | some u, some v => u.Perm v
  | _, _ => False

theorem mapM_perm {α β : Type} (f : α → Option β) {xs ys : List α} (h : xs.Perm ys) :
    PermOption (xs.mapM f) (ys.mapM f) := by
  induction h with
  | nil => simp [PermOption]
  | @cons x l₁ l₂ _ ih =>
    simp only [List.mapM_cons]
    revert ih
    generalize List.mapM f l₁ = o₁
    generalize List.mapM f l₂ = o₂
    intro ih
    cases f x <;> cases o₁ <;> cases o₂ <;> simp_all [PermOption]
  | swap x y l =>
    simp only [List.mapM_cons]
    generalize List.mapM f l = o
    cases f x <;> cases f y <;> cases o <;> simp [PermOption]
    exact List.Perm.swap _ _ _
  | trans _ _ ih₁ ih₂ =>
    revert ih₁ ih₂
    generalize List.mapM f _ = o₁
    generalize List.mapM f _ = o₂
    generalize List.mapM f _ = o₃
    intro h₁ h₂
    cases o₁ <;> cases o₂ <;> cases o₃ <;> simp_all [PermOption]
    exact h₁.trans h₂

theorem accumulator_perm {p : Model} {c : Decoded} {ps qs : List (Decoded × Decoded)}
    (h : ps.Perm qs) :
    (PreparedBlock.mk p ps c).accumulator = (PreparedBlock.mk p qs c).accumulator := by
  have ht : (PreparedBlock.mk p ps c).terms.Perm (PreparedBlock.mk p qs c).terms :=
    (h.map _).cons _
  unfold PreparedBlock.accumulator PreparedBlock.alignedBits PreparedBlock.alignGridExponent
    PreparedBlock.alignExp
  rw [maxTermExp_perm ht, sumZ_perm (ht.map _)]

/-- **The output depends on the products only as a multiset.** Permuting the products of a block
FMA changes neither whether it succeeds nor its output. -/
theorem evalBlock_perm {p : Model} {x y : BlockInput p} (hc : x.c = y.c)
    (hp : x.products.Perm y.products) :
    (evalBlock x).map (·.output) = (evalBlock y).map (·.output) := by
  have hm : PermOption (prepareProducts p x.products) (prepareProducts p y.products) := by
    unfold prepareProducts
    exact mapM_perm _ hp
  unfold evalBlock prepare
  rw [hp.length_eq, hc]
  split
  · rfl
  · revert hm
    generalize prepareProducts p x.products = o₁
    generalize prepareProducts p y.products = o₂
    intro hm
    cases o₁ <;> cases o₂ <;> simp only [PermOption] at hm <;> cases decode32 y.c <;> try rfl
    unfold evalPrepared
    simp only
    rw [accumulator_perm hm]
    split <;> try rfl
    split <;> rfl

end TensorCore
