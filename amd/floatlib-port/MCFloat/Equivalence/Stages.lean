import MCFloat.Equivalence.Words

/-! # Accumulation stages

For agreeing operands, FloatLib's products, `e_max`, aligned and grouped sums, and late addition
of `c` compute the `MatrixCore` values. -/

set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false

namespace MCFloat.Equivalence
open FloatLib.Floats.Formats.BinaryInterchange

structure ProdAgree (t : MCFloat.Term) (u : MatrixCore.Unpacked) : Prop where
  value : t.value = u.value
  exponent : t.exponent = u.e
  zero : t.isZero = (u.m == 0)

theorem mul_agree {a b : MCFloat.Term} {u v : MatrixCore.Unpacked}
    (ha : TermAgree a u) (hb : TermAgree b v) : ProdAgree (a.mul b) (u.mul v) where
  value := by
    simp only [MCFloat.Term.mul, MCFloat.Term.value, FloatLib.Numerics.Dyadic.mul_toRat,
      MatrixCore.Unpacked.value_mul]
    rw [← ha.value, ← hb.value]; rfl
  exponent := by simp [MCFloat.Term.mul, MatrixCore.Unpacked.mul, ha.exponent, hb.exponent]
  zero := by
    have hz := ha.zero
    have hz' := hb.zero
    unfold MCFloat.Term.isZero at hz hz' ⊢
    simp only [MCFloat.Term.mul, FloatLib.Numerics.Dyadic.mul, FloatLib.Numerics.Dyadic.mulFields,
      MatrixCore.Unpacked.mul]
    by_cases h1 : a.dyadic.significand = 0 <;> by_cases h2 : b.dyadic.significand = 0 <;>
      simp_all

theorem zip_agree {as bs : List MCFloat.Term} {us vs : List MatrixCore.Unpacked}
    (ha : List.Forall₂ TermAgree as us) (hb : List.Forall₂ TermAgree bs vs) :
    List.Forall₂ ProdAgree (List.zipWith MCFloat.Term.mul as bs)
      (List.zipWith MatrixCore.Unpacked.mul us vs) := by
  induction ha generalizing bs vs with
  | nil => simp
  | cons h _ ih =>
    cases hb with
    | nil => simp
    | cons h' hs => exact .cons (mul_agree h h') (ih hs)

theorem sum_agree {R : α → β → Prop} {f : α → ℚ} {g : β → ℚ} {xs : List α} {ys : List β}
    (h : List.Forall₂ R xs ys) (hfg : ∀ x y, R x y → f x = g y) :
    (xs.map f).sum = MatrixCore.sumQ (ys.map g) := by
  induction h with
  | nil => rfl
  | cons hr _ ih => simp only [List.map_cons, List.sum_cons, MatrixCore.sumQ, ih, hfg _ _ hr]

/-! ## `e_max` -/

theorem foldl_maxExpStep (acc : Option ℤ) (us : List MatrixCore.Unpacked) :
    us.foldl MatrixCore.maxExpStep acc =
      MatrixCore.joinExp acc (us.foldl MatrixCore.maxExpStep none) := by
  induction us generalizing acc with
  | nil => cases acc <;> rfl
  | cons u us ih =>
    simp only [List.foldl_cons]
    rw [ih, ih (MatrixCore.maxExpStep none u)]
    generalize us.foldl MatrixCore.maxExpStep none = r
    unfold MatrixCore.maxExpStep
    by_cases hm : u.m = 0 <;> cases acc <;> cases r <;> simp [hm, MatrixCore.joinExp]

theorem maxExp_cons (u : MatrixCore.Unpacked) (us : List MatrixCore.Unpacked) :
    MatrixCore.maxExp (u :: us) =
      MatrixCore.joinExp (MatrixCore.maxExpStep none u) (MatrixCore.maxExp us) := by
  unfold MatrixCore.maxExp
  rw [List.foldl_cons, foldl_maxExpStep]

theorem maxExp_agree {ps : List MCFloat.Term} {us : List MatrixCore.Unpacked}
    (h : List.Forall₂ ProdAgree ps us) : MCFloat.maxExp ps = MatrixCore.maxExp us := by
  induction h with
  | nil => rfl
  | @cons p u ps us hr _ ih =>
    have hz := hr.zero
    have hstep : MCFloat.maxExp (p :: ps) = if p.isZero then MCFloat.maxExp ps
        else some (match MCFloat.maxExp ps with | none => p.exponent | some e => max p.exponent e) :=
      rfl
    rw [hstep, ih, maxExp_cons]
    generalize MatrixCore.maxExp us = r
    unfold MatrixCore.maxExpStep
    by_cases hm : u.m = 0
    · have h0 : p.isZero = true := by simp [hz, hm]
      simp only [h0, hm, ite_true]
      cases r <;> rfl
    · have h0 : p.isZero = false := by simp [hz, hm]
      simp only [h0, hm, Bool.false_eq_true, ite_false, hr.exponent]
      cases r <;> simp [MatrixCore.joinExp]

/-! ## Aligned and grouped sums -/

theorem alignedSum_agree {ps : List MCFloat.Term} {us : List MatrixCore.Unpacked}
    (h : List.Forall₂ ProdAgree ps us) : MCFloat.alignedSum ps = MatrixCore.alignedSum 1 us := by
  unfold MCFloat.alignedSum MatrixCore.alignedSum
  rw [maxExp_agree h]
  cases MatrixCore.maxExp us with
  | none => rfl
  | some e =>
    simp only [Prod.mk.injEq, true_and]
    apply sum_agree h
    intro p u hp
    rw [hp.value]
    simp only [MatrixCore.truncMantissa, truncGrid_eq]
    congr 1

theorem odds_agree {R : α → β → Prop} :
    ∀ {l : List α} {l' : List β}, List.Forall₂ R l l' →
      List.Forall₂ R (MCFloat.odds l) (MatrixCore.oddIndexed l') ∧
        List.Forall₂ R (MCFloat.evens l) (MatrixCore.evenIndexed l')
  | [], [], .nil => by simp [MCFloat.odds, MCFloat.evens, MatrixCore.oddIndexed, MatrixCore.evenIndexed]
  | [_], [_], .cons h .nil => by
    simp [MCFloat.odds, MCFloat.evens, MatrixCore.oddIndexed, MatrixCore.evenIndexed, h]
  | _ :: _ :: _, _ :: _ :: _, .cons h1 (.cons h2 h3) => by
    have ih := odds_agree h3
    simp only [MCFloat.odds, MCFloat.evens, MatrixCore.oddIndexed, MatrixCore.evenIndexed]
    exact ⟨.cons h1 ih.1, .cons h2 ih.2⟩

theorem productSum_agree (Q : MatrixCore.Model) (hpadding : Q.padding = 1) (i : Bool)
    (hacc : Q.accumulation = if i then .oddEvenGrouping else .globalAlignment)
    {ps : List MCFloat.Term} {us : List MatrixCore.Unpacked} (h : List.Forall₂ ProdAgree ps us) :
    (if i then MCFloat.groupedSum ps else MCFloat.alignedSum ps) = MatrixCore.productSum Q us := by
  unfold MatrixCore.productSum
  rw [hacc, hpadding]
  cases i
  · exact alignedSum_agree h
  · simp only [ite_true]
    unfold MCFloat.groupedSum
    rw [alignedSum_agree (odds_agree h).1, alignedSum_agree (odds_agree h).2]
    generalize MatrixCore.alignedSum 1 (MatrixCore.oddIndexed us) = o
    generalize MatrixCore.alignedSum 1 (MatrixCore.evenIndexed us) = v
    obtain ⟨o1, o2⟩ := o
    obtain ⟨v1, v2⟩ := v
    cases o1 <;> cases v1 <;> simp [MatrixCore.joinExp, MatrixCore.rdMantissa]

/-! ## Late `c` -/

theorem lateC_agree (Q : MatrixCore.Model) (cut : Option ℕ)
    (hz : Q.cZeroExp = some (-126)) (hl : Q.late = { cCutoff := cut })
    {c : MCFloat.Term} {u : MatrixCore.Unpacked} (hc : TermAgree c u) (eMax : Option ℤ) (s : ℚ) :
    MCFloat.lateC cut eMax s c = MatrixCore.lateSum Q eMax s u := by
  have heC : (if c.isZero then (-126 : ℤ) else c.exponent) = if u.m = 0 then -126 else u.e := by
    have := hc.zero
    have he := hc.exponent
    by_cases hm : u.m = 0 <;> simp_all
  unfold MCFloat.lateC MatrixCore.lateSum MatrixCore.cExp MatrixCore.shiftedC MatrixCore.shiftedSum
    MatrixCore.normalizeRD
  rw [hz, hl, heC, hc.value]
  have hcexp : (if u.m = 0 then some (-126 : ℤ) else some u.e) =
      some (if u.m = 0 then -126 else u.e) := by split <;> rfl
  rw [hcexp]
  simp only [MatrixCore.rdMantissa, rdGrid_eq]
  generalize (if u.m = 0 then (-126 : ℤ) else u.e) = eC
  have hshift : (if MCFloat.rdGrid s (eC - 32) + u.value = 0 then 0
      else MCFloat.rdGrid (MCFloat.rdGrid s (eC - 32) + u.value)
        (MCFloat.normExp (MCFloat.rdGrid s (eC - 32) + u.value) - 31)) =
      (if MCFloat.rdGrid s (eC - ((32 : ℕ) : ℤ)) + u.value = 0 then 0
      else MCFloat.rdGrid (MCFloat.rdGrid s (eC - ((32 : ℕ) : ℤ)) + u.value)
        (MatrixCore.normExp (MatrixCore.absQ (MCFloat.rdGrid s (eC - ((32 : ℕ) : ℤ)) + u.value)) -
          ((31 : ℕ) : ℤ))) := by
    push_cast
    split
    · rfl
    · rename_i hne; rw [normExp_eq _ hne]
  cases eMax with
  | none => exact hshift
  | some e =>
    simp only
    split
    · cases cut <;> simp
    · exact hshift

end MCFloat.Equivalence
