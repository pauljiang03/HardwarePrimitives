import TCFloat.Equivalence.Decode

set_option backward.isDefEq.respectTransparency false
namespace TCFloat.Equivalence
open FloatLib.Floats.Formats.BinaryInterchange

def model (p : TCModel) : TensorCore.Model :=
  ⟨format p.format,p.nfma,23+p.neab,p.eAlignMin⟩
def block (b : Block) : TensorCore.PreparedBlock :=
  ⟨model b.model,b.products.map (fun (a,b) => (project a,project b)),project b.c⟩
def unnormalizedTerm (t : Term) : TensorCore.UnnormalizedProduct :=
  ⟨t.dyadic.signedSignificand,t.unnormalizedExp,t.mantissaBits⟩

def ValidTerm (t : Term) : Prop := t.value = (project t).value
def ValidBlock (b : Block) : Prop :=
  ValidTerm b.c ∧ ∀ ab ∈ b.products, ValidTerm ab.1 ∧ ValidTerm ab.2

theorem unnormalizedTerm_mul (a b : Term) : unnormalizedTerm (a.mul b) = TensorCore.unnormalizedMul (project a) (project b) := by
  unfold unnormalizedTerm Term.mul TensorCore.unnormalizedMul project
  simp only [FloatLib.Numerics.Dyadic.mul,FloatLib.Numerics.Dyadic.mulFields,
    FloatLib.Numerics.Dyadic.signedSignificand]
  cases a.dyadic.negative <;> cases b.dyadic.negative <;> simp [Bool.xor]

theorem mul_valid {a b : Term} (ha : ValidTerm a) (hb : ValidTerm b) : ValidTerm (a.mul b) := by
  change (a.mul b).value = (unnormalizedTerm (a.mul b)).value
  rw [unnormalizedTerm_mul,TensorCore.unnormalizedProduct_value,TCFloat.mul_value,ha,hb]

theorem terms_eq (b : Block) : (block b).terms = b.terms.map unnormalizedTerm := by
  simp only [block,TensorCore.PreparedBlock.terms,Block.terms,List.map_cons,List.map_map]
  congr 1
  apply List.map_congr_left
  intro ab _
  exact (unnormalizedTerm_mul ab.1 ab.2).symm

theorem terms_valid (b : Block) (hb : ValidBlock b) :
    ∀ t ∈ b.terms, ValidTerm t := by
  intro t ht
  rcases List.mem_cons.mp ht with rfl | ht
  · exact hb.1
  · obtain ⟨⟨a,c⟩,hm,rfl⟩ := List.mem_map.mp ht
    exact mul_valid (hb.2 _ hm).1 (hb.2 _ hm).2

theorem ideal_eq (b : Block) (hb : ValidBlock b) : (block b).exactDot = b.ideal := by
  simp only [block,TensorCore.PreparedBlock.exactDot,TensorCore.PreparedBlock.exactProducts,
    Block.ideal,List.map_map,sumQ_eq]
  rw [← (show b.c.value = (project b.c).value from hb.1)]
  congr 1
  apply congrArg List.sum
  apply List.map_congr_left
  intro ab hm
  change (project ab.1).value * (project ab.2).value = ab.1.value * ab.2.value
  rw [← (hb.2 ab hm).1,← (hb.2 ab hm).2]

def maxOption (a b : Option Int) : Option Int :=
  match a,b with
  | none,b => b
  | a,none => a
  | some a,some b => some (max a b)

theorem maxOption_assoc (a b c : Option Int) :
    maxOption (maxOption a b) c = maxOption a (maxOption b c) := by
  cases a <;> cases b <;> cases c <;> simp [maxOption,max_assoc]

theorem fold_max (xs : List Int) (a : Option Int) :
    xs.foldl (fun acc e => some (match acc with | none => e | some v => max v e)) a =
      maxOption a (xs.foldr (fun e acc => maxOption (some e) acc) none) := by
  induction xs generalizing a with
  | nil => cases a <;> rfl
  | cons x xs ih =>
    simp only [List.foldl_cons,List.foldr_cons]
    rw [ih,← maxOption_assoc]
    cases a <;> rfl

theorem unnormalizedTerm_zero (t : Term) : (unnormalizedTerm t).significand = 0 ↔ t.dyadic.significand = 0 := by
  change t.dyadic.signedSignificand = 0 ↔ _
  rw [← Int.natAbs_eq_zero,FloatLib.Numerics.Dyadic.natAbs_signedSignificand]

theorem alignment_eq (ts : List Term) :
    TensorCore.maxTermExp (ts.map unnormalizedTerm) = maxTermExp ts := by
  have hf := fold_max
    ((ts.map unnormalizedTerm).filterMap fun t => if t.significand=0 then none else some t.unnormalizedExp) none
  change TensorCore.maxTermExp (ts.map unnormalizedTerm) =
    (List.foldr (fun e acc => maxOption (some e) acc) none
      ((ts.map unnormalizedTerm).filterMap fun t => if t.significand=0 then none else some t.unnormalizedExp)) at hf
  rw [hf]
  clear hf
  induction ts with
  | nil => rfl
  | cons t ts ih =>
    simp only [List.map_cons,List.filterMap_cons,unnormalizedTerm_zero,maxTermExp]
    by_cases hz : t.dyadic.significand = 0
    · simp only [hz,ite_true]
      exact ih
    · simp only [hz,ite_false,List.foldr_cons,ih]
      cases maxTermExp ts <;> rfl

theorem alignExp_eq (b : Block) : (block b).alignExp = b.alignExp := by
  unfold TensorCore.PreparedBlock.alignExp
  rw [terms_eq,alignment_eq]
  simp only [Block.alignExp,
    TensorCore.Model.applyEAlignMin,block,model]
  cases maxTermExp b.terms <;> cases b.model.eAlignMin <;> rfl

theorem q_eq (b : Block) : (block b).alignGridExponent = b.q := by
  unfold TensorCore.PreparedBlock.alignGridExponent
  rw [alignExp_eq]
  simp [Block.q,block,model]

theorem accumulator_eq (b : Block) (hb : ValidBlock b) : (block b).accumulator = b.accumulator := by
  rw [TensorCore.PreparedBlock.accumulator,← TensorCore.sum_coefficients]
  simp only [TensorCore.PreparedBlock.alignedBits,terms_eq,List.map_map,q_eq,
    truncCoeff_eq,pow2_eq,sumQ_eq,Block.accumulator,Block.aligned]
  apply congrArg List.sum
  apply List.map_congr_left
  intro t ht
  have hv := terms_valid b hb t ht
  change truncGrid (project t).value b.q = truncGrid t.value b.q
  rw [← hv]

theorem residuals_eq (b : Block) (hb : ValidBlock b) :
    (block b).alignmentResiduals = b.residuals := by
  simp only [TensorCore.PreparedBlock.alignmentResiduals,terms_eq,List.map_map,
    q_eq,truncGrid_eq,Block.residuals]
  apply List.map_congr_left
  intro t ht
  change (project t).value - truncGrid (project t).value b.q = _
  rw [← terms_valid b hb t ht]

end TCFloat.Equivalence
