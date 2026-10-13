import TCFloat.Equivalence.PortedTheorems

set_option backward.isDefEq.respectTransparency false
namespace TCFloat.Equivalence

/-- Both directions preserve every bit, including signed zeros and special encodings. -/
def wordEquiv (w : Nat) : BitVec w ≃ Fin (2^w) where
  toFun b := ⟨b.toNat,b.isLt⟩
  invFun n := BitVec.ofNat w n.val
  left_inv b := BitVec.eq_of_toNat_eq (Nat.mod_eq_of_lt b.isLt)
  right_inv n := Fin.ext (Nat.mod_eq_of_lt n.isLt)

def input (p : TCModel) (x : TensorCore.BlockInput (model p)) : Interface.Input p :=
  ⟨x.products.map fun (a,b) => (wordEquiv _ a,wordEquiv _ b),wordEquiv 32 x.c⟩

def sourceInput (p : TCModel) (x : Interface.Input p) : TensorCore.BlockInput (model p) :=
  ⟨x.products.map fun (a,b) => ((wordEquiv _).symm a,(wordEquiv _).symm b),
    (wordEquiv 32).symm x.c⟩

@[simp] theorem sourceInput_input (p : TCModel) (x : TensorCore.BlockInput (model p)) :
    sourceInput p (input p x)=x := by
  cases x with
  | mk ps c =>
    unfold sourceInput input
    congr 1
    · rw [List.map_map]
      change ps.map (fun ab => ((wordEquiv p.format.bitWidth).symm (wordEquiv p.format.bitWidth ab.1),
        (wordEquiv p.format.bitWidth).symm (wordEquiv p.format.bitWidth ab.2)))=ps
      simp only [Equiv.symm_apply_apply,Prod.mk.eta]
      exact List.map_id ps
    · exact (wordEquiv 32).symm_apply_apply c

@[simp] theorem input_sourceInput (p : TCModel) (x : Interface.Input p) :
    input p (sourceInput p x)=x := by
  cases x with
  | mk ps c =>
    unfold sourceInput input
    congr 1
    · rw [List.map_map]
      change ps.map (fun ab => (wordEquiv p.format.bitWidth ((wordEquiv p.format.bitWidth).symm ab.1),
        wordEquiv p.format.bitWidth ((wordEquiv p.format.bitWidth).symm ab.2)))=ps
      simp only [Equiv.apply_symm_apply,Prod.mk.eta]
      exact List.map_id ps
    · exact (wordEquiv 32).apply_symm_apply c

/-- A genuine isomorphism of the complete bounded encoded input carriers. -/
def inputEquiv (p : TCModel) : TensorCore.BlockInput (model p) ≃ Interface.Input p where
  toFun := input p
  invFun := sourceInput p
  left_inv := sourceInput_input p
  right_inv := input_sourceInput p

@[simp] theorem input_pairs (p : TCModel) (x : TensorCore.BlockInput (model p)) :
    (input p x).pairs=inputPairs x := by
  simp [input,Interface.Input.pairs,inputPairs,List.map_map,Function.comp_def,wordEquiv]

@[simp] theorem input_c (p : TCModel) (x : TensorCore.BlockInput (model p)) :
    (input p x).c.val=x.c.toNat := rfl
@[simp] theorem input_length (p : TCModel) (x : TensorCore.BlockInput (model p)) :
    (input p x).products.length=x.products.length := by simp [input]

def error : TensorCore.ModelError → Interface.Error
  | .wrongProductCount => .wrongProductCount
  | .nonfiniteInput => .nonfiniteInput
  | .accumulatorOutOfRange => .accumulatorOutOfRange
  | .nonfiniteOutput => .nonfiniteOutput

/-- Validation constructors correspond bijectively. -/
def errorEquiv : TensorCore.ModelError ≃ Interface.Error where
  toFun := error
  invFun e := match e with
    | .wrongProductCount => .wrongProductCount
    | .nonfiniteInput => .nonfiniteInput
    | .accumulatorOutOfRange => .accumulatorOutOfRange
    | .nonfiniteOutput => .nonfiniteOutput
  left_inv e := by cases e <;> rfl
  right_inv e := by cases e <;> rfl

theorem result_injective : Function.Injective result := by
  intro a b h
  cases a <;> cases b <;> simp [result] at h
  all_goals first | rfl | (cases BitVec.eq_of_toNat_eq h; rfl)

theorem encodedResult_injective : Function.Injective encodedResult := by
  intro a b h
  cases a with
  | allZero =>
    cases b with
    | allZero => rfl
    | consolidated b => cases b <;> simp [encodedResult,result] at h
  | consolidated a =>
    cases b with
    | allZero => cases a <;> simp [encodedResult,result] at h
    | consolidated b => exact congrArg TensorCore.EncodedEFTResult.consolidated (result_injective h)

/-- Exactly the legitimate tagged EFT outcomes, with a two-sided inverse. -/
noncomputable def eftResultEquiv : TensorCore.EncodedEFTResult ≃ Set.range encodedResult :=
  Equiv.ofInjective encodedResult encodedResult_injective

def observe {α β : Type} (f : α → β) : Except TensorCore.ModelError α → Except Interface.Error β
  | .error e => .error (error e)
  | .ok a => .ok (f a)

theorem tc_checked_eq (p : TCModel) (hf : p.format.isIEEE=true)
    (x : TensorCore.BlockInput (model p)) :
    Interface.tcChecked p (input p x)=observe (fun t => t.output.bits.toNat) (TensorCore.evalBlock x) := by
  by_cases hs : x.products.length=p.nfma
  · have hp := prepare_eq p hf x hs
    unfold Interface.tcChecked TensorCore.evalBlock
    simp only [input_length,input_pairs,input_c,model,hs,bne_self_eq_false,Bool.false_eq_true,ite_false]
    rw [← hp]
    cases hb : TCFloat.prepare p (inputPairs x) x.c.toNat with
    | none => rfl
    | some b =>
      simp only [Option.map_some]
      rw [evaluate_eq b (prepare_valid p hf x b hb)]
      cases hr : TensorCore.round32 .truncate (block b).accumulator with
      | none => simp [TensorCore.evalPrepared,hr,observe,error]
      | some bits =>
        obtain ⟨d,hd,hbits⟩ := round_finite .truncate _ bits hr
        simp [TensorCore.evalPrepared,hr,hd,observe,hbits]
  · have hs' : (x.products.length != p.nfma)=true := bne_iff_ne.mpr hs
    simp [Interface.tcChecked,TensorCore.evalBlock,input_length,model,hs',observe,error]

theorem eft_checked_eq (p : TCModel) (hf : p.format.isIEEE=true)
    (x : TensorCore.BlockInput (model p)) (D : TensorCore.F32) :
    Interface.eftChecked p (input p x) (wordEquiv 32 D)=
      observe encodedResult (TensorCore.tcEftEncoded x D) := by
  by_cases hs : x.products.length=p.nfma
  · have hp := prepare_eq p hf x hs
    unfold Interface.eftChecked TensorCore.tcEftEncoded TensorCore.prepareEncodedEFT
    simp only [input_length,input_pairs,input_c,model,hs,bne_self_eq_false,Bool.false_eq_true,ite_false]
    rw [← hp]
    cases hb : TCFloat.prepare p (inputPairs x) x.c.toNat with
    | none => rfl
    | some b =>
      simp only [Option.map_some]
      have ht := trace_algorithm_eq b (prepare_valid p hf x b hb) D
      change (match TCFloat.trace b D.toNat with
        | none => Except.error Interface.Error.nonfiniteOutput
        | some t => Except.ok t.encodedAlgorithm) = _
      cases htr : TCFloat.trace b D.toNat <;> cases hd : TensorCore.finite32 D <;>
        simp [htr,hd] at ht ⊢ <;> simp_all [observe,error]
  · have hs' : (x.products.length != p.nfma)=true := bne_iff_ne.mpr hs
    simp [Interface.eftChecked,TensorCore.tcEftEncoded,TensorCore.prepareEncodedEFT,
      input_length,model,hs',observe,error]

/-- Paper-scope equivalence through a two-sided input isomorphism, preserving errors, EFT branches and all output bits. -/
theorem floatlib_eq_reference (p : TCModel) (hf : SupportedFormat p.format)
    (x : TensorCore.BlockInput (model p)) (D : TensorCore.F32) :
    Interface.tcChecked p (inputEquiv p x)=
      observe (fun t => t.output.bits.toNat) (TensorCore.evalBlock x) ∧
    Interface.eftChecked p (inputEquiv p x) (wordEquiv 32 D)=
      observe encodedResult (TensorCore.tcEftEncoded x D) :=
  ⟨tc_checked_eq p hf.ieee x,eft_checked_eq p hf.ieee x D⟩

/-- The same theorem quantified over every port input, by the inverse isomorphism. -/
theorem floatlib_eq_reference_inverse (p : TCModel) (hf : SupportedFormat p.format)
    (x : Interface.Input p) (D : Fin (2^32)) :
    Interface.tcChecked p x=
      observe (fun t => t.output.bits.toNat) (TensorCore.evalBlock ((inputEquiv p).symm x)) ∧
    Interface.eftChecked p x D=
      observe encodedResult (TensorCore.tcEftEncoded ((inputEquiv p).symm x) ((wordEquiv 32).symm D)) := by
  simpa only [Equiv.apply_symm_apply] using floatlib_eq_reference p hf ((inputEquiv p).symm x) ((wordEquiv 32).symm D)

end TCFloat.Equivalence
