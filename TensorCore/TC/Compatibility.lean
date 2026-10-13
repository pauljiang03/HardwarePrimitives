import TensorCore.TC.InvocationProperties

/-! Block profiles agree with their invocation descriptors. -/

namespace TensorCore


def BlockInput.toInvocation {p : Model} (x : BlockInput p) (F : ℕ) :
    InvocationInput (p.toInvocation F) := ⟨x.products, x.c⟩

theorem prepareInvocation_legacy {p : Model} (x : BlockInput p) (F : ℕ) :
    prepareInvocation (x.toInvocation F) =
      (prepare x).map (fun b => (⟨b.products, b.c⟩ : PreparedInvocation (p.toInvocation F))) := by
  simp only [prepareInvocation, BlockInput.toInvocation, Model.toInvocation,
    packedIEEE, OperandEncoding.decode, ValueFormat.classifyNat, OperandEncoding.width,
    Nat.add_zero, Nat.pow_zero, Nat.mod_one, Nat.div_one, bne_self_eq_false,
    Bool.false_eq_true, ↓reduceIte]
  change (do
    let c ← decode32 x.c
    let ps ← prepareProducts p x.products
    return (⟨ps, c⟩ : PreparedInvocation (p.toInvocation F))) = _
  unfold prepare
  cases decode32 x.c <;> cases prepareProducts p x.products <;> rfl

private theorem finite32_none {bits : F32} (hd : decode32 bits = none) : finite32 bits = none := by
  unfold finite32
  split
  · rfl
  · rename_i d h
    rw [hd] at h
    contradiction

private theorem finite32_some {bits : F32} {d : Decoded} (hd : decode32 bits = some d) :
    finite32 bits = some ⟨bits, d, hd⟩ := by
  unfold finite32
  split
  · rename_i h
    rw [hd] at h
    contradiction
  · rename_i d' h
    rw [hd] at h
    cases Option.some.inj h
    rfl

set_option maxRecDepth 4096 in
theorem legacy_prepared_bits (p : Model) (ps : List (Decoded × Decoded)) (c : Decoded)
    (F : ℕ) (hF : p.alignFracBits = F) :
    (evalInvocationPrepared (p := p.toInvocation F) ⟨ps, c⟩).toOption.map (fun t => t.output.bits) =
      (evalPrepared ⟨p, ps, c⟩).toOption.map (fun t => t.output.bits) := by
  rcases p with ⟨f, K, af, eAlignMin⟩
  simp only at hF
  subst af
  simp only [evalInvocationPrepared, accumulateInvocation, Model.toInvocation,
    PreparedInvocation.alignedBlock, runRoundings]
  simp only [RoundingStage.roundValue, evalPrepared]
  simp only [packedIEEE, ite_true]
  rw [roundBinary_fp32 .truncate]
  cases hr : round32 .truncate (PreparedBlock.mk ⟨f, K, F, eAlignMin⟩ ps c).accumulator with
  | none => rfl
  | some bits =>
    cases hd : decode32 bits with
    | none => simp [finite32_none hd, finiteBinary_none hd]; rfl
    | some d => simp [finite32_some hd, finiteBinary_some hd]; rfl

set_option maxRecDepth 4096 in
theorem legacy_invocation_bits {p : Model} (x : BlockInput p) (F : ℕ)
    (hinput : p.input.WellFormed) (hF : p.alignFracBits = F) :
    invocationBits (x.toInvocation F) = (evalBlock x).toOption.map (fun t => t.output.bits) := by
  have hv : (p.toInvocation F).Valid := by
    refine ⟨hinput, ?_, rfl, ?_, trivial⟩ <;> change fp32.WellFormed <;> decide
  unfold invocationBits
  rw [evalInvocation, if_neg (by intro hn; exact hn hv)]
  simp only [BlockInput.toInvocation, Model.toInvocation]
  unfold evalBlock
  by_cases hs : x.products.length != p.nfma
  · simp [hs]; rfl
  · simp only [hs]
    have hp := prepareInvocation_legacy x F
    dsimp only [BlockInput.toInvocation, Model.toInvocation] at hp
    rw [hp]
    unfold prepare
    cases hc : decode32 x.c with
    | none => rfl
    | some c =>
      cases hp : prepareProducts p x.products with
      | none => rfl
      | some ps => exact legacy_prepared_bits p ps c F hF

theorem v100_invocation_bits (x : BlockInput v100F16F32) :
    invocationBits (x.toInvocation 23) = (evalV100 x).toOption.map (fun t => t.output.bits) :=
  legacy_invocation_bits x 23 (by decide) rfl

end TensorCore
