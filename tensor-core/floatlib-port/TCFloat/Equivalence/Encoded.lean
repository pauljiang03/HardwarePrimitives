import TCFloat.Equivalence.EFT
import TCFloat.Interface

set_option backward.isDefEq.respectTransparency false
namespace TCFloat.Equivalence
open FloatLib.Floats.Formats.BinaryInterchange

def inputPairs {p : TCModel} (x : TensorCore.BlockInput (model p)) : List (Nat × Nat) :=
  x.products.map fun (a,b) => (a.toNat,b.toNat)

theorem option_mapM {α β γ : Type} (xs : List α) (f : α → Option β) (g : α → Option γ)
    (proj : β → γ) (h : ∀ a, (f a).map proj = g a) :
    (xs.mapM f).map (List.map proj) = xs.mapM g := by
  induction xs with
  | nil => rfl
  | cons a xs ih =>
    simp only [List.mapM_cons]
    rw [← h a]
    cases hf : f a <;> cases hs : xs.mapM f <;>
      simp [hs] at ih ⊢ <;> simp [← ih]

theorem option_mapM_valid {α β : Type} (xs : List α) (f : α → Option β) (P : β → Prop)
    (h : ∀ a b, f a = some b → P b) (ys : List β) (hy : xs.mapM f = some ys) :
    ∀ b ∈ ys, P b := by
  induction xs generalizing ys with
  | nil => simp at hy; subst ys; simp
  | cons a xs ih =>
    simp only [List.mapM_cons] at hy
    cases hf : f a with
    | none => simp [hf] at hy
    | some b =>
      cases hs : xs.mapM f with
      | none => simp [hf,hs] at hy
      | some bs =>
        simp [hf,hs] at hy
        subst ys
        intro c hc
        rcases List.mem_cons.mp hc with hcb|hc
        · subst c
          exact h a b hf
        · exact ih bs hs c hc

def pairDecode (p : TCModel) (ab : (model p).Word × (model p).Word) : Option (Term × Term) := do
  return (← decode p.format ab.1.toNat, ← decode p.format ab.2.toNat)

theorem pair_decode_eq (p : TCModel) (hf : p.format.isIEEE=true)
    (ab : (model p).Word × (model p).Word) :
    (pairDecode p ab).map (fun (a,b) => (project a,project b)) =
      (do return (← (model p).decode ab.1, ← (model p).decode ab.2)) := by
  have ha := decode_project p.format hf ab.1.toNat ab.1.isLt
  have hb := decode_project p.format hf ab.2.toNat ab.2.isLt
  change _ = (model p).decode ab.1 at ha
  change _ = (model p).decode ab.2 at hb
  rw [← ha,← hb]
  cases hda : decode p.format ab.1.toNat <;> cases hdb : decode p.format ab.2.toNat <;>
    simp [pairDecode,hda,hdb]

theorem pair_decode_valid (p : TCModel) (hf : p.format.isIEEE=true)
    (ab : (model p).Word × (model p).Word) (v : Term × Term)
    (hv : pairDecode p ab=some v) : ValidTerm v.1 ∧ ValidTerm v.2 := by
  unfold pairDecode at hv
  cases ha : decode p.format ab.1.toNat <;> cases hb : decode p.format ab.2.toNat <;>
    simp [ha,hb] at hv
  subst v
  exact ⟨decode_value p.format hf _ _ ha,decode_value p.format hf _ _ hb⟩

/-- Preparation commutes with projection, given the shape check. -/
theorem prepare_eq (p : TCModel) (hf : p.format.isIEEE=true)
    (x : TensorCore.BlockInput (model p)) (hshape : x.products.length=p.nfma) :
    (TCFloat.prepare p (inputPairs x) x.c.toNat).map block = TensorCore.prepare x := by
  have hc := decode_project .binary32 (by decide) x.c.toNat x.c.isLt
  change _ = TensorCore.decode32 x.c at hc
  have hp := option_mapM x.products (pairDecode p)
    (fun (a,b) => do return (← (model p).decode a,← (model p).decode b))
    (fun (a,b) => (project a,project b)) (pair_decode_eq p hf)
  change _ = TensorCore.prepareProducts (model p) x.products at hp
  unfold TCFloat.prepare inputPairs
  simp only [List.length_map,hshape,bne_self_eq_false,List.mapM_map]
  change (do
    let c ← decode .binary32 x.c.toNat
    let ps ← x.products.mapM (pairDecode p)
    pure (Block.mk p c ps)).map block = _
  unfold TensorCore.prepare
  rw [← hc,← hp]
  cases decode .binary32 x.c.toNat <;> cases x.products.mapM (pairDecode p) <;> rfl

theorem prepare_valid (p : TCModel) (hf : p.format.isIEEE=true)
    (x : TensorCore.BlockInput (model p)) (b : Block)
    (hb : TCFloat.prepare p (inputPairs x) x.c.toNat=some b) : ValidBlock b := by
  unfold TCFloat.prepare inputPairs at hb
  simp only [List.length_map,List.mapM_map] at hb
  split at hb
  · simp at hb
  · change (do
      let c ← decode .binary32 x.c.toNat
      let ps ← x.products.mapM (pairDecode p)
      pure (Block.mk p c ps)) = some b at hb
    cases hc : decode .binary32 x.c.toNat with
    | none => simp [hc] at hb
    | some c =>
      cases hp : x.products.mapM (pairDecode p) with
      | none => simp [hc,hp] at hb
      | some ps =>
        simp [hc,hp] at hb
        subst b
        exact ⟨decode_value .binary32 (by decide) _ _ hc,
          option_mapM_valid x.products (pairDecode p) _ (pair_decode_valid p hf) ps hp⟩

theorem finite32_value (d : TensorCore.F32) :
    (TensorCore.finite32 d).map TensorCore.Finite32.value = TensorCore.value32 d := by
  unfold TensorCore.finite32
  split <;> rename_i hd <;>
    simp only [Option.map_none,Option.map_some,TensorCore.value32,hd,TensorCore.Finite32.value]

theorem finite32_bits (d : TensorCore.F32) (v : TensorCore.Finite32)
    (h : TensorCore.finite32 d=some v) : v.bits=d := by
  unfold TensorCore.finite32 at h
  split at h
  · contradiction
  · cases Option.some.inj h; rfl

theorem round_finite (m : TensorCore.RoundingMode) (x : Rat) (b : TensorCore.F32)
    (h : TensorCore.round32 m x=some b) :
    ∃ d, TensorCore.finite32 b=some d ∧ d.bits=b := by
  have hv : ∃ v, TensorCore.value32 b=some v := by
    by_cases hz : x=0
    · subst x
      have hh : TensorCore.round32 m 0=some 0 := by cases m <;> decide +kernel
      rw [hh] at h
      cases Option.some.inj h
      exact ⟨0,by decide +kernel⟩
    · obtain ⟨b',hb,hv,_,_⟩ := TensorCore.round32_nonzero_spec m x hz (TensorCore.round32_range h)
      rw [h] at hb
      cases Option.some.inj hb
      exact ⟨_,hv⟩
  obtain ⟨v,hv⟩ := hv
  obtain ⟨d,hd,hb,_⟩ := TensorCore.finite32_of_value32 b v hv
  exact ⟨d,hd,hb⟩

theorem evalPrepared_bits (b : TensorCore.PreparedBlock) (hw : b.model.outputMantissaBits = 23) :
    (TensorCore.evalPrepared b).toOption.map (fun t => t.output.bits.toNat) =
      (TensorCore.round32 .truncate b.accumulator).map BitVec.toNat := by
  cases hr : TensorCore.round32 .truncate b.accumulator with
  | none => simp [TensorCore.evalPrepared,hr,Except.toOption]
  | some bits =>
    obtain ⟨d,hd,hb⟩ := round_finite .truncate _ bits hr
    simp [TensorCore.evalPrepared,hr,hw,hd,hb,Except.toOption]

theorem trace_algorithm_eq (b : Block) (hb : ValidBlock b) (D : TensorCore.F32) :
    (TCFloat.trace b D.toNat).map Trace.encodedAlgorithm =
      (TensorCore.finite32 D).map (fun d => encodedResult
        (if (block b).allZeroTerms then .allZero else .consolidated (TensorCore.BlockTrace.mk (block b) d).tcEft)) := by
  have hv := finite32_value D
  have hn : ¬D.toNat ≥ 2^32 := Nat.not_le.mpr D.isLt
  rw [← value32_eq] at hv
  cases hd : TensorCore.finite32 D with
  | none =>
    rw [hd] at hv
    simp only [Option.map_none] at hv
    simp [TCFloat.trace,hv.symm]
  | some d =>
    rw [hd] at hv
    simp only [Option.map_some] at hv
    have hbits := finite32_bits D d hd
    have hrel : TraceRel ⟨block b,d⟩ ⟨b,D.toNat,d.value⟩ :=
      ⟨rfl,congrArg BitVec.toNat hbits,rfl,hb⟩
    have ht : TCFloat.trace b D.toNat=some ⟨b,D.toNat,d.value⟩ := by
      unfold TCFloat.trace
      rw [ite_eq_right hn,hv.symm]
      rfl
    rw [ht]
    exact congrArg some (encoded_trace_eq hrel)

/-- Encoded Tensor Core equality on every input, including malformed and rejected inputs. -/
theorem tc_encoded_eq (p : TCModel) (hf : p.format.isIEEE=true)
    (x : TensorCore.BlockInput (model p)) :
    Interface.tc p (inputPairs x) x.c.toNat =
      (TensorCore.evalBlock x).toOption.map (fun t => t.output.bits.toNat) := by
  by_cases hs : x.products.length=p.nfma
  · have hp := prepare_eq p hf x hs
    unfold Interface.tc TensorCore.evalBlock
    simp only [model,hs,bne_self_eq_false,Bool.false_eq_true,ite_false]
    rw [← hp]
    cases hb : TCFloat.prepare p (inputPairs x) x.c.toNat with
    | none => rfl
    | some b =>
      simp only [Option.map_some,Option.bind_some]
      rw [evalPrepared_bits _ (block_outputMantissaBits b)]
      exact evaluate_eq b (prepare_valid p hf x b hb)
  · have hs' : (x.products.length != p.nfma)=true := bne_iff_ne.mpr hs
    simp [Interface.tc,TCFloat.prepare,inputPairs,TensorCore.evalBlock,model,hs',Except.toOption]

/-- Encoded EFT equality: the same validation, branch and bits, for every supplied FP32 D. -/
theorem eft_encoded_eq (p : TCModel) (hf : p.format.isIEEE=true)
    (x : TensorCore.BlockInput (model p)) (D : TensorCore.F32) :
    Interface.eft p (inputPairs x) x.c.toNat D.toNat =
      (TensorCore.tcEftEncoded x D).toOption.map encodedResult := by
  by_cases hs : x.products.length=p.nfma
  · have hp := prepare_eq p hf x hs
    unfold Interface.eft TensorCore.tcEftEncoded TensorCore.prepareEncodedEFT
    simp only [model,hs,bne_self_eq_false,Bool.false_eq_true,ite_false]
    rw [← hp]
    cases hb : TCFloat.prepare p (inputPairs x) x.c.toNat with
    | none => rfl
    | some b =>
      simp only [Option.map_some,Option.bind_some]
      rw [trace_algorithm_eq b (prepare_valid p hf x b hb) D]
      cases TensorCore.finite32 D <;> rfl
  · have hs' : (x.products.length != p.nfma)=true := bne_iff_ne.mpr hs
    simp [Interface.eft,TCFloat.prepare,inputPairs,TensorCore.tcEftEncoded,
      TensorCore.prepareEncodedEFT,model,hs',Except.toOption]

/-- The encoded Tensor Core and EFT interfaces commute with the same input translation. -/
theorem universal_equivalence (p : TCModel) (hf : p.format.isIEEE=true)
    (x : TensorCore.BlockInput (model p)) (D : TensorCore.F32) :
    Interface.tc p (inputPairs x) x.c.toNat =
        (TensorCore.evalBlock x).toOption.map (fun t => t.output.bits.toNat) ∧
    Interface.eft p (inputPairs x) x.c.toNat D.toNat =
        (TensorCore.tcEftEncoded x D).toOption.map encodedResult :=
  ⟨tc_encoded_eq p hf x,eft_encoded_eq p hf x D⟩

end TCFloat.Equivalence
