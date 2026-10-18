import TensorCore.TC.CanonicalFormatDefs
import TensorCore.TC.Canonical

/-! Contracts of the BF16 and TF32 models. -/

namespace TensorCore

/-- Uncorrected output, error, and machine-width contract for any model. -/
theorem model_contract (p : Model) (F carryBits : ℕ) (hF : p.alignMantissaBits = F)
    (hc : p.nfma + 1 ≤ 2 ^ carryBits) (hw : 23 ≤ p.outputMantissaBits) (x : BlockInput p)
    (t : BlockTrace) (h : evalBlock x = .ok t) :
    exactDot x = some t.block.exactDot ∧
    round32 .truncate t.block.accumulator = some t.output.bits ∧
    absQ (t.block.exactDot - t.output.value) <
      ((p.nfma + 1 : ℕ) : ℚ) * pow2 t.block.alignGridExponent +
        pow2 (outputUlpExponent t.output.bits) ∧
    t.block.machineAccumulator (F + 3 + carryBits) = t.block.accumulator := by
  have hp := evalBlock_prepared h
  have hlen := (prepare_terms_bounded hp).1
  have hshape : x.products.length = p.nfma := by
    unfold evalBlock at h
    split at h <;> simp_all
  have herr := evalBlock_error_bound h hw
  have hm := evalBlock_machineAccumulator h F carryBits hF hc
  refine ⟨by simp [exactDot, hp], evalBlock_output h hw, ?_, ?_⟩
  · simpa [hlen, hshape] using herr
  · have he : F + 2 + carryBits + 1 = F + 3 + carryBits := by omega
    simpa [he] using hm

theorem bf16Fp32_contract (K padding carryBits : ℕ) (eAlignMin : Option ℤ)
    (x : BlockInput (bf16Fp32Model K padding eAlignMin)) (t : BlockTrace)
    (h : evalBlock x = .ok t) (hc : K + 1 ≤ 2 ^ carryBits) :
    exactDot x = some t.block.exactDot ∧
    round32 .truncate t.block.accumulator = some t.output.bits ∧
    absQ (t.block.exactDot - t.output.value) <
      ((K + 1 : ℕ) : ℚ) * pow2 t.block.alignGridExponent +
        pow2 (outputUlpExponent t.output.bits) ∧
    t.block.machineAccumulator (26 + padding + carryBits) = t.block.accumulator := by
  have := model_contract (bf16Fp32Model K padding eAlignMin) (23 + padding) carryBits rfl hc
    (Nat.le_refl 23) x t h
  have he : 23 + padding + 3 + carryBits = 26 + padding + carryBits := by omega
  simpa [he, bf16Fp32Model] using this

theorem tf19Fp32_contract (K padding carryBits : ℕ) (eAlignMin : Option ℤ)
    (x : BlockInput (tf19Fp32Model K padding eAlignMin)) (t : BlockTrace)
    (h : evalBlock x = .ok t) (hc : K + 1 ≤ 2 ^ carryBits) :
    exactDot x = some t.block.exactDot ∧
    round32 .truncate t.block.accumulator = some t.output.bits ∧
    absQ (t.block.exactDot - t.output.value) <
      ((K + 1 : ℕ) : ℚ) * pow2 t.block.alignGridExponent +
        pow2 (outputUlpExponent t.output.bits) ∧
    t.block.machineAccumulator (26 + padding + carryBits) = t.block.accumulator := by
  have := model_contract (tf19Fp32Model K padding eAlignMin) (23 + padding) carryBits rfl hc
    (Nat.le_refl 23) x t h
  have he : 23 + padding + 3 + carryBits = 26 + padding + carryBits := by omega
  simpa [he, tf19Fp32Model] using this

theorem a100BF16_descriptor : a100BF16Invocation = a100BF16F32.toInvocation 24 := rfl
theorem hopperBF16_descriptor : hopperBF16Invocation = hopperBF16F32.toInvocation 25 := rfl

theorem bf16Fp32_invocation_compatible (K padding : ℕ) (eAlignMin : Option ℤ)
    (x : BlockInput (bf16Fp32Model K padding eAlignMin)) :
    invocationBits (x.toInvocation (23 + padding)) =
      (evalBlock x).toOption.map (fun t => t.output.bits) :=
  legacy_invocation_bits x (23 + padding) (by change bf16.WellFormed; decide) rfl (Nat.le_refl 23)

theorem tf32Register_decode (K padding : ℕ) (eAlignMin : Option ℤ) (w : tf32Register.Word)
    (hp : tf32Padded w = true) :
    tf32Register.decode w = (tf19Fp32Model K padding eAlignMin).decode (tf32Unpack w) := by
  have hp' : w.toNat % 2 ^ 13 = 0 := by simpa [tf32Padded] using hp
  have hlt : w.toNat < 2 ^ 32 := w.isLt
  have hq : w.toNat / 2 ^ 13 % 2 ^ 19 = w.toNat / 2 ^ 13 := Nat.mod_eq_of_lt (by omega)
  show (if (w.toNat % 2 ^ 13 != 0) = true then none
    else (classifyNat tf19 (w.toNat / 2 ^ 13)).finite) =
    (classifyNat tf19 ((BitVec.ofNat 19 (w.toNat / 2 ^ 13)).toNat)).finite
  rw [BitVec.toNat_ofNat, hq, hp']
  rfl

theorem tf32Register_decode_unpadded (w : tf32Register.Word) (hp : tf32Padded w = false) :
    tf32Register.decode w = none := by
  have hp' : (w.toNat % 2 ^ 13 != 0) = true := by
    unfold tf32Padded at hp
    simpa using hp
  show (if (w.toNat % 2 ^ 13 != 0) = true then none
    else (classifyNat tf19 (w.toNat / 2 ^ 13)).finite) = none
  rw [if_pos hp']

theorem tf32_mapM (K padding : ℕ) (eAlignMin : Option ℤ)
    (ps : List (tf32Register.Word × tf32Register.Word))
    (hp : ∀ pair ∈ ps, tf32Padded pair.1 = true ∧ tf32Padded pair.2 = true) :
    ps.mapM (fun (a, b) => do return (← tf32Register.decode a, ← tf32Register.decode b)) =
      (tf32UnpackPairs ps).mapM (fun (a, b) => do
        return (← (tf19Fp32Model K padding eAlignMin).decode a,
          ← (tf19Fp32Model K padding eAlignMin).decode b)) := by
  induction ps with
  | nil => rfl
  | cons pair rest ih =>
    rcases pair with ⟨a, b⟩
    obtain ⟨ha, hb⟩ := hp (a, b) (by simp)
    simp only [tf32UnpackPairs, List.map_cons, List.mapM_cons]
    rw [tf32Register_decode K padding eAlignMin a ha, tf32Register_decode K padding eAlignMin b hb]
    have ih' := ih (fun q hq => hp q (by simp [hq]))
    simp only [tf32UnpackPairs] at ih'
    rw [ih']

/-- Descriptor evaluation of a TF32 variant on explicit register words. -/
def tf32InvocationBits (K F : ℕ) (eAlignMin : Option ℤ)
    (ps : List (tf32Register.Word × tf32Register.Word)) (c : F32) : Option F32 :=
  invocationBits (p := alignedInvocation tf32Register K F eAlignMin) ⟨ps, c⟩

theorem tf32_prepare (K F padding : ℕ) (eAlignMin : Option ℤ)
    (ps : List (tf32Register.Word × tf32Register.Word)) (c : F32)
    (hp : ∀ pair ∈ ps, tf32Padded pair.1 = true ∧ tf32Padded pair.2 = true) :
    prepareInvocation (p := alignedInvocation tf32Register K F eAlignMin) ⟨ps, c⟩ =
      (prepare (⟨tf32UnpackPairs ps, c⟩ : BlockInput (tf19Fp32Model K padding eAlignMin))).map
        (fun b => (⟨b.products, b.c⟩ : PreparedInvocation (alignedInvocation tf32Register K F eAlignMin))) := by
  show (do
    let c ← decode32 c
    let ps ← ps.mapM fun (a, b) => do
      return (← tf32Register.decode a, ← tf32Register.decode b)
    return (⟨ps, c⟩ : PreparedInvocation (alignedInvocation tf32Register K F eAlignMin))) = _
  rw [tf32_mapM K padding eAlignMin ps hp]
  change (do
    let c ← decode32 c
    let ps ← prepareProducts (tf19Fp32Model K padding eAlignMin) (tf32UnpackPairs ps)
    return (⟨ps, c⟩ : PreparedInvocation (alignedInvocation tf32Register K F eAlignMin))) = _
  unfold prepare
  cases decode32 c <;>
    cases prepareProducts (tf19Fp32Model K padding eAlignMin) (tf32UnpackPairs ps) <;> rfl

private theorem finite32_none' {bits : F32} (hd : decode32 bits = none) : finite32 bits = none := by
  unfold finite32
  split
  · rfl
  · rename_i d h
    rw [hd] at h
    contradiction

private theorem finite32_some' {bits : F32} {d : Decoded} (hd : decode32 bits = some d) :
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
theorem padded_prepared_bits (f : Format) (pad K F : ℕ) (eAlignMin : Option ℤ)
    (ps : List (Decoded × Decoded)) (c : Decoded) :
    (evalInvocationPrepared (p := alignedInvocation ⟨⟨f, .ieee⟩, pad⟩ K F eAlignMin)
      ⟨ps, c⟩).toOption.map (fun t => t.output.bits) =
      (evalPrepared ⟨⟨f, K, F, eAlignMin, 23⟩, ps, c⟩).toOption.map (fun t => t.output.bits) := by
  simp only [evalInvocationPrepared, accumulateInvocation, alignedInvocation,
    PreparedInvocation.alignedBlock, runRoundings]
  simp only [RoundingStage.roundValue, evalPrepared, ite_true, truncateMantissa32_23]
  rw [roundBinary_fp32 .truncate]
  cases hr : round32 .truncate (PreparedBlock.mk ⟨f, K, F, eAlignMin, 23⟩ ps c).accumulator with
  | none => rfl
  | some bits =>
    cases hd : decode32 bits with
    | none => simp [finite32_none' hd, finiteBinary_none hd]; rfl
    | some d => simp [finite32_some' hd, finiteBinary_some hd]; rfl

/-- On padded register words, a TF32 descriptor computes the block of the `tf19` model. -/
theorem tf32_invocation_bits (K padding : ℕ) (eAlignMin : Option ℤ)
    (ps : List (tf32Register.Word × tf32Register.Word)) (c : F32)
    (hp : ∀ pair ∈ ps, tf32Padded pair.1 = true ∧ tf32Padded pair.2 = true) :
    tf32InvocationBits K (23 + padding) eAlignMin ps c =
      (evalBlock (⟨tf32UnpackPairs ps, c⟩ : BlockInput (tf19Fp32Model K padding eAlignMin))).toOption.map
        (fun t => t.output.bits) := by
  have hv : (alignedInvocation tf32Register K (23 + padding) eAlignMin).Valid := by
    refine ⟨?_, ?_, rfl, ?_, trivial⟩
    · change tf19.WellFormed; decide
    · change fp32.WellFormed; decide
    · change fp32.WellFormed; decide
  unfold tf32InvocationBits invocationBits
  rw [evalInvocation, if_neg (by intro hn; exact hn hv)]
  unfold evalBlock
  dsimp only [alignedInvocation]
  have hlen : (tf32UnpackPairs ps).length = ps.length := by simp [tf32UnpackPairs]
  have hK : (tf19Fp32Model K padding eAlignMin).nfma = K := rfl
  rw [hlen, hK]
  by_cases hs : (ps.length != K) = true
  · rw [if_pos hs, if_pos hs]; rfl
  · rw [if_neg hs, if_neg hs, tf32_prepare K (23 + padding) padding eAlignMin ps c hp]
    dsimp only [prepare]
    cases decode32 c with
    | none => rfl
    | some c' =>
      cases prepareProducts (tf19Fp32Model K padding eAlignMin) (tf32UnpackPairs ps) with
      | none => rfl
      | some ps' => exact padded_prepared_bits tf19 13 K (23 + padding) eAlignMin ps' c'

theorem tf32_input_bits (K padding : ℕ) (eAlignMin : Option ℤ)
    (x : InvocationInput (alignedInvocation tf32Register K (23 + padding) eAlignMin))
    (hp : ∀ pair ∈ x.products, tf32Padded pair.1 = true ∧ tf32Padded pair.2 = true) :
    invocationBits x = (evalBlock (tf32Input x padding)).toOption.map (fun t => t.output.bits) :=
  tf32_invocation_bits K padding eAlignMin x.products x.c hp

theorem a100TF32_descriptor :
    a100TF32Invocation = alignedInvocation tf32Register 4 (23 + 1) (some (-132)) := rfl
theorem hopperTF32Wmma_descriptor :
    hopperTF32WmmaInvocation = alignedInvocation tf32Register 4 (23 + 2) (some (-133)) := rfl
theorem hopperTF32Mma_descriptor :
    hopperTF32MmaInvocation = alignedInvocation tf32Register 8 (23 + 2) (some (-133)) := rfl

end TensorCore
