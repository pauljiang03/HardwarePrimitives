import TensorCore.Numerics.FP8
import TensorCore.Numerics.CorrectRounding
import TensorCore.TC.Instruction
import TensorCore.TC.CanonicalEAlignMin
import TensorCore.TC.CanonicalFormats

/-! # Ada, H200, B200 and the FP8 block FMAs

Ada and B200 reuse the FP16, BF16 and TF32 models of A100 and H100 respectively (*Accurate
Models*, Table 3), and H200 uses the Hopper models. The FP8 block FMAs of Ada, Hopper and B200 all
truncate, and Table 3 lists no minimum alignment exponent for them. -/

namespace TensorCore

/-! ## FP16, BF16 and TF32 -/

/-- Ada (RTX 1000 Ada, L40S) FP16 → FP32: A100's features. -/
@[implicit_reducible] def adaF16F32 : Model := ampereF16F32
/-- Ada BF16 → FP32: A100's features. -/
@[implicit_reducible] def adaBF16F32 : Model := a100BF16F32
/-- Ada TF32 → FP32: A100's features. -/
@[implicit_reducible] def adaTF32F32 : Model := a100TF32F32

/-- B200 FP16 → FP32: H100's features. -/
@[implicit_reducible] def blackwellF16F32 : Model := hopperF16F32
/-- B200 BF16 → FP32: H100's features. -/
@[implicit_reducible] def blackwellBF16F32 : Model := hopperBF16F32
/-- B200 TF32 → FP32 through WMMA, with blocks of four products: H100's features. -/
@[implicit_reducible] def blackwellTF32WmmaF32 : Model := hopperTF32WmmaF32
/-- B200 TF32 → FP32 with N_FMA = 8: H100's features. -/
@[implicit_reducible] def blackwellTF32MmaF32 : Model := hopperTF32MmaF32

/-! ## FP8 -/

/-- Ada (RTX 1000 Ada, L40S) E4M3 → FP32, with operands in the `e4m3x` layout. -/
@[implicit_reducible] def adaE4M3F32 : Model := ⟨e4m3x, 16, 13, none, 13⟩
/-- Ada (RTX 1000 Ada, L40S) E5M2 → FP32. -/
@[implicit_reducible] def adaE5M2F32 : Model := ⟨e5m2, 16, 13, none, 13⟩
/-- H100 and H200 E4M3 → FP32 through `wgmma`, with operands in the `e4m3x` layout. -/
@[implicit_reducible] def hopperE4M3F32 : Model := ⟨e4m3x, 32, 13, none, 13⟩
/-- H100 and H200 E5M2 → FP32 through `wgmma`. -/
@[implicit_reducible] def hopperE5M2F32 : Model := ⟨e5m2, 32, 13, none, 13⟩
/-- B200 E4M3 → FP32 through `tcgen05.mma`, with operands in the `e4m3x` layout. -/
@[implicit_reducible] def blackwellE4M3F32 : Model := ⟨e4m3x, 32, 25, none, 23⟩
/-- B200 E5M2 → FP32 through `tcgen05.mma`. -/
@[implicit_reducible] def blackwellE5M2F32 : Model := ⟨e5m2, 32, 25, none, 23⟩

/-- E4M3 operand pairs in the `e4m3x` layout of the block model. -/
def widenE4M3Pairs (ps : List (BitVec 8 × BitVec 8)) : List (BitVec 9 × BitVec 9) :=
  ps.map fun (a, b) => (widenE4M3 a, widenE4M3 b)

theorem prepareProducts_widenE4M3 (K : ℕ) (F : ℤ) (e : Option ℤ) (m : ℕ)
    (ps : List (BitVec 8 × BitVec 8)) :
    prepareProducts (⟨e4m3x, K, F, e, m⟩ : Model) (widenE4M3Pairs ps) =
      ps.mapM fun (a, b) => do return (← e4m3Encoding.decode a, ← e4m3Encoding.decode b) := by
  induction ps with
  | nil => rfl
  | cons ab rest ih =>
    rcases ab with ⟨a, b⟩
    simp only [widenE4M3Pairs, List.map_cons, prepareProducts, List.mapM_cons] at ih ⊢
    rw [ih, e4m3_decode_widen a, e4m3_decode_widen b]
    rfl

/-! ## The block output -/

theorem fp8_outputMantissaBits :
    adaE4M3F32.outputMantissaBits = 13 ∧ adaE5M2F32.outputMantissaBits = 13 ∧
    hopperE4M3F32.outputMantissaBits = 13 ∧ hopperE5M2F32.outputMantissaBits = 13 ∧
    blackwellE4M3F32.outputMantissaBits = 23 ∧ blackwellE5M2F32.outputMantissaBits = 23 :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- Ada and Hopper FP8: the FP32 truncation of the accumulator with the ten low mantissa bits cleared. -/
theorem fp8_output_thirteen_bits {p : Model} (hp : p.outputMantissaBits = 13) {x : BlockInput p}
    {t : BlockTrace} (h : evalBlock x = .ok t) :
    ∃ bits, round32 .truncate t.block.accumulator = some bits ∧
      t.output.bits = BitVec.ofNat 32 (bits.toNat / 2 ^ 10 * 2 ^ 10) := by
  obtain ⟨bits, hr, ht⟩ := evalPrepared_output_mantissa (evalBlock_evalPrepared h)
  refine ⟨bits, hr, ?_⟩
  rw [ht, evalBlock_model h, hp]
  rfl

/-! ## The minimum alignment exponent -/

theorem prepare_terms_lower (p : Model) (hbias : p.input.bias ≤ 64) (x : BlockInput p)
    (b : PreparedBlock) (h : prepare x = some b) :
    ∀ t ∈ b.terms, t.significand ≠ 0 → -126 ≤ t.exponent := by
  unfold prepare at h
  cases hc : decode32 x.c with
  | none => simp [hc] at h
  | some c =>
    cases hp : prepareProducts p x.products with
    | none => simp [hc, hp] at h
    | some ps =>
      simp [hc, hp] at h
      subst b
      intro t ht hnz
      simp only [PreparedBlock.terms, List.mem_cons, List.mem_map] at ht
      rcases ht with ht | ⟨pair, hpair, ht⟩
      · subst t
        exact classifyNat_scale_lower fp32 x.c.toNat c hc hnz
      · subst t
        obtain ⟨w, _, ha, hb⟩ := prepareProducts_origin _ _ _ hp pair hpair
        have hnza : pair.1.significand ≠ 0 := by
          intro hz; apply hnz; simp [denormalizedMul, hz]
        have hnzb : pair.2.significand ≠ 0 := by
          intro hz; apply hnz; simp [denormalizedMul, hz]
        have hla := classifyNat_scale_lower p.input w.1.toNat pair.1 ha hnza
        have hlb := classifyNat_scale_lower p.input w.2.toNat pair.2 hb hnzb
        change -126 ≤ pair.1.exponent + pair.2.exponent
        omega

theorem evalPrepared_bits_of_accumulator {b b' : PreparedBlock}
    (h : b.accumulator = b'.accumulator) (hw : b.model.outputMantissaBits = b'.model.outputMantissaBits) :
    (evalPrepared b).toOption.map (fun t => t.output.bits) =
      (evalPrepared b').toOption.map (fun t => t.output.bits) := by
  unfold evalPrepared
  rw [h, hw]
  split
  · rfl
  · split <;> rfl

/-- A minimum alignment exponent of at most −126 is inactive for input formats of bias at most 64. -/
theorem evalBlock_eAlignMin_inactive (p : Model) (hbias : p.input.bias ≤ 64)
    (hf : ∀ f ∈ p.eAlignMin, f ≤ -126) (x : BlockInput p) :
    (evalBlock x).toOption.map (fun t => t.output.bits) =
      (evalBlock (⟨x.products, x.c⟩ : BlockInput {p with eAlignMin := none})).toOption.map
        (fun t => t.output.bits) := by
  unfold evalBlock
  by_cases hs : (x.products.length != p.nfma) = true
  · rw [if_pos hs, if_pos hs]
  · rw [if_neg hs, if_neg hs]
    have hprep := prepare_terms_lower p hbias x
    unfold prepare at hprep ⊢
    cases hc : decode32 x.c with
    | none => rfl
    | some c =>
      have hq : prepareProducts {p with eAlignMin := none} x.products =
          prepareProducts p x.products := rfl
      rw [hq]
      cases hps : prepareProducts p x.products with
      | none => rfl
      | some ds =>
        simp only [hc, hps] at hprep
        have hl := hprep ⟨p, ds, c⟩ rfl
        show (evalPrepared ⟨p, ds, c⟩).toOption.map _ =
          (evalPrepared ⟨{p with eAlignMin := none}, ds, c⟩).toOption.map _
        refine evalPrepared_bits_of_accumulator (b := ⟨p, ds, c⟩)
          (b' := ⟨{p with eAlignMin := none}, ds, c⟩) ?_ rfl
        have he : (PreparedBlock.mk p ds c).alignExp =
            (PreparedBlock.mk {p with eAlignMin := none} ds c).alignExp := by
          change p.applyEAlignMin (maxTermExp (PreparedBlock.mk p ds c).terms) =
            Model.applyEAlignMin {p with eAlignMin := none}
              (maxTermExp (PreparedBlock.mk p ds c).terms)
          cases hm : maxTermExp (PreparedBlock.mk p ds c).terms with
          | none => rfl
          | some e =>
            have hemin := maxTermExp_lower _ (-126) e hl hm
            cases hpe : p.eAlignMin with
            | none => simp [Model.applyEAlignMin, hpe]
            | some f =>
              have hf' := hf f (by simp [hpe])
              simp only [Model.applyEAlignMin, hpe, Option.some.injEq]
              omega
        unfold PreparedBlock.accumulator PreparedBlock.alignedBits PreparedBlock.alignGridExponent
        rw [he]
        rfl

/-- The toolbox's minimum alignment exponents (−132, −133) are inactive on every FP8 model. -/
theorem fp8_eAlignMin_inactive :
    (∀ x : BlockInput adaE4M3F32,
      (evalBlock (⟨x.products, x.c⟩ : BlockInput {adaE4M3F32 with eAlignMin := some (-132)})).toOption.map
        (·.output.bits) = (evalBlock x).toOption.map (·.output.bits)) ∧
    (∀ x : BlockInput adaE5M2F32,
      (evalBlock (⟨x.products, x.c⟩ : BlockInput {adaE5M2F32 with eAlignMin := some (-132)})).toOption.map
        (·.output.bits) = (evalBlock x).toOption.map (·.output.bits)) ∧
    (∀ x : BlockInput hopperE4M3F32,
      (evalBlock (⟨x.products, x.c⟩ : BlockInput {hopperE4M3F32 with eAlignMin := some (-133)})).toOption.map
        (·.output.bits) = (evalBlock x).toOption.map (·.output.bits)) ∧
    (∀ x : BlockInput hopperE5M2F32,
      (evalBlock (⟨x.products, x.c⟩ : BlockInput {hopperE5M2F32 with eAlignMin := some (-133)})).toOption.map
        (·.output.bits) = (evalBlock x).toOption.map (·.output.bits)) ∧
    (∀ x : BlockInput blackwellE4M3F32,
      (evalBlock (⟨x.products, x.c⟩ :
        BlockInput {blackwellE4M3F32 with eAlignMin := some (-133)})).toOption.map
        (·.output.bits) = (evalBlock x).toOption.map (·.output.bits)) ∧
    (∀ x : BlockInput blackwellE5M2F32,
      (evalBlock (⟨x.products, x.c⟩ :
        BlockInput {blackwellE5M2F32 with eAlignMin := some (-133)})).toOption.map
        (·.output.bits) = (evalBlock x).toOption.map (·.output.bits)) := by
  have hf : ∀ e : ℤ, e ≤ -126 → ∀ f ∈ some e, f ≤ -126 := by
    intro e he f hf
    simp only [Option.mem_def, Option.some.injEq] at hf
    omega
  exact ⟨fun x => evalBlock_eAlignMin_inactive {adaE4M3F32 with eAlignMin := some (-132)}
      (by decide) (hf _ (by decide)) ⟨x.products, x.c⟩,
    fun x => evalBlock_eAlignMin_inactive {adaE5M2F32 with eAlignMin := some (-132)}
      (by decide) (hf _ (by decide)) ⟨x.products, x.c⟩,
    fun x => evalBlock_eAlignMin_inactive {hopperE4M3F32 with eAlignMin := some (-133)}
      (by decide) (hf _ (by decide)) ⟨x.products, x.c⟩,
    fun x => evalBlock_eAlignMin_inactive {hopperE5M2F32 with eAlignMin := some (-133)}
      (by decide) (hf _ (by decide)) ⟨x.products, x.c⟩,
    fun x => evalBlock_eAlignMin_inactive {blackwellE4M3F32 with eAlignMin := some (-133)}
      (by decide) (hf _ (by decide)) ⟨x.products, x.c⟩,
    fun x => evalBlock_eAlignMin_inactive {blackwellE5M2F32 with eAlignMin := some (-133)}
      (by decide) (hf _ (by decide)) ⟨x.products, x.c⟩⟩

/-! ## Recursive summation of block FMAs -/

/-- Blocks as the toolbox's `GEMM.m` forms them: increasing `k`, zero-padded to a multiple of N_FMA. -/
def Model.blocksOf (p : Model) (ps : List (p.Word × p.Word)) : List (List (p.Word × p.Word)) :=
  let n := (ps.length + p.nfma - 1) / p.nfma
  chunks p.nfma n (ps ++ List.replicate (n * p.nfma - ps.length) (0, 0))

/-- `c + Σ aᵢbᵢ` by recursive summation of block FMAs; `c` when there are no products. -/
def Model.dot (p : Model) (c : F32) (ps : List (p.Word × p.Word)) : Option F32 :=
  match runBlocks p c (p.blocksOf ps) with
  | .ok ts => some ((ts.getLast?.map fun t => t.output.bits).getD c)
  | .error _ => none

/-- With exactly N_FMA products the inner product is one block FMA. -/
theorem Model.dot_one_block (p : Model) (hK : 0 < p.nfma) (c : F32)
    (ps : List (p.Word × p.Word)) (h : ps.length = p.nfma) :
    p.dot c ps = (evalBlock (⟨ps, c⟩ : BlockInput p)).toOption.map (fun t => t.output.bits) := by
  have hn : (ps.length + p.nfma - 1) / p.nfma = 1 := by
    rw [h, show p.nfma + p.nfma - 1 = p.nfma - 1 + 1 * p.nfma by omega,
      Nat.add_mul_div_right _ _ hK, Nat.div_eq_of_lt (by omega)]
  have hb : p.blocksOf ps = [ps] := by
    show chunks p.nfma ((ps.length + p.nfma - 1) / p.nfma)
      (ps ++ List.replicate ((ps.length + p.nfma - 1) / p.nfma * p.nfma - ps.length) (0, 0)) = [ps]
    rw [hn, Nat.one_mul, h, Nat.sub_self, List.replicate_zero, List.append_nil]
    show ps.take p.nfma :: chunks p.nfma 0 (ps.drop p.nfma) = [ps]
    rw [List.take_of_length_le (by omega)]
    rfl
  unfold Model.dot
  rw [hb]
  simp only [runBlocks]
  cases evalBlock (⟨ps, c⟩ : BlockInput p) <;> rfl

/-- `d + c` in FP32, rounded to nearest even. -/
def addFp32 (d c : F32) : Option F32 := do
  round32 .nearestEven ((← value32 d) + (← value32 c))

/-- `addFp32` returns the FP32 value nearest the exact sum, ties to even. -/
theorem addFp32_nearestEven {d c o : F32} {u v : ℚ} (hd : value32 d = some u)
    (hc : value32 c = some v) (h : addFp32 d c = some o) : NearestEven32 (u + v) o := by
  simp only [addFp32, hd, hc, Option.bind_eq_bind, Option.bind_some] at h
  obtain ⟨b, hb, hn⟩ := round32_nearestEven_correct (u + v) (round32_range h)
  rw [h] at hb
  cases Option.some.inj hb
  exact hn

/-- The block FMAs from `c = 0`, then `c` added in FP32 with round-to-nearest-even. -/
def Model.dotThenAdd (p : Model) (c : F32) (ps : List (p.Word × p.Word)) : Option F32 := do
  addFp32 (← p.dot 0 ps) c

/-! ## Invocation descriptors -/

/-- FP32's exponent range with 13 mantissa bits: the block output of Ada and Hopper FP8. -/
@[implicit_reducible] def fp32Mantissa13 : Format := ⟨13, 8, 127⟩

/-- An FP8 descriptor with a 13-bit block output. -/
@[implicit_reducible] def narrowInvocation (input : OperandEncoding) (K : ℕ) : InvocationSpec :=
  ⟨input, fp32, K, .aligned 13 none .early, [⟨fp32Mantissa13, .truncate⟩], ⟨fp32, .truncate⟩⟩

def adaE4M3Invocation : InvocationSpec := narrowInvocation e4m3Encoding 16
def adaE5M2Invocation : InvocationSpec := narrowInvocation e5m2Encoding 16
def hopperE4M3Invocation : InvocationSpec := narrowInvocation e4m3Encoding 32
def hopperE5M2Invocation : InvocationSpec := narrowInvocation e5m2Encoding 32
def blackwellE4M3Invocation : InvocationSpec := alignedInvocation e4m3Encoding 32 25 none
def blackwellE5M2Invocation : InvocationSpec := alignedInvocation e5m2Encoding 32 25 none

/-- A B200 FP8 block from `c = 0` truncated to FP32, then `c` added with round-to-nearest-even. -/
@[implicit_reducible] def thenAddInvocation (input : OperandEncoding) : InvocationSpec :=
  ⟨input, fp32, 32, .aligned 25 none (.late [⟨fp32, .truncate⟩]), [], ⟨fp32, .nearestEven⟩⟩

def blackwellE4M3ThenAddInvocation : InvocationSpec := thenAddInvocation e4m3Encoding
def blackwellE5M2ThenAddInvocation : InvocationSpec := thenAddInvocation e5m2Encoding

theorem fp8_descriptors_valid :
    adaE4M3Invocation.Valid ∧ adaE5M2Invocation.Valid ∧ hopperE4M3Invocation.Valid ∧
    hopperE5M2Invocation.Valid ∧ blackwellE4M3Invocation.Valid ∧ blackwellE5M2Invocation.Valid ∧
    blackwellE4M3ThenAddInvocation.Valid ∧ blackwellE5M2ThenAddInvocation.Valid := by
  decide

end TensorCore
