import MatrixCore.MC.Chain
import MatrixCore.MC.CorrectRounding
import MatrixCore.MC.PairWiseSum
import MatrixCore.MC.LateAccumulation
import MatrixCore.MC.MachineRefinement
import MatrixCore.MC.ErrorBounds
import MatrixCore.MC.AprioriBounds

/-! # Per-model contracts

What is proved about one accepted block, bundled per configuration and carried to every block of
an inner product. -/

namespace MatrixCore

/-! ## Every model -/

/-- Guarantees of one accepted block on any model. -/
structure BlockContract {P : Model} (x : BlockInput P) (t : BlockTrace P) : Prop where
  lengths : x.a.length = P.nfma ∧ x.b.length = P.nfma
  prepared : prepare x = some t.prepared
  c : (fp32.decode x.c).toFinite = some t.prepared.c
  /-- Every operand has a significand below 2, so every product has one below 4. -/
  operands : (∀ u ∈ t.prepared.a, u.m < 2 ^ (u.t + 1)) ∧ (∀ u ∈ t.prepared.b, u.m < 2 ^ (u.t + 1))
  products : ∀ p ∈ t.prepared.p, p.m < 2 ^ (p.t + 2)
  accumulated : accumulate P t.prepared = .ok t.sAcc
  inRange : absQ t.sAcc < overflowThreshold32
  /-- `d = fl{S_acc}`. -/
  output : fl32 (!P.subnormals) t.sAcc = some t.d
  /-- The output is finite. -/
  value : value32 t.d = some (wordValue t.d)
  /-- The final `fl{·}`: half an ulp, plus `2^-126` where subnormal results are flushed. -/
  outputError : absQ (t.sAcc - wordValue t.d) ≤ flBound (!P.subnormals) t.sAcc
  nearestEven : P.subnormals = true → NearestEven32 t.sAcc t.d

theorem evalBlock_contract {P : Model} {x : BlockInput P} {t : BlockTrace P}
    (h : evalBlock x = .ok t) : BlockContract x t := by
  obtain ⟨ha, hb, hp, hs, hd⟩ := evalBlock_ok h
  obtain ⟨_, hA, hB⟩ := prepare_bounded hp
  refine ⟨⟨ha, hb⟩, hp, prepare_c hp, ⟨hA, hB⟩, products_bounded hA hB, hs, ?_, hd,
    fl32_value hd, evalBlock_output_error h, fun hsub => evalBlock_nearestEven h hsub⟩
  rw [← fl32_isSome_iff (!P.subnormals), hd]; rfl

/-! ## SFMA and CDNA 1 -/

structure CorrectRoundingContract {P : Model} (x : BlockInput P) (t : BlockTrace P) : Prop
    extends BlockContract x t where
  exact : t.sAcc = t.prepared.exact
  nearest : NearestEven32 t.prepared.exact t.d
  error : absQ (t.prepared.exact - wordValue t.d) ≤ halfUlp32 t.prepared.exact
  /-- From the inputs alone. -/
  apriori : absQ (t.prepared.exact - wordValue t.d) ≤ pow2 (-24) * t.prepared.absSum + pow2 (-150)

theorem correctRounding_contract {P : Model} (hacc : P.accumulation = .correctRounding)
    (hov : P.productOverflow = false) (hs : P.subnormals = true)
    {x : BlockInput P} {t : BlockTrace P} (h : evalBlock x = .ok t) :
    CorrectRoundingContract x t :=
  { evalBlock_contract h with
    exact := (correctRounding_nearestEven hacc hov hs h).1
    nearest := (correctRounding_nearestEven hacc hov hs h).2
    error := correctRounding_error hacc hov hs h
    apriori := correctRounding_apriori hacc hov hs h }

/-! ## CDNA 2 -/

structure PairwiseContract {P : Model} (x : BlockInput P) (t : BlockTrace P) : Prop
    extends BlockContract x t where
  /-- `S_acc` is `c` plus the pairwise sum of the rounded products. -/
  tree : pairwiseSum P t.prepared = some t.sAcc
  /-- Input flushing, product conversion, the pairwise sum and the final `fl{·}`. -/
  error : absQ (t.prepared.exact - wordValue t.d) ≤
    pairwiseBound P t.prepared + flBound (!P.subnormals) t.sAcc
  /-- From the inputs alone, after flushing subnormals. -/
  apriori : absQ (t.prepared.exact - wordValue t.d) ≤
    absQ (t.prepared.exact - (if P.subnormals then t.prepared else t.prepared.flushed).exact) +
      pow2 (-21) * (if P.subnormals then t.prepared else t.prepared.flushed).absSum + pow2 (-120)

theorem pairwise_contract {P : Model} (hacc : P.accumulation = .pairWiseSum) (hn : P.nfma ≤ 4)
    {x : BlockInput P} {t : BlockTrace P} (h : evalBlock x = .ok t) : PairwiseContract x t :=
  { evalBlock_contract h with
    tree := accumulate_pairwise hacc (evalBlock_ok h).2.2.2.1
    error := pairwise_error hacc h
    apriori := pairwise_apriori hacc hn h }

/-! ## CDNA 3 -/

/-- The error bounds of `alignedAccumulation_error` for a prepared block. -/
def AlignedErrorBounds (P : Model) (x : Prepared) : Prop :=
  let s := productSum P x.p
  let F : ℕ := 23 + P.padding
  let D := x.exact - alignedAccumulation P x
  (cExp P x.c = none → ∀ e, s.1 = some e → absQ D ≤ (x.p.length + 2) * pow2 (e - F)) ∧
  (∀ e eC, s.1 = some e → cExp P x.c = some eC → eC ≤ e →
    absQ D < (x.p.length + 2) * pow2 (e - F) + pow2 (e - P.late.cMantissaBits)) ∧
  (∀ e eC, s.1 = some e → cExp P x.c = some eC → e < eC →
    let T := rdGrid s.2 (eC - P.late.sumMantissaBits) + x.c.value
    0 ≤ D + (x.p.length + 2) * pow2 (e - F) ∧
      D < (x.p.length + 2) * pow2 (e - F) + pow2 (eC - P.late.sumMantissaBits) +
        pow2 (normExp (absQ T) - P.late.accMantissaBits)) ∧
  (∀ eC, s.1 = none → cExp P x.c = some eC →
    let T := rdGrid s.2 (eC - P.late.sumMantissaBits) + x.c.value
    0 ≤ D ∧ D < pow2 (eC - P.late.sumMantissaBits) + pow2 (normExp (absQ T) - P.late.accMantissaBits))

structure AlignedContract {P : Model} (x : BlockInput P) (t : BlockTrace P) (w : ℕ) : Prop
    extends BlockContract x t where
  /-- `S_acc` of Algorithm 1 or 2. -/
  sum : t.sAcc = alignedAccumulation P t.prepared
  /-- Error of `S_acc` against the exact `Σ p_ℓ + c`, by branch. -/
  sumError : AlignedErrorBounds P t.prepared
  error : absQ (t.prepared.exact - wordValue t.d) ≤
    alignedBound P t.prepared + flBound (!P.subnormals) t.sAcc
  /-- Accumulating in `w`-bit registers gives the same block. -/
  register : evalBlockMachine w x = .ok t
  /-- From the inputs alone. -/
  apriori : absQ (t.prepared.exact - wordValue t.d) ≤ pow2 (-23) * t.prepared.absSum +
    (t.prepared.p.length + 4) * gridTerm (productSum P t.prepared.p).1 + pow2 (-149)

theorem aligned_contract {P : Model}
    (hacc : P.accumulation = .globalAlignment ∨ P.accumulation = .oddEvenGrouping)
    (hL : LateModel P) (hsub : P.subnormals = true) (w carryBits : ℕ) (hcount : P.nfma ≤ 2 ^ carryBits)
    (hw : P.alignMantissaBits + 2 + carryBits + 1 ≤ w)
    {x : BlockInput P} {t : BlockTrace P} (h : evalBlock x = .ok t) : AlignedContract x t w := by
  have hb := evalBlock_contract h
  have hcut : ∀ n, P.late.cCutoff = some n → P.late.cMantissaBits ≤ n := fun n h => by
    rw [hL.cMantissa]; exact hL.cut n h
  have hcz : P.cZeroExp ≠ none := by rw [hL.cZero]; simp
  have hsum : t.sAcc = alignedAccumulation P t.prepared := accumulate_aligned hacc hb.accumulated
  refine ⟨hb, hsum, ?_, aligned_error hacc hcut hcz h, ?_, aligned_apriori hL hacc hsub h⟩
  · exact alignedAccumulation_error P t.prepared hcut (prepare_cExp_bound hb.prepared)
  · rw [evalBlockMachine_eq x w carryBits hcount hw]; exact h

/-! ## The models -/

theorem sfmaF32_contract {x : BlockInput sfmaF32} {t : BlockTrace sfmaF32}
    (h : evalBlock x = .ok t) : CorrectRoundingContract x t :=
  correctRounding_contract rfl rfl rfl h

theorem cdna1F16_contract {x : BlockInput cdna1F16} {t : BlockTrace cdna1F16}
    (h : evalBlock x = .ok t) : CorrectRoundingContract x t :=
  correctRounding_contract rfl rfl rfl h

theorem cdna1BF16_contract {x : BlockInput cdna1BF16} {t : BlockTrace cdna1BF16}
    (h : evalBlock x = .ok t) : CorrectRoundingContract x t :=
  correctRounding_contract rfl rfl rfl h

theorem cdna2F16_contract {x : BlockInput cdna2F16} {t : BlockTrace cdna2F16}
    (h : evalBlock x = .ok t) : PairwiseContract x t :=
  pairwise_contract rfl (by decide) h

theorem cdna2BF16_contract {x : BlockInput cdna2BF16} {t : BlockTrace cdna2BF16}
    (h : evalBlock x = .ok t) : PairwiseContract x t :=
  pairwise_contract rfl (by decide) h

theorem cdna2BF16_1k_contract {x : BlockInput cdna2BF16_1k} {t : BlockTrace cdna2BF16_1k}
    (h : evalBlock x = .ok t) : PairwiseContract x t :=
  pairwise_contract rfl (by decide) h

theorem cdna3F16_contract {x : BlockInput cdna3F16} {t : BlockTrace cdna3F16}
    (h : evalBlock x = .ok t) : AlignedContract x t 30 :=
  aligned_contract (.inl rfl) lateModel_cdna3F16 rfl 30 3 (by decide) (by decide) h

theorem cdna3BF16_contract {x : BlockInput cdna3BF16} {t : BlockTrace cdna3BF16}
    (h : evalBlock x = .ok t) : AlignedContract x t 30 :=
  aligned_contract (.inl rfl) lateModel_cdna3BF16 rfl 30 3 (by decide) (by decide) h

theorem cdna3XF32_contract {x : BlockInput cdna3XF32} {t : BlockTrace cdna3XF32}
    (h : evalBlock x = .ok t) : AlignedContract x t 29 :=
  aligned_contract (.inl rfl) lateModel_cdna3XF32 rfl 29 2 (by decide) (by decide) h

theorem cdna3FP8_contract (fa fb : Format) {x : BlockInput (cdna3FP8 fa fb)}
    {t : BlockTrace (cdna3FP8 fa fb)} (h : evalBlock x = .ok t) : AlignedContract x t 31 :=
  aligned_contract (.inr rfl) (lateModel_cdna3FP8 fa fb) rfl 31 4 (by simp [cdna3FP8])
    (by simp [cdna3FP8, Model.alignMantissaBits]) h

/-! ## Inner products -/

/-- An accepted inner product is a run of linked blocks, each with any property `Q` of blocks. -/
theorem dotBits_blocks (P : Model) {Q : BlockInput P → BlockTrace P → Prop}
    (hQ : ∀ x t, evalBlock x = .ok t → Q x t)
    {a : List P.a.Word} {b : List P.b.Word} {c d : F32}
    (hlen : a.length = b.length) (h : dotBits P a b c = .ok d) :
    ∃ ts, runBlocks P c (blocks P a b) = .ok ts ∧ lastOutput c ts = d ∧ Chain c ts ∧
      (∀ t ∈ ts, ∃ x, Q x t) ∧
      wordValue c + sumQ (ts.map fun t => t.prepared.products) =
        wordValue d + sumQ (ts.map BlockTrace.residual) := by
  obtain ⟨ts, hr, hd, hc, _, hl⟩ := dotBits_residual_ledger P hlen h
  exact ⟨ts, hr, hd, hc, runBlocks_all hQ hr, hl⟩

/-- Every block of an accepted inner product satisfies the contract of every model. -/
theorem dotBits_contract (P : Model) {a : List P.a.Word} {b : List P.b.Word} {c d : F32}
    (hlen : a.length = b.length) (h : dotBits P a b c = .ok d) :
    ∃ ts, runBlocks P c (blocks P a b) = .ok ts ∧ lastOutput c ts = d ∧ Chain c ts ∧
      ∀ t ∈ ts, ∃ x, BlockContract x t := by
  obtain ⟨ts, hr, hd, hc, hall, _⟩ := dotBits_blocks P (fun _ _ h => evalBlock_contract h) hlen h
  exact ⟨ts, hr, hd, hc, hall⟩

/-- Error of an inner product: at most the sum of the blocks' residual bounds `B`. -/
theorem dotBits_error_bound (P : Model) {B : BlockTrace P → ℚ}
    (hB : ∀ x t, evalBlock x = .ok t → absQ t.residual ≤ B t)
    {a : List P.a.Word} {b : List P.b.Word} {c d : F32}
    (hlen : a.length = b.length) (h : dotBits P a b c = .ok d) :
    ∃ ts, runBlocks P c (blocks P a b) = .ok ts ∧ lastOutput c ts = d ∧
      absQ (wordValue c + sumQ (ts.map fun t => t.prepared.products) - wordValue d) ≤
        sumQ (ts.map B) := by
  obtain ⟨ts, hr, hd, _, hall, hl⟩ :=
    dotBits_blocks P (Q := fun _ t => absQ t.residual ≤ B t) hB hlen h
  refine ⟨ts, hr, hd, ?_⟩
  rw [hl, show wordValue d + sumQ (ts.map BlockTrace.residual) - wordValue d =
    sumQ (ts.map BlockTrace.residual) by grind]
  refine Rat.le_trans (absQ_sumQ_le _) ?_
  rw [List.map_map]
  apply sumQ_map_mono
  intro t ht
  obtain ⟨_, hx⟩ := hall t ht
  exact hx

/-- SFMA and CDNA 1: an inner product is within the sum of half an ulp of each block's exact sum. -/
theorem correctRounding_dot_error {P : Model} (hacc : P.accumulation = .correctRounding)
    (hov : P.productOverflow = false) (hs : P.subnormals = true)
    {a : List P.a.Word} {b : List P.b.Word} {c d : F32}
    (hlen : a.length = b.length) (h : dotBits P a b c = .ok d) :
    ∃ ts, runBlocks P c (blocks P a b) = .ok ts ∧ lastOutput c ts = d ∧
      absQ (wordValue c + sumQ (ts.map fun t => t.prepared.products) - wordValue d) ≤
        sumQ (ts.map fun t => halfUlp32 t.prepared.exact) :=
  dotBits_error_bound P (fun _ _ ht => (correctRounding_contract hacc hov hs ht).error) hlen h

end MatrixCore
