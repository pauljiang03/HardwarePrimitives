import TCFloat.Equivalence.RoundingStage
import TCFloat.Equivalence.Block

set_option backward.isDefEq.respectTransparency false
namespace TCFloat.Equivalence

/-- Representation relation only: no arithmetic or algorithm agreement is assumed. -/
structure TraceRel (s : TensorCore.BlockTrace) (t : Trace) : Prop where
  block_eq : s.block = block t.block
  bits_eq : s.output.bits.toNat = t.bits
  output_eq : s.output.value = t.output
  valid : ValidBlock t.block

theorem evaluate_eq (b : Block) (hb : ValidBlock b) :
    b.evaluate = (TensorCore.round32 .truncate (block b).accumulator).map
      (fun w => truncateMantissa b.model.outputMantissaBits w.toNat) := by
  rw [accumulator_eq b hb, Block.evaluate, round32_rtz_eq, Option.map_map]
  rfl

theorem representable_eq (x : Rat) : TCFloat.representable x = TensorCore.representable32 x := by
  unfold TCFloat.representable TensorCore.representable32
  rw [round32_rne_eq]
  cases h : TensorCore.round32 .nearestEven x <;> simp [value32_eq]

theorem add_eq (x y : Rat) : TCFloat.add32 x y = TensorCore.fp32Add x y := by
  unfold TCFloat.add32 TensorCore.fp32Add
  rw [round32_rne_eq]
  cases h : TensorCore.round32 .nearestEven (x+y) <;> simp [value32_eq]

theorem naiveSum_eq (a : Rat) (xs : List Rat) :
    TCFloat.naiveSumFrom a xs = TensorCore.naiveSum32From a xs := by
  induction xs generalizing a with
  | nil => rfl
  | cons x xs ih =>
    simp only [TCFloat.naiveSumFrom,TensorCore.naiveSum32From,add_eq]
    cases TensorCore.fp32Add a x <;> simp [ih]

theorem extraction_eq {s : TensorCore.BlockTrace} {t : Trace} (h : TraceRel s t) :
    s.extractionExponent = t.extractionExponent := by
  unfold TensorCore.BlockTrace.extractionExponent Trace.extractionExponent
  rw [h.block_eq,q_eq]
  unfold TensorCore.outputUlpExponent
  rw [h.bits_eq]
  rfl

theorem coarse_eq {s : TensorCore.BlockTrace} {t : Trace} (h : TraceRel s t) : s.coarse = t.coarse := by
  unfold TensorCore.BlockTrace.coarse Trace.coarse
  rw [h.block_eq,terms_eq,extraction_eq h]
  simp only [List.map_map,truncGrid_eq]
  apply List.map_congr_left
  intro x hx
  change truncGrid (project x).value t.extractionExponent = _
  rw [← terms_valid t.block h.valid x hx]

theorem lows_eq {s : TensorCore.BlockTrace} {t : Trace} (h : TraceRel s t) : s.lowParts = t.lowParts := by
  unfold TensorCore.BlockTrace.lowParts Trace.lowParts
  rw [h.block_eq,terms_eq,extraction_eq h]
  simp only [List.map_map,truncGrid_eq]
  apply List.map_congr_left
  intro x hx
  change (project x).value - truncGrid (project x).value t.extractionExponent = _
  rw [← terms_valid t.block h.valid x hx]

theorem retained_eq {s : TensorCore.BlockTrace} {t : Trace} (h : TraceRel s t) :
    s.retainedSum = t.retained := by
  simp only [TensorCore.BlockTrace.retainedSum,coarse_eq h,sumQ_eq,Trace.retained]

theorem overlap_eq {s : TensorCore.BlockTrace} {t : Trace} (h : TraceRel s t) :
    s.overlap = t.overlap := by
  simp only [TensorCore.BlockTrace.overlap,retained_eq h,h.output_eq,Trace.overlap]

theorem residual_eq {s : TensorCore.BlockTrace} {t : Trace} (h : TraceRel s t) :
    s.residual = t.residual := by
  simp only [TensorCore.BlockTrace.residual,TensorCore.PreparedBlock.extractReference,
    h.block_eq,accumulator_eq _ h.valid,h.output_eq,residuals_eq _ h.valid,sumQ_eq,Trace.residual]

theorem trailingZeroBitsAux_eq (fuel n : Nat) :
    TensorCore.trailingZeroBitsAux fuel n = trailingZeroBitsAux fuel n := by
  induction fuel generalizing n with
  | zero => rfl
  | succ k ih => simp only [TensorCore.trailingZeroBitsAux, trailingZeroBitsAux, ih]

theorem lowestBitExp_eq (x : ℚ) : TensorCore.lowestBitExp x = lowestBitExp x := by
  simp only [TensorCore.lowestBitExp, TensorCore.trailingZeroBits, lowestBitExp, trailingZeroBitsAux_eq]

theorem support_eq {s : TensorCore.BlockTrace} {t : Trace} (h : TraceRel s t) :
    s.lowestLowBitExp = t.supportExponent := by
  unfold TensorCore.BlockTrace.lowestLowBitExp Trace.supportExponent
  rw [lows_eq h,extraction_eq h]
  simp only [lowestBitExp_eq]

theorem lowCoefficients_eq {s : TensorCore.BlockTrace} {t : Trace} (h : TraceRel s t) :
    s.lowBits = t.lowCoefficients := by
  unfold TensorCore.BlockTrace.lowBits Trace.lowCoefficients
  rw [lows_eq h,support_eq h]
  rfl

theorem magnitudeSum_eq (xs : List Int) : TensorCore.magnitudeSum xs = (xs.map Int.natAbs).sum := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [TensorCore.magnitudeSum,ih]

theorem guard_eq {s : TensorCore.BlockTrace} {t : Trace} (h : TraceRel s t) :
    s.scalarPredicate = t.scalarPredicate := by
  simp only [TensorCore.BlockTrace.scalarPredicate,Trace.scalarPredicate,
    support_eq h,lows_eq h,lowCoefficients_eq h,magnitudeSum_eq,
    h.output_eq,overlap_eq h,retained_eq h,representable_eq,
    abs_eq,maxFinite_eq,sumQ_eq,pow2_eq]

theorem scalarUnchecked_eq {s : TensorCore.BlockTrace} {t : Trace} (h : TraceRel s t) :
    t.scalarUnchecked = s.scalarCorrectedUnchecked.map BitVec.toNat := by
  unfold Trace.scalarUnchecked TensorCore.BlockTrace.scalarCorrectedUnchecked TensorCore.naiveSum32
  rw [lows_eq h,h.output_eq,overlap_eq h]
  rw [naiveSum_eq,add_eq]
  cases TensorCore.naiveSum32From 0 t.lowParts <;> simp only [Option.bind_none,Option.bind_some,Option.map_none]
  cases TensorCore.fp32Add t.output (-t.overlap) <;>
    simp only [Option.bind_none,Option.bind_some,Option.map_none]
  exact round32_eq .nearestEven _

theorem scalar_eq {s : TensorCore.BlockTrace} {t : Trace} (h : TraceRel s t) :
    t.scalar = s.scalarCorrected.map BitVec.toNat := by
  unfold Trace.scalar TensorCore.BlockTrace.scalarCorrected
  rw [guard_eq h]
  cases t.scalarPredicate <;> simp [scalarUnchecked_eq h]

theorem consolidation_eq {s : TensorCore.BlockTrace} {t : Trace} (h : TraceRel s t) :
    t.exactConsolidation = s.exactConsolidation.map BitVec.toNat := by
  unfold Trace.exactConsolidation TensorCore.BlockTrace.exactConsolidation
  rw [h.output_eq,overlap_eq h,lows_eq h,sumQ_eq]
  exact round32_eq .nearestEven _

def result : TensorCore.TcEftResult → Option Nat × String
  | .scalar b => (some b.toNat,"scalar")
  | .exactReference b => (some b.toNat,"exactReference")
  | .outOfRange => (none,"outOfRange")

/-- Both the branch and returned bits agree, for any supplied finite D. -/
theorem algorithm_eq {s : TensorCore.BlockTrace} {t : Trace} (h : TraceRel s t) :
    t.algorithm = result s.tcEft := by
  unfold Trace.algorithm TensorCore.BlockTrace.tcEft
  rw [scalar_eq h,consolidation_eq h]
  cases s.scalarCorrected <;> cases s.exactConsolidation <;> rfl

theorem allZero_eq (b : Block) : (block b).allZeroTerms = b.terms.all (fun t => t.dyadic.significand==0) := by
  unfold TensorCore.PreparedBlock.allZeroTerms
  rw [terms_eq,List.all_map]
  congr 1
  funext t
  apply Bool.eq_iff_iff.mpr
  simpa only [Function.comp_apply,beq_iff_eq] using denormalizedTerm_zero t

def encodedResult : TensorCore.EncodedEFTResult → Option Nat × String
  | .allZero => (some 0,"allZero")
  | .consolidated r => result r

theorem encoded_trace_eq {s : TensorCore.BlockTrace} {t : Trace} (h : TraceRel s t) :
    t.encodedAlgorithm = encodedResult
      (if s.block.allZeroTerms then .allZero else .consolidated s.tcEft) := by
  rw [h.block_eq,allZero_eq]
  unfold Trace.encodedAlgorithm
  cases t.block.terms.all (fun t => t.dyadic.significand==0) <;> simp [encodedResult,algorithm_eq h]

end TCFloat.Equivalence
