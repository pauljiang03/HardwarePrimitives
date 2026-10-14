import TensorCore.Numerics.DenormalizedProduct
import TensorCore.TC.Defs
import TensorCore.Numerics.RoundOp

/-! The Tensor Core block model. -/

namespace TensorCore

/-- Encoded operands of one block FMA of a model; `c` is always FP32. -/
structure BlockInput (p : Model) where
  products : List (p.Word × p.Word)
  c : F32
  deriving Repr, DecidableEq

/-- Decoded operands together with the model that fixes their alignment semantics. -/
structure PreparedBlock where
  model : Model
  products : List (Decoded × Decoded)
  c : Decoded
  deriving Repr, DecidableEq

def prepareProducts (p : Model) (ps : List (p.Word × p.Word)) :
    Option (List (Decoded × Decoded)) :=
  ps.mapM fun (a, b) => do
    return (← p.decode a, ← p.decode b)

def prepare {p : Model} (x : BlockInput p) : Option PreparedBlock :=
  match decode32 x.c, prepareProducts p x.products with
  | some c, some ps => some ⟨p, ps, c⟩
  | _, _ => none

/-- Ideal sum from decoded operands, without multiplication into denormalized form, alignment, or correction. -/
def PreparedBlock.exactProducts (b : PreparedBlock) : ℚ :=
  sumQ (b.products.map fun (a, b) => a.value * b.value)

def PreparedBlock.exactDot (b : PreparedBlock) : ℚ := b.c.value + b.exactProducts

def exactDot {p : Model} (x : BlockInput p) : Option ℚ :=
  (prepare x).map PreparedBlock.exactDot

def PreparedBlock.terms (b : PreparedBlock) : List DenormalizedProduct :=
  ⟨b.c.significand, b.c.exponent, b.c.mantissaBits⟩ ::
    b.products.map fun (a, b) => denormalizedMul a b

/-- A nonempty maximum ignores zero terms; none explicitly represents an all-zero block. -/
def maxTermExp (ts : List DenormalizedProduct) : Option ℤ :=
  (ts.filterMap fun t => if t.significand = 0 then none else some t.exponent).foldl
    (fun acc e => some (match acc with | none => e | some v => max v e)) none

/-- Alignment exponent `eta`: the largest exponent of a nonzero term, raised to the model's minimum alignment exponent. -/
def PreparedBlock.alignExp (b : PreparedBlock) : Option ℤ :=
  b.model.applyEAlignMin (maxTermExp b.terms)

/-- Grid exponent `eta - F`. -/
def PreparedBlock.alignGridExponent (b : PreparedBlock) : ℤ :=
  b.alignExp.getD 0 - b.model.alignFracBits

def PreparedBlock.alignedBits (b : PreparedBlock) : List ℤ :=
  b.terms.map fun t => truncBits t.value b.alignGridExponent

def PreparedBlock.accumulator (b : PreparedBlock) : ℚ :=
  (sumZ b.alignedBits : ℚ) * pow2 b.alignGridExponent

def PreparedBlock.alignmentResiduals (b : PreparedBlock) : List ℚ :=
  b.terms.map fun t => t.value - truncGrid t.value b.alignGridExponent

/-- Exact stage extractor for any supplied numerical output. -/
def PreparedBlock.extractReference (b : PreparedBlock) (d : ℚ) : ℚ :=
  (b.accumulator - d) + sumQ b.alignmentResiduals

/-- All trace fields except the accepted input/output are derived by definitions. -/
structure BlockTrace where
  block : PreparedBlock
  output : Finite32
  deriving Repr, DecidableEq

def BlockTrace.residual (t : BlockTrace) : ℚ := t.block.extractReference t.output.value
def BlockTrace.outputResidual (t : BlockTrace) : ℚ := t.block.accumulator - t.output.value
def BlockTrace.recovered (t : BlockTrace) : ℚ := t.output.value + t.residual
def BlockTrace.corrected (t : BlockTrace) : Option F32 := round32 .nearestEven t.recovered

inductive ModelError where
  | wrongProductCount
  | nonfiniteInput
  | accumulatorOutOfRange
  | nonfiniteOutput
  deriving Repr, DecidableEq

/-- The accumulator truncated to binary32, then to the model's block-output fraction bits. -/
def evalPrepared (b : PreparedBlock) : Except ModelError BlockTrace :=
  match round32 .truncate b.accumulator with
  | none => .error .accumulatorOutOfRange
  | some bits => match finite32 (truncateFraction32 b.model.outputFracBits bits) with
    | none => .error .nonfiniteOutput
    | some d => .ok ⟨b, d⟩

/-- One block FMA of the model, not a complete PTX tile or GEMM. -/
def evalBlock {p : Model} (x : BlockInput p) : Except ModelError BlockTrace :=
  if x.products.length != p.nfma then .error .wrongProductCount
  else match prepare x with
    | none => .error .nonfiniteInput
    | some b => evalPrepared b

abbrev evalV100 (x : BlockInput v100F16F32) : Except ModelError BlockTrace := evalBlock x

theorem prepareProducts_replicate (p : Model) (a b : p.Word) (da db : Decoded) (K : ℕ)
    (ha : p.decode a = some da) (hb : p.decode b = some db) :
    prepareProducts p (List.replicate K (a, b)) = some (List.replicate K (da, db)) := by
  induction K with
  | zero => rfl
  | succ n ih =>
    have ih' := ih
    simp [prepareProducts] at ih'
    simp [prepareProducts, List.replicate_succ, List.mapM_cons, ha, hb, ih']

/-- Coefficients of a block with one repeated operand pair. -/
theorem construction_alignedBits (prof : Model) (K : ℕ) (da db c : Decoded) :
    (PreparedBlock.mk prof (List.replicate K (da, db)) c).alignedBits =
      truncBits c.value (PreparedBlock.mk prof (List.replicate K (da, db)) c).alignGridExponent ::
      List.replicate K (truncBits (denormalizedMul da db).value
        (PreparedBlock.mk prof (List.replicate K (da, db)) c).alignGridExponent) := by
  simp [PreparedBlock.alignedBits, PreparedBlock.terms, List.map_replicate, DenormalizedProduct.value,
    Decoded.value]

end TensorCore
