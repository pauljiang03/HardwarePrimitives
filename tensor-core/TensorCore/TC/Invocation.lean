import TensorCore.Numerics.RoundingStage
import TensorCore.TC.Block

/-! General Tensor Core invocations. -/

namespace TensorCore

inductive CPlacement where
  /-- Early accumulation: `c` is aligned and added together with the products. -/
  | early
  /-- Late accumulation: round the product accumulator through these stages, then add `c` exactly. -/
  | late (stages : List RoundingStage)
  deriving Repr, DecidableEq

inductive AccumulationKind where
  | aligned (alignMantissaBits : ℕ) (eAlignMin : Option ℤ) (cPlacement : CPlacement)
  /-- An exact single-product FMA, with no lossy alignment stage. -/
  | fused
  deriving Repr, DecidableEq

structure InvocationSpec where
  input : OperandEncoding
  cFormat : Format
  nfma : ℕ
  accumulation : AccumulationKind
  intermediate : List RoundingStage := []
  output : RoundingStage
  deriving Repr, DecidableEq

def stagesValid (ss : List RoundingStage) : Bool := ss.all fun s => decide s.format.WellFormed

def InvocationSpec.Valid (p : InvocationSpec) : Prop :=
  p.input.valueFormat.layout.WellFormed ∧ p.cFormat.WellFormed ∧
  stagesValid p.intermediate = true ∧ p.output.format.WellFormed ∧
  match p.accumulation with
  | .fused => p.nfma = 1
  | .aligned _ _ .early => True
  | .aligned _ _ (.late ss) => stagesValid ss = true

instance (p : InvocationSpec) : Decidable p.Valid := by
  unfold InvocationSpec.Valid
  cases p.accumulation with
  | fused => infer_instance
  | aligned _ _ cp => cases cp <;> infer_instance

structure InvocationInput (p : InvocationSpec) where
  products : List (p.input.Word × p.input.Word)
  c : BitVec p.cFormat.width
  deriving Repr, DecidableEq

structure PreparedInvocation (p : InvocationSpec) where
  products : List (Decoded × Decoded)
  c : Decoded
  deriving Repr, DecidableEq

def prepareInvocation {p : InvocationSpec} (x : InvocationInput p) : Option (PreparedInvocation p) := do
  let c ← (classify p.cFormat x.c).finite
  let ps ← x.products.mapM fun (a, b) => do return (← p.input.decode a, ← p.input.decode b)
  return ⟨ps, c⟩

def PreparedInvocation.exactProducts {p : InvocationSpec} (b : PreparedInvocation p) : ℚ :=
  sumQ (b.products.map fun (a, b) => a.value * b.value)

def PreparedInvocation.exactDot {p : InvocationSpec} (b : PreparedInvocation p) : ℚ :=
  b.c.value + b.exactProducts

/-- Original-bit ideal. -/
def invocationIdeal {p : InvocationSpec} (x : InvocationInput p) : Option ℚ :=
  (prepareInvocation x).map PreparedInvocation.exactDot

def PreparedInvocation.alignedBlock {p : InvocationSpec} (b : PreparedInvocation p)
    (F : ℕ) (eAlignMin : Option ℤ) (includeC : Bool) : PreparedBlock :=
  ⟨⟨p.input.valueFormat.layout, p.nfma, F, eAlignMin, 23⟩, b.products,
    if includeC then b.c else ⟨0, 0, 0⟩⟩

structure LocalAccumulation where
  value : ℚ
  alignmentLoss : ℚ
  roundings : List RoundingEvent
  deriving Repr, DecidableEq

def LocalAccumulation.loss (r : LocalAccumulation) : ℚ :=
  r.alignmentLoss + sumQ (r.roundings.map RoundingEvent.loss)

def accumulateInvocation {p : InvocationSpec} (b : PreparedInvocation p) : Option LocalAccumulation :=
  match p.accumulation with
  | .fused => some ⟨b.exactDot, 0, []⟩
  | .aligned F eAlignMin cp =>
    match cp with
    | .early =>
      let a := b.alignedBlock F eAlignMin true
      some ⟨a.accumulator, sumQ a.alignmentResiduals, []⟩
    | .late stages => do
      let a := b.alignedBlock F eAlignMin false
      let r ← runRoundings stages a.accumulator
      return ⟨r.value + b.c.value, sumQ a.alignmentResiduals, r.events⟩

structure InvocationTrace (p : InvocationSpec) where
  prepared : PreparedInvocation p
  accumulation : LocalAccumulation
  intermediate : RoundingRun
  output : FiniteBinary p.output.format
  deriving Repr, DecidableEq

def InvocationTrace.residual {p : InvocationSpec} (t : InvocationTrace p) : ℚ :=
  t.accumulation.loss + t.intermediate.loss + (t.intermediate.value - t.output.value)

inductive InvocationError where
  | invalidSpec
  | wrongProductCount
  | nonfiniteOrInvalidEncoding
  | localRoundingFailed
  | intermediateRoundingFailed
  | outputRoundingFailed
  deriving Repr, DecidableEq

def evalInvocationPrepared {p : InvocationSpec} (b : PreparedInvocation p) :
    Except InvocationError (InvocationTrace p) :=
  match accumulateInvocation b with
  | none => .error .localRoundingFailed
  | some a => match runRoundings p.intermediate a.value with
    | none => .error .intermediateRoundingFailed
    | some r => match p.output.roundValue r.value with
      | none => .error .outputRoundingFailed
      | some d => .ok ⟨b, a, r, d⟩

def evalInvocation {p : InvocationSpec} (x : InvocationInput p) :
    Except InvocationError (InvocationTrace p) :=
  if ¬ p.Valid then .error .invalidSpec
  else if x.products.length != p.nfma then .error .wrongProductCount
  else match prepareInvocation x with
    | none => .error .nonfiniteOrInvalidEncoding
    | some b => evalInvocationPrepared b

/-- Embed a model as an aligned invocation with FP32 truncated output. -/
@[implicit_reducible] def Model.toInvocation (p : Model) (F : ℕ) : InvocationSpec :=
  ⟨packedIEEE p.input, fp32, p.nfma, .aligned F p.eAlignMin .early,
    [], ⟨fp32, .truncate⟩⟩

def v100Invocation : InvocationSpec := v100F16F32.toInvocation 23

/-- Output bits, with every rejection as `none`. -/
def invocationBits {p : InvocationSpec} (x : InvocationInput p) : Option (BitVec p.output.format.width) :=
  (evalInvocation x).toOption.map fun t => t.output.bits

end TensorCore
