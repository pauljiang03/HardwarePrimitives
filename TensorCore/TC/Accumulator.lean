import TensorCore.TC.Block

/-! A fixed-width register model of accumulation. -/

namespace TensorCore

/-- Actual modular signed-word additions, starting from a supplied register. -/
def machineAccumulate (w : ℕ) (acc : BitVec w) : List ℤ → BitVec w
  | [] => acc
  | z :: zs => machineAccumulate w (acc + BitVec.ofInt w z) zs

/-- Interpret the signed machine sum at the reference alignment quantum. -/
def PreparedBlock.machineAccumulator (b : PreparedBlock) (w : ℕ) : ℚ :=
  ((machineAccumulate w 0 b.alignedBits).toInt : ℚ) * pow2 b.alignGridExponent

/-- Execute accumulation with w-bit additions, then the ordinary rounding to FP32 and the block output. -/
def evalPreparedMachine (w : ℕ) (b : PreparedBlock) : Except ModelError BlockTrace :=
  match round32 .truncate (b.machineAccumulator w) with
  | none => .error .accumulatorOutOfRange
  | some bits => match finite32 (truncateFraction32 b.model.outputFracBits bits) with
    | none => .error .nonfiniteOutput
    | some d => .ok ⟨b, d⟩

def evalBlockMachine (w : ℕ) {p : Model} (x : BlockInput p) :
    Except ModelError BlockTrace :=
  if x.products.length != p.nfma then .error .wrongProductCount
  else match prepare x with
    | none => .error .nonfiniteInput
    | some b => evalPreparedMachine w b

end TensorCore
