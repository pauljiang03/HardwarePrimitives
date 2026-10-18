import TCFloat.Model

/-! The two encoded interfaces: the Tensor Core model and the TC-EFT correction. -/
namespace TCFloat.Interface

def tc (p : TCModel) (pairs : List (Nat × Nat)) (c : Nat) : Option Nat :=
  (prepare p pairs c).bind Block.evaluate

def eft (p : TCModel) (pairs : List (Nat × Nat)) (c d : Nat) : Option (Option Nat × String) :=
  (prepare p pairs c).bind fun b =>
    (trace b d).map Trace.encodedAlgorithm

end TCFloat.Interface

namespace TCFloat.Trace
def retainedLowParts (t : Trace) : List Rat :=
  t.lowParts.map fun e => truncGrid e t.block.q
def outputResidual (t : Trace) : Rat := t.block.accumulator-t.output
end TCFloat.Trace

namespace TCFloat.Interface
/-- Bounded encodings for one block. -/
structure Input (p : TCModel) where
  products : List (Fin (2^p.format.bitWidth) × Fin (2^p.format.bitWidth))
  c : Fin (2^32)

def Input.pairs {p : TCModel} (x : Input p) : List (Nat × Nat) :=
  x.products.map fun (a,b) => (a.val,b.val)

inductive Error where
  | wrongProductCount
  | nonfiniteInput
  | accumulatorOutOfRange
  | nonfiniteOutput
  deriving Repr, DecidableEq

/-- Typed outcomes with the reference interface's error distinctions. -/
def tcChecked (p : TCModel) (x : Input p) : Except Error Nat :=
  if x.products.length != p.nfma then .error .wrongProductCount
  else match prepare p x.pairs x.c.val with
    | none => .error .nonfiniteInput
    | some b => match b.evaluate with
      | none => .error .accumulatorOutOfRange
      | some bits => .ok bits

def eftChecked (p : TCModel) (x : Input p) (d : Fin (2^32)) :
    Except Error (Option Nat × String) :=
  if x.products.length != p.nfma then .error .wrongProductCount
  else match prepare p x.pairs x.c.val with
    | none => .error .nonfiniteInput
    | some b => match trace b d.val with
      | none => .error .nonfiniteOutput
      | some t => .ok t.encodedAlgorithm
end TCFloat.Interface

namespace TCFloat.Trace
/-- Residual coefficients on an explicitly chosen paper grid. -/
def coefficientsAt (t : Trace) (e : Int) : List Int :=
  t.lowParts.map fun x => (x / pow2 e).floor
end TCFloat.Trace
