import TensorCore.Kernels.EFT.DecodeDefs

/-! The complete bounded execution path for TC-EFT Algorithm 1. -/

namespace TensorCore.EFMachine

inductive Error where
  | wrongProductCount | nonfiniteInput | nonfiniteOutput | arithmeticOverflow
  deriving Repr, DecidableEq

structure Prepared where
  terms : List Term
  output : Word
  grid : Grid
  deriving Repr, DecidableEq

/-- Select the common extraction grid from the unnormalized exponents. -/
def selectedGrid (variant : Variant) (ts : List Term) (D : F32) : Grid :=
  let alignExp := ts.foldl (fun e t => if t.word.magnitude == 0 then e
    else if e ≤ t.biasedExp then t.biasedExp else e) variant.eAlignMin
  let offset := variant.alignmentBits + 240
  let qa := if alignExp < offset then 0 else alignExp - offset
  if qa ≤ outputGrid D then outputGrid D else qa

def prepare (variant : Variant) (x : BlockInput variant.model) (D : F32) : Except Error Prepared := do
  if x.products.length != variant.model.nfma then throw .wrongProductCount
  let some c := decode32Term x.c | throw .nonfiniteInput
  let some ps := x.products.mapM (decodeProduct variant) | throw .nonfiniteInput
  let some d := decode32Word D | throw .nonfiniteOutput
  let ts := c :: ps
  return ⟨ts, d, selectedGrid variant ts D⟩

structure Components where
  prepared : Prepared
  coarse : List Word
  low : List Word
  retained : Word
  overlap : Word
  residualSum : Word
  recovered : Word
  deriving Repr, DecidableEq

/-- Lines 13–17 and exact consolidation: preserve the signed identity S = D - overlap + sum(low). -/
def extract (p : Prepared) : Option Components := do
  let splits := p.terms.map fun t => t.word.split p.grid
  let hi := splits.map WordSplit.coarse
  let lo := splits.map WordSplit.low
  let h ← sumWords hi
  let overlap ← p.output.sub h
  let e ← sumWords lo
  let d0 ← p.output.sub overlap
  let s ← d0.add e
  return ⟨p, hi, lo, h, overlap, e, s⟩

def Word.sameValue (x y : Word) : Bool :=
  x.magnitude == y.magnitude && (x.magnitude == 0 || x.negative == y.negative)

/-- A representability guard constructed solely with bounded conversion/decoding. -/
def Word.exact32 (x : Word) : Option F32 := do
  let b ← x.round32
  let y ← decode32Word b
  if x.sameValue y then some b else none

def magnitudeSumWords : List Magnitude → Option Magnitude
  | [] => some 0
  | x :: xs => do
    let y ← magnitudeSumWords xs
    let s := x + y
    if s < x then none else some s

/-- Lowest bit actually set in any nonzero low part, capped at the extraction grid. -/
def Components.lowGrid (c : Components) : Magnitude :=
  c.low.foldl (fun e x =>
    if x.magnitude == 0 then e else
      let trailing := trailingZeros x.magnitude
      if e ≤ trailing then e else trailing)
    (c.prepared.grid.zeroExtend 576)

/-- Sufficient scalar support/range predicate. -/
def Components.scalarGuard (c : Components) : Bool :=
  let ell := c.lowGrid
  (ell ≥ 123) && (ell ≤ 376) &&
  c.low.all (fun x => ((x.magnitude >>> ell) <<< ell) == x.magnitude) &&
  ((magnitudeSumWords (c.low.map fun x => x.magnitude >>> ell)).any (· < 16777216)) &&
  c.overlap.exact32.isSome && c.retained.exact32.isSome &&
  (c.recovered.magnitude ≤ maxMagnitude32)

/-- Naive summation in the specified left-to-right ordering, including encoded FP32 boundaries. -/
def scalarSum (xs : List Word) : Option F32 := do
  let bs ← xs.mapM Word.round32
  bs.foldlM add32 0

/-- The scalar branch: plain FP32 operations, taken when the guard accepts. -/
def Components.scalar (c : Components) : Option F32 := do
  if !c.scalarGuard then none else do
    let eBits ← scalarSum c.low
    let dBits ← c.prepared.output.round32
    let oBits ← c.overlap.neg.round32
    let hBits ← add32 dBits oBits
    add32 hBits eBits

inductive Result where
  | allZero
  | scalar (bits : F32)
  | boundedExact (bits : F32)
  | outOfRange
  deriving Repr, DecidableEq

def Result.bits : Result → Option F32
  | .allZero => some 0
  | .scalar b | .boundedExact b => some b
  | .outOfRange => none

/-- Full bounded Algorithm 1, on each of the eight supported variants with encoded inputs. -/
def tcEft (variant : Variant) (x : BlockInput variant.model) (D : F32) : Except Error Result := do
  let p ← prepare variant x D
  if p.terms.all (fun t => t.word.magnitude == 0) then return .allZero
  let some c := extract p | throw .arithmeticOverflow
  match c.scalar with
  | some b => return .scalar b
  | none =>
    match c.recovered.round32 with
    | some b => return .boundedExact b
    | none => return .outOfRange

end TensorCore.EFMachine
