import FloatLib.Floats.Formats.BinaryInterchange.Rounding.Directed.Runtime
import FloatLib.Numerics.Exact.Dyadic.Order
import Mathlib.Data.Rat.Floor
import Mathlib.Tactic

/-! Independent FP32-output TC semantics. -/
namespace TCFloat
open FloatLib.Floats.Formats.BinaryInterchange
abbrev ExactDyadic := FloatLib.Numerics.Dyadic

abbrev F32 := Model FloatFormat.binary32
abbrev Mode := Model.IEEERoundingMode

def pow2 (e : Int) : ℚ := (2 : ℚ) ^ e

def maxFinite32 : ℚ := (2^24 - 1 : ℕ) * pow2 104

def ofNat (f : FloatFormat) (n : Nat) : Model f := Model.ofBits (BitVec.ofNat _ n)

def value32 (n : Nat) : Option ℚ := (ofNat .binary32 n).toRat?

/-- Source finite-accumulator domain, before FloatLib rounding (including RTZ). -/
def round32 (mode : Mode) (x : ℚ) : Option Nat :=
  if |x| > maxFinite32 then none else
    some (Model.roundRatWithRounding .binary32 mode (x.num < 0) x.num.natAbs x.den).bits.toNat

def truncCoeff (x : ℚ) (e : Int) : Int :=
  if x < 0 then -⌊-x / pow2 e⌋ else ⌊x / pow2 e⌋
def truncGrid (x : ℚ) (e : Int) : ℚ := truncCoeff x e * pow2 e

structure TCModel where
  format : FloatFormat
  nfma : Nat
  neab : Nat
  eAlignMin : Option Int

def fp16 (k neab : Nat) (eAlignMin : Option Int := none) : TCModel := ⟨.binary16, k, neab, eAlignMin⟩
def bf16 (k neab : Nat) (eAlignMin : Option Int := none) : TCModel := ⟨.bfloat16, k, neab, eAlignMin⟩
def tf32 (k neab : Nat) (eAlignMin : Option Int := none) : TCModel := ⟨.tf32, k, neab, eAlignMin⟩
def v100 := fp16 4 0
def a100 := fp16 8 1 (some (-132))
def h100 := fp16 16 2 (some (-133))

structure Term where
  dyadic : ExactDyadic
  exponent : Int
  mantissaBits : Int

def Term.value (t : Term) : ℚ := t.dyadic.toRat

def decode (f : FloatFormat) (n : Nat) : Option Term := do
  if n ≥ 2 ^ f.bitWidth then none else do
    let x := ofNat f n
    let d ← x.toDyadic?
    if d.significand = 0 then return ⟨d, 0, 0⟩
    let scale := max 1 (Model.expField x) - (f.exponentBias : Int)
    return ⟨d, scale, f.fracWidth⟩

def Term.mul (a b : Term) : Term :=
  ⟨a.dyadic.mul b.dyadic, a.exponent + b.exponent, a.mantissaBits + b.mantissaBits⟩

structure Block where
  model : TCModel
  c : Term
  products : List (Term × Term)

def prepare (p : TCModel) (pairs : List (Nat × Nat)) (c : Nat) : Option Block := do
  if pairs.length != p.nfma then none else do
    let c ← decode .binary32 c
    let ps ← pairs.mapM fun (a,b) => do return (← decode p.format a, ← decode p.format b)
    return ⟨p,c,ps⟩

def Block.terms (b : Block) : List Term := b.c :: b.products.map fun (a,c) => a.mul c
/-- Independent original-input ideal, not used by the correction implementation. -/
def Block.ideal (b : Block) : ℚ := b.c.value + (b.products.map fun (a,c) => a.value*c.value).sum

def maxTermExp : List Term → Option Int
  | [] => none
  | t :: ts =>
    let rest := maxTermExp ts
    if t.dyadic.significand = 0 then rest
    else some (rest.map (max t.exponent) |>.getD t.exponent)
def Block.alignExp (b : Block) : Option Int :=
  (maxTermExp b.terms).map fun e => b.model.eAlignMin.map (max e) |>.getD e
def Block.q (b : Block) : Int := b.alignExp.getD 0 - (23 + b.model.neab : Nat)
def Block.aligned (b : Block) : List ℚ := b.terms.map fun t => truncGrid t.value b.q
def Block.accumulator (b : Block) : ℚ := b.aligned.sum
def Block.residuals (b : Block) : List ℚ := b.terms.map fun t => t.value - truncGrid t.value b.q

def Block.evaluate (b : Block) : Option Nat := round32 .towardZero b.accumulator

structure Trace where
  block : Block
  bits : Nat
  output : ℚ

def trace (b : Block) (bits : Nat) : Option Trace := do
  if bits ≥ 2^32 then none else return ⟨b, bits, ← value32 bits⟩

def outputUlpExponent (bits : Nat) : Int := max ((bits / 2^23 % 2^8 : Nat) - (127 : Int)) (-126) - 23

def Trace.extractionExponent (t : Trace) : Int := max t.block.q (outputUlpExponent t.bits)
def Trace.coarse (t : Trace) : List ℚ := t.block.terms.map fun x => truncGrid x.value t.extractionExponent
def Trace.lowParts (t : Trace) : List ℚ := t.block.terms.map fun x => x.value - truncGrid x.value t.extractionExponent
def Trace.retained (t : Trace) : ℚ := t.coarse.sum
def Trace.overlap (t : Trace) : ℚ := t.output - t.retained
/-- Reference EFT residual includes both alignment and output losses. -/
def Trace.residual (t : Trace) : ℚ := (t.block.accumulator - t.output) + t.block.residuals.sum

def representable (x : ℚ) : Bool := (round32 .nearestEven x >>= value32) == some x

def add32 (x y : ℚ) : Option ℚ := round32 .nearestEven (x+y) >>= value32

def naiveSumFrom (a : ℚ) : List ℚ → Option ℚ
  | [] => some a
  | x :: xs => (add32 a x).bind fun s => naiveSumFrom s xs

/-- Trailing zero bits of `n` (`0` for `n = 0`), by structural recursion on a fuel argument. -/
def trailingZeroBitsAux : Nat → Nat → Nat
  | 0, _ => 0
  | fuel + 1, n => if n ≠ 0 ∧ n % 2 = 0 then trailingZeroBitsAux fuel (n / 2) + 1 else 0

/-- Exponent of the lowest set bit of a nonzero dyadic rational. -/
def lowestBitExp (x : ℚ) : Int := (trailingZeroBitsAux x.num.natAbs x.num.natAbs : Int) - (x.den.log2 : Int)

/-- Lowest bit actually set in any low part, capped at the extraction grid; zeros are ignored. -/
def Trace.supportExponent (t : Trace) : Int :=
  t.lowParts.foldl (fun e x => if x = 0 then e else min e (lowestBitExp x)) t.extractionExponent

def Trace.lowCoefficients (t : Trace) : List Int :=
  let q := pow2 t.supportExponent
  t.lowParts.map fun x => ⌊x / q⌋

/-- Scalar guard on the tightest common grid of the low parts. -/
def Trace.scalarPredicate (t : Trace) : Bool :=
  let ℓ := t.supportExponent
  let q := pow2 ℓ
  let zs := t.lowCoefficients
  decide (-149 ≤ ℓ) && decide (ℓ ≤ 104) &&
  (t.lowParts == zs.map fun (z : Int) => (z : ℚ)*q) &&
  decide ((zs.map Int.natAbs).sum < 2^24) &&
  representable t.output && representable t.overlap && representable t.retained &&
  decide (|t.retained + t.lowParts.sum| ≤ maxFinite32)

def Trace.scalarUnchecked (t : Trace) : Option Nat :=
  (naiveSumFrom 0 t.lowParts).bind fun e =>
    (add32 t.output (-t.overlap)).bind fun h => round32 .nearestEven (h+e)
def Trace.scalar (t : Trace) : Option Nat := if t.scalarPredicate then t.scalarUnchecked else none

def Trace.exactConsolidation (t : Trace) : Option Nat :=
  round32 .nearestEven (t.output - t.overlap + t.lowParts.sum)

def Trace.algorithm (t : Trace) : Option Nat × String :=
  match t.scalar with
  | some bits => (some bits, "scalar")
  | none => match t.exactConsolidation with
    | some bits => (some bits, "exactReference")
    | none => (none, "outOfRange")

/-- Uses supplied finite D; never invokes the TC model or original-input ideal. -/
def Trace.encodedAlgorithm (t : Trace) : Option Nat × String :=
  if t.block.terms.all (fun x => x.dyadic.significand == 0) then (some 0, "allZero")
  else t.algorithm

end TCFloat
