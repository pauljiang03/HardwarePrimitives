import TensorCore.Scalar.Rounding

/-! Encoded conversions, add/subtract, multiply, and one-rounding FMA. -/

namespace TensorCore.IEEE

structure NaNInfo where
  negative : Bool
  signaling : Bool
  payload : ℕ
  deriving Repr, DecidableEq

def Datum.nanInfo : Datum → Option NaNInfo
  | .nan s sig p => some ⟨s, sig, p⟩
  | _ => none

def chooseNaN (xs : List Datum) : Option NaNInfo :=
  let ns := xs.filterMap Datum.nanInfo
  (ns.find? (·.signaling)).or ns.head?

def nanResult (f : BinaryFormat) (xs : List Datum) (extraInvalid : Bool := false) : Result f :=
  let n := (chooseNaN xs).getD ⟨false, false, 0⟩
  ⟨nan f n.negative n.payload, { invalid := extraInvalid || xs.any Datum.isSignaling }⟩

def infinityResult (f : BinaryFormat) (s : Bool) : Result f := ⟨infinity f s, {}⟩

def invalidResult (f : BinaryFormat) : Result f := nanResult f [] true

/-- Used only for an exact zero sum. -/
def sumZeroSign (mode : BinaryRoundingMode) (a b : Bool) : Bool :=
  if a == b then a else mode == .towardNegative

def addDatum (f : BinaryFormat) (cfg : Context) (a b : Datum) : Result f :=
  if a.isNaN || b.isNaN then nanResult f [a, b] else
  match a, b with
  | .finite sa x, .finite sb y => round f cfg (sumZeroSign cfg.mode sa sb) (x + y)
  | .infinity sa, .infinity sb =>
      if sa == sb then infinityResult f sa else invalidResult f
  | .infinity s, _ | _, .infinity s => infinityResult f s
  | _, _ => invalidResult f

def mulDatum (f : BinaryFormat) (cfg : Context) (a b : Datum) : Result f :=
  if a.isNaN || b.isNaN then nanResult f [a, b] else
  match a, b with
  | .finite sa x, .finite sb y => round f cfg (xor sa sb) (x * y)
  | .infinity sa, .infinity sb => infinityResult f (xor sa sb)
  | .infinity sa, .finite sb y =>
      if y = 0 then invalidResult f else infinityResult f (xor sa sb)
  | .finite sa x, .infinity sb =>
      if x = 0 then invalidResult f else infinityResult f (xor sa sb)
  | _, _ => invalidResult f

def invalidProduct (a b : Datum) : Bool :=
  (a.isInfinite && b.isZero) || (a.isZero && b.isInfinite)

def fmaDatum (f : BinaryFormat) (cfg : Context) (a b c : Datum) : Result f :=
  if a.isNaN || b.isNaN || c.isNaN then nanResult f [a, b, c] (invalidProduct a b) else
  if invalidProduct a b then invalidResult f else
  let sp := xor a.negative b.negative
  if a.isInfinite || b.isInfinite then
    if c.isInfinite && sp != c.negative then invalidResult f else infinityResult f sp
  else
    match a, b, c with
    | .finite _ x, .finite _ y, .finite sc z =>
        round f cfg (sumZeroSign cfg.mode sp sc) (x * y + z)
    | _, _, .infinity s => infinityResult f s
    | _, _, _ => invalidResult f

def add (f : BinaryFormat) (cfg : Context) (a b : Word f) : Result f :=
  addDatum f cfg (decode f a) (decode f b)

def sub (f : BinaryFormat) (cfg : Context) (a b : Word f) : Result f :=
  addDatum f cfg (decode f a) (decode f b).negate

def mul (f : BinaryFormat) (cfg : Context) (a b : Word f) : Result f :=
  mulDatum f cfg (decode f a) (decode f b)

def fma (f : BinaryFormat) (cfg : Context) (a b c : Word f) : Result f :=
  fmaDatum f cfg (decode f a) (decode f b) (decode f c)

/-- Payloads are left aligned, matching their positions following the quiet bit. -/
def convertPayload (source target : BinaryFormat) (p : ℕ) : ℕ :=
  if source.layout.mantissaBits ≤ target.layout.mantissaBits then
    p * 2 ^ (target.layout.mantissaBits - source.layout.mantissaBits)
  else p / 2 ^ (source.layout.mantissaBits - target.layout.mantissaBits)

def convertDatum (source target : BinaryFormat) (cfg : Context) (a : Datum) : Result target :=
  match a with
  | .finite s x => round target cfg s x
  | .infinity s => infinityResult target s
  | .nan s sig p => ⟨nan target s (convertPayload source target p), { invalid := sig }⟩

def convert (source target : BinaryFormat) (cfg : Context) (a : Word source) : Result target :=
  convertDatum source target cfg (decode source a)

end TensorCore.IEEE
