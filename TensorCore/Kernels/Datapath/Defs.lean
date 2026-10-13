import TensorCore.Kernels.EFT.DecodeDefs

/-! A fixed-width bitvector datapath for one Tensor Core normalization group. -/

namespace TensorCore.Datapath

open EFMachine

/-- Exponent registers: 9 bits, enough for the alignment exponent from the floor −133 up to 254. -/
abbrev Exp := BitVec 9

/-- F = 23 + p: the mantissa bits each term keeps after alignment. -/
def alignBits : Variant → BitVec 5
  | .v100F16 => 23
  | .ampereF16 | .ampereBF16 | .ampereTF32 => 24
  | _ => 25

/-- The alignment floor, biased by 256; 0 on V100, which has none. -/
def eAlignMin : Variant → Exp
  | .v100F16 => 0
  | .ampereF16 | .ampereBF16 | .ampereTF32 => 124
  | _ => 123

/-- Carry bits for summing the K products and c: `K + 1 ≤ 2 ^ carryBits`. -/
def carryBits (variant : Variant) : ℕ := variant.model.nfma.log2 + 1

/-- An aligned term: the implicit bit, one implicit padding bit for a product's carry, and F bits after the binary point. -/
def termWidth (variant : Variant) : ℕ := (alignBits variant).toNat + 2

/-- The two's complement accumulator: an aligned term's width, the carry bits and a sign bit. -/
def accWidth (variant : Variant) : ℕ := termWidth variant + carryBits variant + 1

/-- A decoded input: sign, significand with its hidden bit, mantissa width, and unnormalized exponent biased by 128. -/
structure Input where
  negative : Bool
  significand : BitVec 11
  mantissaBits : BitVec 5
  biasedExp : Exp
  deriving Repr, DecidableEq

/-- Field extraction for FP16, BF16 and packed TF32 words; infinities and NaNs are rejected. -/
def decodeInput (kind : InputKind) (bits : F32) : Option Input :=
  let f := kind.format
  let e := ((bits >>> f.mantissaBits) &&& (((1 : F32) <<< f.exponentBits) - 1)).setWidth 9
  let m := (bits &&& (((1 : F32) <<< f.mantissaBits) - 1)).setWidth 11
  let negative := (bits >>> (f.mantissaBits + f.exponentBits)) != 0
  -- converts the format's exponent bias to 128
  let offset : Exp := match kind with | .fp16 => 113 | _ => 1
  let top : Exp := match kind with | .fp16 => 31 | _ => 255
  let frac : BitVec 5 := match kind with | .bf16 => 7 | _ => 10
  if e == top then none
  else if e == 0 then
    if m == 0 then some ⟨negative, 0, 0, 128⟩
    else some ⟨negative, m, frac, offset + 1⟩
  else some ⟨negative, ((1 : BitVec 11) <<< f.mantissaBits) + m, frac, e + offset⟩

/-- A product or c: sign, significand with `mantissaBits` bits after the binary point, and unnormalized exponent biased by 256. -/
structure Term where
  negative : Bool
  significand : BitVec 24
  mantissaBits : BitVec 5
  biasedExp : Exp
  deriving Repr, DecidableEq

/-- Exact product of two decoded inputs; exponents add without normalizing. -/
def product (a b : Input) : Term :=
  ⟨a.negative != b.negative, multiplySignificands a.significand b.significand,
    a.mantissaBits + b.mantissaBits, a.biasedExp + b.biasedExp⟩

/-- FP32 decoding of c; infinities and NaNs are rejected. -/
def decodeC (bits : F32) : Option Term :=
  let e := ((bits >>> 23).setWidth 8).zeroExtend 9
  let m := (bits &&& 0x007fffff).setWidth 24
  let negative := bits.msb
  if e == 255 then none
  else if e == 0 then
    if m == 0 then some ⟨negative, 0, 0, 256⟩
    else some ⟨negative, m, 23, 130⟩
  else some ⟨negative, 8388608 + m, 23, e + 129⟩

def decodeTerm (variant : Variant) (pair : variant.model.Word × variant.model.Word) : Option Term := do
  let a ← decodeInput variant.kind (pair.1.zeroExtend 32)
  let b ← decodeInput variant.kind (pair.2.zeroExtend 32)
  return product a b

/-- Largest unnormalized exponent of a nonzero term, raised to the profile floor. -/
def alignExp (variant : Variant) (ts : List Term) : Exp :=
  ts.foldl (fun e t => if t.significand == 0 then e
    else if e ≤ t.biasedExp then t.biasedExp else e) (eAlignMin variant)

/-- The term's magnitude truncated to the grid `2 ^ (e - 256 - F)`. -/
def Term.aligned (variant : Variant) (e : Exp) (t : Term) : BitVec (termWidth variant) :=
  (t.significand.zeroExtend (termWidth variant) <<< (alignBits variant - t.mantissaBits)) >>>
    (e - t.biasedExp)

def Term.signedAligned (variant : Variant) (e : Exp) (t : Term) : BitVec (accWidth variant) :=
  let a := (t.aligned variant e).zeroExtend (accWidth variant)
  if t.negative then -a else a

def accumulate (variant : Variant) (e : Exp) (ts : List Term) : BitVec (accWidth variant) :=
  ts.foldl (fun s t => s + t.signedAligned variant e) 0

/-- Normalization and final truncation of an accumulator on the grid `2 ^ (e - 256 - F)`;
`none` when the value exceeds the largest finite FP32 value. -/
def normalize (s : BitVec w) (e : Exp) (F : BitVec 5) : Option F32 :=
  let negative := s.msb
  let m := if negative then -s else s
  if m == 0 then some 0 else
    let F : Exp := F.setWidth 9
    -- position of the leading one
    let lead : Exp := BitVec.ofNat 9 (w - 1) - m.clz.setWidth 9
    -- the FP32 exponent field is e + lead - F - 129: at least 255, or at least 1
    let overflow : Bool := F + 384 - lead ≤ e
    let normal : Bool := F + 130 - lead ≤ e
    let biased : Exp := if normal then e - (F + 129 - lead) else 1
    -- keep 24 bits: shift by lead - 23 for a normal result, F + 107 - e for a subnormal
    let left : Bool := if normal then lead ≤ 23 else F + 107 ≤ e
    let amount : Exp := if normal then (if left then 23 - lead else lead - 23)
      else (if left then e - (F + 107) else F + 107 - e)
    let k := if left then m <<< amount else m >>> amount
    let exact := left || k <<< amount == m
    if overflow || (biased == 254 && k == 0xffffff && !exact) then none
    else
      let k := k.setWidth 32
      let payload := if k < 0x800000 then k else (biased.setWidth 32 <<< 23) + (k - 0x800000)
      some ((if negative then 0x80000000 else 0) + payload)

/-- One normalization group, computed with bitvector operations only. -/
def evalBlock (variant : Variant) (x : BlockInput variant.model) : Except ModelError F32 := do
  if x.products.length != variant.model.nfma then throw .wrongProductCount
  let some c := decodeC x.c | throw .nonfiniteInput
  let some ps := x.products.mapM (decodeTerm variant) | throw .nonfiniteInput
  let ts := c :: ps
  let e := alignExp variant ts
  let some bits := normalize (accumulate variant e ts) e (alignBits variant) | throw .accumulatorOutOfRange
  return bits

end TensorCore.Datapath
