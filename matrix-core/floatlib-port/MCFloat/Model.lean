import FloatLib.Floats.Formats.BinaryInterchange.Rounding.Directed.Runtime
import FloatLib.Numerics.Exact.Dyadic.Order
import Mathlib.Data.Rat.Floor
import Mathlib.Tactic

/-! # AMD Matrix Cores on FloatLib

The CDNA 1, CDNA 2 and CDNA 3 blocks of Khattak, Mikaitis and Graziani, *Accurate Models of AMD
Matrix Cores*, written against FloatLib's formats and rounding. -/

namespace MCFloat
open FloatLib.Floats.Formats.BinaryInterchange

abbrev ExactDyadic := FloatLib.Numerics.Dyadic
abbrev F32 := Model FloatFormat.binary32

def pow2 (e : ℤ) : ℚ := (2 : ℚ) ^ e

def ofNat (f : FloatFormat) (n : ℕ) : Model f := Model.ofBits (BitVec.ofNat _ n)

def bits (w : F32) : ℕ := w.bits.toNat

/-! ## Decoding -/

/-- A finite term; `exponent` is the minimum normal exponent for subnormals and zero. -/
structure Term where
  dyadic : ExactDyadic
  exponent : ℤ
  small : Bool
  deriving DecidableEq

def Term.value (t : Term) : ℚ := t.dyadic.toRat
def Term.isZero (t : Term) : Bool := t.dyadic.significand == 0

def Term.mul (a b : Term) : Term := ⟨a.dyadic.mul b.dyadic, a.exponent + b.exponent, false⟩

/-- Flush to zero: the value of a term, or zero when its significand is below one. -/
def Term.flushed (t : Term) : ℚ := if t.small then 0 else t.value

/-- A word as FloatLib classifies it. -/
inductive Value where
  | finite (t : Term)
  | inf (negative : Bool)
  | nan

def classifyModel {f : FloatFormat} (x : Model f) : Value :=
  if Model.isNaN x then .nan
  else if Model.isInf x then .inf (Model.signBit x)
  else match x.toDyadic? with
    | some d => .finite ⟨d, max 1 (Model.expField x : ℤ) - f.exponentBias, Model.expField x == 0⟩
    | none => .nan

def classify (f : FloatFormat) (n : ℕ) : Value := classifyModel (ofNat f n)

def Value.finite? : Value → Option Term
  | .finite t => some t
  | _ => none

inductive Operand where
  /-- A FloatLib format: FP32, FP16, BF16, E4M3 or E5M2 FNUZ. -/
  | fmt (f : FloatFormat)
  /-- XF32: an FP32 word whose finite values are read as the TF32 word of its upper 19 bits. -/
  | xf32

def Operand.read : Operand → ℕ → Value
  | .fmt f, n => classify f n
  | .xf32, n =>
    match classify .binary32 n with
    | .finite _ => classify .tf32 (n / 2 ^ 13)
    | v => v

/-! ## FP32 rounding -/

/-- `fl{x}`: FloatLib's FP32 round-to-nearest-even of the exact value; `±∞` on overflow. -/
def round32 (x : ℚ) : F32 :=
  Model.roundRatWithRounding .binary32 .nearestEven (decide (x < 0)) x.num.natAbs x.den

/-- Replace a subnormal word by the zero of its sign. -/
def flush (w : F32) : F32 :=
  if Model.isSubnormal w then Model.zero .binary32 (Model.signBit w) else w

def fl (ftz : Bool) (x : ℚ) : F32 := if ftz then flush (round32 x) else round32 x

def nan32 : F32 := Model.canonicalNaN .binary32

/-! ## Grids -/

/-- Truncation of the magnitude to a multiple of `2^g`. -/
def truncGrid (x : ℚ) (g : ℤ) : ℚ :=
  if x < 0 then -(⌊-x / pow2 g⌋ * pow2 g) else ⌊x / pow2 g⌋ * pow2 g

/-- RD to a multiple of `2^g`. -/
def rdGrid (x : ℚ) (g : ℤ) : ℚ := ⌊x / pow2 g⌋ * pow2 g

/-- Leading-bit exponent of a nonzero rational, not below FP32's `−126`. -/
def normExp (x : ℚ) : ℤ :=
  max (FloatLib.Numerics.RationalBinary.floorLog2 x.num.natAbs x.den) (-126)

/-! ## Models -/

inductive Kind where
  /-- `correct_rounding`: the exact sum, one final RNE. -/
  | exact
  /-- `pair_wise_sum`, subnormals flushed. -/
  | pairwise
  /-- `global_alignment`, or `odd_even_grouping` when `interleaved`; `c` is added late. -/
  | late (interleaved : Bool) (cutoff : Option ℕ)

structure MCModel where
  a : Operand
  b : Operand
  nfma : ℕ
  kind : Kind
  /-- Products with `|p_ℓ| ≥ 2^128` overflow (CDNA 3). -/
  productLimit : Bool

def sfma : MCModel := ⟨.fmt .binary32, .fmt .binary32, 1, .exact, false⟩
def cdna1F16 : MCModel := ⟨.fmt .binary16, .fmt .binary16, 4, .exact, false⟩
def cdna1BF16 : MCModel := ⟨.fmt .bfloat16, .fmt .bfloat16, 2, .exact, false⟩
def cdna2F16 : MCModel := ⟨.fmt .binary16, .fmt .binary16, 4, .pairwise, false⟩
def cdna2BF16 : MCModel := ⟨.fmt .bfloat16, .fmt .bfloat16, 2, .pairwise, false⟩
def cdna2BF16_1k : MCModel := ⟨.fmt .bfloat16, .fmt .bfloat16, 4, .pairwise, false⟩
def cdna3F16 : MCModel := ⟨.fmt .binary16, .fmt .binary16, 8, .late false none, true⟩
def cdna3BF16 : MCModel := ⟨.fmt .bfloat16, .fmt .bfloat16, 8, .late false none, true⟩
def cdna3XF32 : MCModel := ⟨.xf32, .xf32, 4, .late false none, true⟩
def cdna3FP8 (a b : FloatFormat) : MCModel := ⟨.fmt a, .fmt b, 16, .late true (some 25), true⟩

/-! ## CDNA 3 alignment -/

/-- `e_max` of the nonzero terms. -/
def maxExp : List Term → Option ℤ
  | [] => none
  | t :: ts =>
    if t.isZero then maxExp ts
    else some (match maxExp ts with | none => t.exponent | some e => max t.exponent e)

/-- `(e_max, S_{p_i,sum})`: each term truncated to 24 mantissa bits of `e_max`, then summed. -/
def alignedSum (ps : List Term) : Option ℤ × ℚ :=
  match maxExp ps with
  | none => (none, 0)
  | some e => (some e, (ps.map fun p => truncGrid p.value (e - 24)).sum)

def odds : List α → List α
  | [] => []
  | [x] => [x]
  | x :: _ :: xs => x :: odds xs

def evens : List α → List α
  | [] => []
  | [_] => []
  | _ :: y :: xs => y :: evens xs

/-- Odd and even groups each aligned to their own maximum, then RD at the common `e_max`. -/
def groupedSum (ps : List Term) : Option ℤ × ℚ :=
  let o := alignedSum (odds ps)
  let v := alignedSum (evens ps)
  let e : Option ℤ := match o.1, v.1 with
    | none, x => x
    | x, none => x
    | some a, some b => some (max a b)
  match e with
  | none => (none, 0)
  | some e => (some e, rdGrid o.2 (e - 24) + rdGrid v.2 (e - 24))

/-- `S_acc` after adding `c` late (Algorithm 1 lines 3–11, Algorithm 2's cutoff). -/
def lateC (cutoff : Option ℕ) (eMax : Option ℤ) (s : ℚ) (c : Term) : ℚ :=
  let eC : ℤ := if c.isZero then -126 else c.exponent
  let shifted : ℚ :=
    let t := rdGrid s (eC - 32) + c.value
    if t = 0 then 0 else rdGrid t (normExp t - 31)
  match eMax with
  | some e =>
    if eC ≤ e then
      let cut : Bool := match cutoff with | some n => decide (e - eC > n) | none => false
      s + (if cut then 0 else rdGrid c.value (e - 24))
    else shifted
  | none => shifted

/-! ## Special values -/

/-- A product or input before accumulation. -/
inductive Ext where
  | fin (q : ℚ)
  | inf (negative : Bool)
  | nan
  deriving DecidableEq

def Value.ext : Value → Ext
  | .finite t => .fin t.value
  | .inf s => .inf s
  | .nan => .nan

def Ext.isNaN : Ext → Bool | .nan => true | _ => false
def Ext.isInf (s : Bool) : Ext → Bool | .inf t => t == s | _ => false

/-- Block result with a special value: NaN dominates, `+∞` with `−∞` is NaN, else the infinity. -/
def special (xs : List Ext) : F32 :=
  if xs.any Ext.isNaN then nan32
  else if xs.any (Ext.isInf false) && xs.any (Ext.isInf true) then nan32
  else if xs.any (Ext.isInf false) then Model.posInf .binary32
  else if xs.any (Ext.isInf true) then Model.negInf .binary32
  else nan32

/-- `a_ℓ · b_ℓ` with IEEE special values and the CDNA 3 and CDNA 2 product overflows. -/
def product (P : MCModel) : Value → Value → Ext
  | .finite a, .finite b =>
    let q := (a.mul b).value
    if P.productLimit && decide (pow2 128 ≤ |q|) then .inf (decide (q < 0))
    else if (P.kind matches .pairwise) && Model.isInf (fl true q) then .inf (decide (q < 0))
    else .fin q
  | .nan, _ | _, .nan => .nan
  | .inf s, .inf t => .inf (s != t)
  | .inf s, .finite b | .finite b, .inf s => if b.isZero then .nan else .inf (s != b.dyadic.negative)

/-! ## CDNA 2 FP32 arithmetic -/

/-- `fl{u + v}` on FP32 words, subnormals flushed; NaN and infinities as in IEEE addition. -/
def add32 (u v : F32) : F32 :=
  match classifyModel u, classifyModel v with
  | .finite p, .finite q => fl true (p.value + q.value)
  | .nan, _ | _, .nan => nan32
  | .inf s, .inf t => if s == t then u else nan32
  | .inf _, .finite _ => u
  | .finite _, .inf _ => v

/-- The balanced pairwise sum of a group with `add32`. -/
def pairwiseGroupSum : ℕ → List F32 → F32
  | _, [] => Model.posZero .binary32
  | _, [x] => x
  | 0, _ => nan32
  | depth + 1, xs =>
    let h := xs.length / 2
    add32 (pairwiseGroupSum depth (xs.take h)) (pairwiseGroupSum depth (xs.drop h))

/-- CDNA 2: flushed inputs, products rounded to FP32, the pairwise sum, then `c` and `fl{·}`. -/
def pairwiseBlock (as bs : List Term) (c : Term) : F32 :=
  let leaves := List.zipWith (fun a b => fl true (a.flushed * b.flushed)) as bs
  let t := pairwiseGroupSum leaves.length leaves
  match classifyModel t with
  | .finite q => fl true (c.flushed + q.value)
  | _ => t

/-! ## Blocks -/

def finiteBlock (P : MCModel) (as bs : List Term) (c : Term) : F32 :=
  let ps := List.zipWith Term.mul as bs
  if P.productLimit && ps.any (fun p => decide (pow2 128 ≤ |p.value|)) then
    special (ps.map fun p =>
      if pow2 128 ≤ |p.value| then .inf (decide (p.value < 0)) else .fin p.value)
  else
    match P.kind with
    | .exact => fl false ((ps.map Term.value).sum + c.value)
    | .pairwise => pairwiseBlock as bs c
    | .late interleaved cutoff =>
      let s := if interleaved then groupedSum ps else alignedSum ps
      fl false (lateC cutoff s.1 s.2 c)

/-- One block `d = Σ a_ℓ b_ℓ + c` on words; `none` unless `a` and `b` have `N_FMA` entries. -/
def block (P : MCModel) (a b : List ℕ) (c : ℕ) : Option F32 :=
  if a.length ≠ P.nfma ∨ b.length ≠ P.nfma then none
  else
    let A := a.map P.a.read
    let B := b.map P.b.read
    let C := classify .binary32 c
    match A.mapM Value.finite?, B.mapM Value.finite?, C.finite? with
    | some as, some bs, some ct => some (finiteBlock P as bs ct)
    | _, _, _ => some (special (C.ext :: List.zipWith (product P) A B))

/-! ## Inner products -/

def chunks (n : ℕ) : ℕ → List α → List (List α)
  | _, [] => []
  | 0, _ => []
  | fuel + 1, xs => xs.take n :: chunks n fuel (xs.drop n)

def pad (n : ℕ) (xs : List ℕ) : List ℕ := xs ++ List.replicate ((n - xs.length % n) % n) 0

/-- `d = Σ a_ℓ b_ℓ + c` in zero-padded blocks of `N_FMA`, each output the next block's `c`. -/
def dot (P : MCModel) (a b : List ℕ) (c : ℕ) : Option F32 :=
  if a.length ≠ b.length then none
  else
    let a' := pad P.nfma a
    let b' := pad P.nfma b
    (List.zip (chunks P.nfma a'.length a') (chunks P.nfma b'.length b')).foldlM
      (fun w ab =>
        match classifyModel w with
        | .nan => some w
        | _ => block P ab.1 ab.2 (bits w)) (ofNat .binary32 c)

end MCFloat
