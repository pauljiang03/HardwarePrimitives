import MatrixCore.Numerics.Notation
import Init.GrindInstances.Ring.Rat

/-! # Independent specification

A second transcription of the paper's matrix-core blocks, written in its fixed-point language
and sharing only standard-library arithmetic with the implementation:

* Table 1 layouts and IEEE/FNUZ field decoding;
* products `s_p = s_a s_b`, `e_p = e_a + e_b`;
* Algorithm 1 and Algorithm 2 on integer significands: "align to `e_max` and truncate to
  `24` fractional bits", "shift right and RD to `k` fractional bits", "normalize
  (subnormal-aware) and RD to `31` fractional bits";
* the exact sum of CDNA 1;
* binary32 RNE stated as a property of the result word over all finite binary32 words. -/

namespace MatrixCore.Spec

/-- A layout of Table 1: exponent bits, fraction bits, bias, and the FNUZ convention. -/
structure Layout where
  exponent : ℕ
  fraction : ℕ
  bias : ℤ
  fnuz : Bool
  deriving Repr, DecidableEq

def binary32 : Layout := ⟨8, 23, 127, false⟩
def binary16 : Layout := ⟨5, 10, 15, false⟩
def bfloat16 : Layout := ⟨8, 7, 127, false⟩
def e4m3 : Layout := ⟨4, 3, 8, true⟩
def e5m2 : Layout := ⟨5, 2, 16, true⟩

/-- A finite number `(−1)^σ · M · 2^(e − f)`: significand `s = M / 2^f`, exponent `e`. -/
structure Num where
  neg : Bool
  M : ℕ
  f : ℕ
  e : ℤ
  deriving Repr, DecidableEq

def Num.val (x : Num) : ℚ := (if x.neg then -1 else 1) * (x.M : ℚ) * (2 : ℚ) ^ (x.e - x.f)

/-- The signed integer `±M`. -/
def Num.int (x : Num) : ℤ := if x.neg then -(x.M : ℤ) else x.M

/-- Decode a word: `none` for an infinity or NaN; subnormals and zero carry the minimum normal
exponent `1 − bias`. -/
def decode (L : Layout) (w : ℕ) : Option Num :=
  let F := w % 2 ^ L.fraction
  let E := w / 2 ^ L.fraction % 2 ^ L.exponent
  let s := w / 2 ^ (L.fraction + L.exponent) % 2 = 1
  if (L.fnuz = false ∧ E = 2 ^ L.exponent - 1) ∨ (L.fnuz = true ∧ s ∧ E = 0 ∧ F = 0) then none
  else if E = 0 then some ⟨s, F, L.fraction, 1 - L.bias⟩
  else some ⟨s, 2 ^ L.fraction + F, L.fraction, (E : ℤ) - L.bias⟩

/-- How an operand word is read. -/
inductive Operand where
  | layout (L : Layout)
  /-- XF32: a binary32 word with its fraction cut to ten bits. -/
  | xf32
  deriving Repr, DecidableEq

def Operand.decode : Operand → ℕ → Option Num
  | .layout L, w => Spec.decode L w
  | .xf32, w => (Spec.decode binary32 w).map fun x => ⟨x.neg, x.M / 2 ^ 13, 10, x.e⟩

/-- `p = a · b`: significands multiplied, exponents added. -/
def mul (a b : Num) : Num := ⟨a.neg != b.neg, a.M * b.M, a.f + b.f, a.e + b.e⟩

/-! ## Fixed-point alignment -/

/-- `⌊M · 2^s⌋` for a natural `M`. -/
def shiftNat (M : ℕ) (s : ℤ) : ℕ := if 0 ≤ s then M * 2 ^ s.toNat else M / 2 ^ (-s).toNat

/-- Align `x` to exponent `e` and truncate to `k` fractional bits: the integer `A` such that
`A · 2^(e − k)` is `x` with its magnitude truncated. -/
def alignTrunc (x : Num) (e : ℤ) (k : ℕ) : ℤ :=
  let A := shiftNat x.M (x.e - x.f - (e - k))
  if x.neg then -(A : ℤ) else A

/-- RD of `V · 2^g` onto the grid `2^h`: the integer `⌊V · 2^(g − h)⌋`. -/
def shiftRD (V : ℤ) (g h : ℤ) : ℤ :=
  if h ≤ g then V * 2 ^ (g - h).toNat else V / (2 ^ (h - g).toNat : ℕ)

/-- `e_max` over the nonzero products. -/
def emax (ps : List Num) : Option ℤ := ((ps.filter fun p => p.M ≠ 0).map Num.e).max?

/-! ## Algorithms 1 and 2 -/

/-- Parameters of the late addition of `c`. -/
structure Late where
  /-- `n_eab`: products keep `23 + n_eab` fractional bits. -/
  neab : ℕ
  /-- `s'_c` is RD to this many fractional bits. -/
  cFrac : ℕ
  /-- `S'_{p_i,sum}` is RD to this many fractional bits. -/
  sumFrac : ℕ
  /-- The normalized `S_acc` is RD to this many fractional bits. -/
  accFrac : ℕ
  /-- binary8: `s'_c = 0` once `e_max − e_c` exceeds this. -/
  cCutoff : Option ℕ
  /-- `e_{c=0}`; `none` discards a zero `c`. -/
  cZero : Option ℤ
  deriving Repr, DecidableEq

/-- `e_c`, with `e_{c=0}` for a zero `c`. -/
def cExp (L : Late) (c : Num) : Option ℤ := if c.M = 0 then L.cZero else some c.e

/-- Lines 8–11 of Algorithm 1: `S'_{p_i,sum}` is `S` (on the grid `2^g`) shifted to `e_c` and RD
to `sumFrac` fractional bits; `S_acc = S'_{p_i,sum} + s_c`; `S_acc` is normalized, without going
below exponent `−126`, and RD to `accFrac` fractional bits. -/
def shiftedBranch (L : Late) (S : ℤ) (g : ℤ) (c : Num) (ec : ℤ) : ℚ :=
  let G := ec - L.sumFrac
  let A := shiftRD S g G + shiftRD c.int (c.e - c.f) G
  if A = 0 then 0
  else
    let lead := (A.natAbs.log2 : ℤ) + G
    let H := max lead (-126) - L.accFrac
    (shiftRD A G H : ℚ) * (2 : ℚ) ^ H

/-- Lines 3–11 of Algorithm 1 (and 7–15 of Algorithm 2) for the product sum `S · 2^(e_max − F)`. -/
def lateC (L : Late) (em : Option ℤ) (S : ℤ) (c : Num) : ℚ :=
  let F : ℤ := 23 + L.neab
  match em, cExp L c with
  | none, none => 0
  | some e, none => (S : ℚ) * (2 : ℚ) ^ (e - F)
  | none, some ec => shiftedBranch L 0 0 c ec
  | some e, some ec =>
    if ec ≤ e then
      let cut := match L.cCutoff with
        | some n => decide (e - ec > n)
        | none => false
      let sc : ℤ := if cut then 0 else shiftRD c.int (c.e - c.f) (e - L.cFrac)
      (S : ℚ) * (2 : ℚ) ^ (e - F) + (sc : ℚ) * (2 : ℚ) ^ (e - L.cFrac)
    else shiftedBranch L S (e - F) c ec

/-- Algorithm 1: global alignment of the products, then late `c`. -/
def algorithm1 (L : Late) (ps : List Num) (c : Num) : ℚ :=
  match emax ps with
  | none => lateC L none 0 c
  | some e => lateC L (some e) (ps.map fun p => alignTrunc p e (23 + L.neab)).sum c

/-- Elements at even 0-based positions: `p₁, p₃, …`. -/
def odds (ps : List Num) : List Num := ((ps.zipIdx).filter fun q => q.2 % 2 = 0).map (·.1)

/-- Elements at odd 0-based positions: `p₂, p₄, …`. -/
def evens (ps : List Num) : List Num := ((ps.zipIdx).filter fun q => q.2 % 2 = 1).map (·.1)

/-- One group of Algorithm 2: aligned to its own maximum exponent and truncated to `F`
fractional bits, then shifted to `e_max` and RD to `F` fractional bits. -/
def groupPart (F : ℕ) (qs : List Num) (e : ℤ) : ℤ :=
  match emax qs with
  | none => 0
  | some eq => shiftRD ((qs.map fun p => alignTrunc p eq F).sum) (eq - F) (e - F)

/-- Algorithm 2: odd and even products aligned to their own maxima and truncated, the two sums
shifted to the common `e_max` and RD to `23 + n_eab` fractional bits, then late `c`. -/
def algorithm2 (L : Late) (ps : List Num) (c : Num) : ℚ :=
  match emax ps with
  | none => lateC L none 0 c
  | some e => lateC L (some e)
      (groupPart (23 + L.neab) (odds ps) e + groupPart (23 + L.neab) (evens ps) e) c

/-! ## Blocks -/

inductive Kind where
  /-- CDNA 1: the exact `Σ p_ℓ + c`. -/
  | exact
  | algorithm1 (L : Late)
  | algorithm2 (L : Late)
  deriving Repr, DecidableEq

structure Params where
  a : Operand
  b : Operand
  nfma : ℕ
  kind : Kind
  /-- `|p_ℓ| ≥ 2^128` overflows. -/
  productLimit : Bool
  deriving Repr, DecidableEq

def magnitude (q : ℚ) : ℚ := if q < 0 then -q else q

/-- The value presented to the final RNE. -/
def accumulated (P : Params) (as bs : List Num) (c : Num) : ℚ :=
  let ps := List.zipWith mul as bs
  match P.kind with
  | .exact => (ps.map Num.val).sum + c.val
  | .algorithm1 L => algorithm1 L ps c
  | .algorithm2 L => algorithm2 L ps c

/-- Value of a finite binary32 word. -/
def value32 (w : BitVec 32) : Option ℚ := (decode binary32 w.toNat).map Num.val

/-- Binary32 RNE of `x` to the word `w`: the sign of `x`, a value nearest to `x` among all finite
binary32 words, and an even last bit when another finite word is equally near. -/
def RoundsNearestEven (x : ℚ) (w : BitVec 32) : Prop :=
  (w.toNat / 2147483648 % 2 = 1 ↔ x < 0) ∧
  ∃ d, value32 w = some d ∧
    (∀ v y, value32 v = some y → magnitude (x - d) ≤ magnitude (x - y)) ∧
    (∀ v y, value32 v = some y → y ≠ d → magnitude (x - y) = magnitude (x - d) →
      w.toNat % 2 = 0)

/-- RNE into binary32 overflows at `2^128 − 2^103`. -/
def overflows (x : ℚ) : Prop := (2 : ℚ) ^ (128 : ℤ) - (2 : ℚ) ^ (103 : ℤ) ≤ magnitude x

/-- `w` is the output of the block for words `a`, `b`, `c`. -/
def Result (P : Params) (a b : List ℕ) (c : BitVec 32) (w : BitVec 32) : Prop :=
  a.length = P.nfma ∧ b.length = P.nfma ∧
    ∃ as bs cn, a.mapM P.a.decode = some as ∧ b.mapM P.b.decode = some bs ∧
      decode binary32 c.toNat = some cn ∧
      (P.productLimit = true →
        ∀ p ∈ List.zipWith mul as bs, magnitude p.val < (2 : ℚ) ^ (128 : ℤ)) ∧
      ¬ overflows (accumulated P as bs cn) ∧ RoundsNearestEven (accumulated P as bs cn) w

/-! ## CDNA 2: pairwise sums of binary32 values (Fig. 2) -/

/-- A CDNA 2 block: operand formats and group size (`2`, or `4` for fp16 and bf16 `_1k`). -/
structure PairwiseParams where
  a : Operand
  b : Operand
  group : ℕ
  deriving Repr, DecidableEq

/-- No subnormal inputs: a significand below one becomes zero. -/
def flushNum (x : Num) : Num := if x.M < 2 ^ x.f then { x with M := 0 } else x

/-- Smallest normal binary32 magnitude. -/
def minNormal : ℚ := (2 : ℚ) ^ (-126 : ℤ)

/-- `fl{x} = y` on CDNA 2: binary32 RNE of `x` without overflow, a subnormal result replaced by
zero. -/
def Fl (x y : ℚ) : Prop :=
  ¬ overflows x ∧ ∃ w d, RoundsNearestEven x w ∧ value32 w = some d ∧
    y = (if d ≠ 0 ∧ magnitude d < minNormal then 0 else d)

/-- The output word of `fl{x}` on CDNA 2: a subnormal result is replaced by the zero of its
sign. -/
def FlWord (x : ℚ) (w : BitVec 32) : Prop :=
  ¬ overflows x ∧ ∃ w₀ d, RoundsNearestEven x w₀ ∧ value32 w₀ = some d ∧
    w = (if d ≠ 0 ∧ magnitude d < minNormal then
      BitVec.ofNat 32 (w₀.toNat / 2147483648 % 2 * 2147483648) else w₀)

/-- Fig. 2 for the products `p_ℓ` and the flushed `c`: groups of two
`d = fl{c + fl{fl{p₁} + fl{p₂}}}` and groups of four
`d = fl{c + fl{fl{fl{p₁} + fl{p₂}} + fl{fl{p₃} + fl{p₄}}}}`, where `fl{p_ℓ}` converts each product
to binary32. -/
def pairwiseOutput (ps : List ℚ) (c : ℚ) (w : BitVec 32) : Prop :=
  match ps with
  | [x₁, x₂] => ∃ q₁ q₂ t, Fl x₁ q₁ ∧ Fl x₂ q₂ ∧ Fl (q₁ + q₂) t ∧ FlWord (c + t) w
  | [x₁, x₂, x₃, x₄] => ∃ q₁ q₂ q₃ q₄ u v t,
      Fl x₁ q₁ ∧ Fl x₂ q₂ ∧ Fl x₃ q₃ ∧ Fl x₄ q₄ ∧
      Fl (q₁ + q₂) u ∧ Fl (q₃ + q₄) v ∧ Fl (u + v) t ∧ FlWord (c + t) w
  | _ => False

/-- `w` is the output of a CDNA 2 block for the words `a`, `b`, `c`: the inputs are decoded and
flushed, multiplied exactly, and summed as in Fig. 2. -/
def PairwiseResult (P : PairwiseParams) (a b : List ℕ) (c : BitVec 32) (w : BitVec 32) : Prop :=
  a.length = P.group ∧ b.length = P.group ∧
    ∃ as bs cn, a.mapM P.a.decode = some as ∧ b.mapM P.b.decode = some bs ∧
      decode binary32 c.toNat = some cn ∧
      pairwiseOutput ((List.zipWith mul (as.map flushNum) (bs.map flushNum)).map Num.val)
        (flushNum cn).val w

def cdna2F16 : PairwiseParams := ⟨.layout binary16, .layout binary16, 4⟩
def cdna2BF16 : PairwiseParams := ⟨.layout bfloat16, .layout bfloat16, 2⟩
def cdna2BF16_1k : PairwiseParams := ⟨.layout bfloat16, .layout bfloat16, 4⟩

/-! ## The paper's parameters -/

/-- `align(c, S_{p_i,sum}) = (24, 32, RD)`, `n_eab = 1`, `e_{c=0} = −126`. -/
def cdna3Late : Late := ⟨1, 24, 32, 31, none, some (-126)⟩

/-- binary8: as `cdna3Late`, with `s'_c = 0` beyond a shift of `25`. -/
def cdna3Late8 : Late := ⟨1, 24, 32, 31, some 25, some (-126)⟩

def sfma : Params := ⟨.layout binary32, .layout binary32, 1, .exact, false⟩
def cdna1F16 : Params := ⟨.layout binary16, .layout binary16, 4, .exact, false⟩
def cdna1BF16 : Params := ⟨.layout bfloat16, .layout bfloat16, 2, .exact, false⟩
def cdna3F16 : Params := ⟨.layout binary16, .layout binary16, 8, .algorithm1 cdna3Late, true⟩
def cdna3BF16 : Params := ⟨.layout bfloat16, .layout bfloat16, 8, .algorithm1 cdna3Late, true⟩
def cdna3XF32 : Params := ⟨.xf32, .xf32, 4, .algorithm1 cdna3Late, true⟩
def cdna3FP8 (a b : Layout) : Params := ⟨.layout a, .layout b, 16, .algorithm2 cdna3Late8, true⟩

end MatrixCore.Spec
