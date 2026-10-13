import TensorCore.Numerics.Notation
import Std
import Init.Data.Rat
import Init.GrindInstances.Ring.Rat

/-! Independent specification of the aligned FP32-output variants in Accurate Models v4, Section 4.1 (especially 4.1.1, 4.1.2, 4.1.6), Figures 2/3/5, and Table 3. -/

namespace TensorCore.IndependentSpec

structure Layout where
  mantissaBits : ℕ
  exponent : ℕ
  bias : ℤ
  deriving Repr, DecidableEq

@[implicit_reducible] def Layout.width (f : Layout) : ℕ := 1 + f.exponent + f.mantissaBits

def binary32 : Layout := ⟨23, 8, 127⟩

structure Parameters where
  input : Layout
  nfma : ℕ
  alignFracBits : ℤ
  eAlignMin : Option ℤ
  deriving Repr, DecidableEq

structure Input (p : Parameters) where
  products : List (BitVec p.input.width × BitVec p.input.width)
  c : BitVec 32
  deriving Repr, DecidableEq

structure Term where
  value : ℚ
  exponent : ℤ
  deriving Repr, DecidableEq

/-- IEEE fields, including the minimum-normal unnormalized exponent of subnormal inputs. -/
def decode (f : Layout) (word : ℕ) : Option Term :=
  let E := word / 2 ^ f.mantissaBits % 2 ^ f.exponent
  let M := word % 2 ^ f.mantissaBits
  if E = 2 ^ f.exponent - 1 then none
  else if E = 0 ∧ M = 0 then some ⟨0, 0⟩
  else
    let e := (if E = 0 then 1 else (E : ℤ)) - f.bias
    let m := if E = 0 then M else 2 ^ f.mantissaBits + M
    let s : ℤ := if word / 2 ^ (f.mantissaBits + f.exponent) = 0 then 1 else -1
    some ⟨(s : ℚ) * (m : ℚ) * (2 : ℚ) ^ (e - f.mantissaBits), e⟩

/-- Unnormalized exponents are added, even when the resulting significand is at least two. -/
def product (a b : Term) : Term := ⟨a.value * b.value, a.exponent + b.exponent⟩

def terms (p : Parameters) (x : Input p) : Option (List Term) := do
  let c ← decode binary32 x.c.toNat
  let ps ← x.products.mapM fun (a, b) => do
    return product (← decode p.input a.toNat) (← decode p.input b.toNat)
  return c :: ps

def joinExponent : Option ℤ → Option ℤ → Option ℤ
  | none, b => b
  | a, none => a
  | some a, some b => some (max a b)

/-- A right fold of nonzero terms; exact zero never selects the alignment grid. -/
def largestExponent (ts : List Term) : Option ℤ :=
  ts.foldr (fun t rest => if t.value = 0 then rest
    else joinExponent (some t.exponent) rest) none

def exponent (p : Parameters) (ts : List Term) : Option ℤ :=
  match largestExponent ts with
  | none => none
  | some e => some (match p.eAlignMin with | none => e | some f => max e f)

def magnitude (v : ℚ) : ℚ := if v < 0 then -v else v

/-- Discard magnitude bits on the common grid, then restore the sign. -/
def keptBits (v q : ℚ) : ℤ :=
  (if v < 0 then -1 else 1) * (magnitude v / q).floor

def accumulated (p : Parameters) (ts : List Term) : ℚ :=
  let q := (2 : ℚ) ^ ((exponent p ts).getD 0 - p.alignFracBits)
  ((ts.foldr (fun t z => keptBits t.value q + z) 0 : ℤ) : ℚ) * q

def maxFinite : ℚ := (16777215 : ℚ) * (2 : ℚ) ^ (104 : ℤ)

/-- Domain from the specification-side computation, without evaluating the implementation. -/
def Valid (p : Parameters) (x : Input p) : Prop :=
  x.products.length = p.nfma ∧
    ∃ ts, terms p x = some ts ∧ magnitude (accumulated p ts) ≤ maxFinite

def value32 (bits : BitVec 32) : Option ℚ := (decode binary32 bits.toNat).map Term.value

/-- A finite value lies between zero and the pre-conversion accumulated value. -/
def Between (x y : ℚ) : Prop :=
  (0 ≤ x ∧ 0 ≤ y ∧ y ≤ x) ∨ (x ≤ 0 ∧ x ≤ y ∧ y ≤ 0)

/-- FP32 truncation specified by ordering *all finite encoded values*, plus the sign bit. -/
def Rounds (x : ℚ) (bits : BitVec 32) : Prop :=
  (bits.toNat / 2147483648 != 0) = decide (x < 0) ∧
  ∃ d, value32 bits = some d ∧ Between x d ∧
    ∀ other y, value32 other = some y → Between x y → magnitude y ≤ magnitude d

def Result (p : Parameters) (x : Input p) (bits : BitVec 32) : Prop :=
  x.products.length = p.nfma ∧ ∃ ts,
    terms p x = some ts ∧ magnitude (accumulated p ts) ≤ maxFinite ∧
      Rounds (accumulated p ts) bits

/-- Mathematical output selector. -/
noncomputable def bits (p : Parameters) (x : Input p) : Option (BitVec 32) := by
  classical
  exact if h : ∃ b, Result p x b then some (Classical.choose h) else none

end TensorCore.IndependentSpec
