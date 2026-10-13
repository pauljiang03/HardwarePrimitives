import MatrixCore

/-! Test inputs written as decoded values.

Every input value is encoded exactly or the test fails to produce an observation, so a value
that a format cannot represent cannot enter a test silently. -/

namespace MatrixCoreTests

open MatrixCore

/-- An input value: finite, an infinity, or NaN. -/
inductive In where
  | v (q : ℚ)
  | inf (negative : Bool)
  | nan
  deriving Repr, DecidableEq

instance : Coe ℚ In := ⟨In.v⟩
instance : OfNat In n := ⟨.v n⟩
instance : Neg In := ⟨fun | .v q => .v (-q) | .inf s => .inf (!s) | .nan => .nan⟩

/-- Observed output with finite results as values. -/
inductive Obs where
  | v (q : ℚ)
  | inf (negative : Bool)
  | nan
  deriving Repr, DecidableEq

def encodeIn : (i : InputFormat) → In → Option i.Word
  | i, .v q => i.encodeExact q
  | .packed f, .inf s =>
    if f.specials = .ieee then some (f.pack s (2 ^ f.exponentBits - 1) 0) else none
  | .xf32, .inf s => some (infinity32 s)
  | .packed f, .nan =>
    if f.specials = .ieee then some (f.pack false (2 ^ f.exponentBits - 1) 1)
    else some (f.pack true 0 0)
  | .xf32, .nan => some 0x7FC00000

def encodeC : In → Option F32
  | .v q => fp32Exact q
  | .inf s => some (infinity32 s)
  | .nan => some 0x7FC00000

def toObs : Outcome → Obs
  | .finite d => .v ((value32 d).getD 0)
  | .infinity s => .inf s
  | .nan => .nan

/-- `d = Σ a_ℓ b_ℓ + c` through the chained blocks of a profile, for operand pairs `(a_ℓ, b_ℓ)`. -/
def observe (P : Model) (ps : List (In × In)) (c : In) : Option Obs := do
  let a ← ps.mapM fun q => encodeIn P.a q.1
  let b ← ps.mapM fun q => encodeIn P.b q.2
  let cw ← encodeC c
  let o ← dotOutcome P a b cw
  return toObs o

/-- Operands `(a, b)` with `a · b = p`, splitting the exponent of `p` evenly so that both are
normal whenever `p` is a product of two normal values; then `e_a + e_b = ⌊log₂ |p|⌋`. -/
def splitProduct (p : ℚ) : In × In :=
  if p = 0 then (.v 0, .v 1)
  else
    let h := -(log2Floor (absQ p) / 2)
    (.v (p * pow2 h), .v (pow2 (-h)))

/-- Products given by value, each from normal operands as by `splitProduct`. -/
def observeP (P : Model) (ps : List ℚ) (c : In) : Option Obs :=
  observe P (ps.map splitProduct) c

/-- `2^e`. -/
abbrev p2 (e : ℤ) : ℚ := pow2 e

/-- `Σ_{ℓ=lo}^{hi} 2^{-ℓ}`. -/
def bits (lo hi : ℕ) : ℚ := sumQ ((List.range (hi + 1 - lo)).map fun i => pow2 (-((lo + i : ℕ) : ℤ)))

end MatrixCoreTests
