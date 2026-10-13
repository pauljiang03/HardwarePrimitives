import OzakiTCTests.LongFP64
import OzakiTC.Bounded

/-! # Correctly rounded FP64 with bounded registers

The binary64 cases of [`data/correct-reference.json`](../../data/correct-reference.json) through
`tcOzaki1CRBD`, the correctly rounded Ozaki-I whose rounding test, exact fallback and final rounding
run in integer registers of bounded width, on V100 fp16 blocks with split-K. It returns the
exact-fraction oracle's words with the rounding test succeeding on entries (five, then six slices, a
`96`-bit truncated sum), and with no rounding test at all (`ss = []`), so that every entry goes
through the bounded exact fallback.

The same cases through `tcOzaki1CRID`, whose inputs are the stored entries `(m, e)` and whose slicing
is integer too, and three zero results through `tcOzaki1CRIDS`, which gives them IEEE's sign. -/

open TensorCore Ozaki Ozaki.TC OzakiTCTests.Correct OzakiTCTests.LongFP64

namespace OzakiTCTests.Bounded

example : (do
    let A ← decode64 A_narrow64; let B ← decode64 B_narrow64
    let C ← A.mapM fun x => (transpose B).mapM fun y => tcOzaki1CRBD v100F16F32 11 96 [5, 6] 175 x y
    encode64 C) = some C_narrow64 := by
  decide +kernel

example : (do
    let A ← decode64 A_wide64; let B ← decode64 B_wide64
    let C ← A.mapM fun x => (transpose B).mapM fun y => tcOzaki1CRBD v100F16F32 11 96 [5, 6] 175 x y
    encode64 C) = some C_wide64 := by
  decide +kernel

/-! Every entry through the bounded exact fallback. -/

example : (do
    let A ← decode64 A_narrow64; let B ← decode64 B_narrow64
    let C ← A.mapM fun x => (transpose B).mapM fun y => tcOzaki1CRBD v100F16F32 11 96 [] 175 x y
    encode64 C) = some C_narrow64 := by
  decide +kernel

example : (do
    let A ← decode64 A_wide64; let B ← decode64 B_wide64
    let C ← A.mapM fun x => (transpose B).mapM fun y => tcOzaki1CRBD v100F16F32 11 96 [] 175 x y
    encode64 C) = some C_wide64 := by
  decide +kernel

/-! ## Every step off the Tensor Core in integers -/

/-- A finite binary64 word as the entry `(m, e)` it stores, worth `m · 2^e`. -/
def entry64 (w : BitVec 64) : ℤ × ℤ :=
  let n : ℕ := w.toNat
  let e : ℕ := (n / 2 ^ 52) % 2 ^ 11
  let m : ℕ := n % 2 ^ 52
  let mag : ℤ × ℤ := if e = 0 then ((m : ℤ), -1074) else (((2 ^ 52 + m : ℕ) : ℤ), (e : ℤ) - 1075)
  if n / 2 ^ 63 = 1 then (-mag.1, mag.2) else mag

/-- The columns of a matrix given by rows. -/
def cols {α : Type} [Inhabited α] (B : List (List α)) : List (List α) :=
  (List.range (B.headD []).length).map fun j => B.map fun r => r.getD j default

/-- The entries are the words' values. -/
example : (A_narrow64.map (·.map entry64)).map entryVals = (decode64 A_narrow64).getD [] ∧
    (B_wide64.map (·.map entry64)).map entryVals = (decode64 B_wide64).getD [] := by
  decide +kernel

/-- The product of two binary64 matrices given as words, by `tcOzaki1CRID` on V100 fp16 blocks. -/
def gemmI (ss : List ℕ) (A B : List (List (BitVec 64))) : Option (List (List (BitVec 64))) := do
  let C ← (A.map (·.map entry64)).mapM fun x =>
    (cols (B.map (·.map entry64))).mapM fun y => tcOzaki1CRID v100F16F32 11 96 ss 175 x y
  encode64 C

example : gemmI [5, 6] A_narrow64 B_narrow64 = some C_narrow64 := by decide +kernel

example : gemmI [5, 6] A_wide64 B_wide64 = some C_wide64 := by decide +kernel

example : gemmI [] A_narrow64 B_narrow64 = some C_narrow64 := by decide +kernel

example : gemmI [] A_wide64 B_wide64 = some C_wide64 := by decide +kernel

/-! ## Signed zeros -/

/-- Every product is `−0`: `(−0) · 1` and `(+0) · (−0)`. -/
def negZerosI : List SEntry × List SEntry :=
  ([((0, 0), true), ((0, 0), false)], [((1, 0), false), ((0, 0), true)])

/-- The products cancel exactly: `1 · 1 + (−1) · 1`. -/
def cancelsI : List SEntry × List SEntry :=
  ([((1, 0), false), ((-1, 0), true)], [((1, 0), false), ((1, 0), false)])

/-- A negative product underflows: `2^-540 · (−2^-540) = −2^-1080`. -/
def underflowsI : List SEntry × List SEntry := ([((1, -540), false)], [((-1, -540), true)])

example : tcOzaki1CRIDS v100F16F32 11 96 [5, 6] 175 negZerosI.1 negZerosI.2 = some ⟨0, true⟩ ∧
    crSigned rne64 (negZerosI.1.map toSigned) (negZerosI.2.map toSigned) = some ⟨0, true⟩ := by
  decide +kernel

example : tcOzaki1CRIDS v100F16F32 11 96 [5, 6] 175 cancelsI.1 cancelsI.2 = some ⟨0, false⟩ ∧
    crSigned rne64 (cancelsI.1.map toSigned) (cancelsI.2.map toSigned) = some ⟨0, false⟩ := by
  decide +kernel

example : tcOzaki1CRIDS v100F16F32 11 96 [5, 6] 175 underflowsI.1 underflowsI.2 = some ⟨0, true⟩ ∧
    crSigned rne64 (underflowsI.1.map toSigned) (underflowsI.2.map toSigned) = some ⟨0, true⟩ := by
  decide +kernel

end OzakiTCTests.Bounded
