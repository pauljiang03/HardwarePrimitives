import OzakiTCTests.LongFP64
import OzakiTC.ZeroCheck

/-! # Exact-zero results without the exact path

A row and a column with disjoint supports (`x = [3, 0, 2^-30, 0]`, `y = [0, 5, 0, −7 · 2^40]`, binary64
values): every product is zero, but `x` and `y` are not. On V100 fp16 blocks with split-K:

* the normwise check never settles it, so the entry goes to the exact path: with a sentinel in
  place of the exact path, the normwise scheme returns the sentinel;
* the check with the overlap count settles it on the first slice count: with the same sentinel,
  the scheme returns `0`; the bounded integer check does too;
* with signed zeros, the result is `−0` when every product is `−0` and `+0` otherwise, again from the
  first check.

The binary64 oracle cases still come out as the oracle's words, with the window check and in
bounded registers. -/

open TensorCore Ozaki Ozaki.TC OzakiTCTests.Correct OzakiTCTests.LongFP64

namespace OzakiTCTests.Zeros

def xs : List ℚ := [3, 0, 2 ^ (-30 : ℤ), 0]
def ys : List ℚ := [0, 5, 0, -7 * 2 ^ (40 : ℤ)]

def mult : MatrixMultiplier := tcSplitK v100F16F32 11

example : supportOverlap xs ys = 0 := by decide +kernel

/-- The normwise check does not settle the entry, so the scheme falls back: with the sentinel
`12345` as its exact path it returns the sentinel. -/
example : (ozaki1TruncatedEnclosure mult 11 5 96 xs ys).bind
    (fun e => roundEnclosure rne64 e.1 e.2) = none := by decide +kernel
example : roundingTest rne64 ([5, 6].map fun s => ozaki1TruncatedEnclosure mult 11 s 96 xs ys)
    (some 12345) = some 12345 := by decide +kernel

/-- The check with the overlap count settles it on the first slice count: enclosure `(0, 0)`, and
the sentinel is never used. -/
example : ozaki1TruncatedEnclosureZ mult 11 5 96 (supportOverlap xs ys) xs ys = some (0, 0) := by
  decide +kernel
example : roundingTest rne64
    (overlapTests mult (fun s N => ozaki1TruncatedEnclosureZ mult 11 s 96 N xs ys) [5, 6] xs ys)
    (some 12345) = some 0 := by decide +kernel
example : ozaki1TestBZ mult 53 (-1022) 1023 11 5 96 (supportOverlap xs ys) xs ys = some 0 := by
  decide +kernel
example : tcOzaki1CRDZ v100F16F32 11 96 [5, 6] 175 xs ys = some 0 ∧
    tcOzaki1CRBDZ v100F16F32 11 96 [5, 6] 175 xs ys = some 0 := by decide +kernel

/-! Signed zeros: `3 · (−0)` and `(−0) · 5` are both `−0`, so the sum is `−0`; with `+0` in place of
the second `−0` one product is `+0`, and the sum is `+0`. Both from the first check, with a sentinel
exact path. -/

def sx : List Signed := [⟨3, false⟩, ⟨0, true⟩]
def sy : List Signed := [⟨0, true⟩, ⟨5, false⟩]
def sx' : List Signed := [⟨3, false⟩, ⟨0, false⟩]

example : roundingTestSignedZ rne64
    (overlapTests mult (fun s N => ozaki1TruncatedEnclosureZ mult 11 s 96 N (vals sx) (vals sy)) [5]
      (vals sx) (vals sy)) (some 12345) (allNegZero sx sy) = some ⟨0, true⟩ ∧
    crSigned rne64 sx sy = some ⟨0, true⟩ := by decide +kernel
example : tcOzaki1CRDSZ v100F16F32 11 96 [5, 6] 175 sx' sy = some ⟨0, false⟩ ∧
    crSigned rne64 sx' sy = some ⟨0, false⟩ := by decide +kernel

/-! ## The oracle cases -/

example : (do
    let A ← decode64 A_narrow64; let B ← decode64 B_narrow64
    let C ← A.mapM fun x => (transpose B).mapM fun y => tcOzaki1CRDZ v100F16F32 11 96 [5, 6] 175 x y
    encode64 C) = some C_narrow64 := by
  decide +kernel

example : (do
    let A ← decode64 A_wide64; let B ← decode64 B_wide64
    let C ← A.mapM fun x => (transpose B).mapM fun y => tcOzaki1CRDZ v100F16F32 11 96 [5, 6] 175 x y
    encode64 C) = some C_wide64 := by
  decide +kernel

example : (do
    let A ← decode64 A_wide64; let B ← decode64 B_wide64
    let C ← A.mapM fun x => (transpose B).mapM fun y => tcOzaki1CRBDZ v100F16F32 11 96 [5, 6] 175 x y
    encode64 C) = some C_wide64 := by
  decide +kernel

end OzakiTCTests.Zeros
