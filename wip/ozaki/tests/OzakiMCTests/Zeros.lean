import OzakiMCTests.LongFP64
import OzakiMC.ZeroCheck

/-! # Exact-zero results without the exact fallback on CDNA 3

The same disjoint-support row and column as on the Tensor Core (`x = [3, 0, 2^-30, 0]`,
`y = [0, 5, 0, −7 · 2^40]`), on CDNA 3 fp16 blocks with split-K: the rounding test with the normwise
bound falls back to the exact fallback (a sentinel is returned in its place), the rounding test with
the bound that counts only nonzero positions returns `0` from the first slice count, in rational and
bounded integer form, and with signed zeros `−0` exactly when every product is `−0`. The binary64
oracle cases still come out as the oracle's values. -/

open MatrixCore Ozaki Ozaki.MC OzakiMCTests.LongFP64

namespace OzakiMCTests.Zeros

def xs : List ℚ := [3, 0, 2 ^ (-30 : ℤ), 0]
def ys : List ℚ := [0, 5, 0, -7 * 2 ^ (40 : ℤ)]

def mult : MatrixMultiplier := mcSplitK cdna3F16 11

example : roundingTest rne64 ([5, 6].map fun s => ozaki1TruncatedEnclosure mult 11 s 96 xs ys)
    (some 12345) = some 12345 := by decide +kernel

example : roundingTest rne64
    (overlapTests mult (fun s N => ozaki1TruncatedEnclosureZ mult 11 s 96 N xs ys) [5, 6] xs ys)
    (some 12345) = some 0 := by decide +kernel

example : mcOzaki1CRDZ cdna3F16 11 96 [5, 6] 175 xs ys = some 0 ∧
    mcOzaki1CRBDZ cdna3F16 11 96 [5, 6] 175 xs ys = some 0 := by decide +kernel

def sx : List Signed := [⟨3, false⟩, ⟨0, true⟩]
def sy : List Signed := [⟨0, true⟩, ⟨5, false⟩]
def sx' : List Signed := [⟨3, false⟩, ⟨0, false⟩]

example : mcOzaki1CRDSZ cdna3F16 11 96 [5, 6] 175 sx sy = some ⟨0, true⟩ ∧
    mcOzaki1CRDSZ cdna3F16 11 96 [5, 6] 175 sx' sy = some ⟨0, false⟩ := by decide +kernel

/-- Correctly rounded FP64 with the bound that counts only nonzero positions equals the oracle on
both cases, with the rounding test on the truncated sum and in bounded registers. -/
def agreesZ (P : Model) : Bool :=
  [(A_narrow64, B_narrow64, C_narrow64), (A_wide64, B_wide64, C_wide64)].all fun (A, B, C) =>
    let Aq := A.map (·.map val64)
    let Bq := transpose (B.map (·.map val64))
    (Aq.zip (C.map (·.map val64))).all fun (x, crow) =>
      (Bq.zip crow).all fun (y, c) =>
        mcOzaki1CRDZ P 11 96 [5, 6] 175 x y == some c &&
          mcOzaki1CRBDZ P 11 96 [5, 6] 175 x y == some c

example : agreesZ cdna3F16 = true := by decide +kernel

end OzakiMCTests.Zeros
