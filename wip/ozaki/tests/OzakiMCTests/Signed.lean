import OzakiMC.Signed

/-! # Signed zeros

Three cases where the sign of a zero result matters, each checked against the specification
`crSigned` and against the expected IEEE word by kernel evaluation:

* every product is `−0` (`(−0)·1` and `(+0)·(−0)`): the result is `−0`;
* the products cancel exactly (`1·1 + (−1)·1`): the result is `+0`;
* a negative product underflows (`2^-540 · (−2^-540) = −2^-1080`): the result is `−0`. -/

open MatrixCore Ozaki Ozaki.MC

namespace OzakiMCTests.Signed

def negZeros : List Signed × List Signed := ([⟨0, true⟩, ⟨0, false⟩], [⟨1, false⟩, ⟨0, true⟩])
def cancels : List Signed × List Signed := ([⟨1, false⟩, ⟨-1, true⟩], [⟨1, false⟩, ⟨1, false⟩])
def underflows : List Signed × List Signed :=
  ([⟨2 ^ (-540 : ℤ), false⟩], [⟨-2 ^ (-540 : ℤ), true⟩])

example : mcOzaki1CRDS cdna3F16 11 96 [5, 6] 175 negZeros.1 negZeros.2 = some ⟨0, true⟩ ∧
    crSigned rne64 negZeros.1 negZeros.2 = some ⟨0, true⟩ := by decide +kernel

example : mcOzaki1CRDS cdna3F16 11 96 [5, 6] 175 cancels.1 cancels.2 = some ⟨0, false⟩ ∧
    crSigned rne64 cancels.1 cancels.2 = some ⟨0, false⟩ := by decide +kernel

example : mcOzaki1CRDS cdna3F16 11 96 [5, 6] 175 underflows.1 underflows.2 = some ⟨0, true⟩ ∧
    crSigned rne64 underflows.1 underflows.2 = some ⟨0, true⟩ := by decide +kernel

end OzakiMCTests.Signed
