import OzakiMCTests.LongFP64
import OzakiMCTests.Signed
import OzakiMC.Ozaki2Bounded

/-! # Ozaki-II with bounded registers, signed zeros, and as an integer pipeline, on CDNA 3

* `mcOzaki2CRB`: correctly rounded FP64 by Ozaki-II on CDNA 3 fp16 blocks with split-K, the check on
  integer enclosures and the bounded exact path (twelve moduli at most `4096`, `P = 69`), returns
  the exact-fraction oracle's values on both binary64 cases.
* `mcOzaki2CRZ`: the same as an integer pipeline, inputs as integer pairs `(m, e)` decoded from the
  binary64 words by bit operations (the pairs are the decoded values).
* **Signed zeros** for Ozaki-II, rational and bounded: products that are all `−0` give `−0`,
  exact cancellation `+0`, an underflowing negative product `−0`. -/

open MatrixCore Ozaki Ozaki.MC OzakiMCTests.LongFP64

namespace OzakiMCTests.BoundedSchemes

/-- Twelve pairwise coprime moduli at most `4096`. -/
def basis12 : CRTBasis := crtBasis [4096, 4095, 4093, 4091, 4087, 4079, 4073, 4063, 4061, 4057, 4051, 4049]

/-- A binary64 word as an integer pair `(m, e)` worth `m 2^e`, by bit operations. -/
def pair64 (w : ℕ) : ℤ × ℤ :=
  let e : ℕ := (w / 2 ^ 52) % 2 ^ 11
  let m : ℕ := w % 2 ^ 52
  let mag : ℤ := if e = 0 then (m : ℤ) else ((2 ^ 52 + m : ℕ) : ℤ)
  (if w / 2 ^ 63 = 1 then -mag else mag, if e = 0 then -1074 else (e : ℤ) - 1075)

/-- Columns of a matrix. -/
def transposeG {α : Type} : List (List α) → List (List α)
  | [] => []
  | [r] => r.map fun a => [a]
  | r :: rs => List.zipWith List.cons r (transposeG rs)

def cases64 : List (List (List ℕ) × List (List ℕ) × List (List ℕ)) :=
  [(A_narrow64, B_narrow64, C_narrow64), (A_wide64, B_wide64, C_wide64)]

/-- The decoded pairs are the decoded values. -/
example : cases64.all (fun (A, B, _) =>
    (A ++ B).all fun row => row.all fun w => entryVal (pair64 w) == val64 w) = true := by
  decide +kernel

/-- Ozaki-II with bounded registers returns the oracle's values on both cases. -/
def agreesB (P : Model) : Bool :=
  cases64.all fun (A, B, C) =>
    let Aq := A.map (·.map val64)
    let Bq := transposeG (B.map (·.map val64))
    (Aq.zip (C.map (·.map val64))).all fun (x, crow) =>
      (Bq.zip crow).all fun (y, c) => mcOzaki2CRB P [(basis12, 69)] 11 175 x y == some c

/-- The integer pipeline returns the oracle's values on both cases. -/
def agreesZ (P : Model) : Bool :=
  cases64.all fun (A, B, C) =>
    let Ap := A.map (·.map pair64)
    let Bp := transposeG (B.map (·.map pair64))
    (Ap.zip (C.map (·.map val64))).all fun (x, crow) =>
      (Bp.zip crow).all fun (y, c) => mcOzaki2CRZ P [(basis12, 69)] 11 175 x y == some c

example : agreesB cdna3F16 = true := by decide +kernel

example : agreesZ cdna3F16 = true := by decide +kernel

open OzakiMCTests.Signed in
example : mcOzaki2CRDS cdna3F16 [(basis12, 69)] 11 175 negZeros.1 negZeros.2 = some ⟨0, true⟩ ∧
    mcOzaki2CRBS cdna3F16 [(basis12, 69)] 11 175 negZeros.1 negZeros.2 = some ⟨0, true⟩ ∧
    mcOzaki2CRDS cdna3F16 [(basis12, 69)] 11 175 cancels.1 cancels.2 = some ⟨0, false⟩ ∧
    mcOzaki2CRBS cdna3F16 [(basis12, 69)] 11 175 cancels.1 cancels.2 = some ⟨0, false⟩ ∧
    mcOzaki2CRDS cdna3F16 [(basis12, 69)] 11 175 underflows.1 underflows.2 = some ⟨0, true⟩ ∧
    mcOzaki2CRBS cdna3F16 [(basis12, 69)] 11 175 underflows.1 underflows.2 = some ⟨0, true⟩ := by
  decide +kernel

end OzakiMCTests.BoundedSchemes
