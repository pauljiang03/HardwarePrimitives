import OzakiMCTests.LongFP64
import OzakiMC.Bounded

/-! # Correctly rounded FP64 with bounded registers

`mcOzaki1CRBD` on CDNA 3 fp16 blocks with split-K returns the exact-fraction oracle's words on both
binary64 cases, with the check settling entries (five, then six slices, `96`-bit window) and with
every entry through the bounded exact path (`ss = []`). `mcOzaki1CRID`, from the stored entries
`(m, e)` with the slicing in integers too, does the same, and `mcOzaki1CRIDS` gives zero results
IEEE's sign. -/

open MatrixCore Ozaki Ozaki.MC OzakiMCTests.LongFP64

namespace OzakiMCTests.Bounded

/-- Correctly rounded FP64 with bounded registers equals the oracle on both cases. -/
def agreesB (P : Model) (ss : List ℕ) : Bool :=
  [(A_narrow64, B_narrow64, C_narrow64), (A_wide64, B_wide64, C_wide64)].all fun (A, B, C) =>
    let Aq := A.map (·.map val64)
    let Bq := transpose (B.map (·.map val64))
    (Aq.zip (C.map (·.map val64))).all fun (x, crow) =>
      (Bq.zip crow).all fun (y, c) => mcOzaki1CRBD P 11 96 ss 175 x y == some c

example : agreesB cdna3F16 [5, 6] = true := by decide +kernel

example : agreesB cdna3F16 [] = true := by decide +kernel

/-- A finite binary64 word as the entry `(m, e)` it stores. -/
def entry64 (w : ℕ) : ℤ × ℤ :=
  let e : ℕ := (w / 2 ^ 52) % 2 ^ 11
  let m : ℕ := w % 2 ^ 52
  let mag : ℤ × ℤ := if e = 0 then ((m : ℤ), -1074) else (((2 ^ 52 + m : ℕ) : ℤ), (e : ℤ) - 1075)
  if w / 2 ^ 63 = 1 then (-mag.1, mag.2) else mag

def cols {α : Type} [Inhabited α] (B : List (List α)) : List (List α) :=
  (List.range (B.headD []).length).map fun j => B.map fun r => r.getD j default

/-- Correctly rounded FP64 from the stored entries equals the oracle on both cases. -/
def agreesI (P : Model) (ss : List ℕ) : Bool :=
  [(A_narrow64, B_narrow64, C_narrow64), (A_wide64, B_wide64, C_wide64)].all fun (A, B, C) =>
    let Ae := A.map (·.map entry64)
    let Be := cols (B.map (·.map entry64))
    (Ae.zip (C.map (·.map val64))).all fun (x, crow) =>
      (Be.zip crow).all fun (y, c) => mcOzaki1CRID P 11 96 ss 175 x y == some c

example : agreesI cdna3F16 [5, 6] = true := by decide +kernel

example : agreesI cdna3F16 [] = true := by decide +kernel

example : mcOzaki1CRIDS cdna3F16 11 96 [5, 6] 175 [((0, 0), true), ((0, 0), false)]
      [((1, 0), false), ((0, 0), true)] = some ⟨0, true⟩ ∧
    mcOzaki1CRIDS cdna3F16 11 96 [5, 6] 175 [((1, 0), false), ((-1, 0), true)]
      [((1, 0), false), ((1, 0), false)] = some ⟨0, false⟩ ∧
    mcOzaki1CRIDS cdna3F16 11 96 [5, 6] 175 [((1, -540), false)] [((-1, -540), true)] =
      some ⟨0, true⟩ := by
  decide +kernel

end OzakiMCTests.Bounded
