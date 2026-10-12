import OzakiTC.ADPZeroPolicyIff

/-! # When an unsafe zero policy breaks Grade A, on explicit words

Both directions of `OzakiTC/ADPZeroPolicyIff.lean`, checked by kernel evaluation with the default
configuration (block size `2`, speed ratio `100`) and zeros skipped.

* **Necessary.** The pattern `x = (2^10, 1, 0, 0)`, `y = (0, 1, 0, 0)`: skipping zeros gives the
  matrix ESC `0`, so `W = 54`, and the product `1 · 1` has `xₜ = 1` losing `D = 10 + 53 − 54 = 9`
  bits. The pattern condition `36 · 2^-53 · 1 + 2^-1074 < 2^-44` holds, so
  `adpPolicy_unmasked_fails_left` applies to the original words; on its constructed words
  (`1 + 2^-44` in place of `1`) the run emulates, returns `1` for the exact `1 + 2^-44`, and
  breaks Grade A. The `−∞` policy meets Grade A on the same words.
* **Sufficient.** Adding a column `z = (2^-15, 2^-15, 1, 1)` raises the matrix ESC under skipping
  to `15`, at least the exact ESC `10` of the entry `x · y`: the failure is masked, and the run
  emulates and meets Grade A (`adpPolicy_entry_gradeA`). -/

open TensorCore Ozaki Ozaki.TC Ozaki.ADP

namespace OzakiTCTests.ZeroPolicyIff

def w1024 : BitVec 64 := 0x4090000000000000
def w1 : BitVec 64 := 0x3FF0000000000000
def w1p : BitVec 64 := 0x3FF0000000000100
def wm15 : BitVec 64 := 0x3F00000000000000

/-- The original words: `A = [x]`, `B` the column `y`. -/
def A : List (List (BitVec 64)) := [[w1024, w1, 0, 0]]
def B : List (List (BitVec 64)) := [[0], [w1], [0], [0]]

/-- The constructed words: `1` replaced by `lossyOf 0 9 = 1 + 2^-44`. -/
def A' : List (List (BitVec 64)) := [[w1024, w1p, 0, 0]]

def xq : List ℚ := [2 ^ (10 : ℤ), 1, 0, 0]
def yq : List ℚ := [0, 1, 0, 0]

/-- Grade A of an emulated run, as a test (`false` for any other outcome). -/
def emulatedGradeA (r : ADPPath × Option (List (List ℚ))) (Aq Bq : List (List ℚ)) : Bool :=
  match r with
  | (.emulated, some C) => gradeA Aq Bq C
  | _ => false

/-! ## Necessary -/

example : decodeMatrix64 A = some [xq] := by decide +kernel
example : decodeMatrix64 B = some (yq.map fun v => [v]) := by decide +kernel
example : matrixEscPolicy .skip 2 [xq] (transpose (yq.map fun v => [v])) = some 0 := by
  decide +kernel
example : adpWidth 0 = 54 := by decide
example : lossyOf 0 9 = 1 + 2 ^ (-44 : ℤ) := by decide +kernel
example : decodeMatrix64 A' = some ([xq].map (·.map (lossyMap 0 9))) := by decide +kernel
example : decodeMatrix64 B = some ((yq.map fun v => [v]).map (·.map pow2Of)) := by decide +kernel
/-- The pattern condition with `k = 4`, `P = 2^0`. -/
example : (8 * ((4 : ℕ) : ℚ) + 4) * 2 ^ (-53 : ℤ) * patSum (expsOf xq) (expsOf yq) +
    2 ^ (-1074 : ℤ) < 2 ^ ((0 : ℤ) + 0 - 53 + min 9 53) := by decide +kernel

/-- The run on the constructed words emulates and returns `1` … -/
example : adpPolicy {} .skip A' B = (.emulated, some [[1]]) := by decide +kernel
/-- … where the exact product is `1 + 2^-44`: Grade A fails. -/
example : gradeAEntry (xq.map (lossyMap 0 9)) (yq.map pow2Of) 1 = false := by decide +kernel
/-- The paper's policy meets Grade A on the same words. -/
example : emulatedGradeA (adp {} A' B) [xq.map (lossyMap 0 9)] ((yq.map pow2Of).map fun v => [v]) =
    true := by decide +kernel

/-- **The theorem itself, on the original words.** -/
example : ∃ (A'' B'' : List (List (BitVec 64))) (C' : List (List ℚ)) (row : List ℚ) (c : ℚ),
    decodeMatrix64 A'' = some ([xq].map (·.map (lossyMap 0 9))) ∧
    decodeMatrix64 B'' = some ((yq.map fun v => [v]).map (·.map pow2Of)) ∧
    matrixEscPolicy .skip ({} : ADPConfig).block ([xq].map (·.map (lossyMap 0 9)))
      (transpose ((yq.map fun v => [v]).map (·.map pow2Of))) = some 0 ∧
    adpPolicy {} .skip A'' B'' = (.emulated, some C') ∧ C'[0]? = some row ∧ row[0]? = some c ∧
    gradeAEntry (xq.map (lossyMap 0 9)) (yq.map pow2Of) c = false :=
  adpPolicy_unmasked_fails_left (cfg := {}) (pol := .skip) (A := A) (B := B)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (i := 0) (j := 0) (t := 1) (x := xq) (y := yq) (by decide +kernel) (by decide +kernel)
    (a := 1) (b := 1) (by decide +kernel) (by decide +kernel) (by decide) (by decide)
    (ep := 10) (e := 0) (D := 9) (by decide +kernel) (by decide +kernel) (by decide) (by decide)
    (by decide +kernel)

/-! ## Sufficient: masked by another column -/

/-- `B` with a second column `z = (2^-15, 2^-15, 1, 1)`. -/
def Bm : List (List (BitVec 64)) := [[0, wm15], [w1, wm15], [0, w1], [0, w1]]

def zq : List ℚ := [2 ^ (-15 : ℤ), 2 ^ (-15 : ℤ), 1, 1]

example : decodeMatrix64 Bm = some (List.zipWith (fun a b => [a, b]) yq zq) := by decide +kernel
example : matrixEscPolicy .skip 2 [xq] (transpose (List.zipWith (fun a b => [a, b]) yq zq)) =
    some 15 := by decide +kernel
example : escExact xq yq = 10 := by decide +kernel
/-- The skipped-zeros run, masked, meets Grade A on every entry, the original words included. -/
example : emulatedGradeA (adpPolicy {} .skip A' Bm) [xq.map (lossyMap 0 9)]
    (List.zipWith (fun a b => [a, b]) yq zq) = true := by decide +kernel
example : emulatedGradeA (adpPolicy {} .skip A Bm) [xq]
    (List.zipWith (fun a b => [a, b]) yq zq) = true := by decide +kernel

end OzakiTCTests.ZeroPolicyIff
