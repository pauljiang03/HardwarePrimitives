import OzakiTC.ADPZeroPolicy

/-! # ADP with the Z3 model's zero policies, on its own inputs and two constructed ones

[`scripts/z3_adp_zero_policies.py`](../../scripts/z3_adp_zero_policies.py) records the Z3 model's
`zeros_case` and `field0_case` and two constructed inputs, with the model's run with zeros as `−∞`;
the model stops every run with an unsafe policy at its assertion `[X.4]` (except `field0` on
`zeros_case`, where the field-0 estimate happens to be safe). Here the Lean routine runs with each
policy:

| input | `−∞` | zeros skipped | zeros at `−1022` |
| --- | --- | --- | --- |
| `zeros_case` | emulated, the model's `C`, Grade A | ESC `3` instead of `10`, same `C` | Grade A |
| `field0_case` | native, the model's `C` | ESC `0`: `0` for the nonzero entry, Grade A fails | native (speed heuristic) |
| `skip_breaks` | emulated, the model's `C`, Grade A | ESC `0`: off by about `2^-42`, Grade A fails | Grade A |
| `field0_breaks` | native, the model's `C` | ESC `0`: `0` for a nonzero product | ESC `22`: `0` for a nonzero product |

So the unsafe policies return wrong results whenever nothing stops them, already on one of the
model's own inputs; the `−∞` policy returns the model's values on all four. -/

open TensorCore Ozaki Ozaki.TC Ozaki.ADP

namespace OzakiTCTests.ADPZeroPolicy

/-- `zeros_case`: `A`. -/
def A_zerosCase : List (List (BitVec 64)) :=
  [[0x4098000000000000, 0x3FF4000000000000, 0x0000000000000000, 0x0000000000000000],
    [0x3FD0179A594B2B8C, 0xBFEBCE600B27BB70, 0xBFEF284170BABD6C, 0x3FE59917EBC0FCE2],
    [0xBFDECD7CD72FFC74, 0xBFE100B8B6774EE0, 0x3FEFB8A51DBCB81C, 0xBFAE733E3AC15E40],
    [0x3FE588959C65A506, 0xBFA836DD4D2AB1C0, 0x3FD1CCFC1DC6BF1C, 0xBFE65C4CEE250614]]

/-- `zeros_case`: `B`. -/
def B_zerosCase : List (List (BitVec 64)) :=
  [[0x0000000000000000, 0x3FD3333333333333, 0x3FC999999999999A, 0x3FB999999999999A],
    [0x3FFC000000000000, 0x3FD999999999999A, 0x3FE0000000000000, 0x3FE3333333333333],
    [0x0000000000000000, 0x3FE6666666666666, 0x3FE999999999999A, 0x3FECCCCCCCCCCCCD],
    [0x0000000000000000, 0x3FB999999999999A, 0x3FC999999999999A, 0x3FD3333333333333]]

/-- `zeros_case`: the Z3 model's `C` with zeros as `−∞` (path `emulated`). -/
def C_zerosCase : List (List (BitVec 64)) :=
  [[0x4001800000000000, 0x407CD4CCCCCCCCCD, 0x40733D3333333334, 0x40634B3333333333],
    [0xBFF8549409C2C402, 0xBFEC5BE114CDA2F3, 0xBFF07334E0A3F8C3, 0xBFF2B87936E1200D],
    [0xBFEDC1433F50CA08, 0x3FD52FA38FF7F289, 0x3FDAD454F301CFA8, 0x3FE03C832B05D662],
    [0xBFB53001A3855B88, 0x3FD3B2A2FF31C516, 0x3FC8CAF1DE32C11D, 0x3FB4613B7C03F01B]]

/-- `field0_case`: `A`. -/
def A_field0Case : List (List (BitVec 64)) :=
  [[0x7E78000000000000, 0x0174000000000000, 0x0000000000000000, 0x0000000000000000],
    [0x0000000000000000, 0x0000000000000000, 0x0000000000000000, 0x0000000000000000],
    [0x0000000000000000, 0x0000000000000000, 0x0000000000000000, 0x0000000000000000],
    [0x0000000000000000, 0x0000000000000000, 0x0000000000000000, 0x0000000000000000]]

/-- `field0_case`: `B`. -/
def B_field0Case : List (List (BitVec 64)) :=
  [[0x0000000000000000, 0x0000000000000000, 0x0000000000000000, 0x0000000000000000],
    [0x3EBC000000000000, 0x0000000000000000, 0x0000000000000000, 0x0000000000000000],
    [0x0000000000000000, 0x0000000000000000, 0x0000000000000000, 0x0000000000000000],
    [0x0000000000000000, 0x0000000000000000, 0x0000000000000000, 0x0000000000000000]]

/-- `field0_case`: the Z3 model's `C` with zeros as `−∞` (path `native-slow`). -/
def C_field0Case : List (List (BitVec 64)) :=
  [[0x0041800000000000, 0x0000000000000000, 0x0000000000000000, 0x0000000000000000],
    [0x0000000000000000, 0x0000000000000000, 0x0000000000000000, 0x0000000000000000],
    [0x0000000000000000, 0x0000000000000000, 0x0000000000000000, 0x0000000000000000],
    [0x0000000000000000, 0x0000000000000000, 0x0000000000000000, 0x0000000000000000]]

/-- `skip_breaks`: `A`. -/
def A_skipBreaks : List (List (BitVec 64)) :=
  [[0x4090000000000000, 0x3FFFFFFFFFFFFFFF, 0x0000000000000000, 0x0000000000000000]]

/-- `skip_breaks`: `B`. -/
def B_skipBreaks : List (List (BitVec 64)) :=
  [[0x0000000000000000],
    [0x3FFC000000000000],
    [0x0000000000000000],
    [0x0000000000000000]]

/-- `skip_breaks`: the Z3 model's `C` with zeros as `−∞` (path `emulated`). -/
def C_skipBreaks : List (List (BitVec 64)) :=
  [[0x400BFFFFFFFFFFFF]]

/-- `field0_breaks`: `A`. -/
def A_field0Breaks : List (List (BitVec 64)) :=
  [[0x7E78000000000000, 0x3EB4000000000000, 0x0000000000000000, 0x0000000000000000]]

/-- `field0_breaks`: `B`. -/
def B_field0Breaks : List (List (BitVec 64)) :=
  [[0x0000000000000000],
    [0x017C000000000000],
    [0x0000000000000000],
    [0x0000000000000000]]

/-- `field0_breaks`: the Z3 model's `C` with zeros as `−∞` (path `native-slow`). -/
def C_field0Breaks : List (List (BitVec 64)) :=
  [[0x0041800000000000]]

/-- Grade A of the routine's result under a policy, checked exactly. -/
def gradeAOf (pol : ZeroPolicy) (A B : List (List (BitVec 64))) : Bool :=
  match decodeMatrix64 A, decodeMatrix64 B, (adpPolicy {} pol A B).2 with
  | some Aq, some Bq, some C => gradeA Aq Bq C
  | _, _, _ => false

/-- The matrix ESC under a policy. -/
def escOf (pol : ZeroPolicy) (A B : List (List (BitVec 64))) : Option ℤ := do
  let Aq ← decodeMatrix64 A
  let Bq ← decodeMatrix64 B
  matrixEscPolicy pol 2 Aq (transpose Bq)

/-! ## `zeros_case`: no wrong result -/

example : adpPolicy {} .negInf A_zerosCase B_zerosCase = (.emulated, decodeMatrix64 C_zerosCase) := by
  decide +kernel
example : escOf .skip A_zerosCase B_zerosCase = some 3 ∧ escOf .negInf A_zerosCase B_zerosCase = some 10 ∧
    adpPolicy {} .skip A_zerosCase B_zerosCase = (.emulated, decodeMatrix64 C_zerosCase) := by
  decide +kernel
example : gradeAOf .negInf A_zerosCase B_zerosCase = true ∧ gradeAOf .skip A_zerosCase B_zerosCase = true ∧
    gradeAOf .field0 A_zerosCase B_zerosCase = true := by
  decide +kernel

/-! ## `field0_case`: skipping zeros returns `0` for the nonzero entry -/

example : adpPolicy {} .negInf A_field0Case B_field0Case = (.nativeSlow, decodeMatrix64 C_field0Case) := by
  decide +kernel
example : escOf .skip A_field0Case B_field0Case = some 0 ∧
    (adpPolicy {} .skip A_field0Case B_field0Case).1 = .emulated ∧
    gradeAOf .skip A_field0Case B_field0Case = false := by
  decide +kernel
example : (adpPolicy {} .field0 A_field0Case B_field0Case).1 = .nativeSlow ∧
    gradeAOf .field0 A_field0Case B_field0Case = true := by
  decide +kernel

/-! ## A large entry beside a zero: skipping zeros breaks Grade A -/

example : adpPolicy {} .negInf A_skipBreaks B_skipBreaks = (.emulated, decodeMatrix64 C_skipBreaks) ∧
    gradeAOf .negInf A_skipBreaks B_skipBreaks = true := by
  decide +kernel
example : escOf .skip A_skipBreaks B_skipBreaks = some 0 ∧
    adpPolicy {} .skip A_skipBreaks B_skipBreaks =
      (.emulated, some [[123145302310905 / 35184372088832]]) ∧
    gradeAOf .skip A_skipBreaks B_skipBreaks = false := by
  decide +kernel
example : gradeAOf .field0 A_skipBreaks B_skipBreaks = true := by decide +kernel

/-! ## A zero paired with `2^1000`: both unsafe policies return `0` for a nonzero product -/

example : adpPolicy {} .negInf A_field0Breaks B_field0Breaks =
    (.nativeSlow, decodeMatrix64 C_field0Breaks) := by
  decide +kernel
example : escOf .field0 A_field0Breaks B_field0Breaks = some 22 ∧
    adpPolicy {} .field0 A_field0Breaks B_field0Breaks = (.emulated, some [[0]]) ∧
    adpPolicy {} .skip A_field0Breaks B_field0Breaks = (.emulated, some [[0]]) ∧
    gradeAOf .field0 A_field0Breaks B_field0Breaks = false := by
  decide +kernel

end OzakiTCTests.ADPZeroPolicy
