import OzakiTC.ADPZeroPolicyShapes

/-! # The zero-policy failures on a padded matrix

The counterexample of `tests/OzakiTCTests/ZeroPolicyGeneral.lean` padded to a `2 × 4` matrix `A`
(a zero second row) and a `4 × 3` matrix `B` (two zero columns), on explicit binary64 words with
the default configuration. With zeros skipped, and with zeros at `−1022`, ADP emulates and returns
the zero matrix, so the entry `x · y`, nonzero, is `0` and Grade A fails, as
`adpPolicy_skip_wrong_shape` and `adpPolicy_field0_wrong_shape` say for every shape. The paper's
policy takes the native path and returns the right values. -/

open TensorCore Ozaki Ozaki.TC

namespace OzakiTCTests.ZeroPolicyShapes

/-- `A`: `x = (2^1000, 1, 0, 0)` and a zero row. -/
def A : List (List (BitVec 64)) := [[0x7E70000000000000, 0x3FF0000000000000, 0, 0], [0, 0, 0, 0]]
/-- `B` with columns `y = (0, 1, 0, 0)` and two zero columns. -/
def Bskip : List (List (BitVec 64)) := [[0, 0, 0], [0x3FF0000000000000, 0, 0], [0, 0, 0], [0, 0, 0]]
/-- `B` with columns `y = (0, 2^-1000, 0, 0)` and two zero columns. -/
def Bfield0 : List (List (BitVec 64)) :=
  [[0, 0, 0], [0x0170000000000000, 0, 0], [0, 0, 0], [0, 0, 0]]

example : decodeMatrix64 A = some (zpA 1000 4 1) ∧ decodeMatrix64 Bskip = some (zpB 0 4 2) ∧
    decodeMatrix64 Bfield0 = some (zpB (-1000) 4 2) := by decide +kernel

example : adpPolicy {} .skip A Bskip = (.emulated, some [[0, 0, 0], [0, 0, 0]]) ∧
    gradeA (zpA 1000 4 1) (zpB 0 4 2) [[0, 0, 0], [0, 0, 0]] = false := by decide +kernel

example : adpPolicy {} .field0 A Bfield0 = (.emulated, some [[0, 0, 0], [0, 0, 0]]) ∧
    gradeA (zpA 1000 4 1) (zpB (-1000) 4 2) [[0, 0, 0], [0, 0, 0]] = false := by decide +kernel

/-- The paper's policy: native path, the right values. -/
example : adp {} A Bskip = (.nativeSlow, some [[1, 0, 0], [0, 0, 0]]) := by decide +kernel

end OzakiTCTests.ZeroPolicyShapes
