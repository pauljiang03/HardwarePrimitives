import OzakiTC.ADPZeroPolicyGeneral
import Ozaki.SharpBounds2
import Ozaki.Parameters

/-! # The general zero-policy failures and the new bounds, on concrete inputs

* **ADP's unsafe zero policies.** Members of the families of `OzakiTC/ADPZeroPolicyGeneral.lean`
  on explicit binary64 words, with the default configuration (blocks of `2`, speed ratio `100`):
  `x = (2^1000, 1, 0, 0)` against `y = (0, 1, 0, 0)` with zeros skipped, and against
  `y = (0, 2^-1000, 0, 0)` with zeros at `−1022`. Both emulate and return `0` for a nonzero
  product, as the theorems say; with blocks of `1` skipping zeros is the exact estimate and the
  routine takes the native path and returns the right value; with zeros as `−∞` (`adp`) the
  routine takes the native path on both.
* **Different slice counts.** The uniform bound of `exactTermsRect_error_uniform` holds, by
  exact evaluation, for `3` slices of `x`, `2` of `y` and the pairs `t + u < 4`.
* **Any order.** A binary32 sum and a dot product evaluated along a balanced tree stay within
  Jeannerod and Rump's `(n − 1) u Σ|tᵢ|` and `k u Σ|xᵢyᵢ|`.
* **Inexact CRT.** With the Z3 models' four moduli (`P = 22`), Ozaki-II with the CRT sum
  accumulated in binary64 returns the same binary32 result as the exact reconstruction, and the
  margin `2 k 2^(2P) + 2ε < M` of `ozaki2FP64_error` holds for `k = 4`. -/

open TensorCore Ozaki Ozaki.TC

namespace OzakiTCTests.ZeroPolicyGeneral

/-- `x = (2^1000, 1, 0, 0)`. -/
def A : List (List (BitVec 64)) := [[0x7E70000000000000, 0x3FF0000000000000, 0, 0]]
/-- `y = (0, 1, 0, 0)` as a column. -/
def Bskip : List (List (BitVec 64)) := [[0], [0x3FF0000000000000], [0], [0]]
/-- `y = (0, 2^-1000, 0, 0)` as a column. -/
def Bfield0 : List (List (BitVec 64)) := [[0], [0x0170000000000000], [0], [0]]

example : decodeMatrix64 A = some [zpX 1000 4] ∧
    decodeMatrix64 Bskip = some ((zpY 0 4).map fun v => [v]) ∧
    decodeMatrix64 Bfield0 = some ((zpY (-1000) 4).map fun v => [v]) := by decide +kernel

/-- Skipping zeros: emulated, `0` for the product `1`. -/
example : adpPolicy {} .skip A Bskip = (.emulated, some [[0]]) := by decide +kernel

/-- Zeros at `−1022`: emulated, `0` for the product `2^-1000`. -/
example : adpPolicy {} .field0 A Bfield0 = (.emulated, some [[0]]) := by decide +kernel

/-- With blocks of `1`, skipping zeros is the exact estimate: native path, the right value. -/
example : adpPolicy { block := 1 } .skip A Bskip = (.nativeSlow, some [[1]]) := by decide +kernel

/-- The paper's policy takes the native path on both and returns the right values. -/
example : adp {} A Bskip = (.nativeSlow, some [[1]]) ∧
    adp {} A Bfield0 = (.nativeSlow, some [[2 ^ (-1000 : ℤ)]]) := by decide +kernel

/-- Different slice counts: `3` slices of `x`, `2` of `y`, pairs `t + u < 4`, within the uniform
bound `(sx + 1) k 2^(E + F − c(b+1))`, `c = 2`. -/
def x4 : List ℚ := [1/3, -2/7, 5/11, 1/13]
def y4 : List ℚ := [3/5, 1/9, -4/7, 2/3]

example : Rat.abs (dot x4 y4 - (exactTermsRect 11 3 2 4 x4 y4).sum) ≤
    ((3 + 1 : ℕ) : ℚ) * x4.length *
      2 ^ (splitExp 11 x4 + splitExp 11 y4 - (min (min 3 2) 4 : ℕ) * (11 + 1)) := by
  decide +kernel

/-- A balanced binary32 sum with cancellation: `((1 + 2^-24) + (2^-24 − 1))`. -/
def ts : List ℚ := [1, 2 ^ (-24 : ℤ), 2 ^ (-24 : ℤ), -1]
def T : SumTree := .node (.node (.leaf 1) (.leaf (2 ^ (-24 : ℤ))))
  (.node (.leaf (2 ^ (-24 : ℤ))) (.leaf (-1)))

example : (T.evalWith some rne32Q).any (fun v =>
    decide (Rat.abs (v - ts.sum) ≤ ((ts.length : ℚ) - 1) * 2 ^ (-24 : ℤ) * (ts.map Rat.abs).sum)) =
      true := by
  decide +kernel

/-- A dot product along a balanced tree of rounded products. -/
def xs : List ℚ := [3, 1/3, -5, 1/7]
def ys : List ℚ := [1/3, 3, 1/5, 7]
def D : SumTree := .node (.node (.leaf 1) (.leaf 1)) (.node (.leaf (-1)) (.leaf 1))

example : D.leaves = List.zipWith (· * ·) xs ys := by decide +kernel

example : (D.evalWith rne32Q rne32Q).any (fun v =>
    decide (Rat.abs (v - dot xs ys) ≤
      4 * 2 ^ (-24 : ℤ) * ((List.zipWith (· * ·) xs ys).map Rat.abs).sum)) = true := by
  decide +kernel

example : ozaki2Approx exactMultiplier rne32Q crtAccFP64 z3Basis 22 x4 y4 =
    ozaki2 exactMultiplier rne32Q z3Basis 22 x4 y4 := by decide +kernel

example : 2 * ((4 * (2 ^ 22 * 2 ^ 22) : ℕ) : ℚ) +
    2 * (z3Basis.weights.length * 2 ^ (-53 : ℤ) *
      (2 ^ (11 + 1 : ℤ) * (z3Basis.weights.map fun w : ℤ => Rat.abs (w : ℚ)).sum)) <
      z3Basis.modulus := by decide +kernel

end OzakiTCTests.ZeroPolicyGeneral
