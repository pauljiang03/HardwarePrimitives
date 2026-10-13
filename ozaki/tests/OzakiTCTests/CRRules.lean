import OzakiTC.Ozaki2ChoiceCR

/-! # The design rules and the margin, by kernel evaluation

* **The shortcut.** Small integers leave nothing over after one slice, so the exact fallback costs
  `1` product on the matrix multiplier against `15` for a five-slice test: the adaptive scheme goes
  straight to it, costs `1`, and returns the exact sum. Values with full 53-bit significands need
  five slices (`25` products), more than the first test's `15`, so the adaptive scheme keeps the
  test; the test succeeds, at a cost of `15`.
* **Slice counts from `k`.** At `k = 4` the first test has `5` slices; the scheme with both rules
  returns the correctly rounded product.
* **Ozaki-II with the margin** on H100 fp16, `13` moduli and `P = 65`, returns the correctly
  rounded product of a pair of binary64 vectors. -/

open TensorCore Ozaki Ozaki.TC

namespace OzakiTCTests.CRRules

def xs : List ℚ := [1, 2, 3, 4]
def ys : List ℚ := [5, 6, 7, 8]

/-- The binary64 value nearest `1/3`, and one nearest `2/7`. -/
def third : ℚ := 6004799503160661 * 2 ^ (-54 : ℤ)
def twoSevenths : ℚ := 5146971002709138 * 2 ^ (-54 : ℤ)

def xw : List ℚ := [third, -twoSevenths, third, 1]
def yw : List ℚ := [twoSevenths, twoSevenths, 1, third]

example : exactCount 11 175 xs ys = some 1 ∧ adaptList (exactCount 11 175 xs ys) [5, 6] = [] ∧
    tcOzaki1CRDA v100F16F32 11 [5, 6] 175 xs ys = some 70 ∧
    craCost (tcSplitK v100F16F32 11) rne64 11 [5, 6] 175 xs ys = 1 ∧
    creCost (tcSplitK v100F16F32 11) rne64 11 [5, 6] 175 xs ys = 15 := by
  decide +kernel

example : exactCount 11 175 xw yw = some 5 ∧ adaptList (exactCount 11 175 xw yw) [5, 6] = [5, 6] ∧
    craCost (tcSplitK v100F16F32 11) rne64 11 [5, 6] 175 xw yw = 15 ∧
    tcOzaki1CRDA v100F16F32 11 [5, 6] 175 xw yw = rne64 (dot xw yw) := by
  decide +kernel

example : crSlices 11 53 4 1 = [5, 6] ∧
    tcOzaki1CRDKA v100F16F32 11 53 1 175 xw yw = rne64 (dot xw yw) := by
  decide +kernel

example : tcOzaki2CRD hopperF16F32 [(moduliBasis 10 13, 65)] 10 191 xw yw = rne64 (dot xw yw) := by
  decide +kernel

end OzakiTCTests.CRRules
