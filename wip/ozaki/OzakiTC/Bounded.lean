import OzakiTC.LongDot
import Ozaki.BoundedOzaki
import Ozaki.BoundedInt
import Ozaki.BoundedChecked

/-! # Correctly rounded Ozaki-I with bounded registers on the Tensor Core model

`Ozaki.ozaki1CRB` is the correctly rounded Ozaki-I of `Ozaki.ozaki1CRW` with every step after the
matrix multiplier in integer registers whose width depends on the format, the slice width and the
number of slice products, never on the inputs' exponents: the rounding test on a truncated sum, the
exact fallback by a top-down summation over ranges with a sign oracle, and the final round to
nearest even by a few integer comparisons. Here its matrix multiplier is Tensor Core blocks with
split-K, so every slice product runs on the hardware model and the rest in bounded integer
arithmetic, for binary32 and FP64 inputs of any length.

`tcOzaki1CRID` and `tcOzaki1CRIL` go further: their inputs are the entries `(m, e)` a binary format
stores, and the slicing is integer too (`Ozaki.ozaki1CRI`), so every step off the Tensor Core is an
integer operation. `tcOzaki1CRIDS` and `tcOzaki1CRILS` give zero results IEEE's sign
(`Ozaki.ozaki1CRIS`).

`v100_fp64CRI_widths` and `v100_binary32CRI_widths` bound every integer of the whole computation
off the Tensor Core together: with every data integer guarded by `|v| < 2^332` and every exponent,
shift amount and counter by `|e| < 2^24` (binary32: `2^303`, `2^17`), the checked function
(`Ozaki.Checked.ozaki1CRIC`) never fails a guard and returns the correctly rounded result. -/

open TensorCore

namespace Ozaki.TC

/-- Correctly rounded binary32 Ozaki-I of any inner dimension: slice products on Tensor Core
blocks, the rounding test and the exact fallback in bounded integer registers. -/
def tcOzaki1CRBL (p : Model) (b W : ℕ) (ss : List ℕ) (smax : ℕ) (x y : List ℚ) : Option ℚ :=
  ozaki1CRB (tcSplitK p b) 24 (-126) 127 b W ss smax x y

/-- Correctly rounded FP64 by Ozaki-I: slice products on Tensor Core blocks, the rounding test and
the exact fallback in bounded integer registers. -/
def tcOzaki1CRBD (p : Model) (b W : ℕ) (ss : List ℕ) (smax : ℕ) (x y : List ℚ) : Option ℚ :=
  ozaki1CRB (tcSplitK p b) 53 (-1022) 1023 b W ss smax x y

theorem tcOzaki1CRBL_eq {p : Model} {b : ℕ} (hmult : (tcMultiplier p).ExactOn b (2 ^ 24))
    (hb : 2 * b ≤ 24) (W : ℕ) (ss : List ℕ) {smax : ℕ} (hsmax : 277 < smax * (b + 1))
    {x y : List ℚ} (hx : ∀ a ∈ x, Binary32Value a) (hy : ∀ a ∈ y, Binary32Value a)
    (hlen : x.length = y.length) :
    tcOzaki1CRBL p b W ss smax x y = rne32Q (dot x y) :=
  ozaki1CRB32_eq (tcSplitK_exactOn hmult hb _) W ss (by omega) hsmax hlen (Nat.le_refl _) hx hy

/-- **Correctly rounded FP64 GEMM on Tensor Cores with bounded registers**, for binary64 inputs of
any length. -/
theorem tcOzaki1CRBD_eq {p : Model} {b : ℕ} (hmult : (tcMultiplier p).ExactOn b (2 ^ 24))
    (hb : 2 * b ≤ 24) (W : ℕ) (ss : List ℕ) {smax : ℕ} (hsmax : 2098 < smax * (b + 1))
    {x y : List ℚ} (hx : ∀ a ∈ x, Binary64Value a) (hy : ∀ a ∈ y, Binary64Value a)
    (hlen : x.length = y.length) :
    tcOzaki1CRBD p b W ss smax x y = rne64 (dot x y) :=
  ozaki1CRB64_eq (tcSplitK_exactOn hmult hb _) W ss (by omega) hsmax hlen (Nat.le_refl _) hx hy

/-- FP64 on V100 fp16 with bounded registers: correctly rounded for every length. -/
theorem v100_fp64CRB (W : ℕ) (ss : List ℕ) {x y : List ℚ} (hx : ∀ a ∈ x, Binary64Value a)
    (hy : ∀ a ∈ y, Binary64Value a) (hlen : x.length = y.length) :
    tcOzaki1CRBD v100F16F32 11 W ss 175 x y = rne64 (dot x y) :=
  tcOzaki1CRBD_eq v100_exactOn (by decide) W ss (by decide) hx hy hlen

/-! ## Every step in integers, from the stored entries -/

/-- Correctly rounded FP64 by Ozaki-I from binary64 entries: slice products on Tensor Core blocks,
everything else in integer operations. -/
def tcOzaki1CRID (p : Model) (b W : ℕ) (ss : List ℕ) (smax : ℕ) (xs ys : List (ℤ × ℤ)) :
    Option ℚ :=
  ozaki1CRI (tcSplitK p b) 53 (-1022) 1023 b W ss smax xs ys

/-- Correctly rounded binary32 Ozaki-I from binary32 entries. -/
def tcOzaki1CRIL (p : Model) (b W : ℕ) (ss : List ℕ) (smax : ℕ) (xs ys : List (ℤ × ℤ)) :
    Option ℚ :=
  ozaki1CRI (tcSplitK p b) 24 (-126) 127 b W ss smax xs ys

/-- FP64 with signed zeros. -/
def tcOzaki1CRIDS (p : Model) (b W : ℕ) (ss : List ℕ) (smax : ℕ) (xs ys : List SEntry) :
    Option Signed :=
  ozaki1CRIS (tcSplitK p b) 53 (-1022) 1023 b W ss smax xs ys

/-- Binary32 with signed zeros. -/
def tcOzaki1CRILS (p : Model) (b W : ℕ) (ss : List ℕ) (smax : ℕ) (xs ys : List SEntry) :
    Option Signed :=
  ozaki1CRIS (tcSplitK p b) 24 (-126) 127 b W ss smax xs ys

/-- **Correctly rounded FP64 GEMM on Tensor Cores, every step off the Tensor Core in integers**,
for binary64 entries of any length. -/
theorem tcOzaki1CRID_eq {p : Model} {b : ℕ} (hmult : (tcMultiplier p).ExactOn b (2 ^ 24))
    (hb : 2 * b ≤ 24) (W : ℕ) (ss : List ℕ) {smax : ℕ} (hsmax : 2098 < smax * (b + 1))
    {xs ys : List (ℤ × ℤ)} (hx : ∀ a ∈ xs, Binary64Value (entryVal a))
    (hy : ∀ a ∈ ys, Binary64Value (entryVal a)) (hlen : xs.length = ys.length) :
    tcOzaki1CRID p b W ss smax xs ys = rne64 (dot (entryVals xs) (entryVals ys)) :=
  ozaki1CRI64_eq (tcSplitK_exactOn hmult hb _) W ss (by omega) hsmax hlen (Nat.le_refl _) hx hy

theorem tcOzaki1CRIL_eq {p : Model} {b : ℕ} (hmult : (tcMultiplier p).ExactOn b (2 ^ 24))
    (hb : 2 * b ≤ 24) (W : ℕ) (ss : List ℕ) {smax : ℕ} (hsmax : 277 < smax * (b + 1))
    {xs ys : List (ℤ × ℤ)} (hx : ∀ a ∈ xs, Binary32Value (entryVal a))
    (hy : ∀ a ∈ ys, Binary32Value (entryVal a)) (hlen : xs.length = ys.length) :
    tcOzaki1CRIL p b W ss smax xs ys = rne32Q (dot (entryVals xs) (entryVals ys)) :=
  ozaki1CRI32_eq (tcSplitK_exactOn hmult hb _) W ss (by omega) hsmax hlen (Nat.le_refl _) hx hy

/-- **The same with signed zeros**: the IEEE binary64 result, sign of a zero included. -/
theorem tcOzaki1CRIDS_eq {p : Model} {b : ℕ} (hmult : (tcMultiplier p).ExactOn b (2 ^ 24))
    (hb : 2 * b ≤ 24) (W : ℕ) (ss : List ℕ) {smax : ℕ} (hsmax : 2098 < smax * (b + 1))
    {xs ys : List SEntry} (hx : ∀ a ∈ xs, Binary64Value (entryVal a.1))
    (hy : ∀ a ∈ ys, Binary64Value (entryVal a.1)) (hlen : xs.length = ys.length) :
    tcOzaki1CRIDS p b W ss smax xs ys = crSigned rne64 (xs.map toSigned) (ys.map toSigned) :=
  ozaki1CRIS64_eq (tcSplitK_exactOn hmult hb _) W ss (by omega) hsmax hlen (Nat.le_refl _) hx hy

theorem tcOzaki1CRILS_eq {p : Model} {b : ℕ} (hmult : (tcMultiplier p).ExactOn b (2 ^ 24))
    (hb : 2 * b ≤ 24) (W : ℕ) (ss : List ℕ) {smax : ℕ} (hsmax : 277 < smax * (b + 1))
    {xs ys : List SEntry} (hx : ∀ a ∈ xs, Binary32Value (entryVal a.1))
    (hy : ∀ a ∈ ys, Binary32Value (entryVal a.1)) (hlen : xs.length = ys.length) :
    tcOzaki1CRILS p b W ss smax xs ys = crSigned rne32Q (xs.map toSigned) (ys.map toSigned) :=
  ozaki1CRIS32_eq (tcSplitK_exactOn hmult hb _) W ss (by omega) hsmax hlen (Nat.le_refl _) hx hy

/-- FP64 on V100 fp16 from binary64 entries, every step off the Tensor Core in integers. -/
theorem v100_fp64CRI (W : ℕ) (ss : List ℕ) {xs ys : List (ℤ × ℤ)}
    (hx : ∀ a ∈ xs, Binary64Value (entryVal a)) (hy : ∀ a ∈ ys, Binary64Value (entryVal a))
    (hlen : xs.length = ys.length) :
    tcOzaki1CRID v100F16F32 11 W ss 175 xs ys = rne64 (dot (entryVals xs) (entryVals ys)) :=
  tcOzaki1CRID_eq v100_exactOn (by decide) W ss (by decide) hx hy hlen

/-- **FP64 on V100 fp16, every integer bounded**: for binary64 entries with `k ≤ 2^20` and at most
`8` slices in each test, every data integer off the Tensor Core fits `332` bits and every exponent
and counter `24` bits, and the result is the binary64 round to nearest of `x · y`. -/
theorem v100_fp64CRI_widths {xs ys : List (ℤ × ℤ)} (hlen : xs.length = ys.length)
    (hk : xs.length ≤ 2 ^ 20) (hx : ∀ a ∈ xs, FormatEntry 53 (-1022) 1023 a)
    (hy : ∀ a ∈ ys, FormatEntry 53 (-1022) 1023 a) {ss : List ℕ} (hss : ∀ s ∈ ss, s ≤ 8) :
    Checked.ozaki1CRIC ⟨332, 24⟩ (tcSplitK v100F16F32 11) 53 (-1022) 1023 11 96 ss 175 xs ys =
      some (rne64 (dot (entryVals xs) (entryVals ys))) :=
  ozaki1CRIC_binary64_eq (tcSplitK_exactOn v100_exactOn (by decide) _) hlen hk hx hy hss

/-- **Binary32 on V100 fp16, every integer bounded**: `303` bits for data, `17` for exponents and
counters. -/
theorem v100_binary32CRI_widths {xs ys : List (ℤ × ℤ)} (hlen : xs.length = ys.length)
    (hk : xs.length ≤ 2 ^ 20) (hx : ∀ a ∈ xs, FormatEntry 24 (-126) 127 a)
    (hy : ∀ a ∈ ys, FormatEntry 24 (-126) 127 a) {ss : List ℕ} (hss : ∀ s ∈ ss, s ≤ 8) :
    Checked.ozaki1CRIC ⟨303, 17⟩ (tcSplitK v100F16F32 11) 24 (-126) 127 11 96 ss 24 xs ys =
      some (rne32Q (dot (entryVals xs) (entryVals ys))) :=
  ozaki1CRIC_binary32_eq (tcSplitK_exactOn v100_exactOn (by decide) _) hlen hk hx hy hss

end Ozaki.TC
