import OzakiMC.LongDot
import Ozaki.BoundedOzaki
import Ozaki.BoundedInt
import Ozaki.BoundedChecked

/-! # Correctly rounded Ozaki-I with bounded registers on the matrix-core model

`Ozaki.ozaki1CRB` on matrix-core blocks with split-K: every slice product on the hardware model,
the check, the exact path and the final rounding in integer registers whose width does not depend
on the inputs' exponents, for binary32 and FP64 inputs of any length. `mcOzaki1CRID`,
`mcOzaki1CRIL` take the stored entries `(m, e)` and slice in integers too (`Ozaki.ozaki1CRI`);
`mcOzaki1CRIDS`, `mcOzaki1CRILS` add IEEE's signed zeros. `cdna3F16_fp64CRI_widths` and
`cdna3F16_binary32CRI_widths` bound every integer off the matrix core at once
(`Ozaki.Checked.ozaki1CRIC`). -/

open MatrixCore

namespace Ozaki.MC

def mcOzaki1CRBL (P : Model) (b W : ℕ) (ss : List ℕ) (smax : ℕ) (x y : List ℚ) : Option ℚ :=
  ozaki1CRB (mcSplitK P b) 24 (-126) 127 b W ss smax x y

def mcOzaki1CRBD (P : Model) (b W : ℕ) (ss : List ℕ) (smax : ℕ) (x y : List ℚ) : Option ℚ :=
  ozaki1CRB (mcSplitK P b) 53 (-1022) 1023 b W ss smax x y

theorem mcOzaki1CRBL_eq {P : Model} {b : ℕ} (hP : ExactMultiplier P b) (hb : 2 * b ≤ 24) (W : ℕ)
    (ss : List ℕ) {smax : ℕ} (hsmax : 277 < smax * (b + 1)) {x y : List ℚ}
    (hx : ∀ a ∈ x, Binary32Value a) (hy : ∀ a ∈ y, Binary32Value a) (hlen : x.length = y.length) :
    mcOzaki1CRBL P b W ss smax x y = rne32Q (dot x y) :=
  ozaki1CRB32_eq (mcSplitK_exactOn hP hb _) W ss (by omega) hsmax hlen (Nat.le_refl _) hx hy

/-- **Correctly rounded FP64 GEMM on AMD matrix cores with bounded registers.** -/
theorem mcOzaki1CRBD_eq {P : Model} {b : ℕ} (hP : ExactMultiplier P b) (hb : 2 * b ≤ 24) (W : ℕ)
    (ss : List ℕ) {smax : ℕ} (hsmax : 2098 < smax * (b + 1)) {x y : List ℚ}
    (hx : ∀ a ∈ x, Binary64Value a) (hy : ∀ a ∈ y, Binary64Value a) (hlen : x.length = y.length) :
    mcOzaki1CRBD P b W ss smax x y = rne64 (dot x y) :=
  ozaki1CRB64_eq (mcSplitK_exactOn hP hb _) W ss (by omega) hsmax hlen (Nat.le_refl _) hx hy

/-! ## Every step in integers, from the stored entries -/

def mcOzaki1CRID (P : Model) (b W : ℕ) (ss : List ℕ) (smax : ℕ) (xs ys : List (ℤ × ℤ)) :
    Option ℚ :=
  ozaki1CRI (mcSplitK P b) 53 (-1022) 1023 b W ss smax xs ys

def mcOzaki1CRIL (P : Model) (b W : ℕ) (ss : List ℕ) (smax : ℕ) (xs ys : List (ℤ × ℤ)) :
    Option ℚ :=
  ozaki1CRI (mcSplitK P b) 24 (-126) 127 b W ss smax xs ys

def mcOzaki1CRIDS (P : Model) (b W : ℕ) (ss : List ℕ) (smax : ℕ) (xs ys : List SEntry) :
    Option Signed :=
  ozaki1CRIS (mcSplitK P b) 53 (-1022) 1023 b W ss smax xs ys

def mcOzaki1CRILS (P : Model) (b W : ℕ) (ss : List ℕ) (smax : ℕ) (xs ys : List SEntry) :
    Option Signed :=
  ozaki1CRIS (mcSplitK P b) 24 (-126) 127 b W ss smax xs ys

/-- **Correctly rounded FP64 GEMM on AMD matrix cores, every step off the matrix core in
integers.** -/
theorem mcOzaki1CRID_eq {P : Model} {b : ℕ} (hP : ExactMultiplier P b) (hb : 2 * b ≤ 24) (W : ℕ)
    (ss : List ℕ) {smax : ℕ} (hsmax : 2098 < smax * (b + 1)) {xs ys : List (ℤ × ℤ)}
    (hx : ∀ a ∈ xs, Binary64Value (entryVal a)) (hy : ∀ a ∈ ys, Binary64Value (entryVal a))
    (hlen : xs.length = ys.length) :
    mcOzaki1CRID P b W ss smax xs ys = rne64 (dot (entryVals xs) (entryVals ys)) :=
  ozaki1CRI64_eq (mcSplitK_exactOn hP hb _) W ss (by omega) hsmax hlen (Nat.le_refl _) hx hy

theorem mcOzaki1CRIL_eq {P : Model} {b : ℕ} (hP : ExactMultiplier P b) (hb : 2 * b ≤ 24) (W : ℕ)
    (ss : List ℕ) {smax : ℕ} (hsmax : 277 < smax * (b + 1)) {xs ys : List (ℤ × ℤ)}
    (hx : ∀ a ∈ xs, Binary32Value (entryVal a)) (hy : ∀ a ∈ ys, Binary32Value (entryVal a))
    (hlen : xs.length = ys.length) :
    mcOzaki1CRIL P b W ss smax xs ys = rne32Q (dot (entryVals xs) (entryVals ys)) :=
  ozaki1CRI32_eq (mcSplitK_exactOn hP hb _) W ss (by omega) hsmax hlen (Nat.le_refl _) hx hy

theorem mcOzaki1CRIDS_eq {P : Model} {b : ℕ} (hP : ExactMultiplier P b) (hb : 2 * b ≤ 24) (W : ℕ)
    (ss : List ℕ) {smax : ℕ} (hsmax : 2098 < smax * (b + 1)) {xs ys : List SEntry}
    (hx : ∀ a ∈ xs, Binary64Value (entryVal a.1)) (hy : ∀ a ∈ ys, Binary64Value (entryVal a.1))
    (hlen : xs.length = ys.length) :
    mcOzaki1CRIDS P b W ss smax xs ys = crSigned rne64 (xs.map toSigned) (ys.map toSigned) :=
  ozaki1CRIS64_eq (mcSplitK_exactOn hP hb _) W ss (by omega) hsmax hlen (Nat.le_refl _) hx hy

theorem mcOzaki1CRILS_eq {P : Model} {b : ℕ} (hP : ExactMultiplier P b) (hb : 2 * b ≤ 24) (W : ℕ)
    (ss : List ℕ) {smax : ℕ} (hsmax : 277 < smax * (b + 1)) {xs ys : List SEntry}
    (hx : ∀ a ∈ xs, Binary32Value (entryVal a.1)) (hy : ∀ a ∈ ys, Binary32Value (entryVal a.1))
    (hlen : xs.length = ys.length) :
    mcOzaki1CRILS P b W ss smax xs ys = crSigned rne32Q (xs.map toSigned) (ys.map toSigned) :=
  ozaki1CRIS32_eq (mcSplitK_exactOn hP hb _) W ss (by omega) hsmax hlen (Nat.le_refl _) hx hy

/-- **FP64 on CDNA 3 fp16, every integer bounded**: `332` bits for data, `24` for exponents and
counters, and the result is the binary64 round to nearest of `x · y`. -/
theorem cdna3F16_fp64CRI_widths {xs ys : List (ℤ × ℤ)} (hlen : xs.length = ys.length)
    (hk : xs.length ≤ 2 ^ 20) (hx : ∀ a ∈ xs, FormatEntry 53 (-1022) 1023 a)
    (hy : ∀ a ∈ ys, FormatEntry 53 (-1022) 1023 a) {ss : List ℕ} (hss : ∀ s ∈ ss, s ≤ 8) :
    Checked.ozaki1CRIC ⟨332, 24⟩ (mcSplitK cdna3F16 11) 53 (-1022) 1023 11 96 ss 175 xs ys =
      some (rne64 (dot (entryVals xs) (entryVals ys))) :=
  ozaki1CRIC_binary64_eq (mcSplitK_exactOn (cdna3F16_exactMultiplier (by decide)) (by decide) _)
    hlen hk hx hy hss

theorem cdna3F16_binary32CRI_widths {xs ys : List (ℤ × ℤ)} (hlen : xs.length = ys.length)
    (hk : xs.length ≤ 2 ^ 20) (hx : ∀ a ∈ xs, FormatEntry 24 (-126) 127 a)
    (hy : ∀ a ∈ ys, FormatEntry 24 (-126) 127 a) {ss : List ℕ} (hss : ∀ s ∈ ss, s ≤ 8) :
    Checked.ozaki1CRIC ⟨303, 17⟩ (mcSplitK cdna3F16 11) 24 (-126) 127 11 96 ss 24 xs ys =
      some (rne32Q (dot (entryVals xs) (entryVals ys))) :=
  ozaki1CRIC_binary32_eq (mcSplitK_exactOn (cdna3F16_exactMultiplier (by decide)) (by decide) _)
    hlen hk hx hy hss

end Ozaki.MC
