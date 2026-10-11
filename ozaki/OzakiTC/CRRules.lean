import OzakiTC.LongDot
import Ozaki.Adaptive

/-! # The two design rules on the Tensor Core model

`Ozaki.Adaptive`'s rules on Tensor Core blocks with split-K: slice counts that grow with the inner
dimension (`crSlices`, starting at `slicesForCR b t k`) and the shortcut straight to the exact path
when it costs no more than the first check (`adaptList`). Every variant is correctly rounded for
every length, as `tcOzaki1CRD` is: the rules change only which checks run.

`slicesForCR_table` gives the first slice count for `11`-bit slices: `5` at `k = 4`, `6` from
`k = 256` to `4096`, `7` at `k = 2^20` for FP64 (`t = 53`); `4` for binary32 at `k = 1024`. The
plain rule takes `5` and `3` whatever `k`. -/

open TensorCore

namespace Ozaki.TC

/-- The first slice count of the rule for correct rounding, for `11`-, `10`- and `8`-bit slices. -/
theorem slicesForCR_table :
    slicesForCR 11 53 4 = 5 ∧ slicesForCR 11 53 256 = 6 ∧ slicesForCR 11 53 1024 = 6 ∧
    slicesForCR 11 53 4096 = 6 ∧ slicesForCR 11 53 (2 ^ 20) = 7 ∧
    slicesForCR 11 24 1024 = 4 ∧ slicesForCR 10 53 1024 = 7 ∧ slicesForCR 8 53 1024 = 8 ∧
    slicesFor 11 53 = 5 ∧ slicesFor 11 24 = 3 := by
  decide +kernel

/-- Correctly rounded FP64 by Ozaki-I with slice counts from the inner dimension. -/
def tcOzaki1CRDK (p : Profile) (b t r smax : ℕ) (x y : List ℚ) : Option ℚ :=
  ozaki1CRK (tcSplitK p b) rne64 b t r smax x y

/-- With the shortcut, for a given list of slice counts. -/
def tcOzaki1CRDA (p : Profile) (b : ℕ) (ss : List ℕ) (smax : ℕ) (x y : List ℚ) : Option ℚ :=
  ozaki1CRA (tcSplitK p b) rne64 b ss smax x y

/-- With both rules. -/
def tcOzaki1CRDKA (p : Profile) (b t r smax : ℕ) (x y : List ℚ) : Option ℚ :=
  ozaki1CRKA (tcSplitK p b) rne64 b t r smax x y

/-- Both rules for binary32. -/
def tcOzaki1CRLKA (p : Profile) (b t r smax : ℕ) (x y : List ℚ) : Option ℚ :=
  ozaki1CRKA (tcSplitK p b) rne32Q b t r smax x y

/-- Both rules as one integer function from binary64 entries. -/
def tcOzaki1CRIKA (p : Profile) (b W t r smax : ℕ) (xs ys : List (ℤ × ℤ)) : Option ℚ :=
  ozaki1CRIKA (tcSplitK p b) 53 (-1022) 1023 b W t r smax xs ys

theorem tcOzaki1CRDK_eq {p : Profile} {b : ℕ} (heng : (tcEngine p).ExactOn b (2 ^ 24))
    (hb : 2 * b ≤ 24) (t r : ℕ) {smax : ℕ} (hsmax : 2098 < smax * (b + 1)) {x y : List ℚ}
    (hx : ∀ a ∈ x, Binary64Value a) (hy : ∀ a ∈ y, Binary64Value a)
    (hlen : x.length = y.length) :
    tcOzaki1CRDK p b t r smax x y = rne64 (dot x y) :=
  ozaki1CRK_eq rne64_nearest rne64_intervals (tcSplitK_exactOn heng hb _) t r hlen
    (Nat.le_refl _) (vanish64 (by omega) hsmax hx hy)

theorem tcOzaki1CRDA_eq {p : Profile} {b : ℕ} (heng : (tcEngine p).ExactOn b (2 ^ 24))
    (hb : 2 * b ≤ 24) (ss : List ℕ) {smax : ℕ} (hsmax : 2098 < smax * (b + 1)) {x y : List ℚ}
    (hx : ∀ a ∈ x, Binary64Value a) (hy : ∀ a ∈ y, Binary64Value a)
    (hlen : x.length = y.length) :
    tcOzaki1CRDA p b ss smax x y = rne64 (dot x y) :=
  ozaki1CRA_eq rne64_nearest rne64_intervals (tcSplitK_exactOn heng hb _) ss hlen
    (Nat.le_refl _) (vanish64 (by omega) hsmax hx hy)

/-- **Correctly rounded FP64 GEMM on Tensor Cores with both rules**, for binary64 inputs of any
length. -/
theorem tcOzaki1CRDKA_eq {p : Profile} {b : ℕ} (heng : (tcEngine p).ExactOn b (2 ^ 24))
    (hb : 2 * b ≤ 24) (t r : ℕ) {smax : ℕ} (hsmax : 2098 < smax * (b + 1)) {x y : List ℚ}
    (hx : ∀ a ∈ x, Binary64Value a) (hy : ∀ a ∈ y, Binary64Value a)
    (hlen : x.length = y.length) :
    tcOzaki1CRDKA p b t r smax x y = rne64 (dot x y) :=
  ozaki1CRKA_eq rne64_nearest rne64_intervals (tcSplitK_exactOn heng hb _) t r hlen
    (Nat.le_refl _) (vanish64 (by omega) hsmax hx hy)

theorem tcOzaki1CRLKA_eq {p : Profile} {b : ℕ} (heng : (tcEngine p).ExactOn b (2 ^ 24))
    (hb : 2 * b ≤ 24) (t r : ℕ) {smax : ℕ} (hsmax : 277 < smax * (b + 1)) {x y : List ℚ}
    (hx : ∀ a ∈ x, Binary32Value a) (hy : ∀ a ∈ y, Binary32Value a)
    (hlen : x.length = y.length) :
    tcOzaki1CRLKA p b t r smax x y = rne32Q (dot x y) :=
  ozaki1CRKA_eq rne32Q_nearest rne32Q_intervals (tcSplitK_exactOn heng hb _) t r hlen
    (Nat.le_refl _) (vanish32Q (by omega) hsmax hx hy)

/-- **Both rules as one integer function**, correctly rounded for binary64 entries of any length. -/
theorem tcOzaki1CRIKA_eq {p : Profile} {b : ℕ} (heng : (tcEngine p).ExactOn b (2 ^ 24))
    (hb : 2 * b ≤ 24) (W t r : ℕ) {smax : ℕ} (hsmax : 2098 < smax * (b + 1))
    {xs ys : List (ℤ × ℤ)} (hx : ∀ a ∈ xs, Binary64Value (entryVal a))
    (hy : ∀ a ∈ ys, Binary64Value (entryVal a)) (hlen : xs.length = ys.length) :
    tcOzaki1CRIKA p b W t r smax xs ys = rne64 (dot (entryVals xs) (entryVals ys)) :=
  ozaki1CRI64_eq (tcSplitK_exactOn heng hb _) W _ (by omega) hsmax hlen (Nat.le_refl _) hx hy

/-- On V100 fp16 with `11`-bit slices: FP64 with both rules, for every length. -/
theorem v100_fp64CRKA (r : ℕ) {x y : List ℚ} (hx : ∀ a ∈ x, Binary64Value a)
    (hy : ∀ a ∈ y, Binary64Value a) (hlen : x.length = y.length) :
    tcOzaki1CRDKA v100F16F32 11 53 r 175 x y = rne64 (dot x y) :=
  tcOzaki1CRDKA_eq v100_exactOn (by decide) 53 r (by decide) hx hy hlen

end Ozaki.TC
