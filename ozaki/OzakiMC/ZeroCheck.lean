import OzakiMC.Signed
import Ozaki.ZeroCheck

/-! # Exact-zero results without the exact path on the matrix-core model

Correctly rounded Ozaki-I of any inner dimension on matrix-core blocks with split-K, with the overlap bound
of `Ozaki.ZeroCheck`: the slicing bound uses the number of indices where both `xᵢ` and `yᵢ` are
nonzero, which one extra engine product of the `0`/`1` support indicators computes. Correctly
rounded for binary64 and binary32 inputs (`mcOzaki1CRDZ_eq`, `mcOzaki1CRLZ_eq`), in bounded
integer registers (`mcOzaki1CRBDZ_eq`, `mcOzaki1CRBLZ_eq`) and with signed zeros
(`mcOzaki1CRDSZ_eq`); an entry whose products are all zero, such as a sparse row against a column
with disjoint support, settles on the first check (`mcOzaki1CRDZ_zero`, `mcOzaki1CRBDZ_zero`,
`mcOzaki1CRDSZ_zero`). -/

open MatrixCore

namespace Ozaki.MC

/-- Correctly rounded FP64 by Ozaki-I with the overlap bound and a `W`-bit window. -/
def mcOzaki1CRDZ (P : Model) (b W : ℕ) (ss : List ℕ) (smax : ℕ) (x y : List ℚ) : Option ℚ :=
  ozaki1CRWZ (mcSplitK P b) rne64 b W ss smax x y

/-- Correctly rounded binary32 by Ozaki-I with the overlap bound and a `W`-bit window. -/
def mcOzaki1CRLZ (P : Model) (b W : ℕ) (ss : List ℕ) (smax : ℕ) (x y : List ℚ) : Option ℚ :=
  ozaki1CRWZ (mcSplitK P b) rne32Q b W ss smax x y

/-- Correctly rounded FP64 with the overlap bound, in bounded integer registers. -/
def mcOzaki1CRBDZ (P : Model) (b W : ℕ) (ss : List ℕ) (smax : ℕ) (x y : List ℚ) : Option ℚ :=
  ozaki1CRBZ (mcSplitK P b) 53 (-1022) 1023 b W ss smax x y

/-- Correctly rounded binary32 with the overlap bound, in bounded integer registers. -/
def mcOzaki1CRBLZ (P : Model) (b W : ℕ) (ss : List ℕ) (smax : ℕ) (x y : List ℚ) : Option ℚ :=
  ozaki1CRBZ (mcSplitK P b) 24 (-126) 127 b W ss smax x y

/-- Correctly rounded FP64 with the overlap bound and signed zeros. -/
def mcOzaki1CRDSZ (P : Model) (b W : ℕ) (ss : List ℕ) (smax : ℕ) (xs ys : List Signed) :
    Option Signed :=
  ozaki1CRWSZ (mcSplitK P b) rne64 b W ss smax xs ys

theorem mcOzaki1CRDZ_eq {P : Model} {b : ℕ} (hP : ExactMultiplier P b) (hb : 2 * b ≤ 24) (W : ℕ)
    (ss : List ℕ) {smax : ℕ} (hsmax : 2098 < smax * (b + 1)) {x y : List ℚ}
    (hx : ∀ a ∈ x, Binary64Value a) (hy : ∀ a ∈ y, Binary64Value a) (hlen : x.length = y.length) :
    mcOzaki1CRDZ P b W ss smax x y = rne64 (dot x y) :=
  ozaki1CRWZ_eq rne64_nearest rne64_intervals (mcSplitK_exactOn hP hb _) W ss hlen (Nat.le_refl _)
    (vanish64 (by omega) hsmax hx hy)

theorem mcOzaki1CRLZ_eq {P : Model} {b : ℕ} (hP : ExactMultiplier P b) (hb : 2 * b ≤ 24) (W : ℕ)
    (ss : List ℕ) {smax : ℕ} (hsmax : 277 < smax * (b + 1)) {x y : List ℚ}
    (hx : ∀ a ∈ x, Binary32Value a) (hy : ∀ a ∈ y, Binary32Value a) (hlen : x.length = y.length) :
    mcOzaki1CRLZ P b W ss smax x y = rne32Q (dot x y) :=
  ozaki1CRWZ_eq rne32Q_nearest rne32Q_intervals (mcSplitK_exactOn hP hb _) W ss hlen (Nat.le_refl _)
    (vanish32Q (by omega) hsmax hx hy)

theorem mcOzaki1CRBDZ_eq {P : Model} {b : ℕ} (hP : ExactMultiplier P b) (hb : 2 * b ≤ 24) (W : ℕ)
    (ss : List ℕ) {smax : ℕ} (hsmax : 2098 < smax * (b + 1)) {x y : List ℚ}
    (hx : ∀ a ∈ x, Binary64Value a) (hy : ∀ a ∈ y, Binary64Value a) (hlen : x.length = y.length) :
    mcOzaki1CRBDZ P b W ss smax x y = rne64 (dot x y) :=
  ozaki1CRBZ64_eq (mcSplitK_exactOn hP hb _) W ss (by omega) hsmax hlen (Nat.le_refl _) hx hy

theorem mcOzaki1CRBLZ_eq {P : Model} {b : ℕ} (hP : ExactMultiplier P b) (hb : 2 * b ≤ 24) (W : ℕ)
    (ss : List ℕ) {smax : ℕ} (hsmax : 277 < smax * (b + 1)) {x y : List ℚ}
    (hx : ∀ a ∈ x, Binary32Value a) (hy : ∀ a ∈ y, Binary32Value a) (hlen : x.length = y.length) :
    mcOzaki1CRBLZ P b W ss smax x y = rne32Q (dot x y) :=
  ozaki1CRBZ32_eq (mcSplitK_exactOn hP hb _) W ss (by omega) hsmax hlen (Nat.le_refl _) hx hy

theorem mcOzaki1CRDSZ_eq {P : Model} {b : ℕ} (hP : ExactMultiplier P b) (hb : 2 * b ≤ 24) (W : ℕ)
    (ss : List ℕ) {smax : ℕ} (hsmax : 2098 < smax * (b + 1)) {xs ys : List Signed}
    (hx : ∀ a ∈ xs, Binary64Value a.val) (hy : ∀ a ∈ ys, Binary64Value a.val)
    (hlen : xs.length = ys.length) :
    mcOzaki1CRDSZ P b W ss smax xs ys = crSigned rne64 xs ys :=
  ozaki1CRWSZ_eq rne64_nearest rne64_intervals rne64_zero (mcSplitK_exactOn hP hb _) W ss hlen (Nat.le_refl _)
    (vanish64 (by omega) hsmax (vals_mem hx) (vals_mem hy))

/-- **Exact zeros settle on the first check**: when every product is zero, the result is `0` from the
first slice count, for every input length and whatever the exact path would return. -/
theorem mcOzaki1CRDZ_zero {P : Model} {b : ℕ} (hP : ExactMultiplier P b) (hb : 2 * b ≤ 24) (W s : ℕ)
    (ss : List ℕ) (smax : ℕ) {x y : List ℚ} (hlen : x.length = y.length) (hz : ProductsZero x y) :
    mcOzaki1CRDZ P b W (s :: ss) smax x y = some 0 :=
  ozaki1CRWZ_zero rne64_zero (mcSplitK_exactOn hP hb _) s W ss hlen (Nat.le_refl _) hz _

theorem mcOzaki1CRBDZ_zero {P : Model} {b : ℕ} (hP : ExactMultiplier P b) (hb : 2 * b ≤ 24) (W s : ℕ)
    (ss : List ℕ) (smax : ℕ) {x y : List ℚ} (hlen : x.length = y.length) (hz : ProductsZero x y) :
    mcOzaki1CRBDZ P b W (s :: ss) smax x y = some 0 := by
  unfold mcOzaki1CRBDZ ozaki1CRBZ
  rw [overlapMultiplier_eq (mcSplitK_exactOn hP hb _) hlen (Nat.le_refl _)]
  exact (ozaki1CRBZFrom_zero (mcSplitK_exactOn hP hb _) 53 (-1022) 1023 W smax s ss hlen (Nat.le_refl _) hz).2

theorem mcOzaki1CRDSZ_zero {P : Model} {b : ℕ} (hP : ExactMultiplier P b) (hb : 2 * b ≤ 24) (W s : ℕ)
    (ss : List ℕ) (smax : ℕ) {xs ys : List Signed} (hlen : xs.length = ys.length)
    (hz : ProductsZero (vals xs) (vals ys)) :
    mcOzaki1CRDSZ P b W (s :: ss) smax xs ys = some ⟨0, allNegZero xs ys⟩ :=
  ozaki1CRWSZ_zero rne64_zero (mcSplitK_exactOn hP hb _) s W ss hlen (Nat.le_refl _) hz _

end Ozaki.MC
