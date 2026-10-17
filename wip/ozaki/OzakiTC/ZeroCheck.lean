import OzakiTC.Signed
import Ozaki.ZeroCheck

/-! # Exact-zero results without the exact fallback on the Tensor Core model

Correctly rounded Ozaki-I of any inner dimension on Tensor Core blocks with split-K, with the bound
of `Ozaki.ZeroCheck` that counts only nonzero positions: the slicing bound uses the number of
indices where both `xᵢ` and `yᵢ` are nonzero, which one extra dot product on the matrix multiplier
of the `0`/`1` support indicators computes. Correctly rounded for binary64 and binary32 inputs
(`tcOzaki1CRDZ_eq`, `tcOzaki1CRLZ_eq`), in bounded integer registers (`tcOzaki1CRBDZ_eq`,
`tcOzaki1CRBLZ_eq`) and with signed zeros (`tcOzaki1CRDSZ_eq`); an entry whose products are all
zero, such as a sparse row against a column with disjoint support, is decided by the first rounding
test (`tcOzaki1CRDZ_zero`, `tcOzaki1CRBDZ_zero`, `tcOzaki1CRDSZ_zero`). -/

open TensorCore

namespace Ozaki.TC

/-- Correctly rounded FP64 by Ozaki-I with the bound that counts only nonzero positions and a
`W`-bit truncated sum. -/
def tcOzaki1CRDZ (p : Model) (b W : ℕ) (ss : List ℕ) (smax : ℕ) (x y : List ℚ) : Option ℚ :=
  ozaki1CRWZ (tcSplitK p b) rne64 b W ss smax x y

/-- Correctly rounded binary32 by Ozaki-I with the bound that counts only nonzero positions and a
`W`-bit truncated sum. -/
def tcOzaki1CRLZ (p : Model) (b W : ℕ) (ss : List ℕ) (smax : ℕ) (x y : List ℚ) : Option ℚ :=
  ozaki1CRWZ (tcSplitK p b) rne32Q b W ss smax x y

/-- Correctly rounded FP64 with the bound that counts only nonzero positions, in bounded integer
registers. -/
def tcOzaki1CRBDZ (p : Model) (b W : ℕ) (ss : List ℕ) (smax : ℕ) (x y : List ℚ) : Option ℚ :=
  ozaki1CRBZ (tcSplitK p b) 53 (-1022) 1023 b W ss smax x y

/-- Correctly rounded binary32 with the bound that counts only nonzero positions, in bounded integer
registers. -/
def tcOzaki1CRBLZ (p : Model) (b W : ℕ) (ss : List ℕ) (smax : ℕ) (x y : List ℚ) : Option ℚ :=
  ozaki1CRBZ (tcSplitK p b) 24 (-126) 127 b W ss smax x y

/-- Correctly rounded FP64 with the bound that counts only nonzero positions and signed zeros. -/
def tcOzaki1CRDSZ (p : Model) (b W : ℕ) (ss : List ℕ) (smax : ℕ) (xs ys : List Signed) :
    Option Signed :=
  ozaki1CRWSZ (tcSplitK p b) rne64 b W ss smax xs ys

theorem tcOzaki1CRDZ_eq {p : Model} {b : ℕ} (hmult : (tcMultiplier p).ExactOn b (2 ^ 24)) (hb : 2 * b ≤ 24) (W : ℕ)
    (ss : List ℕ) {smax : ℕ} (hsmax : 2098 < smax * (b + 1)) {x y : List ℚ}
    (hx : ∀ a ∈ x, Binary64Value a) (hy : ∀ a ∈ y, Binary64Value a) (hlen : x.length = y.length) :
    tcOzaki1CRDZ p b W ss smax x y = rne64 (dot x y) :=
  ozaki1CRWZ_eq rne64_nearest rne64_intervals (tcSplitK_exactOn hmult hb _) W ss hlen (Nat.le_refl _)
    (vanish64 (by omega) hsmax hx hy)

theorem tcOzaki1CRLZ_eq {p : Model} {b : ℕ} (hmult : (tcMultiplier p).ExactOn b (2 ^ 24)) (hb : 2 * b ≤ 24) (W : ℕ)
    (ss : List ℕ) {smax : ℕ} (hsmax : 277 < smax * (b + 1)) {x y : List ℚ}
    (hx : ∀ a ∈ x, Binary32Value a) (hy : ∀ a ∈ y, Binary32Value a) (hlen : x.length = y.length) :
    tcOzaki1CRLZ p b W ss smax x y = rne32Q (dot x y) :=
  ozaki1CRWZ_eq rne32Q_nearest rne32Q_intervals (tcSplitK_exactOn hmult hb _) W ss hlen (Nat.le_refl _)
    (vanish32Q (by omega) hsmax hx hy)

theorem tcOzaki1CRBDZ_eq {p : Model} {b : ℕ} (hmult : (tcMultiplier p).ExactOn b (2 ^ 24)) (hb : 2 * b ≤ 24) (W : ℕ)
    (ss : List ℕ) {smax : ℕ} (hsmax : 2098 < smax * (b + 1)) {x y : List ℚ}
    (hx : ∀ a ∈ x, Binary64Value a) (hy : ∀ a ∈ y, Binary64Value a) (hlen : x.length = y.length) :
    tcOzaki1CRBDZ p b W ss smax x y = rne64 (dot x y) :=
  ozaki1CRBZ64_eq (tcSplitK_exactOn hmult hb _) W ss (by omega) hsmax hlen (Nat.le_refl _) hx hy

theorem tcOzaki1CRBLZ_eq {p : Model} {b : ℕ} (hmult : (tcMultiplier p).ExactOn b (2 ^ 24)) (hb : 2 * b ≤ 24) (W : ℕ)
    (ss : List ℕ) {smax : ℕ} (hsmax : 277 < smax * (b + 1)) {x y : List ℚ}
    (hx : ∀ a ∈ x, Binary32Value a) (hy : ∀ a ∈ y, Binary32Value a) (hlen : x.length = y.length) :
    tcOzaki1CRBLZ p b W ss smax x y = rne32Q (dot x y) :=
  ozaki1CRBZ32_eq (tcSplitK_exactOn hmult hb _) W ss (by omega) hsmax hlen (Nat.le_refl _) hx hy

theorem tcOzaki1CRDSZ_eq {p : Model} {b : ℕ} (hmult : (tcMultiplier p).ExactOn b (2 ^ 24)) (hb : 2 * b ≤ 24) (W : ℕ)
    (ss : List ℕ) {smax : ℕ} (hsmax : 2098 < smax * (b + 1)) {xs ys : List Signed}
    (hx : ∀ a ∈ xs, Binary64Value a.val) (hy : ∀ a ∈ ys, Binary64Value a.val)
    (hlen : xs.length = ys.length) :
    tcOzaki1CRDSZ p b W ss smax xs ys = crSigned rne64 xs ys :=
  ozaki1CRWSZ_eq rne64_nearest rne64_intervals rne64_zero (tcSplitK_exactOn hmult hb _) W ss hlen (Nat.le_refl _)
    (vanish64 (by omega) hsmax (vals_mem hx) (vals_mem hy))

/-- **The first rounding test succeeds on exact zeros**: when every product is zero, the result is
`0` from the first slice count, for every input length and whatever the exact fallback would return.
-/
theorem tcOzaki1CRDZ_zero {p : Model} {b : ℕ} (hmult : (tcMultiplier p).ExactOn b (2 ^ 24)) (hb : 2 * b ≤ 24) (W s : ℕ)
    (ss : List ℕ) (smax : ℕ) {x y : List ℚ} (hlen : x.length = y.length) (hz : ProductsZero x y) :
    tcOzaki1CRDZ p b W (s :: ss) smax x y = some 0 :=
  ozaki1CRWZ_zero rne64_zero (tcSplitK_exactOn hmult hb _) s W ss hlen (Nat.le_refl _) hz _

theorem tcOzaki1CRBDZ_zero {p : Model} {b : ℕ} (hmult : (tcMultiplier p).ExactOn b (2 ^ 24)) (hb : 2 * b ≤ 24) (W s : ℕ)
    (ss : List ℕ) (smax : ℕ) {x y : List ℚ} (hlen : x.length = y.length) (hz : ProductsZero x y) :
    tcOzaki1CRBDZ p b W (s :: ss) smax x y = some 0 := by
  unfold tcOzaki1CRBDZ ozaki1CRBZ
  rw [overlapMultiplier_eq (tcSplitK_exactOn hmult hb _) hlen (Nat.le_refl _)]
  exact (ozaki1CRBZFrom_zero (tcSplitK_exactOn hmult hb _) 53 (-1022) 1023 W smax s ss hlen (Nat.le_refl _) hz).2

theorem tcOzaki1CRDSZ_zero {p : Model} {b : ℕ} (hmult : (tcMultiplier p).ExactOn b (2 ^ 24)) (hb : 2 * b ≤ 24) (W s : ℕ)
    (ss : List ℕ) (smax : ℕ) {xs ys : List Signed} (hlen : xs.length = ys.length)
    (hz : ProductsZero (vals xs) (vals ys)) :
    tcOzaki1CRDSZ p b W (s :: ss) smax xs ys = some ⟨0, allNegZero xs ys⟩ :=
  ozaki1CRWSZ_zero rne64_zero (tcSplitK_exactOn hmult hb _) s W ss hlen (Nat.le_refl _) hz _

end Ozaki.TC
