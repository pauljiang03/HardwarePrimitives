import OzakiMC.LongDot
import Ozaki.SignedZero

/-! # Signed zeros on the MatrixCore model

Correctly rounded Ozaki-I of any inner dimension, with a `W`-bit truncated sum, returning the
IEEE sign of a zero result (`Ozaki.crSigned`): binary64 (`mcOzaki1CRDS_eq`) and binary32
(`mcOzaki1CRLS_eq`). -/

open MatrixCore

namespace Ozaki.MC

theorem rne64_zero : rne64 0 = some 0 := by decide +kernel
theorem rne32Q_zero : rne32Q 0 = some 0 := by decide +kernel

/-- Correctly rounded FP64 Ozaki-I with signed zeros. -/
def mcOzaki1CRDS (P : Model) (b W : ℕ) (ss : List ℕ) (smax : ℕ) (xs ys : List Signed) :
    Option Signed :=
  ozaki1CRWS (mcSplitK P b) rne64 b W ss smax xs ys

/-- Correctly rounded binary32 Ozaki-I with signed zeros. -/
def mcOzaki1CRLS (P : Model) (b W : ℕ) (ss : List ℕ) (smax : ℕ) (xs ys : List Signed) :
    Option Signed :=
  ozaki1CRWS (mcSplitK P b) rne32Q b W ss smax xs ys

theorem vals_mem {xs : List Signed} {Q : ℚ → Prop} (h : ∀ a ∈ xs, Q a.val) : ∀ v ∈ vals xs, Q v := by
  intro v hv
  obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hv
  exact h a ha

/-- **Signed correct rounding of FP64 GEMM**, any inner dimension: the binary64 round to nearest of
`x · y` with IEEE's sign for zero results. -/
theorem mcOzaki1CRDS_eq {P : Model} {b : ℕ} (hP : ExactMultiplier P b) (hb : 2 * b ≤ 24) (W : ℕ)
    (ss : List ℕ) {smax : ℕ} (hsmax : 2098 < smax * (b + 1)) {xs ys : List Signed}
    (hx : ∀ a ∈ xs, Binary64Value a.val) (hy : ∀ a ∈ ys, Binary64Value a.val)
    (hlen : xs.length = ys.length) :
    mcOzaki1CRDS P b W ss smax xs ys = crSigned rne64 xs ys :=
  ozaki1CRWS_eq rne64_nearest rne64_intervals rne64_zero (mcSplitK_exactOn hP hb _) W ss hlen (Nat.le_refl _)
    (vanish64 (by omega) hsmax (vals_mem hx) (vals_mem hy))

/-- **Signed correct rounding of binary32 GEMM**, any inner dimension. -/
theorem mcOzaki1CRLS_eq {P : Model} {b : ℕ} (hP : ExactMultiplier P b) (hb : 2 * b ≤ 24) (W : ℕ)
    (ss : List ℕ) {smax : ℕ} (hsmax : 277 < smax * (b + 1)) {xs ys : List Signed}
    (hx : ∀ a ∈ xs, Binary32Value a.val) (hy : ∀ a ∈ ys, Binary32Value a.val)
    (hlen : xs.length = ys.length) :
    mcOzaki1CRLS P b W ss smax xs ys = crSigned rne32Q xs ys :=
  ozaki1CRWS_eq rne32Q_nearest rne32Q_intervals rne32Q_zero (mcSplitK_exactOn hP hb _) W ss hlen (Nat.le_refl _)
    (vanish32Q (by omega) hsmax (vals_mem hx) (vals_mem hy))

end Ozaki.MC
