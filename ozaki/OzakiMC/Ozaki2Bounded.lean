import OzakiMC.LongDot
import Ozaki.BoundedOzaki2Int

/-! # Ozaki-II with bounded registers and signed zeros on the matrix-core model

`Ozaki.ozaki2CRB` (the check on integer enclosures, then Ozaki-I's bounded exact path) and
`Ozaki.ozaki2CRS`, `Ozaki.ozaki2CRBS` (signed zeros) with matrix-core blocks and split-K as the engine:
every residue and slice product on the hardware model, for binary64 and binary32 inputs of any
length; and `Ozaki.ozaki2CRZ`, the same from integer-pair inputs with every step integer
arithmetic. -/

open MatrixCore

namespace Ozaki.MC

/-- Correctly rounded FP64 by Ozaki-II with bounded registers on matrix-core blocks. -/
def mcOzaki2CRB (P : Model) (cfgs : List (CRTBasis × ℕ)) (b smax : ℕ) (x y : List ℚ) :
    Option ℚ :=
  ozaki2CRB (mcSplitK P b) 53 (-1022) 1023 cfgs b smax x y

/-- Correctly rounded binary32 Ozaki-II with bounded registers on matrix-core blocks. -/
def mcOzaki2CRBL (P : Model) (cfgs : List (CRTBasis × ℕ)) (b smax : ℕ) (x y : List ℚ) :
    Option ℚ :=
  ozaki2CRB (mcSplitK P b) 24 (-126) 127 cfgs b smax x y

/-- **FP64 GEMM by Ozaki-II on AMD matrix cores with bounded registers, correctly rounded**, any
length. -/
theorem mcOzaki2CRB_eq {P : Model} {b : ℕ} (hP : ExactMultiplier P b)
    (hb : 2 * b ≤ 24) {cfgs : List (CRTBasis × ℕ)} {smax : ℕ} (hsmax : 2098 < smax * (b + 1))
    {x y : List ℚ}
    (hcfg : ∀ c ∈ cfgs, c.1.Valid ∧ (∀ m ∈ c.1.moduli, m ≤ 2 ^ (b + 1)) ∧
      2 * x.length * (2 ^ c.2 * 2 ^ c.2) < c.1.modulus)
    (hx : ∀ a ∈ x, Binary64Value a) (hy : ∀ a ∈ y, Binary64Value a)
    (hlen : x.length = y.length) :
    mcOzaki2CRB P cfgs b smax x y = rne64 (dot x y) :=
  ozaki2CRB64_eq (mcSplitK_exactOn hP hb _) (by omega) hsmax hcfg hlen (Nat.le_refl _) hx hy

theorem mcOzaki2CRBL_eq {P : Model} {b : ℕ} (hP : ExactMultiplier P b)
    (hb : 2 * b ≤ 24) {cfgs : List (CRTBasis × ℕ)} {smax : ℕ} (hsmax : 277 < smax * (b + 1))
    {x y : List ℚ}
    (hcfg : ∀ c ∈ cfgs, c.1.Valid ∧ (∀ m ∈ c.1.moduli, m ≤ 2 ^ (b + 1)) ∧
      2 * x.length * (2 ^ c.2 * 2 ^ c.2) < c.1.modulus)
    (hx : ∀ a ∈ x, Binary32Value a) (hy : ∀ a ∈ y, Binary32Value a)
    (hlen : x.length = y.length) :
    mcOzaki2CRBL P cfgs b smax x y = rne32Q (dot x y) :=
  ozaki2CRB32_eq (mcSplitK_exactOn hP hb _) (by omega) hsmax hcfg hlen (Nat.le_refl _) hx hy

/-- Correctly rounded FP64 Ozaki-II with signed zeros on matrix-core blocks. -/
def mcOzaki2CRDS (P : Model) (cfgs : List (CRTBasis × ℕ)) (b smax : ℕ) (xs ys : List Signed) :
    Option Signed :=
  ozaki2CRS (mcSplitK P b) rne64 cfgs b smax xs ys

/-- Correctly rounded FP64 Ozaki-II with signed zeros and bounded registers on Tensor Core
blocks. -/
def mcOzaki2CRBS (P : Model) (cfgs : List (CRTBasis × ℕ)) (b smax : ℕ) (xs ys : List Signed) :
    Option Signed :=
  ozaki2CRBS (mcSplitK P b) 53 (-1022) 1023 cfgs b smax xs ys

/-- **Signed correct rounding of FP64 GEMM by Ozaki-II**, any length. -/
theorem mcOzaki2CRDS_eq {P : Model} {b : ℕ} (hP : ExactMultiplier P b)
    (hb : 2 * b ≤ 24) {cfgs : List (CRTBasis × ℕ)} {smax : ℕ} (hsmax : 2098 < smax * (b + 1))
    {xs ys : List Signed}
    (hcfg : ∀ c ∈ cfgs, c.1.Valid ∧ (∀ m ∈ c.1.moduli, m ≤ 2 ^ (b + 1)) ∧
      2 * xs.length * (2 ^ c.2 * 2 ^ c.2) < c.1.modulus)
    (hx : ∀ a ∈ xs, Binary64Value a.val) (hy : ∀ a ∈ ys, Binary64Value a.val)
    (hlen : xs.length = ys.length) :
    mcOzaki2CRDS P cfgs b smax xs ys = crSigned rne64 xs ys :=
  ozaki2CRS_eq rne64_nearest rne64_intervals (roundRNE_zero' 53 (-1022) 1023)
    (mcSplitK_exactOn hP hb _) hcfg hlen (Nat.le_refl _)
    (vanish64 (by omega) hsmax (vals_all hx) (vals_all hy))

/-- **Signed correct rounding of FP64 GEMM by Ozaki-II with bounded registers**, any length. -/
theorem mcOzaki2CRBS_eq {P : Model} {b : ℕ} (hP : ExactMultiplier P b)
    (hb : 2 * b ≤ 24) {cfgs : List (CRTBasis × ℕ)} {smax : ℕ} (hsmax : 2098 < smax * (b + 1))
    {xs ys : List Signed}
    (hcfg : ∀ c ∈ cfgs, c.1.Valid ∧ (∀ m ∈ c.1.moduli, m ≤ 2 ^ (b + 1)) ∧
      2 * xs.length * (2 ^ c.2 * 2 ^ c.2) < c.1.modulus)
    (hx : ∀ a ∈ xs, Binary64Value a.val) (hy : ∀ a ∈ ys, Binary64Value a.val)
    (hlen : xs.length = ys.length) :
    mcOzaki2CRBS P cfgs b smax xs ys = crSigned rne64 xs ys :=
  ozaki2CRBS_eq (by decide) (by decide) (mcSplitK_exactOn hP hb _) hcfg hlen (Nat.le_refl _)
    (vanish64 (by omega) hsmax (vals_all hx) (vals_all hy))

/-- **Correctly rounded FP64 by Ozaki-II as an integer pipeline on matrix-core blocks**: binary64
inputs as integer pairs `(m, e)`. -/
def mcOzaki2CRZ (P : Model) (cfgs : List (CRTBasis × ℕ)) (b smax : ℕ) (xs ys : List (ℤ × ℤ)) :
    Option ℚ :=
  ozaki2CRZ (mcSplitK P b) 53 (-1022) 1023 cfgs b smax xs ys

/-- The same for binary32. -/
def mcOzaki2CRZL (P : Model) (cfgs : List (CRTBasis × ℕ)) (b smax : ℕ) (xs ys : List (ℤ × ℤ)) :
    Option ℚ :=
  ozaki2CRZ (mcSplitK P b) 24 (-126) 127 cfgs b smax xs ys

theorem mcOzaki2CRZ_eq {P : Model} {b : ℕ} (hP : ExactMultiplier P b)
    (hb : 2 * b ≤ 24) {cfgs : List (CRTBasis × ℕ)} {smax : ℕ} (hsmax : 2098 < smax * (b + 1))
    {xs ys : List (ℤ × ℤ)}
    (hcfg : ∀ c ∈ cfgs, c.1.Valid ∧ (∀ m ∈ c.1.moduli, m ≤ 2 ^ (b + 1)) ∧
      2 * xs.length * (2 ^ c.2 * 2 ^ c.2) < c.1.modulus)
    (hx : ∀ v ∈ entryVals xs, Binary64Value v) (hy : ∀ v ∈ entryVals ys, Binary64Value v)
    (hlen : xs.length = ys.length) :
    mcOzaki2CRZ P cfgs b smax xs ys = rne64 (dot (entryVals xs) (entryVals ys)) :=
  ozaki2CRZ64_eq (mcSplitK_exactOn hP hb _) (by omega) hsmax hcfg hlen
    (Nat.le_refl _) hx hy

theorem mcOzaki2CRZL_eq {P : Model} {b : ℕ} (hP : ExactMultiplier P b)
    (hb : 2 * b ≤ 24) {cfgs : List (CRTBasis × ℕ)} {smax : ℕ} (hsmax : 277 < smax * (b + 1))
    {xs ys : List (ℤ × ℤ)}
    (hcfg : ∀ c ∈ cfgs, c.1.Valid ∧ (∀ m ∈ c.1.moduli, m ≤ 2 ^ (b + 1)) ∧
      2 * xs.length * (2 ^ c.2 * 2 ^ c.2) < c.1.modulus)
    (hx : ∀ v ∈ entryVals xs, Binary32Value v) (hy : ∀ v ∈ entryVals ys, Binary32Value v)
    (hlen : xs.length = ys.length) :
    mcOzaki2CRZL P cfgs b smax xs ys = rne32Q (dot (entryVals xs) (entryVals ys)) :=
  ozaki2CRZ32_eq (mcSplitK_exactOn hP hb _) (by omega) hsmax hcfg hlen
    (Nat.le_refl _) hx hy

end Ozaki.MC
