import OzakiMC.Ozaki2Bounded
import Ozaki.BoundedOzaki2J

/-! # Ozaki-II as an integer pipeline with the jumping descent on the matrix-core model

`Ozaki.ozaki2CRJ` and its signed variant `Ozaki.ozaki2CRJS` with matrix-core blocks and split-K as
the engine: every residue and slice product on the hardware model, every other step integer
arithmetic, and an exact path whose number of windows does not depend on the inputs' exponents;
binary64 and binary32 inputs of any length. -/

open MatrixCore

namespace Ozaki.MC

/-- Correctly rounded FP64 by Ozaki-II in integers with the jumping descent on matrix-core
blocks. -/
def mcOzaki2CRJ (P : Model) (cfgs : List (CRTBasis × ℕ)) (b smax : ℕ) (xs ys : List (ℤ × ℤ)) :
    Option ℚ :=
  ozaki2CRJ (mcSplitK P b) 53 (-1022) 1023 cfgs b smax xs ys

/-- The same for binary32. -/
def mcOzaki2CRJL (P : Model) (cfgs : List (CRTBasis × ℕ)) (b smax : ℕ) (xs ys : List (ℤ × ℤ)) :
    Option ℚ :=
  ozaki2CRJ (mcSplitK P b) 24 (-126) 127 cfgs b smax xs ys

/-- Correctly rounded FP64 by Ozaki-II in integers with signed zeros on matrix-core blocks. -/
def mcOzaki2CRJS (P : Model) (cfgs : List (CRTBasis × ℕ)) (b smax : ℕ) (xs ys : List SEntry) :
    Option Signed :=
  ozaki2CRJS (mcSplitK P b) 53 (-1022) 1023 cfgs b smax xs ys

theorem mcOzaki2CRJ_eq {P : Model} {b : ℕ} (hP : ExactMultiplier P b)
    (hb : 2 * b ≤ 24) {cfgs : List (CRTBasis × ℕ)} {smax : ℕ} (hsmax : 2098 < smax * (b + 1))
    {xs ys : List (ℤ × ℤ)}
    (hcfg : ∀ c ∈ cfgs, c.1.Valid ∧ (∀ m ∈ c.1.moduli, m ≤ 2 ^ (b + 1)) ∧
      2 * xs.length * (2 ^ c.2 * 2 ^ c.2) < c.1.modulus)
    (hx : ∀ v ∈ entryVals xs, Binary64Value v) (hy : ∀ v ∈ entryVals ys, Binary64Value v)
    (hlen : xs.length = ys.length) :
    mcOzaki2CRJ P cfgs b smax xs ys = rne64 (dot (entryVals xs) (entryVals ys)) :=
  ozaki2CRJ64_eq (mcSplitK_exactOn hP hb _) (by omega) hsmax hcfg hlen (Nat.le_refl _) hx hy

theorem mcOzaki2CRJL_eq {P : Model} {b : ℕ} (hP : ExactMultiplier P b)
    (hb : 2 * b ≤ 24) {cfgs : List (CRTBasis × ℕ)} {smax : ℕ} (hsmax : 277 < smax * (b + 1))
    {xs ys : List (ℤ × ℤ)}
    (hcfg : ∀ c ∈ cfgs, c.1.Valid ∧ (∀ m ∈ c.1.moduli, m ≤ 2 ^ (b + 1)) ∧
      2 * xs.length * (2 ^ c.2 * 2 ^ c.2) < c.1.modulus)
    (hx : ∀ v ∈ entryVals xs, Binary32Value v) (hy : ∀ v ∈ entryVals ys, Binary32Value v)
    (hlen : xs.length = ys.length) :
    mcOzaki2CRJL P cfgs b smax xs ys = rne32Q (dot (entryVals xs) (entryVals ys)) :=
  ozaki2CRJ32_eq (mcSplitK_exactOn hP hb _) (by omega) hsmax hcfg hlen (Nat.le_refl _) hx hy

theorem mcOzaki2CRJS_eq {P : Model} {b : ℕ} (hP : ExactMultiplier P b)
    (hb : 2 * b ≤ 24) {cfgs : List (CRTBasis × ℕ)} {smax : ℕ} (hsmax : 2098 < smax * (b + 1))
    {xs ys : List SEntry}
    (hcfg : ∀ c ∈ cfgs, c.1.Valid ∧ (∀ m ∈ c.1.moduli, m ≤ 2 ^ (b + 1)) ∧
      2 * xs.length * (2 ^ c.2 * 2 ^ c.2) < c.1.modulus)
    (hx : ∀ a ∈ xs, Binary64Value (entryVal a.1)) (hy : ∀ a ∈ ys, Binary64Value (entryVal a.1))
    (hlen : xs.length = ys.length) :
    mcOzaki2CRJS P cfgs b smax xs ys = crSigned rne64 (xs.map toSigned) (ys.map toSigned) :=
  ozaki2CRJS64_eq (mcSplitK_exactOn hP hb _) (by omega) hsmax hcfg hlen (Nat.le_refl _) hx hy

end Ozaki.MC
