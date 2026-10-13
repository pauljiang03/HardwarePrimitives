import OzakiTC.ADPIntPipeline
import OzakiTC.Ozaki2Bounded
import Ozaki.BoundedOzaki2J

/-! # ADP and Ozaki-II as integer pipelines with the jumping descent, on the Tensor Core side

`adpCRJ` is ADP's correctly rounded slicing from integer-pair inputs (`adpCRZ`) with its exact path
through the jumping descent (`Ozaki.ozaki1ExactFallbackI` on the split-K INT8 engine), so the number of
windows the exact path visits does not depend on the inputs' exponents (`Ozaki.exactFallback_ranges`).
It returns what `adpCRZ` returns (`adpCRJ_eq_CRZ`) and is correctly rounded for binary64 inputs of
any length (`adpCRJ_eq`); it is the canonical integer ADP pipeline. `adpCRJS` adds IEEE's signed
zeros on inputs with sign bits (`adpCRJS_eq`).

With Tensor Core blocks as the engine: `tcOzaki2CRJ` (FP64), `tcOzaki2CRJL` (binary32) and
`tcOzaki2CRJS` (FP64 with signed zeros), every residue and slice product on the hardware model, every
other step integer arithmetic, any length. -/

open TensorCore

namespace Ozaki.TC

/-- **ADP's slicing, correctly rounded, as an integer pipeline with the jumping descent.** -/
def adpCRJ (cfgs : List (ℕ × ℕ)) (smax : ℕ) (xs ys : List (ℤ × ℤ)) : Option ℚ :=
  roundingTestB 53 (-1022) 1023 (cfgs.map fun c => some (adpEnclosureZ c.1 c.2 xs ys))
    (ozaki1ExactFallbackI int8SplitK 53 (-1022) 1023 6 smax xs ys)

theorem adpCRJ_eq_CRZ (cfgs : List (ℕ × ℕ)) (smax : ℕ) (xs ys : List (ℤ × ℤ)) :
    adpCRJ cfgs smax xs ys = adpCRZ cfgs smax xs ys := by
  unfold adpCRJ adpCRZ
  rw [ozaki1ExactFallbackI_eq, ozaki1ExactFallbackZ_eq]

/-- **The jumping ADP pipeline is correctly rounded** for binary64 inputs of any length. -/
theorem adpCRJ_eq {cfgs : List (ℕ × ℕ)} (hcfg : ∀ c ∈ cfgs, 0 < c.1 ∧ ADP.remapFits c.2 c.1 = true)
    {smax : ℕ} (hsmax : 2098 < smax * 7) {xs ys : List (ℤ × ℤ)}
    (hx : ∀ v ∈ entryVals xs, Binary64Value v) (hy : ∀ v ∈ entryVals ys, Binary64Value v)
    (hlen : xs.length = ys.length) :
    adpCRJ cfgs smax xs ys = rne64 (dot (entryVals xs) (entryVals ys)) := by
  rw [adpCRJ_eq_CRZ]
  exact adpCRZ_eq hcfg hsmax hx hy hlen

/-- **ADP's slicing in integers with signed zeros.** -/
def adpCRJS (cfgs : List (ℕ × ℕ)) (smax : ℕ) (xs ys : List SEntry) : Option Signed :=
  roundingTestSignedB 53 (-1022) 1023
    (cfgs.map fun c => some (adpEnclosureZ c.1 c.2 (xs.map (·.1)) (ys.map (·.1))))
    (ozaki1ExactFallbackIS int8SplitK 53 (-1022) 1023 6 smax (xs.map (·.1)) (ys.map (·.1)))
    (allNegZeroI xs ys)

theorem adpCRJS_eq_CRBS (cfgs : List (ℕ × ℕ)) (smax : ℕ) (xs ys : List SEntry) :
    adpCRJS cfgs smax xs ys = adpCRBS cfgs smax (xs.map toSigned) (ys.map toSigned) := by
  unfold adpCRJS adpCRBS
  rw [ozaki1ExactFallbackIS_eq, vals_toSigned, vals_toSigned, allNegZeroI_eq]
  congr 1
  apply List.map_congr_left
  intro c _
  rw [adpEnclosureZ_eq]

/-- **Signed correct rounding of ADP's slicing in integers**: the binary64 round to nearest of
`x · y` with IEEE's sign for zero results. -/
theorem adpCRJS_eq {cfgs : List (ℕ × ℕ)} (hcfg : ∀ c ∈ cfgs, 0 < c.1 ∧ ADP.remapFits c.2 c.1 = true)
    {smax : ℕ} (hsmax : 2098 < smax * 7) {xs ys : List SEntry}
    (hx : ∀ a ∈ xs, Binary64Value (entryVal a.1)) (hy : ∀ a ∈ ys, Binary64Value (entryVal a.1))
    (hlen : xs.length = ys.length) :
    adpCRJS cfgs smax xs ys = crSigned rne64 (xs.map toSigned) (ys.map toSigned) := by
  rw [adpCRJS_eq_CRBS]
  have hs : ∀ {zs : List SEntry}, (∀ a ∈ zs, Binary64Value (entryVal a.1)) →
      ∀ a ∈ zs.map toSigned, Binary64Value a.val := by
    intro zs hz a ha
    obtain ⟨c, hc, rfl⟩ := List.mem_map.mp ha
    exact hz c hc
  exact adpCRBS_eq hcfg hsmax (hs hx) (hs hy) (by simp [hlen])

/-! ## Ozaki-II on Tensor Core blocks -/

/-- Correctly rounded FP64 by Ozaki-II as an integer pipeline with the jumping descent on Tensor
Core blocks. -/
def tcOzaki2CRJ (p : Model) (cfgs : List (CRTBasis × ℕ)) (b smax : ℕ) (xs ys : List (ℤ × ℤ)) :
    Option ℚ :=
  ozaki2CRJ (tcSplitK p b) 53 (-1022) 1023 cfgs b smax xs ys

/-- The same for binary32. -/
def tcOzaki2CRJL (p : Model) (cfgs : List (CRTBasis × ℕ)) (b smax : ℕ) (xs ys : List (ℤ × ℤ)) :
    Option ℚ :=
  ozaki2CRJ (tcSplitK p b) 24 (-126) 127 cfgs b smax xs ys

/-- Correctly rounded FP64 by Ozaki-II in integers with signed zeros on Tensor Core blocks. -/
def tcOzaki2CRJS (p : Model) (cfgs : List (CRTBasis × ℕ)) (b smax : ℕ) (xs ys : List SEntry) :
    Option Signed :=
  ozaki2CRJS (tcSplitK p b) 53 (-1022) 1023 cfgs b smax xs ys

theorem tcOzaki2CRJ_eq {p : Model} {b : ℕ} (hmult : (tcMultiplier p).ExactOn b (2 ^ 24))
    (hb : 2 * b ≤ 24) {cfgs : List (CRTBasis × ℕ)} {smax : ℕ} (hsmax : 2098 < smax * (b + 1))
    {xs ys : List (ℤ × ℤ)}
    (hcfg : ∀ c ∈ cfgs, c.1.Valid ∧ (∀ m ∈ c.1.moduli, m ≤ 2 ^ (b + 1)) ∧
      2 * xs.length * (2 ^ c.2 * 2 ^ c.2) < c.1.modulus)
    (hx : ∀ v ∈ entryVals xs, Binary64Value v) (hy : ∀ v ∈ entryVals ys, Binary64Value v)
    (hlen : xs.length = ys.length) :
    tcOzaki2CRJ p cfgs b smax xs ys = rne64 (dot (entryVals xs) (entryVals ys)) :=
  ozaki2CRJ64_eq (tcSplitK_exactOn hmult hb _) (by omega) hsmax hcfg hlen (Nat.le_refl _) hx hy

theorem tcOzaki2CRJL_eq {p : Model} {b : ℕ} (hmult : (tcMultiplier p).ExactOn b (2 ^ 24))
    (hb : 2 * b ≤ 24) {cfgs : List (CRTBasis × ℕ)} {smax : ℕ} (hsmax : 277 < smax * (b + 1))
    {xs ys : List (ℤ × ℤ)}
    (hcfg : ∀ c ∈ cfgs, c.1.Valid ∧ (∀ m ∈ c.1.moduli, m ≤ 2 ^ (b + 1)) ∧
      2 * xs.length * (2 ^ c.2 * 2 ^ c.2) < c.1.modulus)
    (hx : ∀ v ∈ entryVals xs, Binary32Value v) (hy : ∀ v ∈ entryVals ys, Binary32Value v)
    (hlen : xs.length = ys.length) :
    tcOzaki2CRJL p cfgs b smax xs ys = rne32Q (dot (entryVals xs) (entryVals ys)) :=
  ozaki2CRJ32_eq (tcSplitK_exactOn hmult hb _) (by omega) hsmax hcfg hlen (Nat.le_refl _) hx hy

theorem tcOzaki2CRJS_eq {p : Model} {b : ℕ} (hmult : (tcMultiplier p).ExactOn b (2 ^ 24))
    (hb : 2 * b ≤ 24) {cfgs : List (CRTBasis × ℕ)} {smax : ℕ} (hsmax : 2098 < smax * (b + 1))
    {xs ys : List SEntry}
    (hcfg : ∀ c ∈ cfgs, c.1.Valid ∧ (∀ m ∈ c.1.moduli, m ≤ 2 ^ (b + 1)) ∧
      2 * xs.length * (2 ^ c.2 * 2 ^ c.2) < c.1.modulus)
    (hx : ∀ a ∈ xs, Binary64Value (entryVal a.1)) (hy : ∀ a ∈ ys, Binary64Value (entryVal a.1))
    (hlen : xs.length = ys.length) :
    tcOzaki2CRJS p cfgs b smax xs ys = crSigned rne64 (xs.map toSigned) (ys.map toSigned) :=
  ozaki2CRJS64_eq (tcSplitK_exactOn hmult hb _) (by omega) hsmax hcfg hlen (Nat.le_refl _) hx hy

end Ozaki.TC
