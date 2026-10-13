import OzakiTC.ADPIntJ
import OzakiTC.Bounded
import OzakiTC.ZeroCheck
import OzakiTC.IEEESchemes
import Ozaki.IEEEInt

/-! # The bounded and integer Tensor Core schemes with IEEE special values

The correctly rounded schemes in bounded and in integer arithmetic, with IEEE special values
(`±Inf`, NaN, signed zeros), each meeting the IEEE specification `dotIEEE` for every input:

* on rational data (`FVal`), wrapped by `crIEEE` with the sign oracle `exactSignB`: Ozaki-II with
  integer checks (`tcOzaki2CRBI_eq`, `tcOzaki2CRBLI_eq`), ADP-style slicing with integer checks
  (`adpCRBI_eq`), and the zero-aware bounded Ozaki-I (`tcOzaki1CRBDZI_eq`, `tcOzaki1CRBLZI_eq`);
* on stored data (`IDatum`: `((m, e), sign)`, `±Inf`, NaN), wrapped by `crIEEEI` with the integer
  sign oracle `exactSignI`: Ozaki-I in integers (`tcOzaki1CRIDI_eq`, `tcOzaki1CRILI_eq`), Ozaki-II in
  integers (`tcOzaki2CRJI_eq`, `tcOzaki2CRJLI_eq`), and ADP-style slicing in integers
  (`adpCRJI_eq`). -/

open TensorCore

namespace Ozaki.TC

/-! ## Bounded schemes on rational data -/

def tcOzaki2CRBI (p : Model) (cfgs : List (CRTBasis × ℕ)) (b smax : ℕ) :
    List FVal → List FVal → FVal :=
  crIEEE (tcOzaki2CRB p cfgs b smax) (exactSignB (tcSplitK p b) b smax)

def tcOzaki2CRBLI (p : Model) (cfgs : List (CRTBasis × ℕ)) (b smax : ℕ) :
    List FVal → List FVal → FVal :=
  crIEEE (tcOzaki2CRBL p cfgs b smax) (exactSignB (tcSplitK p b) b smax)

def adpCRBI (cfgs : List (ℕ × ℕ)) (smax : ℕ) : List FVal → List FVal → FVal :=
  crIEEE (adpCRB cfgs smax) (exactSignB int8SplitK 6 smax)

def tcOzaki1CRBDZI (p : Model) (b W : ℕ) (ss : List ℕ) (smax : ℕ) :
    List FVal → List FVal → FVal :=
  crIEEE (tcOzaki1CRBDZ p b W ss smax) (exactSignB (tcSplitK p b) b smax)

def tcOzaki1CRBLZI (p : Model) (b W : ℕ) (ss : List ℕ) (smax : ℕ) :
    List FVal → List FVal → FVal :=
  crIEEE (tcOzaki1CRBLZ p b W ss smax) (exactSignB (tcSplitK p b) b smax)

theorem tcOzaki2CRBI_eq {p : Model} {b : ℕ} (hmult : (tcMultiplier p).ExactOn b (2 ^ 24))
    (hb : 2 * b ≤ 24) {cfgs : List (CRTBasis × ℕ)} {smax : ℕ} (hsmax : 2098 < smax * (b + 1))
    {xs ys : List FVal}
    (hcfg : ∀ c ∈ cfgs, c.1.Valid ∧ (∀ m ∈ c.1.moduli, m ≤ 2 ^ (b + 1)) ∧
      2 * xs.length * (2 ^ c.2 * 2 ^ c.2) < c.1.modulus)
    (hx : ∀ a ∈ xs, a.InFormat 53 (-1022) 1023) (hy : ∀ a ∈ ys, a.InFormat 53 (-1022) 1023)
    (hlen : xs.length = ys.length) :
    tcOzaki2CRBI p cfgs b smax xs ys = dotIEEE 53 (-1022) 1023 xs ys :=
  crIEEE_exactSign (by decide) (by decide) (tcSplitK_exactOn hmult hb)
    (fun _ _ hx hy => vanish64 (by omega) hsmax hx hy)
    (fun _ _ hx hy hl1 hl2 => tcOzaki2CRB_eq hmult hb hsmax (by rw [hl1]; exact hcfg) hx hy
      (by rw [hl1, hl2])) hx hy hlen

theorem tcOzaki2CRBLI_eq {p : Model} {b : ℕ} (hmult : (tcMultiplier p).ExactOn b (2 ^ 24))
    (hb : 2 * b ≤ 24) {cfgs : List (CRTBasis × ℕ)} {smax : ℕ} (hsmax : 277 < smax * (b + 1))
    {xs ys : List FVal}
    (hcfg : ∀ c ∈ cfgs, c.1.Valid ∧ (∀ m ∈ c.1.moduli, m ≤ 2 ^ (b + 1)) ∧
      2 * xs.length * (2 ^ c.2 * 2 ^ c.2) < c.1.modulus)
    (hx : ∀ a ∈ xs, a.InFormat 24 (-126) 127) (hy : ∀ a ∈ ys, a.InFormat 24 (-126) 127)
    (hlen : xs.length = ys.length) :
    tcOzaki2CRBLI p cfgs b smax xs ys = dotIEEE 24 (-126) 127 xs ys :=
  crIEEE_exactSign (by decide) (by decide) (tcSplitK_exactOn hmult hb)
    (fun _ _ hx hy => vanish32Q (by omega) hsmax hx hy)
    (fun _ _ hx hy hl1 hl2 => tcOzaki2CRBL_eq hmult hb hsmax (by rw [hl1]; exact hcfg) hx hy
      (by rw [hl1, hl2])) hx hy hlen

theorem adpCRBI_eq {cfgs : List (ℕ × ℕ)} (hcfg : ∀ c ∈ cfgs, 0 < c.1 ∧ ADP.remapFits c.2 c.1 = true)
    {smax : ℕ} (hsmax : 2098 < smax * 7) {xs ys : List FVal}
    (hx : ∀ a ∈ xs, a.InFormat 53 (-1022) 1023) (hy : ∀ a ∈ ys, a.InFormat 53 (-1022) 1023)
    (hlen : xs.length = ys.length) :
    adpCRBI cfgs smax xs ys = dotIEEE 53 (-1022) 1023 xs ys :=
  crIEEE_exactSign (by decide) (by decide) int8SplitK_exactOn
    (fun _ _ hx hy => vanish64 (by decide) (by simpa using hsmax) hx hy)
    (fun _ _ hx hy hl1 hl2 => adpCRB_eq hcfg hsmax hx hy (by rw [hl1, hl2])) hx hy hlen

theorem tcOzaki1CRBDZI_eq {p : Model} {b : ℕ} (hmult : (tcMultiplier p).ExactOn b (2 ^ 24))
    (hb : 2 * b ≤ 24) (W : ℕ) (ss : List ℕ) {smax : ℕ} (hsmax : 2098 < smax * (b + 1))
    {xs ys : List FVal}
    (hx : ∀ a ∈ xs, a.InFormat 53 (-1022) 1023) (hy : ∀ a ∈ ys, a.InFormat 53 (-1022) 1023)
    (hlen : xs.length = ys.length) :
    tcOzaki1CRBDZI p b W ss smax xs ys = dotIEEE 53 (-1022) 1023 xs ys :=
  crIEEE_exactSign (by decide) (by decide) (tcSplitK_exactOn hmult hb)
    (fun _ _ hx hy => vanish64 (by omega) hsmax hx hy)
    (fun _ _ hx hy hl1 hl2 => tcOzaki1CRBDZ_eq hmult hb W ss hsmax hx hy (by rw [hl1, hl2]))
    hx hy hlen

theorem tcOzaki1CRBLZI_eq {p : Model} {b : ℕ} (hmult : (tcMultiplier p).ExactOn b (2 ^ 24))
    (hb : 2 * b ≤ 24) (W : ℕ) (ss : List ℕ) {smax : ℕ} (hsmax : 277 < smax * (b + 1))
    {xs ys : List FVal}
    (hx : ∀ a ∈ xs, a.InFormat 24 (-126) 127) (hy : ∀ a ∈ ys, a.InFormat 24 (-126) 127)
    (hlen : xs.length = ys.length) :
    tcOzaki1CRBLZI p b W ss smax xs ys = dotIEEE 24 (-126) 127 xs ys :=
  crIEEE_exactSign (by decide) (by decide) (tcSplitK_exactOn hmult hb)
    (fun _ _ hx hy => vanish32Q (by omega) hsmax hx hy)
    (fun _ _ hx hy hl1 hl2 => tcOzaki1CRBLZ_eq hmult hb W ss hsmax hx hy (by rw [hl1, hl2]))
    hx hy hlen

/-! ## Integer schemes on stored data -/

def tcOzaki1CRIDI (p : Model) (b W : ℕ) (ss : List ℕ) (smax : ℕ) :
    List IDatum → List IDatum → FVal :=
  crIEEEI (tcOzaki1CRID p b W ss smax) fun x y => (exactSignI (tcSplitK p b) b smax x y).getD 0

def tcOzaki1CRILI (p : Model) (b W : ℕ) (ss : List ℕ) (smax : ℕ) :
    List IDatum → List IDatum → FVal :=
  crIEEEI (tcOzaki1CRIL p b W ss smax) fun x y => (exactSignI (tcSplitK p b) b smax x y).getD 0

def tcOzaki2CRJI (p : Model) (cfgs : List (CRTBasis × ℕ)) (b smax : ℕ) :
    List IDatum → List IDatum → FVal :=
  crIEEEI (tcOzaki2CRJ p cfgs b smax) fun x y => (exactSignI (tcSplitK p b) b smax x y).getD 0

def tcOzaki2CRJLI (p : Model) (cfgs : List (CRTBasis × ℕ)) (b smax : ℕ) :
    List IDatum → List IDatum → FVal :=
  crIEEEI (tcOzaki2CRJL p cfgs b smax) fun x y => (exactSignI (tcSplitK p b) b smax x y).getD 0

def adpCRJI (cfgs : List (ℕ × ℕ)) (smax : ℕ) : List IDatum → List IDatum → FVal :=
  crIEEEI (adpCRJ cfgs smax) fun x y => (exactSignI int8SplitK 6 smax x y).getD 0

/-- **Correctly rounded FP64 by Ozaki-I in integers, with IEEE special values**: for every input of
stored binary64 data, the IEEE correctly rounded dot product of the data. -/
theorem tcOzaki1CRIDI_eq {p : Model} {b : ℕ} (hmult : (tcMultiplier p).ExactOn b (2 ^ 24))
    (hb : 2 * b ≤ 24) (W : ℕ) (ss : List ℕ) {smax : ℕ} (hsmax : 2098 < smax * (b + 1))
    {xs ys : List IDatum}
    (hx : ∀ a ∈ xs, a.InFormat 53 (-1022) 1023) (hy : ∀ a ∈ ys, a.InFormat 53 (-1022) 1023)
    (hlen : xs.length = ys.length) :
    tcOzaki1CRIDI p b W ss smax xs ys =
      dotIEEE 53 (-1022) 1023 (xs.map IDatum.toFVal) (ys.map IDatum.toFVal) :=
  crIEEEI_exactSign (by decide) (by decide) (tcSplitK_exactOn hmult hb)
    (fun _ _ hx hy => vanishInt64 (by omega) hsmax hx hy)
    (fun _ _ hx hy hl1 hl2 => tcOzaki1CRID_eq hmult hb W ss hsmax hx hy (by rw [hl1, hl2]))
    hx hy hlen

theorem tcOzaki1CRILI_eq {p : Model} {b : ℕ} (hmult : (tcMultiplier p).ExactOn b (2 ^ 24))
    (hb : 2 * b ≤ 24) (W : ℕ) (ss : List ℕ) {smax : ℕ} (hsmax : 277 < smax * (b + 1))
    {xs ys : List IDatum}
    (hx : ∀ a ∈ xs, a.InFormat 24 (-126) 127) (hy : ∀ a ∈ ys, a.InFormat 24 (-126) 127)
    (hlen : xs.length = ys.length) :
    tcOzaki1CRILI p b W ss smax xs ys =
      dotIEEE 24 (-126) 127 (xs.map IDatum.toFVal) (ys.map IDatum.toFVal) :=
  crIEEEI_exactSign (by decide) (by decide) (tcSplitK_exactOn hmult hb)
    (fun _ _ hx hy => vanishInt32 (by omega) hsmax hx hy)
    (fun _ _ hx hy hl1 hl2 => tcOzaki1CRIL_eq hmult hb W ss hsmax hx hy (by rw [hl1, hl2]))
    hx hy hlen

theorem tcOzaki2CRJI_eq {p : Model} {b : ℕ} (hmult : (tcMultiplier p).ExactOn b (2 ^ 24))
    (hb : 2 * b ≤ 24) {cfgs : List (CRTBasis × ℕ)} {smax : ℕ} (hsmax : 2098 < smax * (b + 1))
    {xs ys : List IDatum}
    (hcfg : ∀ c ∈ cfgs, c.1.Valid ∧ (∀ m ∈ c.1.moduli, m ≤ 2 ^ (b + 1)) ∧
      2 * xs.length * (2 ^ c.2 * 2 ^ c.2) < c.1.modulus)
    (hx : ∀ a ∈ xs, a.InFormat 53 (-1022) 1023) (hy : ∀ a ∈ ys, a.InFormat 53 (-1022) 1023)
    (hlen : xs.length = ys.length) :
    tcOzaki2CRJI p cfgs b smax xs ys =
      dotIEEE 53 (-1022) 1023 (xs.map IDatum.toFVal) (ys.map IDatum.toFVal) :=
  crIEEEI_exactSign (by decide) (by decide) (tcSplitK_exactOn hmult hb)
    (fun _ _ hx hy => vanishInt64 (by omega) hsmax hx hy)
    (fun _ _ hx hy hl1 hl2 => tcOzaki2CRJ_eq hmult hb hsmax (by rw [hl1]; exact hcfg)
      (binary64_entries hx) (binary64_entries hy) (by rw [hl1, hl2])) hx hy hlen

theorem tcOzaki2CRJLI_eq {p : Model} {b : ℕ} (hmult : (tcMultiplier p).ExactOn b (2 ^ 24))
    (hb : 2 * b ≤ 24) {cfgs : List (CRTBasis × ℕ)} {smax : ℕ} (hsmax : 277 < smax * (b + 1))
    {xs ys : List IDatum}
    (hcfg : ∀ c ∈ cfgs, c.1.Valid ∧ (∀ m ∈ c.1.moduli, m ≤ 2 ^ (b + 1)) ∧
      2 * xs.length * (2 ^ c.2 * 2 ^ c.2) < c.1.modulus)
    (hx : ∀ a ∈ xs, a.InFormat 24 (-126) 127) (hy : ∀ a ∈ ys, a.InFormat 24 (-126) 127)
    (hlen : xs.length = ys.length) :
    tcOzaki2CRJLI p cfgs b smax xs ys =
      dotIEEE 24 (-126) 127 (xs.map IDatum.toFVal) (ys.map IDatum.toFVal) :=
  crIEEEI_exactSign (by decide) (by decide) (tcSplitK_exactOn hmult hb)
    (fun _ _ hx hy => vanishInt32 (by omega) hsmax hx hy)
    (fun _ _ hx hy hl1 hl2 => tcOzaki2CRJL_eq hmult hb hsmax (by rw [hl1]; exact hcfg)
      (binary32_entries hx) (binary32_entries hy) (by rw [hl1, hl2])) hx hy hlen

/-- **ADP's slicing in integers with IEEE special values**: for every input of stored binary64
data, the IEEE correctly rounded dot product of the data. -/
theorem adpCRJI_eq {cfgs : List (ℕ × ℕ)} (hcfg : ∀ c ∈ cfgs, 0 < c.1 ∧ ADP.remapFits c.2 c.1 = true)
    {smax : ℕ} (hsmax : 2098 < smax * 7) {xs ys : List IDatum}
    (hx : ∀ a ∈ xs, a.InFormat 53 (-1022) 1023) (hy : ∀ a ∈ ys, a.InFormat 53 (-1022) 1023)
    (hlen : xs.length = ys.length) :
    adpCRJI cfgs smax xs ys =
      dotIEEE 53 (-1022) 1023 (xs.map IDatum.toFVal) (ys.map IDatum.toFVal) :=
  crIEEEI_exactSign (by decide) (by decide) int8SplitK_exactOn
    (fun _ _ hx hy => vanishInt64 (by decide) (by simpa using hsmax) hx hy)
    (fun _ _ hx hy hl1 hl2 => adpCRJ_eq hcfg hsmax (binary64_entries hx) (binary64_entries hy)
      (by rw [hl1, hl2])) hx hy hlen

end Ozaki.TC
