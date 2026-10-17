import OzakiMC.Ozaki2IntJ
import OzakiMC.Bounded
import OzakiMC.ZeroCheck
import Ozaki.IEEEInt

/-! # The bounded and integer matrix-core schemes with IEEE special values

As on the Tensor Core side (`OzakiTC.IEEEBounded`), on matrix-core blocks with split-K, each meeting
the IEEE specification `dotIEEE` for every input:

* on rational data (`FVal`) with the sign oracle `exactSignB`: Ozaki-II with integer rounding tests
  (`mcOzaki2CRBI_eq`, `mcOzaki2CRBLI_eq`) and the bounded Ozaki-I with the bound that counts only
  nonzero positions (`mcOzaki1CRBDZI_eq`, `mcOzaki1CRBLZI_eq`);
* on stored data (`IDatum`) with the integer sign oracle `exactSignI`: Ozaki-I in integers
  (`mcOzaki1CRIDI_eq`, `mcOzaki1CRILI_eq`) and Ozaki-II in integers (`mcOzaki2CRJI_eq`,
  `mcOzaki2CRJLI_eq`). -/

open MatrixCore

namespace Ozaki.MC

def mcOzaki2CRBI (P : Model) (cfgs : List (CRTBasis × ℕ)) (b smax : ℕ) :
    List FVal → List FVal → FVal :=
  crIEEE (mcOzaki2CRB P cfgs b smax) (exactSignB (mcSplitK P b) b smax)

def mcOzaki2CRBLI (P : Model) (cfgs : List (CRTBasis × ℕ)) (b smax : ℕ) :
    List FVal → List FVal → FVal :=
  crIEEE (mcOzaki2CRBL P cfgs b smax) (exactSignB (mcSplitK P b) b smax)

def mcOzaki1CRBDZI (P : Model) (b W : ℕ) (ss : List ℕ) (smax : ℕ) :
    List FVal → List FVal → FVal :=
  crIEEE (mcOzaki1CRBDZ P b W ss smax) (exactSignB (mcSplitK P b) b smax)

def mcOzaki1CRBLZI (P : Model) (b W : ℕ) (ss : List ℕ) (smax : ℕ) :
    List FVal → List FVal → FVal :=
  crIEEE (mcOzaki1CRBLZ P b W ss smax) (exactSignB (mcSplitK P b) b smax)

def mcOzaki1CRIDI (P : Model) (b W : ℕ) (ss : List ℕ) (smax : ℕ) :
    List IDatum → List IDatum → FVal :=
  crIEEEI (mcOzaki1CRID P b W ss smax) fun x y => (exactSignI (mcSplitK P b) b smax x y).getD 0

def mcOzaki1CRILI (P : Model) (b W : ℕ) (ss : List ℕ) (smax : ℕ) :
    List IDatum → List IDatum → FVal :=
  crIEEEI (mcOzaki1CRIL P b W ss smax) fun x y => (exactSignI (mcSplitK P b) b smax x y).getD 0

def mcOzaki2CRJI (P : Model) (cfgs : List (CRTBasis × ℕ)) (b smax : ℕ) :
    List IDatum → List IDatum → FVal :=
  crIEEEI (mcOzaki2CRJ P cfgs b smax) fun x y => (exactSignI (mcSplitK P b) b smax x y).getD 0

def mcOzaki2CRJLI (P : Model) (cfgs : List (CRTBasis × ℕ)) (b smax : ℕ) :
    List IDatum → List IDatum → FVal :=
  crIEEEI (mcOzaki2CRJL P cfgs b smax) fun x y => (exactSignI (mcSplitK P b) b smax x y).getD 0

theorem mcOzaki2CRBI_eq {P : Model} {b : ℕ} (hP : ExactMultiplier P b) (hb : 2 * b ≤ 24)
    {cfgs : List (CRTBasis × ℕ)} {smax : ℕ} (hsmax : 2098 < smax * (b + 1)) {xs ys : List FVal}
    (hcfg : ∀ c ∈ cfgs, c.1.Valid ∧ (∀ m ∈ c.1.moduli, m ≤ 2 ^ (b + 1)) ∧
      2 * xs.length * (2 ^ c.2 * 2 ^ c.2) < c.1.modulus)
    (hx : ∀ a ∈ xs, a.InFormat 53 (-1022) 1023) (hy : ∀ a ∈ ys, a.InFormat 53 (-1022) 1023)
    (hlen : xs.length = ys.length) :
    mcOzaki2CRBI P cfgs b smax xs ys = dotIEEE 53 (-1022) 1023 xs ys :=
  crIEEE_exactSign (by decide) (by decide) (mcSplitK_exactOn hP hb)
    (fun _ _ hx hy => vanish64 (by omega) hsmax hx hy)
    (fun _ _ hx hy hl1 hl2 => mcOzaki2CRB_eq hP hb hsmax (by rw [hl1]; exact hcfg) hx hy
      (by rw [hl1, hl2])) hx hy hlen

theorem mcOzaki2CRBLI_eq {P : Model} {b : ℕ} (hP : ExactMultiplier P b) (hb : 2 * b ≤ 24)
    {cfgs : List (CRTBasis × ℕ)} {smax : ℕ} (hsmax : 277 < smax * (b + 1)) {xs ys : List FVal}
    (hcfg : ∀ c ∈ cfgs, c.1.Valid ∧ (∀ m ∈ c.1.moduli, m ≤ 2 ^ (b + 1)) ∧
      2 * xs.length * (2 ^ c.2 * 2 ^ c.2) < c.1.modulus)
    (hx : ∀ a ∈ xs, a.InFormat 24 (-126) 127) (hy : ∀ a ∈ ys, a.InFormat 24 (-126) 127)
    (hlen : xs.length = ys.length) :
    mcOzaki2CRBLI P cfgs b smax xs ys = dotIEEE 24 (-126) 127 xs ys :=
  crIEEE_exactSign (by decide) (by decide) (mcSplitK_exactOn hP hb)
    (fun _ _ hx hy => vanish32Q (by omega) hsmax hx hy)
    (fun _ _ hx hy hl1 hl2 => mcOzaki2CRBL_eq hP hb hsmax (by rw [hl1]; exact hcfg) hx hy
      (by rw [hl1, hl2])) hx hy hlen

theorem mcOzaki1CRBDZI_eq {P : Model} {b : ℕ} (hP : ExactMultiplier P b) (hb : 2 * b ≤ 24) (W : ℕ)
    (ss : List ℕ) {smax : ℕ} (hsmax : 2098 < smax * (b + 1)) {xs ys : List FVal}
    (hx : ∀ a ∈ xs, a.InFormat 53 (-1022) 1023) (hy : ∀ a ∈ ys, a.InFormat 53 (-1022) 1023)
    (hlen : xs.length = ys.length) :
    mcOzaki1CRBDZI P b W ss smax xs ys = dotIEEE 53 (-1022) 1023 xs ys :=
  crIEEE_exactSign (by decide) (by decide) (mcSplitK_exactOn hP hb)
    (fun _ _ hx hy => vanish64 (by omega) hsmax hx hy)
    (fun _ _ hx hy hl1 hl2 => mcOzaki1CRBDZ_eq hP hb W ss hsmax hx hy (by rw [hl1, hl2]))
    hx hy hlen

theorem mcOzaki1CRBLZI_eq {P : Model} {b : ℕ} (hP : ExactMultiplier P b) (hb : 2 * b ≤ 24) (W : ℕ)
    (ss : List ℕ) {smax : ℕ} (hsmax : 277 < smax * (b + 1)) {xs ys : List FVal}
    (hx : ∀ a ∈ xs, a.InFormat 24 (-126) 127) (hy : ∀ a ∈ ys, a.InFormat 24 (-126) 127)
    (hlen : xs.length = ys.length) :
    mcOzaki1CRBLZI P b W ss smax xs ys = dotIEEE 24 (-126) 127 xs ys :=
  crIEEE_exactSign (by decide) (by decide) (mcSplitK_exactOn hP hb)
    (fun _ _ hx hy => vanish32Q (by omega) hsmax hx hy)
    (fun _ _ hx hy hl1 hl2 => mcOzaki1CRBLZ_eq hP hb W ss hsmax hx hy (by rw [hl1, hl2]))
    hx hy hlen

theorem mcOzaki1CRIDI_eq {P : Model} {b : ℕ} (hP : ExactMultiplier P b) (hb : 2 * b ≤ 24) (W : ℕ)
    (ss : List ℕ) {smax : ℕ} (hsmax : 2098 < smax * (b + 1)) {xs ys : List IDatum}
    (hx : ∀ a ∈ xs, a.InFormat 53 (-1022) 1023) (hy : ∀ a ∈ ys, a.InFormat 53 (-1022) 1023)
    (hlen : xs.length = ys.length) :
    mcOzaki1CRIDI P b W ss smax xs ys =
      dotIEEE 53 (-1022) 1023 (xs.map IDatum.toFVal) (ys.map IDatum.toFVal) :=
  crIEEEI_exactSign (by decide) (by decide) (mcSplitK_exactOn hP hb)
    (fun _ _ hx hy => vanishInt64 (by omega) hsmax hx hy)
    (fun _ _ hx hy hl1 hl2 => mcOzaki1CRID_eq hP hb W ss hsmax hx hy (by rw [hl1, hl2]))
    hx hy hlen

theorem mcOzaki1CRILI_eq {P : Model} {b : ℕ} (hP : ExactMultiplier P b) (hb : 2 * b ≤ 24) (W : ℕ)
    (ss : List ℕ) {smax : ℕ} (hsmax : 277 < smax * (b + 1)) {xs ys : List IDatum}
    (hx : ∀ a ∈ xs, a.InFormat 24 (-126) 127) (hy : ∀ a ∈ ys, a.InFormat 24 (-126) 127)
    (hlen : xs.length = ys.length) :
    mcOzaki1CRILI P b W ss smax xs ys =
      dotIEEE 24 (-126) 127 (xs.map IDatum.toFVal) (ys.map IDatum.toFVal) :=
  crIEEEI_exactSign (by decide) (by decide) (mcSplitK_exactOn hP hb)
    (fun _ _ hx hy => vanishInt32 (by omega) hsmax hx hy)
    (fun _ _ hx hy hl1 hl2 => mcOzaki1CRIL_eq hP hb W ss hsmax hx hy (by rw [hl1, hl2]))
    hx hy hlen

theorem mcOzaki2CRJI_eq {P : Model} {b : ℕ} (hP : ExactMultiplier P b) (hb : 2 * b ≤ 24)
    {cfgs : List (CRTBasis × ℕ)} {smax : ℕ} (hsmax : 2098 < smax * (b + 1)) {xs ys : List IDatum}
    (hcfg : ∀ c ∈ cfgs, c.1.Valid ∧ (∀ m ∈ c.1.moduli, m ≤ 2 ^ (b + 1)) ∧
      2 * xs.length * (2 ^ c.2 * 2 ^ c.2) < c.1.modulus)
    (hx : ∀ a ∈ xs, a.InFormat 53 (-1022) 1023) (hy : ∀ a ∈ ys, a.InFormat 53 (-1022) 1023)
    (hlen : xs.length = ys.length) :
    mcOzaki2CRJI P cfgs b smax xs ys =
      dotIEEE 53 (-1022) 1023 (xs.map IDatum.toFVal) (ys.map IDatum.toFVal) :=
  crIEEEI_exactSign (by decide) (by decide) (mcSplitK_exactOn hP hb)
    (fun _ _ hx hy => vanishInt64 (by omega) hsmax hx hy)
    (fun _ _ hx hy hl1 hl2 => mcOzaki2CRJ_eq hP hb hsmax (by rw [hl1]; exact hcfg)
      (binary64_entries hx) (binary64_entries hy) (by rw [hl1, hl2])) hx hy hlen

theorem mcOzaki2CRJLI_eq {P : Model} {b : ℕ} (hP : ExactMultiplier P b) (hb : 2 * b ≤ 24)
    {cfgs : List (CRTBasis × ℕ)} {smax : ℕ} (hsmax : 277 < smax * (b + 1)) {xs ys : List IDatum}
    (hcfg : ∀ c ∈ cfgs, c.1.Valid ∧ (∀ m ∈ c.1.moduli, m ≤ 2 ^ (b + 1)) ∧
      2 * xs.length * (2 ^ c.2 * 2 ^ c.2) < c.1.modulus)
    (hx : ∀ a ∈ xs, a.InFormat 24 (-126) 127) (hy : ∀ a ∈ ys, a.InFormat 24 (-126) 127)
    (hlen : xs.length = ys.length) :
    mcOzaki2CRJLI P cfgs b smax xs ys =
      dotIEEE 24 (-126) 127 (xs.map IDatum.toFVal) (ys.map IDatum.toFVal) :=
  crIEEEI_exactSign (by decide) (by decide) (mcSplitK_exactOn hP hb)
    (fun _ _ hx hy => vanishInt32 (by omega) hsmax hx hy)
    (fun _ _ hx hy hl1 hl2 => mcOzaki2CRJL_eq hP hb hsmax (by rw [hl1]; exact hcfg)
      (binary32_entries hx) (binary32_entries hy) (by rw [hl1, hl2])) hx hy hlen

end Ozaki.MC
