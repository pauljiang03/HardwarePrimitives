import OzakiTC.ADPFix
import Ozaki.IEEEDot

/-! # The Tensor Core schemes with IEEE special values

Every correctly rounded scheme of the Tensor Core instantiation, on vectors of IEEE data (`FVal`:
signed zeros, `±Inf`, NaN), meets the IEEE specification `dotIEEE` for every input: NaN for NaN
inputs, `Inf · 0` and `+Inf − Inf`, `±Inf` for infinite products and for overflow, and the IEEE
sign of a zero result. Each is the finite scheme wrapped by `crIEEE`, with the sign of `x · y`, when
a zero result or an overflow needs it, from the exact path's slice products on the same engine
(`exactSignB`):

* Ozaki-I in FP64 and binary32, with the exact sum or a window accumulator (`tcOzaki1CRDI_eq`,
  `tcOzaki1CRLI_eq`, `tcOzaki1CRDWI_eq`, `tcOzaki1CRLWI_eq`);
* Ozaki-II in FP64 and binary32 (`tcOzaki2CRDI_eq`, `tcOzaki2CRLI_eq`);
* ADP-style slicing on the INT8 engine (`adpCREI_eq`).

The plain schemes with special values (`tcOzaki1I`, `tcOzaki2I`, `tcOzaki1DI`) return the rational
schemes' results whenever those are finite (`tcOzaki1I_fin`, `tcOzaki2I_fin`, `tcOzaki1DI_fin`). -/

open TensorCore

namespace Ozaki.TC

/-! ## Correctly rounded -/

/-- Correctly rounded FP64 by Ozaki-I on Tensor Core blocks, with IEEE special values. -/
def tcOzaki1CRDI (p : Model) (b : ℕ) (ss : List ℕ) (smax : ℕ) : List FVal → List FVal → FVal :=
  crIEEE (tcOzaki1CRD p b ss smax) (exactSignB (tcSplitK p b) b smax)

/-- Correctly rounded binary32 by Ozaki-I on Tensor Core blocks, with IEEE special values. -/
def tcOzaki1CRLI (p : Model) (b : ℕ) (ss : List ℕ) (smax : ℕ) : List FVal → List FVal → FVal :=
  crIEEE (tcOzaki1CRL p b ss smax) (exactSignB (tcSplitK p b) b smax)

/-- The same with a `W`-bit window accumulator for the check. -/
def tcOzaki1CRDWI (p : Model) (b W : ℕ) (ss : List ℕ) (smax : ℕ) :
    List FVal → List FVal → FVal :=
  crIEEE (tcOzaki1CRDW p b W ss smax) (exactSignB (tcSplitK p b) b smax)

def tcOzaki1CRLWI (p : Model) (b W : ℕ) (ss : List ℕ) (smax : ℕ) :
    List FVal → List FVal → FVal :=
  crIEEE (tcOzaki1CRLW p b W ss smax) (exactSignB (tcSplitK p b) b smax)

/-- Correctly rounded FP64 and binary32 by Ozaki-II on Tensor Core blocks, with IEEE special
values. -/
def tcOzaki2CRDI (p : Model) (cfgs : List (CRTBasis × ℕ)) (b smax : ℕ) :
    List FVal → List FVal → FVal :=
  crIEEE (tcOzaki2CRD p cfgs b smax) (exactSignB (tcSplitK p b) b smax)

def tcOzaki2CRLI (p : Model) (cfgs : List (CRTBasis × ℕ)) (b smax : ℕ) :
    List FVal → List FVal → FVal :=
  crIEEE (tcOzaki2CRL p cfgs b smax) (exactSignB (tcSplitK p b) b smax)

/-- Correctly rounded ADP-style slicing on the INT8 engine, with IEEE special values. -/
def adpCREI (cfgs : List (ℕ × ℕ)) (smax : ℕ) : List FVal → List FVal → FVal :=
  crIEEE (adpCRE cfgs smax) (exactSignB int8SplitK 6 smax)

/-- **Correctly rounded FP64 GEMM on Tensor Cores with IEEE special values**: for every input of
binary64 data, the IEEE correctly rounded dot product. -/
theorem tcOzaki1CRDI_eq {p : Model} {b : ℕ} (hmult : (tcMultiplier p).ExactOn b (2 ^ 24))
    (hb : 2 * b ≤ 24) (ss : List ℕ) {smax : ℕ} (hsmax : 2098 < smax * (b + 1)) {xs ys : List FVal}
    (hx : ∀ a ∈ xs, a.InFormat 53 (-1022) 1023) (hy : ∀ a ∈ ys, a.InFormat 53 (-1022) 1023)
    (hlen : xs.length = ys.length) :
    tcOzaki1CRDI p b ss smax xs ys = dotIEEE 53 (-1022) 1023 xs ys :=
  crIEEE_exactSign (by decide) (by decide) (tcSplitK_exactOn hmult hb)
    (fun _ _ hx hy => vanish64 (by omega) hsmax hx hy)
    (fun _ _ hx hy hl1 hl2 => tcOzaki1CRD_eq hmult hb ss hsmax hx hy (by rw [hl1, hl2])) hx hy hlen

theorem tcOzaki1CRLI_eq {p : Model} {b : ℕ} (hmult : (tcMultiplier p).ExactOn b (2 ^ 24))
    (hb : 2 * b ≤ 24) (ss : List ℕ) {smax : ℕ} (hsmax : 277 < smax * (b + 1)) {xs ys : List FVal}
    (hx : ∀ a ∈ xs, a.InFormat 24 (-126) 127) (hy : ∀ a ∈ ys, a.InFormat 24 (-126) 127)
    (hlen : xs.length = ys.length) :
    tcOzaki1CRLI p b ss smax xs ys = dotIEEE 24 (-126) 127 xs ys :=
  crIEEE_exactSign (by decide) (by decide) (tcSplitK_exactOn hmult hb)
    (fun _ _ hx hy => vanish32Q (by omega) hsmax hx hy)
    (fun _ _ hx hy hl1 hl2 => tcOzaki1CRL_eq hmult hb ss hsmax hx hy (by rw [hl1, hl2])) hx hy hlen

theorem tcOzaki1CRDWI_eq {p : Model} {b : ℕ} (hmult : (tcMultiplier p).ExactOn b (2 ^ 24))
    (hb : 2 * b ≤ 24) (W : ℕ) (ss : List ℕ) {smax : ℕ} (hsmax : 2098 < smax * (b + 1))
    {xs ys : List FVal}
    (hx : ∀ a ∈ xs, a.InFormat 53 (-1022) 1023) (hy : ∀ a ∈ ys, a.InFormat 53 (-1022) 1023)
    (hlen : xs.length = ys.length) :
    tcOzaki1CRDWI p b W ss smax xs ys = dotIEEE 53 (-1022) 1023 xs ys :=
  crIEEE_exactSign (by decide) (by decide) (tcSplitK_exactOn hmult hb)
    (fun _ _ hx hy => vanish64 (by omega) hsmax hx hy)
    (fun _ _ hx hy hl1 hl2 => tcOzaki1CRDW_eq hmult hb W ss hsmax hx hy (by rw [hl1, hl2]))
    hx hy hlen

theorem tcOzaki1CRLWI_eq {p : Model} {b : ℕ} (hmult : (tcMultiplier p).ExactOn b (2 ^ 24))
    (hb : 2 * b ≤ 24) (W : ℕ) (ss : List ℕ) {smax : ℕ} (hsmax : 277 < smax * (b + 1))
    {xs ys : List FVal}
    (hx : ∀ a ∈ xs, a.InFormat 24 (-126) 127) (hy : ∀ a ∈ ys, a.InFormat 24 (-126) 127)
    (hlen : xs.length = ys.length) :
    tcOzaki1CRLWI p b W ss smax xs ys = dotIEEE 24 (-126) 127 xs ys :=
  crIEEE_exactSign (by decide) (by decide) (tcSplitK_exactOn hmult hb)
    (fun _ _ hx hy => vanish32Q (by omega) hsmax hx hy)
    (fun _ _ hx hy hl1 hl2 => tcOzaki1CRLW_eq hmult hb W ss hsmax hx hy (by rw [hl1, hl2]))
    hx hy hlen

/-- **Correctly rounded FP64 GEMM by Ozaki-II with IEEE special values.** -/
theorem tcOzaki2CRDI_eq {p : Model} {b : ℕ} (hmult : (tcMultiplier p).ExactOn b (2 ^ 24))
    (hb : 2 * b ≤ 24) {cfgs : List (CRTBasis × ℕ)} {smax : ℕ} (hsmax : 2098 < smax * (b + 1))
    {xs ys : List FVal}
    (hcfg : ∀ c ∈ cfgs, c.1.Valid ∧ (∀ m ∈ c.1.moduli, m ≤ 2 ^ (b + 1)) ∧
      2 * xs.length * (2 ^ c.2 * 2 ^ c.2) < c.1.modulus)
    (hx : ∀ a ∈ xs, a.InFormat 53 (-1022) 1023) (hy : ∀ a ∈ ys, a.InFormat 53 (-1022) 1023)
    (hlen : xs.length = ys.length) :
    tcOzaki2CRDI p cfgs b smax xs ys = dotIEEE 53 (-1022) 1023 xs ys :=
  crIEEE_exactSign (by decide) (by decide) (tcSplitK_exactOn hmult hb)
    (fun _ _ hx hy => vanish64 (by omega) hsmax hx hy)
    (fun _ _ hx hy hl1 hl2 => tcOzaki2CRD_eq hmult hb hsmax (by rw [hl1]; exact hcfg) hx hy
      (by rw [hl1, hl2]))
    hx hy hlen

theorem tcOzaki2CRLI_eq {p : Model} {b : ℕ} (hmult : (tcMultiplier p).ExactOn b (2 ^ 24))
    (hb : 2 * b ≤ 24) {cfgs : List (CRTBasis × ℕ)} {smax : ℕ} (hsmax : 277 < smax * (b + 1))
    {xs ys : List FVal}
    (hcfg : ∀ c ∈ cfgs, c.1.Valid ∧ (∀ m ∈ c.1.moduli, m ≤ 2 ^ (b + 1)) ∧
      2 * xs.length * (2 ^ c.2 * 2 ^ c.2) < c.1.modulus)
    (hx : ∀ a ∈ xs, a.InFormat 24 (-126) 127) (hy : ∀ a ∈ ys, a.InFormat 24 (-126) 127)
    (hlen : xs.length = ys.length) :
    tcOzaki2CRLI p cfgs b smax xs ys = dotIEEE 24 (-126) 127 xs ys :=
  crIEEE_exactSign (by decide) (by decide) (tcSplitK_exactOn hmult hb)
    (fun _ _ hx hy => vanish32Q (by omega) hsmax hx hy)
    (fun _ _ hx hy hl1 hl2 => tcOzaki2CRL_eq hmult hb hsmax (by rw [hl1]; exact hcfg) hx hy
      (by rw [hl1, hl2]))
    hx hy hlen

/-- **ADP-style correctly rounded slicing with IEEE special values**, every product on the INT8
engine, for binary64 data of any length. -/
theorem adpCREI_eq {cfgs : List (ℕ × ℕ)} (hcfg : ∀ c ∈ cfgs, 0 < c.1 ∧ ADP.remapFits c.2 c.1 = true)
    {smax : ℕ} (hsmax : 2098 < smax * 7) {xs ys : List FVal}
    (hx : ∀ a ∈ xs, a.InFormat 53 (-1022) 1023) (hy : ∀ a ∈ ys, a.InFormat 53 (-1022) 1023)
    (hlen : xs.length = ys.length) :
    adpCREI cfgs smax xs ys = dotIEEE 53 (-1022) 1023 xs ys :=
  crIEEE_exactSign (by decide) (by decide) int8SplitK_exactOn
    (fun _ _ hx hy => vanish64 (by decide) hsmax hx hy)
    (fun _ _ hx hy hl1 hl2 => adpCRE_eq hcfg hsmax hx hy (by rw [hl1, hl2])) hx hy hlen

/-- FP64 on V100 fp16 with IEEE special values: correctly rounded for every input. -/
theorem v100_fp64CRIEEE (ss : List ℕ) {xs ys : List FVal}
    (hx : ∀ a ∈ xs, a.InFormat 53 (-1022) 1023) (hy : ∀ a ∈ ys, a.InFormat 53 (-1022) 1023)
    (hlen : xs.length = ys.length) :
    tcOzaki1CRDI v100F16F32 11 ss 175 xs ys = dotIEEE 53 (-1022) 1023 xs ys :=
  tcOzaki1CRDI_eq v100_exactOn (by decide) ss (by decide) hx hy hlen

/-! ## The plain schemes -/

/-- Ozaki-I on a Tensor Core path with IEEE special values: binary32 IEEE additions. -/
def tcOzaki1I (p : Model) (b s : ℕ) : List FVal → List FVal → FVal :=
  ozaki1IEEE (tcMultiplier p) 24 (-126) 127 b s

/-- Ozaki-II on a Tensor Core path with IEEE special values: one binary32 IEEE rounding. -/
def tcOzaki2I (p : Model) (B : CRTBasis) (P : ℕ) : List FVal → List FVal → FVal :=
  ozaki2IEEE (tcMultiplier p) 24 (-126) 127 B P

/-- FP64 emulation by Ozaki-I with IEEE special values: binary64 IEEE additions. -/
def tcOzaki1DI (p : Model) (b s : ℕ) : List FVal → List FVal → FVal :=
  ozaki1IEEE (tcSplitK p b) 53 (-1022) 1023 b s

/-- **Plain Ozaki-I with special values returns Ozaki-I's result** whenever it is finite. -/
theorem tcOzaki1I_fin {p : Model} {b s : ℕ} {sx sy : List Signed} {v : ℚ}
    (h : tcOzaki1 p b s (vals sx) (vals sy) = some v) :
    ∃ n, tcOzaki1I p b s (sx.map .fin) (sy.map .fin) = .fin ⟨v, n⟩ :=
  ozaki1IEEE_fin h

theorem tcOzaki2I_fin {p : Model} {B : CRTBasis} {P : ℕ} {sx sy : List Signed} {v : ℚ}
    (h : tcOzaki2 p B P (vals sx) (vals sy) = some v) :
    ∃ n, tcOzaki2I p B P (sx.map .fin) (sy.map .fin) = .fin ⟨v, n⟩ :=
  ozaki2IEEE_fin h

theorem tcOzaki1DI_fin {p : Model} {b s : ℕ} {sx sy : List Signed} {v : ℚ}
    (h : tcOzaki1D p b s (vals sx) (vals sy) = some v) :
    ∃ n, tcOzaki1DI p b s (sx.map .fin) (sy.map .fin) = .fin ⟨v, n⟩ :=
  ozaki1IEEE_fin h

end Ozaki.TC
