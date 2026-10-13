import OzakiMC.LongDot
import OzakiMC.IEEE
import Ozaki.IEEEDot

/-! # The matrix-core schemes with IEEE special values

The correctly rounded schemes of the AMD instantiation on vectors of IEEE data (`FVal`), wrapped by
`crIEEE` with the exact fallback's sign on the same matrix multiplier (`exactSignB`), meet the IEEE
specification `dotIEEE` for every input, in FP64 and binary32, with the exact sum or a truncated
sum, for Ozaki-I and Ozaki-II (`mcOzaki1CRDI_eq`, `mcOzaki1CRLI_eq`, `mcOzaki1CRDWI_eq`,
`mcOzaki1CRLWI_eq`, `mcOzaki2CRDI_eq`, `mcOzaki2CRLI_eq`). They are the same functions of the inputs
as on the Tensor Core model. FP64 emulation by plain Ozaki-I with special values returns the
rational scheme's result whenever it is finite (`mcOzaki1DI_fin`); so do binary32 Ozaki-I and
Ozaki-II (`mcOzaki1I_fin`, `mcOzaki2I_fin`), whose MatrixCore rounding is IEEE's
(`round32Value_eq_rne32Q`). -/

open MatrixCore

namespace Ozaki.MC

def mcOzaki1CRDI (P : Model) (b : ℕ) (ss : List ℕ) (smax : ℕ) : List FVal → List FVal → FVal :=
  crIEEE (mcOzaki1CRD P b ss smax) (exactSignB (mcSplitK P b) b smax)

def mcOzaki1CRLI (P : Model) (b : ℕ) (ss : List ℕ) (smax : ℕ) : List FVal → List FVal → FVal :=
  crIEEE (mcOzaki1CRL P b ss smax) (exactSignB (mcSplitK P b) b smax)

def mcOzaki1CRDWI (P : Model) (b W : ℕ) (ss : List ℕ) (smax : ℕ) :
    List FVal → List FVal → FVal :=
  crIEEE (mcOzaki1CRDW P b W ss smax) (exactSignB (mcSplitK P b) b smax)

def mcOzaki1CRLWI (P : Model) (b W : ℕ) (ss : List ℕ) (smax : ℕ) :
    List FVal → List FVal → FVal :=
  crIEEE (mcOzaki1CRLW P b W ss smax) (exactSignB (mcSplitK P b) b smax)

def mcOzaki2CRDI (P : Model) (cfgs : List (CRTBasis × ℕ)) (b smax : ℕ) :
    List FVal → List FVal → FVal :=
  crIEEE (mcOzaki2CRD P cfgs b smax) (exactSignB (mcSplitK P b) b smax)

def mcOzaki2CRLI (P : Model) (cfgs : List (CRTBasis × ℕ)) (b smax : ℕ) :
    List FVal → List FVal → FVal :=
  crIEEE (mcOzaki2CRL P cfgs b smax) (exactSignB (mcSplitK P b) b smax)

/-- **Correctly rounded FP64 GEMM on AMD matrix cores with IEEE special values.** -/
theorem mcOzaki1CRDI_eq {P : Model} {b : ℕ} (hP : ExactMultiplier P b) (hb : 2 * b ≤ 24)
    (ss : List ℕ) {smax : ℕ} (hsmax : 2098 < smax * (b + 1)) {xs ys : List FVal}
    (hx : ∀ a ∈ xs, a.InFormat 53 (-1022) 1023) (hy : ∀ a ∈ ys, a.InFormat 53 (-1022) 1023)
    (hlen : xs.length = ys.length) :
    mcOzaki1CRDI P b ss smax xs ys = dotIEEE 53 (-1022) 1023 xs ys :=
  crIEEE_exactSign (by decide) (by decide) (mcSplitK_exactOn hP hb)
    (fun _ _ hx hy => vanish64 (by omega) hsmax hx hy)
    (fun _ _ hx hy hl1 hl2 => mcOzaki1CRD_eq hP hb ss hsmax hx hy (by rw [hl1, hl2])) hx hy hlen

theorem mcOzaki1CRLI_eq {P : Model} {b : ℕ} (hP : ExactMultiplier P b) (hb : 2 * b ≤ 24)
    (ss : List ℕ) {smax : ℕ} (hsmax : 277 < smax * (b + 1)) {xs ys : List FVal}
    (hx : ∀ a ∈ xs, a.InFormat 24 (-126) 127) (hy : ∀ a ∈ ys, a.InFormat 24 (-126) 127)
    (hlen : xs.length = ys.length) :
    mcOzaki1CRLI P b ss smax xs ys = dotIEEE 24 (-126) 127 xs ys :=
  crIEEE_exactSign (by decide) (by decide) (mcSplitK_exactOn hP hb)
    (fun _ _ hx hy => vanish32Q (by omega) hsmax hx hy)
    (fun _ _ hx hy hl1 hl2 => mcOzaki1CRL_eq hP hb ss hsmax hx hy (by rw [hl1, hl2])) hx hy hlen

theorem mcOzaki1CRDWI_eq {P : Model} {b : ℕ} (hP : ExactMultiplier P b) (hb : 2 * b ≤ 24) (W : ℕ)
    (ss : List ℕ) {smax : ℕ} (hsmax : 2098 < smax * (b + 1)) {xs ys : List FVal}
    (hx : ∀ a ∈ xs, a.InFormat 53 (-1022) 1023) (hy : ∀ a ∈ ys, a.InFormat 53 (-1022) 1023)
    (hlen : xs.length = ys.length) :
    mcOzaki1CRDWI P b W ss smax xs ys = dotIEEE 53 (-1022) 1023 xs ys :=
  crIEEE_exactSign (by decide) (by decide) (mcSplitK_exactOn hP hb)
    (fun _ _ hx hy => vanish64 (by omega) hsmax hx hy)
    (fun _ _ hx hy hl1 hl2 => mcOzaki1CRDW_eq hP hb W ss hsmax hx hy (by rw [hl1, hl2]))
    hx hy hlen

theorem mcOzaki1CRLWI_eq {P : Model} {b : ℕ} (hP : ExactMultiplier P b) (hb : 2 * b ≤ 24) (W : ℕ)
    (ss : List ℕ) {smax : ℕ} (hsmax : 277 < smax * (b + 1)) {xs ys : List FVal}
    (hx : ∀ a ∈ xs, a.InFormat 24 (-126) 127) (hy : ∀ a ∈ ys, a.InFormat 24 (-126) 127)
    (hlen : xs.length = ys.length) :
    mcOzaki1CRLWI P b W ss smax xs ys = dotIEEE 24 (-126) 127 xs ys :=
  crIEEE_exactSign (by decide) (by decide) (mcSplitK_exactOn hP hb)
    (fun _ _ hx hy => vanish32Q (by omega) hsmax hx hy)
    (fun _ _ hx hy hl1 hl2 => mcOzaki1CRLW_eq hP hb W ss hsmax hx hy (by rw [hl1, hl2]))
    hx hy hlen

theorem mcOzaki2CRDI_eq {P : Model} {b : ℕ} (hP : ExactMultiplier P b) (hb : 2 * b ≤ 24)
    {cfgs : List (CRTBasis × ℕ)} {smax : ℕ} (hsmax : 2098 < smax * (b + 1)) {xs ys : List FVal}
    (hcfg : ∀ c ∈ cfgs, c.1.Valid ∧ (∀ m ∈ c.1.moduli, m ≤ 2 ^ (b + 1)) ∧
      2 * xs.length * (2 ^ c.2 * 2 ^ c.2) < c.1.modulus)
    (hx : ∀ a ∈ xs, a.InFormat 53 (-1022) 1023) (hy : ∀ a ∈ ys, a.InFormat 53 (-1022) 1023)
    (hlen : xs.length = ys.length) :
    mcOzaki2CRDI P cfgs b smax xs ys = dotIEEE 53 (-1022) 1023 xs ys :=
  crIEEE_exactSign (by decide) (by decide) (mcSplitK_exactOn hP hb)
    (fun _ _ hx hy => vanish64 (by omega) hsmax hx hy)
    (fun _ _ hx hy hl1 hl2 => mcOzaki2CRD_eq hP hb hsmax (by rw [hl1]; exact hcfg) hx hy
      (by rw [hl1, hl2]))
    hx hy hlen

theorem mcOzaki2CRLI_eq {P : Model} {b : ℕ} (hP : ExactMultiplier P b) (hb : 2 * b ≤ 24)
    {cfgs : List (CRTBasis × ℕ)} {smax : ℕ} (hsmax : 277 < smax * (b + 1)) {xs ys : List FVal}
    (hcfg : ∀ c ∈ cfgs, c.1.Valid ∧ (∀ m ∈ c.1.moduli, m ≤ 2 ^ (b + 1)) ∧
      2 * xs.length * (2 ^ c.2 * 2 ^ c.2) < c.1.modulus)
    (hx : ∀ a ∈ xs, a.InFormat 24 (-126) 127) (hy : ∀ a ∈ ys, a.InFormat 24 (-126) 127)
    (hlen : xs.length = ys.length) :
    mcOzaki2CRLI P cfgs b smax xs ys = dotIEEE 24 (-126) 127 xs ys :=
  crIEEE_exactSign (by decide) (by decide) (mcSplitK_exactOn hP hb)
    (fun _ _ hx hy => vanish32Q (by omega) hsmax hx hy)
    (fun _ _ hx hy hl1 hl2 => mcOzaki2CRL_eq hP hb hsmax (by rw [hl1]; exact hcfg) hx hy
      (by rw [hl1, hl2]))
    hx hy hlen

/-- FP64 emulation by Ozaki-I on matrix-core blocks with IEEE special values: binary64 IEEE
additions. -/
def mcOzaki1DI (P : Model) (b s : ℕ) : List FVal → List FVal → FVal :=
  ozaki1IEEE (mcSplitK P b) 53 (-1022) 1023 b s

theorem mcOzaki1DI_fin {P : Model} {b s : ℕ} {sx sy : List Signed} {v : ℚ}
    (h : mcOzaki1D P b s (vals sx) (vals sy) = some v) :
    ∃ n, mcOzaki1DI P b s (sx.map .fin) (sy.map .fin) = .fin ⟨v, n⟩ :=
  ozaki1IEEE_fin h

/-- MatrixCore's binary32 addition is IEEE's. -/
theorem fp32Add_eq_rne32Q : fp32Add = addOfRound rne32Q := by
  funext a b
  exact round32Value_eq_rne32Q (a + b)

/-- Ozaki-I on a matrix-core variant with IEEE special values: binary32 IEEE additions. -/
def mcOzaki1I (P : Model) (b s : ℕ) : List FVal → List FVal → FVal :=
  ozaki1IEEE (mcMultiplier P) 24 (-126) 127 b s

/-- Ozaki-II on a matrix-core variant with IEEE special values: one binary32 IEEE rounding. -/
def mcOzaki2I (P : Model) (B : CRTBasis) (Pb : ℕ) : List FVal → List FVal → FVal :=
  ozaki2IEEE (mcMultiplier P) 24 (-126) 127 B Pb

/-- **Plain binary32 Ozaki-I with special values returns Ozaki-I's result** whenever it is finite. -/
theorem mcOzaki1I_fin {P : Model} {b s : ℕ} {sx sy : List Signed} {v : ℚ}
    (h : mcOzaki1 P b s (vals sx) (vals sy) = some v) :
    ∃ n, mcOzaki1I P b s (sx.map .fin) (sy.map .fin) = .fin ⟨v, n⟩ := by
  unfold mcOzaki1 at h
  rw [fp32Add_eq_rne32Q] at h
  exact ozaki1IEEE_fin h

theorem mcOzaki2I_fin {P : Model} {B : CRTBasis} {Pb : ℕ} {sx sy : List Signed} {v : ℚ}
    (h : mcOzaki2 P B Pb (vals sx) (vals sy) = some v) :
    ∃ n, mcOzaki2I P B Pb (sx.map .fin) (sy.map .fin) = .fin ⟨v, n⟩ := by
  unfold mcOzaki2 at h
  have : round32Value = rne32Q := funext round32Value_eq_rne32Q
  rw [this] at h
  exact ozaki2IEEE_fin h

end Ozaki.MC
