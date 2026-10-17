import OzakiMC.Correct
import Ozaki.SplitK
import Ozaki.Exact64
import Ozaki.TruncatedSum

/-! # Long dot products on the AMD matrix-core model

Split-K on matrix-core blocks: chunks of `2^(24 − 2b)` terms, each an exact matrix-core dot
product, added exactly. With it the AMD theorems hold for every inner dimension: Ozaki-I's error
bound, and correctly rounded binary32 Ozaki-I and Ozaki-II whose slice products,
including the exact fallback's, run on matrix-core blocks. The correctly rounded results are stated
with the hardware-independent IEEE round to nearest even of `Ozaki.Binary` (`rne32Q`, `rne64`), the
same function as on the Tensor Core model.

FP64 emulation uses the hardware-independent binary64 round to nearest even of `Ozaki.Binary`
(`rne64`), since `MatrixCore` models no binary64 arithmetic: Ozaki-I with binary64 recombination
(`mcOzaki1D_error`), and correctly rounded binary64 results from Ozaki-I and Ozaki-II
(`mcOzaki1CRD_eq`, `mcOzaki2CRD_eq`) for binary64 inputs of any length, every slice product on
matrix-core blocks. -/

open MatrixCore

namespace Ozaki.MC

/-- **Split-K on matrix-core blocks.** -/
def mcSplitK (P : Model) (b : ℕ) : MatrixMultiplier := chunked (chunkLen b) (mcMultiplier P)

theorem mcSplitK_exactOn {P : Model} {b : ℕ} (hP : ExactMultiplier P b) (hb : 2 * b ≤ 24) (B : ℕ) :
    (mcSplitK P b).ExactOn b B :=
  chunked_exactOn hP.exactOn (chunkLen_pos b) (chunkLen_exactnessBound hb) B

/-- Ozaki-I on matrix-core blocks with split-K, binary32 recombination. -/
def mcOzaki1L (P : Model) (b s : ℕ) (x y : List ℚ) : Option ℚ :=
  ozaki1 (mcSplitK P b) fp32Add b s x y

/-- **Ozaki-I on the matrix core for any inner dimension.** -/
theorem mcOzaki1L_error {P : Model} {b : ℕ} (hP : ExactMultiplier P b) (hb : 2 * b ≤ 24) (s : ℕ)
    {x y : List ℚ} (hlen : x.length = y.length) {v : ℚ} (hv : mcOzaki1L P b s x y = some v) :
    Rat.abs (v - dot x y) ≤
      ((1 + 2 ^ (-24 : ℤ)) ^ (trianglePairs s).length - 1) *
          ((trianglePairs s).length * (x.length * 2 ^ (splitExp b x + splitExp b y))) +
        (trianglePairs s).length * (1 + 2 ^ (-24 : ℤ)) ^ (trianglePairs s).length *
          2 ^ (-150 : ℤ) +
        ((s + 1 : ℕ) : ℚ) * x.length * 2 ^ (splitExp b x + splitExp b y - s * (b + 1)) :=
  ozaki1_error (mcSplitK_exactOn hP hb _) (Rat.le_of_lt (two_pow_pos _))
    (Rat.le_of_lt (two_pow_pos _)) fp32Add_within hlen (Nat.le_refl _) hv

/-- MatrixCore's binary32 values are the binary32 values of `Ozaki.Binary`. -/
theorem finiteValue32_binary32 {v : ℚ} (h : FiniteValue32 v) : Binary32Value v := by
  obtain ⟨k, e, h1, h2, h3, rfl⟩ := h
  exact ⟨k, e, h1, h2, h3, by rw [pow2_eq]; congr 2⟩

/-- Correctly rounded binary32 Ozaki-I of any inner dimension; every slice product on matrix-core
blocks. -/
def mcOzaki1CRL (P : Model) (b : ℕ) (ss : List ℕ) (smax : ℕ) (x y : List ℚ) : Option ℚ :=
  ozaki1CRE (mcSplitK P b) rne32Q b ss smax x y

/-- Correctly rounded binary32 Ozaki-II of any inner dimension; every residue and slice product on
matrix-core blocks. -/
def mcOzaki2CRL (P : Model) (cfgs : List (CRTBasis × ℕ)) (b smax : ℕ) (x y : List ℚ) :
    Option ℚ :=
  ozaki2CRE (mcSplitK P b) rne32Q cfgs b smax x y

/-- **Correctly rounded binary32 Ozaki-I on the matrix core, for any inner dimension**: the IEEE round
to nearest even of `x · y`, the same function as on the Tensor Core model. -/
theorem mcOzaki1CRL_eq {P : Model} {b : ℕ} (hP : ExactMultiplier P b) (hb : 2 * b ≤ 24)
    (ss : List ℕ) {smax : ℕ} (hsmax : 277 < smax * (b + 1)) {x y : List ℚ}
    (hx : ∀ a ∈ x, Binary32Value a) (hy : ∀ a ∈ y, Binary32Value a) (hlen : x.length = y.length) :
    mcOzaki1CRL P b ss smax x y = rne32Q (dot x y) :=
  ozaki1CRE_eq rne32Q_nearest rne32Q_intervals (mcSplitK_exactOn hP hb _) ss hlen
    (Nat.le_refl _) (vanish32Q (by omega) hsmax hx hy)

/-- **Correctly rounded binary32 Ozaki-II on the matrix core, for any inner dimension.** -/
theorem mcOzaki2CRL_eq {P : Model} {b : ℕ} (hP : ExactMultiplier P b) (hb : 2 * b ≤ 24)
    {cfgs : List (CRTBasis × ℕ)} {smax : ℕ} (hsmax : 277 < smax * (b + 1)) {x y : List ℚ}
    (hcfg : ∀ c ∈ cfgs, c.1.Valid ∧ (∀ m ∈ c.1.moduli, m ≤ 2 ^ (b + 1)) ∧
      2 * x.length * (2 ^ c.2 * 2 ^ c.2) < c.1.modulus)
    (hx : ∀ a ∈ x, Binary32Value a) (hy : ∀ a ∈ y, Binary32Value a) (hlen : x.length = y.length) :
    mcOzaki2CRL P cfgs b smax x y = rne32Q (dot x y) :=
  ozaki2CRE_eq rne32Q_nearest rne32Q_intervals (mcSplitK_exactOn hP hb _) hcfg hlen
    (Nat.le_refl _) (vanish32Q (by omega) hsmax hx hy)

/-! ## FP64 emulation -/

/-- Binary64 addition: the exact sum rounded to nearest even (`Ozaki.rne64`). -/
def fp64Add (a b : ℚ) : Option ℚ := rne64 (a + b)

theorem fp64Add_within : AddWithin fp64Add (2 ^ (-53 : ℤ)) (2 ^ (-1075 : ℤ)) :=
  addOfRound_within rne64_within

/-- **FP64 emulation, Ozaki-I**: slices on matrix-core blocks with split-K, binary64
recombination. -/
def mcOzaki1D (P : Model) (b s : ℕ) (x y : List ℚ) : Option ℚ :=
  ozaki1 (mcSplitK P b) fp64Add b s x y

theorem mcOzaki1D_error {P : Model} {b : ℕ} (hP : ExactMultiplier P b) (hb : 2 * b ≤ 24) (s : ℕ)
    {x y : List ℚ} (hlen : x.length = y.length) {v : ℚ} (hv : mcOzaki1D P b s x y = some v) :
    Rat.abs (v - dot x y) ≤
      ((1 + 2 ^ (-53 : ℤ)) ^ (trianglePairs s).length - 1) *
          ((trianglePairs s).length * (x.length * 2 ^ (splitExp b x + splitExp b y))) +
        (trianglePairs s).length * (1 + 2 ^ (-53 : ℤ)) ^ (trianglePairs s).length *
          2 ^ (-1075 : ℤ) +
        ((s + 1 : ℕ) : ℚ) * x.length * 2 ^ (splitExp b x + splitExp b y - s * (b + 1)) :=
  ozaki1_error (mcSplitK_exactOn hP hb _) (Rat.le_of_lt (two_pow_pos _))
    (Rat.le_of_lt (two_pow_pos _)) fp64Add_within hlen (Nat.le_refl _) hv

/-- Correctly rounded FP64 emulation by Ozaki-I; every slice product on matrix-core blocks. -/
def mcOzaki1CRD (P : Model) (b : ℕ) (ss : List ℕ) (smax : ℕ) (x y : List ℚ) : Option ℚ :=
  ozaki1CRE (mcSplitK P b) rne64 b ss smax x y

/-- Correctly rounded FP64 emulation by Ozaki-II; every residue and slice product on matrix-core
blocks. -/
def mcOzaki2CRD (P : Model) (cfgs : List (CRTBasis × ℕ)) (b smax : ℕ) (x y : List ℚ) :
    Option ℚ :=
  ozaki2CRE (mcSplitK P b) rne64 cfgs b smax x y

/-- **FP64 GEMM on AMD matrix cores, correctly rounded.** For binary64 inputs of any length, on any
variant whose matrix multiplier is exact on `b`-bit slices, the result is the binary64 round to
nearest of `x · y`. -/
theorem mcOzaki1CRD_eq {P : Model} {b : ℕ} (hP : ExactMultiplier P b) (hb : 2 * b ≤ 24)
    (ss : List ℕ) {smax : ℕ} (hsmax : 2098 < smax * (b + 1)) {x y : List ℚ}
    (hx : ∀ a ∈ x, Binary64Value a) (hy : ∀ a ∈ y, Binary64Value a) (hlen : x.length = y.length) :
    mcOzaki1CRD P b ss smax x y = rne64 (dot x y) :=
  ozaki1CRE_eq rne64_nearest rne64_intervals (mcSplitK_exactOn hP hb _) ss hlen (Nat.le_refl _)
    (vanish64 (by omega) hsmax hx hy)

/-- **FP64 GEMM by Ozaki-II on AMD matrix cores, correctly rounded.** -/
theorem mcOzaki2CRD_eq {P : Model} {b : ℕ} (hP : ExactMultiplier P b) (hb : 2 * b ≤ 24)
    {cfgs : List (CRTBasis × ℕ)} {smax : ℕ} (hsmax : 2098 < smax * (b + 1)) {x y : List ℚ}
    (hcfg : ∀ c ∈ cfgs, c.1.Valid ∧ (∀ m ∈ c.1.moduli, m ≤ 2 ^ (b + 1)) ∧
      2 * x.length * (2 ^ c.2 * 2 ^ c.2) < c.1.modulus)
    (hx : ∀ a ∈ x, Binary64Value a) (hy : ∀ a ∈ y, Binary64Value a) (hlen : x.length = y.length) :
    mcOzaki2CRD P cfgs b smax x y = rne64 (dot x y) :=
  ozaki2CRE_eq rne64_nearest rne64_intervals (mcSplitK_exactOn hP hb _) hcfg hlen (Nat.le_refl _)
    (vanish64 (by omega) hsmax hx hy)

/-- The instances: FP64 emulation on CDNA 3 fp16 (`11`-bit slices, up to `175`) and CDNA 3 bf16
(`8`-bit slices, up to `234`), correctly rounded, for every length. -/
theorem cdna3F16_fp64CR (ss : List ℕ) {x y : List ℚ} (hx : ∀ a ∈ x, Binary64Value a)
    (hy : ∀ a ∈ y, Binary64Value a) (hlen : x.length = y.length) :
    mcOzaki1CRD cdna3F16 11 ss 175 x y = rne64 (dot x y) :=
  mcOzaki1CRD_eq (cdna3F16_exactMultiplier (by decide)) (by decide) ss (by decide) hx hy hlen

theorem cdna3BF16_fp64CR (ss : List ℕ) {x y : List ℚ} (hx : ∀ a ∈ x, Binary64Value a)
    (hy : ∀ a ∈ y, Binary64Value a) (hlen : x.length = y.length) :
    mcOzaki1CRD cdna3BF16 8 ss 234 x y = rne64 (dot x y) :=
  mcOzaki1CRD_eq (cdna3BF16_exactMultiplier (by decide)) (by decide) ss (by decide) hx hy hlen

/-! ## With a two-word accumulator -/

/-- Correctly rounded binary32 Ozaki-I of any inner dimension with a `W`-bit truncated sum. -/
def mcOzaki1CRLW (P : Model) (b W : ℕ) (ss : List ℕ) (smax : ℕ) (x y : List ℚ) : Option ℚ :=
  ozaki1CRW (mcSplitK P b) rne32Q b W ss smax x y

/-- Correctly rounded FP64 by Ozaki-I with a `W`-bit truncated sum. -/
def mcOzaki1CRDW (P : Model) (b W : ℕ) (ss : List ℕ) (smax : ℕ) (x y : List ℚ) : Option ℚ :=
  ozaki1CRW (mcSplitK P b) rne64 b W ss smax x y

theorem mcOzaki1CRLW_eq {P : Model} {b : ℕ} (hP : ExactMultiplier P b) (hb : 2 * b ≤ 24) (W : ℕ)
    (ss : List ℕ) {smax : ℕ} (hsmax : 277 < smax * (b + 1)) {x y : List ℚ}
    (hx : ∀ a ∈ x, Binary32Value a) (hy : ∀ a ∈ y, Binary32Value a) (hlen : x.length = y.length) :
    mcOzaki1CRLW P b W ss smax x y = rne32Q (dot x y) :=
  ozaki1CRW_eq rne32Q_nearest rne32Q_intervals (mcSplitK_exactOn hP hb _) W ss hlen
    (Nat.le_refl _) (vanish32Q (by omega) hsmax hx hy)

/-- **Correctly rounded FP64 GEMM on AMD matrix cores with a two-word accumulator.** -/
theorem mcOzaki1CRDW_eq {P : Model} {b : ℕ} (hP : ExactMultiplier P b) (hb : 2 * b ≤ 24) (W : ℕ)
    (ss : List ℕ) {smax : ℕ} (hsmax : 2098 < smax * (b + 1)) {x y : List ℚ}
    (hx : ∀ a ∈ x, Binary64Value a) (hy : ∀ a ∈ y, Binary64Value a) (hlen : x.length = y.length) :
    mcOzaki1CRDW P b W ss smax x y = rne64 (dot x y) :=
  ozaki1CRW_eq rne64_nearest rne64_intervals (mcSplitK_exactOn hP hb _) W ss hlen
    (Nat.le_refl _) (vanish64 (by omega) hsmax hx hy)

end Ozaki.MC
