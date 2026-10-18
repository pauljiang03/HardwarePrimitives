import OzakiMC.Models
import OzakiMC.Rounding

/-! # Ozaki-I and Ozaki-II on the AMD Matrix Core model

The schemes of the `Ozaki` library with the Matrix Core of a `MatrixCore` model as the matrix
multiplier and binary32 round-to-nearest in the recombination:

* `mcOzaki1 P b s x y`: Ozaki-I with `s` slices of `b` bits, slice products on the model's
  blocks, scaled products added with `fp32Add`;
* `mcOzaki2 P B Pb x y`: Ozaki-II with CRT basis `B` and precision `Pb`, one product on the matrix
  multiplier per modulus, one final binary32 rounding.

For a model with an exact matrix multiplier on `b`-bit slices (`ExactMultiplier`) and inner
dimension `k` with `k · 2^(2b) ≤ 2^24`:

* `mcOzaki1_eq`, `mcOzaki1_error`: every Matrix Core call returns its slice product exactly; the
  result is the binary32 sum of the exact scaled slice products, within
  `((1 + 2^-24)^n − 1) n k 2^(E+F) + n (1 + 2^-24)^n 2^-150 + (s + 1) k 2^(E+F−s(b+1))` of `x · y`;
* `mcOzaki2_eq`, `mcOzaki2_error`: CRT reconstruction is exact, and the result is one binary32
  rounding of the truncated product.

`ozaki1_z3` and `ozaki2_z3` specialize them to the Z3 models' configuration (`k = 4`, `b = 11`,
four slices; moduli `{4096, 4095, 4093, 4091}`, `P = 22`) on any variant whose matrix multiplier is
exact on `11`-bit slices: SFMA, CDNA 1, 2 and 3 fp16, and CDNA 3 XF32. -/

open MatrixCore

namespace Ozaki.MC

/-- Ozaki-I on a Matrix Core variant, with binary32 recombination. -/
def mcOzaki1 (P : Model) (b s : ℕ) (x y : List ℚ) : Option ℚ :=
  ozaki1 (mcMultiplier P) fp32Add b s x y

/-- Ozaki-II on a Matrix Core variant, with one binary32 rounding. -/
def mcOzaki2 (P : Model) (B : CRTBasis) (Pb : ℕ) (x y : List ℚ) : Option ℚ :=
  ozaki2 (mcMultiplier P) round32Value B Pb x y

/-- `C = AB` with Ozaki-I on a Matrix Core variant; `A` and `B` by rows. -/
def mcOzaki1Gemm (P : Model) (b s : ℕ) (A B : List (List ℚ)) : Option (List (List ℚ)) :=
  ozaki1Gemm (mcMultiplier P) fp32Add b s A B

/-- `C = AB` with Ozaki-II on a Matrix Core variant; `A` and `B` by rows. -/
def mcOzaki2Gemm (P : Model) (B : CRTBasis) (Pb : ℕ) (A Bm : List (List ℚ)) :
    Option (List (List ℚ)) :=
  ozaki2Gemm (mcMultiplier P) round32Value B Pb A Bm

/-- **Ozaki-I on the Matrix Core.** Every block returns its slice product exactly; the result is
the binary32 sum of the exact scaled slice products. -/
theorem mcOzaki1_eq {P : Model} {b : ℕ} (hP : ExactMultiplier P b) (s : ℕ) {x y : List ℚ}
    (hlen : x.length = y.length) (hk : x.length * (2 ^ b * 2 ^ b) ≤ 2 ^ 24) :
    mcOzaki1 P b s x y = sumWith fp32Add 0 (exactTerms b s x y) :=
  ozaki1_eq_sumWith hP.exactOn fp32Add s hlen hk

/-- **Ozaki-I error on the Matrix Core.** -/
theorem mcOzaki1_error {P : Model} {b : ℕ} (hP : ExactMultiplier P b) (s : ℕ) {x y : List ℚ}
    (hlen : x.length = y.length) (hk : x.length * (2 ^ b * 2 ^ b) ≤ 2 ^ 24) {v : ℚ}
    (hv : mcOzaki1 P b s x y = some v) :
    Rat.abs (v - dot x y) ≤
      ((1 + 2 ^ (-24 : ℤ)) ^ (trianglePairs s).length - 1) *
          ((trianglePairs s).length * (x.length * 2 ^ (splitExp b x + splitExp b y))) +
        (trianglePairs s).length * (1 + 2 ^ (-24 : ℤ)) ^ (trianglePairs s).length *
          2 ^ (-150 : ℤ) +
        ((s + 1 : ℕ) : ℚ) * x.length * 2 ^ (splitExp b x + splitExp b y - s * (b + 1)) :=
  ozaki1_error hP.exactOn (Rat.le_of_lt (two_pow_pos _)) (Rat.le_of_lt (two_pow_pos _))
    fp32Add_within hlen hk hv

/-- **Ozaki-II on the Matrix Core.** With moduli at most `2^(b+1)` and `2 k 2^(2P) < M`, every
block returns its residue product exactly, reconstruction is exact, and the result is one binary32
rounding of `2^(−sₓ−s_y) (a · c)`. -/
theorem mcOzaki2_eq {P : Model} {b : ℕ} (hP : ExactMultiplier P b) {B : CRTBasis} (hB : B.Valid)
    (hmb : ∀ m ∈ B.moduli, m ≤ 2 ^ (b + 1)) (Pb : ℕ) {x y : List ℚ}
    (hlen : x.length = y.length) (hk : x.length * (2 ^ b * 2 ^ b) ≤ 2 ^ 24)
    (hrange : 2 * x.length * (2 ^ Pb * 2 ^ Pb) < B.modulus) :
    mcOzaki2 P B Pb x y =
      round32Value ((dotZ (scaleTrunc (scaleShift Pb x) x) (scaleTrunc (scaleShift Pb y) y) : ℚ) *
        2 ^ (-(scaleShift Pb x + scaleShift Pb y))) :=
  ozaki2_eq hP.exactOn round32Value hB hmb Pb hlen hk hrange

/-- **Ozaki-II error on the Matrix Core.** -/
theorem mcOzaki2_error {P : Model} {b : ℕ} (hP : ExactMultiplier P b) {B : CRTBasis}
    (hB : B.Valid) (hmb : ∀ m ∈ B.moduli, m ≤ 2 ^ (b + 1)) (Pb : ℕ) {x y : List ℚ}
    (hlen : x.length = y.length) (hk : x.length * (2 ^ b * 2 ^ b) ≤ 2 ^ 24)
    (hrange : 2 * x.length * (2 ^ Pb * 2 ^ Pb) < B.modulus) {v : ℚ}
    (hv : mcOzaki2 P B Pb x y = some v) :
    Rat.abs (v - dot x y) ≤
      2 ^ (-24 : ℤ) * Rat.abs ((dotZ (scaleTrunc (scaleShift Pb x) x)
        (scaleTrunc (scaleShift Pb y) y) : ℚ) * 2 ^ (-(scaleShift Pb x + scaleShift Pb y))) +
      2 ^ (-150 : ℤ) +
      (List.zipWith (fun a b => 2 ^ (-scaleShift Pb x) * Rat.abs b +
          2 ^ (-(scaleShift Pb x + scaleShift Pb y)) *
            Rat.abs (truncInt (a * 2 ^ scaleShift Pb x) : ℚ)) x y).sum :=
  ozaki2_error hP.exactOn round32Value_within hB hmb Pb hlen hk hrange hv

/-! ## The Z3 configuration -/

/-- **The Z3 Ozaki-I model on a Matrix Core.** For `k = 4` and four slices of `11` bits, on any
variant whose matrix multiplier is exact on `11`-bit slices, all ten slice products are exact and
the result is the binary32 sum, smallest first, of the exact scaled products. -/
theorem ozaki1_z3 {P : Model} (hP : ExactMultiplier P z3SliceBits) {x y : List ℚ}
    (hlen : x.length = y.length) (hk : x.length = z3K) :
    mcOzaki1 P z3SliceBits z3Slices x y = sumWith fp32Add 0 (exactTerms z3SliceBits z3Slices x y) :=
  mcOzaki1_eq hP z3Slices hlen (by rw [hk]; decide)

/-- **The Z3 Ozaki-II model on a Matrix Core.** Moduli `{4096, 4095, 4093, 4091}` and `P = 22`:
every residue product is exact, reconstruction is exact, and the result is one binary32 rounding. -/
theorem ozaki2_z3 {P : Model} (hP : ExactMultiplier P z3SliceBits) {x y : List ℚ}
    (hlen : x.length = y.length) (hk : x.length = z3K) :
    mcOzaki2 P z3Basis z3Bits x y =
      round32Value ((dotZ (scaleTrunc (scaleShift z3Bits x) x)
        (scaleTrunc (scaleShift z3Bits y) y) : ℚ) *
          2 ^ (-(scaleShift z3Bits x + scaleShift z3Bits y))) :=
  mcOzaki2_eq hP z3Basis_valid z3Moduli_le z3Bits hlen (by rw [hk]; decide)
    (by rw [hk]; exact z3_bits.1)

theorem cdna1F16_ozaki1_z3 {x y : List ℚ} (hlen : x.length = y.length) (hk : x.length = z3K) :
    mcOzaki1 cdna1F16 z3SliceBits z3Slices x y =
      sumWith fp32Add 0 (exactTerms z3SliceBits z3Slices x y) :=
  ozaki1_z3 (cdna1F16_exactMultiplier (by decide)) hlen hk

theorem cdna2F16_ozaki1_z3 {x y : List ℚ} (hlen : x.length = y.length) (hk : x.length = z3K) :
    mcOzaki1 cdna2F16 z3SliceBits z3Slices x y =
      sumWith fp32Add 0 (exactTerms z3SliceBits z3Slices x y) :=
  ozaki1_z3 (cdna2F16_exactMultiplier (by decide)) hlen hk

theorem cdna3F16_ozaki1_z3 {x y : List ℚ} (hlen : x.length = y.length) (hk : x.length = z3K) :
    mcOzaki1 cdna3F16 z3SliceBits z3Slices x y =
      sumWith fp32Add 0 (exactTerms z3SliceBits z3Slices x y) :=
  ozaki1_z3 (cdna3F16_exactMultiplier (by decide)) hlen hk

theorem cdna1F16_ozaki2_z3 {x y : List ℚ} (hlen : x.length = y.length) (hk : x.length = z3K) :
    mcOzaki2 cdna1F16 z3Basis z3Bits x y =
      round32Value ((dotZ (scaleTrunc (scaleShift z3Bits x) x)
        (scaleTrunc (scaleShift z3Bits y) y) : ℚ) *
          2 ^ (-(scaleShift z3Bits x + scaleShift z3Bits y))) :=
  ozaki2_z3 (cdna1F16_exactMultiplier (by decide)) hlen hk

theorem cdna2F16_ozaki2_z3 {x y : List ℚ} (hlen : x.length = y.length) (hk : x.length = z3K) :
    mcOzaki2 cdna2F16 z3Basis z3Bits x y =
      round32Value ((dotZ (scaleTrunc (scaleShift z3Bits x) x)
        (scaleTrunc (scaleShift z3Bits y) y) : ℚ) *
          2 ^ (-(scaleShift z3Bits x + scaleShift z3Bits y))) :=
  ozaki2_z3 (cdna2F16_exactMultiplier (by decide)) hlen hk

theorem cdna3F16_ozaki2_z3 {x y : List ℚ} (hlen : x.length = y.length) (hk : x.length = z3K) :
    mcOzaki2 cdna3F16 z3Basis z3Bits x y =
      round32Value ((dotZ (scaleTrunc (scaleShift z3Bits x) x)
        (scaleTrunc (scaleShift z3Bits y) y) : ℚ) *
          2 ^ (-(scaleShift z3Bits x + scaleShift z3Bits y))) :=
  ozaki2_z3 (cdna3F16_exactMultiplier (by decide)) hlen hk

/-! ## Binary32 inputs -/

/-- Decode a matrix of binary32 words; `none` if a word is infinite or NaN. -/
def decodeMatrix (A : List (List F32)) : Option (List (List ℚ)) := A.mapM (·.mapM value32)

/-- Encode a matrix of binary32 values (round to nearest, exact on binary32 values). -/
def encodeMatrix (C : List (List ℚ)) : Option (List (List F32)) := C.mapM (·.mapM rne32)

end Ozaki.MC
