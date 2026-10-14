import OzakiTC.Models
import OzakiTC.Split32

/-! # Ozaki-I and Ozaki-II on the Tensor Core model

The schemes of the `Ozaki` library with the Tensor Core of a `TensorCore` model as the matrix
multiplier and binary32 round-to-nearest in the recombination:

* `tcOzaki1 p b s x y`: Ozaki-I with `s` slices of `b` bits, slice products on the model's
  blocks, scaled products added with `add32` (IEEE binary32 addition);
* `tcOzaki2 p B P x y`: Ozaki-II with CRT basis `B` and precision `P`, one product on the matrix
  multiplier per modulus, one final binary32 rounding.

Main results, for any model and slice width that satisfy `IntExact` and `HoldsInts`, and inner
dimension `k` with `k · 2^(2b) ≤ 2^24`:

* `tcOzaki1_eq`: every Tensor Core call returns its slice product exactly, so the result is the
  binary32 sum of the exact scaled slice products;
* `tcOzaki1_error`: the result is within
  `((1 + 2^-24)^n − 1) n k 2^(E+F) + n (1 + 2^-24)^n 2^-150 + (s + 1) k 2^(E+F−s(b+1))` of `x · y`;
* `tcOzaki2_eq` and `tcOzaki2_error`: CRT reconstruction is exact, and the result is one binary32
  rounding of the truncated product, within `2^-24 |C| + 2^-150` plus the truncation bound.

`v100_ozaki1_z3` and `v100_ozaki2_z3` specialize them to the Z3 models' configuration on V100. -/

open TensorCore

namespace Ozaki.TC

/-- Ozaki-I on a Tensor Core variant, with binary32 recombination. -/
def tcOzaki1 (p : Model) (b s : ℕ) (x y : List ℚ) : Option ℚ :=
  ozaki1 (tcMultiplier p) add32 b s x y

/-- Ozaki-II on a Tensor Core variant, with one binary32 rounding. -/
def tcOzaki2 (p : Model) (B : CRTBasis) (P : ℕ) (x y : List ℚ) : Option ℚ :=
  ozaki2 (tcMultiplier p) round32Value B P x y

/-- `C = AB` with Ozaki-I on a Tensor Core variant; `A` and `B` by rows. -/
def tcOzaki1Gemm (p : Model) (b s : ℕ) (A B : List (List ℚ)) : Option (List (List ℚ)) :=
  ozaki1Gemm (tcMultiplier p) add32 b s A B

/-- `C = AB` with Ozaki-II on a Tensor Core variant; `A` and `B` by rows. -/
def tcOzaki2Gemm (p : Model) (B : CRTBasis) (P : ℕ) (A Bm : List (List ℚ)) :
    Option (List (List ℚ)) :=
  ozaki2Gemm (tcMultiplier p) round32Value B P A Bm

/-- **Ozaki-I on the Tensor Core.** Every block returns its slice product exactly; the result is
the binary32 sum of the exact scaled slice products. -/
theorem tcOzaki1_eq {p : Model} {b : ℕ} (hp : IntExact p b) (hh : HoldsInts p b)
    (hK : 0 < p.nfma) (s : ℕ) {x y : List ℚ} (hlen : x.length = y.length)
    (hk : x.length * (2 ^ b * 2 ^ b) ≤ 2 ^ 24) :
    tcOzaki1 p b s x y = sumWith add32 0 (exactTerms b s x y) :=
  ozaki1_eq_sumWith (tcMultiplier_exactOn hp hh hK) add32 s hlen hk

/-- **Ozaki-I error on the Tensor Core.** -/
theorem tcOzaki1_error {p : Model} {b : ℕ} (hp : IntExact p b) (hh : HoldsInts p b)
    (hK : 0 < p.nfma) (s : ℕ) {x y : List ℚ} (hlen : x.length = y.length)
    (hk : x.length * (2 ^ b * 2 ^ b) ≤ 2 ^ 24) {v : ℚ} (hv : tcOzaki1 p b s x y = some v) :
    Rat.abs (v - dot x y) ≤
      ((1 + 2 ^ (-24 : ℤ)) ^ (trianglePairs s).length - 1) *
          ((trianglePairs s).length * (x.length * 2 ^ (splitExp b x + splitExp b y))) +
        (trianglePairs s).length * (1 + 2 ^ (-24 : ℤ)) ^ (trianglePairs s).length *
          2 ^ (-150 : ℤ) +
        ((s + 1 : ℕ) : ℚ) * x.length * 2 ^ (splitExp b x + splitExp b y - s * (b + 1)) :=
  ozaki1_error (tcMultiplier_exactOn hp hh hK) (Rat.le_of_lt (two_pow_pos _))
    (Rat.le_of_lt (two_pow_pos _)) add32_within hlen hk hv

/-- **Ozaki-II on the Tensor Core.** With moduli at most `2^(b+1)` and `2 k 2^(2P) < M`, every
block returns its residue product exactly, reconstruction is exact, and the result is one
binary32 rounding of `2^(−sₓ−s_y) (a · c)`. -/
theorem tcOzaki2_eq {p : Model} {b : ℕ} (hp : IntExact p b) (hh : HoldsInts p b)
    (hK : 0 < p.nfma) {B : CRTBasis} (hB : B.Valid) (hmb : ∀ m ∈ B.moduli, m ≤ 2 ^ (b + 1))
    (P : ℕ) {x y : List ℚ} (hlen : x.length = y.length)
    (hk : x.length * (2 ^ b * 2 ^ b) ≤ 2 ^ 24)
    (hrange : 2 * x.length * (2 ^ P * 2 ^ P) < B.modulus) :
    tcOzaki2 p B P x y =
      round32Value ((dotZ (scaleTrunc (scaleShift P x) x) (scaleTrunc (scaleShift P y) y) : ℚ) *
        2 ^ (-(scaleShift P x + scaleShift P y))) :=
  ozaki2_eq (tcMultiplier_exactOn hp hh hK) round32Value hB hmb P hlen hk hrange

/-- **Ozaki-II error on the Tensor Core.** -/
theorem tcOzaki2_error {p : Model} {b : ℕ} (hp : IntExact p b) (hh : HoldsInts p b)
    (hK : 0 < p.nfma) {B : CRTBasis} (hB : B.Valid) (hmb : ∀ m ∈ B.moduli, m ≤ 2 ^ (b + 1))
    (P : ℕ) {x y : List ℚ} (hlen : x.length = y.length)
    (hk : x.length * (2 ^ b * 2 ^ b) ≤ 2 ^ 24)
    (hrange : 2 * x.length * (2 ^ P * 2 ^ P) < B.modulus) {v : ℚ}
    (hv : tcOzaki2 p B P x y = some v) :
    Rat.abs (v - dot x y) ≤
      2 ^ (-24 : ℤ) * Rat.abs ((dotZ (scaleTrunc (scaleShift P x) x)
        (scaleTrunc (scaleShift P y) y) : ℚ) * 2 ^ (-(scaleShift P x + scaleShift P y))) +
      2 ^ (-150 : ℤ) +
      (List.zipWith (fun a b => 2 ^ (-scaleShift P x) * Rat.abs b +
          2 ^ (-(scaleShift P x + scaleShift P y)) *
            Rat.abs (truncInt (a * 2 ^ scaleShift P x) : ℚ)) x y).sum :=
  ozaki2_error (tcMultiplier_exactOn hp hh hK) round32Value_within hB hmb P hlen hk hrange hv

/-! ## The Z3 configuration on V100 -/

theorem v100_intExact : IntExact v100F16F32 11 :=
  ⟨by decide, by decide, (fun _ h => by cases h), by decide, by decide⟩
theorem v100_holdsInts : HoldsInts v100F16F32 11 := ⟨by decide, by decide, by decide, by decide⟩

/-- **The Z3 Ozaki-I model on the V100 Tensor Core.** For `k = 4`, four slices of `11` bits: all
ten slice products are exact on V100 blocks, and the result is the binary32 sum, smallest first,
of the exact scaled products. -/
theorem v100_ozaki1_z3 {x y : List ℚ} (hlen : x.length = y.length) (hk : x.length = z3K) :
    tcOzaki1 v100F16F32 z3SliceBits z3Slices x y =
      sumWith add32 0 (exactTerms z3SliceBits z3Slices x y) :=
  tcOzaki1_eq v100_intExact v100_holdsInts (by decide) z3Slices hlen (by rw [hk]; decide)

/-- **The Z3 Ozaki-II model on the V100 Tensor Core.** Moduli `{4096, 4095, 4093, 4091}` and
`P = 22`: every residue product is exact, reconstruction is exact, and the result is one binary32
rounding. -/
theorem v100_ozaki2_z3 {x y : List ℚ} (hlen : x.length = y.length) (hk : x.length = z3K) :
    tcOzaki2 v100F16F32 z3Basis z3Bits x y =
      round32Value ((dotZ (scaleTrunc (scaleShift z3Bits x) x)
        (scaleTrunc (scaleShift z3Bits y) y) : ℚ) *
          2 ^ (-(scaleShift z3Bits x + scaleShift z3Bits y))) :=
  tcOzaki2_eq v100_intExact v100_holdsInts (by decide) z3Basis_valid z3Moduli_le z3Bits hlen
    (by rw [hk]; decide) (by rw [hk]; exact z3_bits.1)

/-! ## Binary32 inputs -/

/-- Decode a matrix of binary32 words; `none` if a word is infinite or NaN. -/
def decodeMatrix (A : List (List F32)) : Option (List (List ℚ)) := A.mapM (·.mapM value32)

/-- Encode a matrix of binary32 values (round to nearest, exact on binary32 values). -/
def encodeMatrix (C : List (List ℚ)) : Option (List (List F32)) :=
  C.mapM (·.mapM (round32 .nearestEven))

end Ozaki.TC
