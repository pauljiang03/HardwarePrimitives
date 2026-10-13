import Ozaki.Ozaki2

/-! # The parameters of the Z3 models

The Z3 models emulate a binary32 `4 × 4` GEMM (inner dimension `k = 4`) on an fp16-input engine.

* Ozaki-I: slices of `b = 11` bits. A product of two `b`-bit integers needs `2b` bits and a sum of
  four needs `2b + 2 = 24`: the slice products total at most `4 · 2^22 = 2^24` (`z3_slice_exactnessBound`).
* Ozaki-II: moduli `{4096, 4095, 4093, 4091}`, pairwise coprime, each at most `2^12`, so the
  symmetric residues are `11`-bit integers. `M ≈ 2^47.997`, and `P = 22` is the largest
  precision with `2 · 4 · 2^(2P) < M` (`z3_bits`).

The Z3 models' sanity queries have exact counterparts: at `P = 23` the reconstruction range is
exceeded (`crt_fails_at_23`), and with `b = 12` the slice products exceed `2^24`
(`slice_exactnessBound_12`); the hardware libraries show the resulting inexact engine outputs. -/

local notation "ℕ" => Nat
local notation "ℤ" => Int
local notation "ℚ" => Rat

namespace Ozaki

/-- Inner dimension of the Z3 models' GEMM. -/
def z3K : ℕ := 4
/-- Slice width of the Z3 Ozaki-I model. -/
def z3SliceBits : ℕ := 11
/-- Number of slices of the Z3 Ozaki-I model. -/
def z3Slices : ℕ := 4
/-- Moduli of the Z3 Ozaki-II model. -/
def z3Moduli : List ℕ := [4096, 4095, 4093, 4091]
/-- The CRT basis of the Z3 Ozaki-II model. -/
def z3Basis : CRTBasis := crtBasis z3Moduli
/-- Precision of the Z3 Ozaki-II model. -/
def z3Bits : ℕ := 22

/-- `k · 2^b · 2^b = 2^24`: four products of `11`-bit integers fit binary32's significand. -/
theorem z3_slice_exactnessBound : z3K * (2 ^ z3SliceBits * 2 ^ z3SliceBits) = 2 ^ 24 := by decide

/-- One more bit per slice doubles twice the budget. -/
theorem slice_exactnessBound_12 : z3K * (2 ^ 12 * 2 ^ 12) = 2 ^ 26 := by decide

/-- Ten slice products for four slices. -/
theorem z3_slice_products : (trianglePairs z3Slices).length = 10 := by decide

/-- The weights computed for the moduli form a valid basis. -/
theorem z3Basis_valid : z3Basis.Valid := by decide +kernel

theorem z3Basis_moduli : z3Basis.moduli = z3Moduli := rfl

/-- Every modulus is at most `2^12`, so its symmetric residues are `11`-bit integers. -/
theorem z3Moduli_le : ∀ m ∈ z3Basis.moduli, m ≤ 2 ^ (z3SliceBits + 1) := by decide

theorem z3_modulus : z3Basis.modulus = 280856887234560 := by decide

/-- `P = 22` is the largest precision with `2 k 2^(2P) < M`. -/
theorem z3_bits : 2 * z3K * (2 ^ z3Bits * 2 ^ z3Bits) < z3Basis.modulus ∧
    ¬ 2 * z3K * (2 ^ (z3Bits + 1) * 2 ^ (z3Bits + 1)) < z3Basis.modulus := by decide

theorem z3_ozaki2Bits : ozaki2Bits z3K z3Basis.modulus 64 = z3Bits := by decide +kernel

/-- At `P = 23` a product of four `23`-bit integers can reach `M` itself, whose residues are all
zero: reconstruction returns `0`. -/
theorem crt_fails_at_23 :
    (z3Basis.modulus : ℤ) ≤ z3K * (2 ^ 23 * 2 ^ 23) ∧
      crt z3Basis (z3Moduli.map fun m : ℕ => (z3Basis.modulus : ℤ) % (m : ℤ)) = 0 := by
  decide +kernel

/-! ## The Z3 models with an exact engine -/

/-- Ozaki-I with the Z3 parameters and an engine exact on `11`-bit slices within `2^24`: the slicing
error is at most `5 · 4 · 2^(E + F − 48)`. -/
theorem z3_ozaki1_slicing_error {mult : MatrixMultiplier} (hmult : mult.ExactOn z3SliceBits (2 ^ 24))
    {x y : List ℚ} (hlen : x.length = y.length) (hk : x.length = z3K) :
    ozaki1 mult exactAdd z3SliceBits z3Slices x y = some (exactTerms z3SliceBits z3Slices x y).sum ∧
      Rat.abs (dot x y - (exactTerms z3SliceBits z3Slices x y).sum) ≤
        ((5 : ℕ) : ℚ) * x.length * 2 ^ (splitExp z3SliceBits x + splitExp z3SliceBits y - 48) :=
  ⟨ozaki1_exactAdd hmult hlen (by rw [hk]; decide), exactTerms_error z3SliceBits z3Slices x y⟩

/-- Ozaki-II with the Z3 parameters and an engine exact on `11`-bit residues within `2^24`:
reconstruction is exact, so the result is one rounding of `2^(−sₓ−s_y) (a · c)`. -/
theorem z3_ozaki2_eq {mult : MatrixMultiplier} (hmult : mult.ExactOn z3SliceBits (2 ^ 24))
    (round : ℚ → Option ℚ) {x y : List ℚ} (hlen : x.length = y.length) (hk : x.length = z3K) :
    ozaki2 mult round z3Basis z3Bits x y =
      round ((dotZ (scaleTrunc (scaleShift z3Bits x) x) (scaleTrunc (scaleShift z3Bits y) y) : ℚ) *
        2 ^ (-(scaleShift z3Bits x + scaleShift z3Bits y))) :=
  ozaki2_eq hmult round z3Basis_valid z3Moduli_le z3Bits hlen (by rw [hk]; decide)
    (by rw [hk]; exact z3_bits.1)

end Ozaki
