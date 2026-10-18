import OzakiMC.Schemes
import Ozaki.Success

/-! # The Matrix Core pipelines return a value

The Z3 models check that no NaN or infinity ever appears (`[H.1]` of both models). On the
Matrix Core model the schemes return `none` only when a binary32 rounding overflows, and
`MatrixCore`'s round to nearest even succeeds below the overflow threshold, so on every value of
magnitude at most `maxFinite32` (`round32Value_succeeds`). With an exact matrix multiplier:

* `mcOzaki1_isSome`: Ozaki-I returns a value when
  `(1 + 2^-24)^n · n k 2^(E+F) + n (1 + 2^-24)^n 2^-150 ≤ maxFinite32`;
* `mcOzaki2_isSome`: Ozaki-II returns a value when `k 2^((P − sₓ) + (P − s_y)) ≤ maxFinite32`;
* `ozaki1_z3_isSome`, `ozaki2_z3_isSome`: in the Z3 configuration, on any variant whose matrix
  multiplier is exact on `11`-bit slices, both return a value whenever every entry is at most
  `2^60`. -/

open MatrixCore

namespace Ozaki.MC

theorem maxFinite32_lt : maxFinite32 < overflowThreshold32 := by decide +kernel

/-- **Binary32 rounding succeeds in range.** `round32Value` returns a value for every rational of
magnitude at most `maxFinite32`. -/
theorem round32Value_succeeds : RoundSucceeds round32Value maxFinite32 := by
  intro q hq
  rw [← absQ_eq] at hq
  obtain ⟨w, hw⟩ := Option.isSome_iff_exists.mp
    ((rne32_isSome_iff q).mpr (lt_of_le_of_lt' hq maxFinite32_lt))
  exact ⟨_, by unfold round32Value; rw [hw, Option.bind_some]; exact rne32_value hw⟩

theorem fp32Add_succeeds : AddSucceeds fp32Add maxFinite32 := by
  rw [fp32Add_eq_addOfRound]; exact addOfRound_succeeds round32Value_succeeds

/-- **Ozaki-I returns a value on the Matrix Core** (`[H.1]`). -/
theorem mcOzaki1_isSome {P : Model} {b : ℕ} (hP : ExactMultiplier P b) (s : ℕ) {x y : List ℚ}
    (hlen : x.length = y.length) (hk : x.length * (2 ^ b * 2 ^ b) ≤ 2 ^ 24)
    (hL : (1 + 2 ^ (-24 : ℤ)) ^ (trianglePairs s).length *
        ((trianglePairs s).length * (x.length * 2 ^ (splitExp b x + splitExp b y))) +
      (trianglePairs s).length * (1 + 2 ^ (-24 : ℤ)) ^ (trianglePairs s).length * 2 ^ (-150 : ℤ) ≤
        maxFinite32) :
    ∃ v, mcOzaki1 P b s x y = some v :=
  ozaki1_isSome hP.exactOn (Rat.le_of_lt (two_pow_pos _)) (Rat.le_of_lt (two_pow_pos _))
    fp32Add_within fp32Add_succeeds hlen hk hL

/-- **Ozaki-II returns a value on the Matrix Core** (`[H.1]`). -/
theorem mcOzaki2_isSome {P : Model} {b : ℕ} (hP : ExactMultiplier P b) {B : CRTBasis} (hB : B.Valid)
    (hmb : ∀ m ∈ B.moduli, m ≤ 2 ^ (b + 1)) (Pb : ℕ) {x y : List ℚ} (hlen : x.length = y.length)
    (hk : x.length * (2 ^ b * 2 ^ b) ≤ 2 ^ 24)
    (hrange : 2 * x.length * (2 ^ Pb * 2 ^ Pb) < B.modulus)
    (hL : x.length * (2 : ℚ) ^ ((Pb - scaleShift Pb x) + (Pb - scaleShift Pb y)) ≤ maxFinite32) :
    ∃ v, mcOzaki2 P B Pb x y = some v :=
  ozaki2_isSome hP.exactOn round32Value_succeeds hB hmb Pb hlen hk hrange hL

/-! ## The Z3 configuration -/

theorem z3_ozaki1_range : (1 + (2 : ℚ) ^ (-24 : ℤ)) ^ 10 * (10 * (4 * 2 ^ (120 : ℤ))) +
    10 * (1 + (2 : ℚ) ^ (-24 : ℤ)) ^ 10 * 2 ^ (-150 : ℤ) ≤ maxFinite32 := by decide +kernel

theorem z3_ozaki2_range : 4 * (2 : ℚ) ^ (120 : ℤ) ≤ maxFinite32 := by decide +kernel

/-- **The Z3 Ozaki-I model returns a value** on any variant whose matrix multiplier is exact on
`11`-bit slices, whenever every entry of `x` and `y` is at most `2^60` in magnitude. -/
theorem ozaki1_z3_isSome {P : Model} (hP : ExactMultiplier P z3SliceBits) {x y : List ℚ}
    (hlen : x.length = y.length) (hk : x.length = z3K)
    (hx : ∀ a ∈ x, Rat.abs a ≤ 2 ^ (60 : ℤ)) (hy : ∀ a ∈ y, Rat.abs a ≤ 2 ^ (60 : ℤ)) :
    ∃ v, mcOzaki1 P z3SliceBits z3Slices x y = some v := by
  refine mcOzaki1_isSome hP z3Slices hlen (by rw [hk]; decide) ?_
  have hE := splitExp_le z3SliceBits hx (by decide)
  have hF := splitExp_le z3SliceBits hy (by decide)
  have hX := two_pow_le (show splitExp z3SliceBits x + splitExp z3SliceBits y ≤ 120 by omega)
  rw [z3_slice_products, hk]
  generalize (2 : ℚ) ^ (splitExp z3SliceBits x + splitExp z3SliceBits y) = X at hX
  have hPow : (0 : ℚ) ≤ (1 + 2 ^ (-24 : ℤ)) ^ 10 := Rat.pow_nonneg (by have := two_pow_pos (-24); grind)
  have h1 : ((10 : ℕ) : ℚ) * (((z3K : ℕ) : ℚ) * X) ≤ 10 * (4 * 2 ^ (120 : ℤ)) := by
    have : ((z3K : ℕ) : ℚ) = 4 := rfl
    rw [this]; have : ((10 : ℕ) : ℚ) = 10 := rfl
    rw [this]; grind
  have h2 := Rat.mul_le_mul_of_nonneg_left h1 hPow
  have h3 : ((10 : ℕ) : ℚ) = 10 := rfl
  rw [h3]
  have := z3_ozaki1_range
  grind

/-- **The Z3 Ozaki-II model returns a value** on any variant whose matrix multiplier is exact on
`11`-bit slices, whenever every entry of `x` and `y` is at most `2^60` in magnitude. -/
theorem ozaki2_z3_isSome {P : Model} (hP : ExactMultiplier P z3SliceBits) {x y : List ℚ}
    (hlen : x.length = y.length) (hk : x.length = z3K)
    (hx : ∀ a ∈ x, Rat.abs a ≤ 2 ^ (60 : ℤ)) (hy : ∀ a ∈ y, Rat.abs a ≤ 2 ^ (60 : ℤ)) :
    ∃ v, mcOzaki2 P z3Basis z3Bits x y = some v := by
  refine mcOzaki2_isSome hP z3Basis_valid z3Moduli_le z3Bits hlen (by rw [hk]; decide)
    (by rw [hk]; exact z3_bits.1) ?_
  have hE := scaleExp_le z3Bits hx (by decide)
  have hF := scaleExp_le z3Bits hy (by decide)
  have hX := two_pow_le (show ((z3Bits : ℤ) - scaleShift z3Bits x) + (z3Bits - scaleShift z3Bits y) ≤ 120
    by omega)
  rw [hk]
  have h4 : ((z3K : ℕ) : ℚ) = 4 := rfl
  rw [h4]
  have := z3_ozaki2_range
  grind

/-- The Z3 Ozaki-I model returns a value on CDNA 3 fp16 for entries at most `2^60`. -/
theorem cdna3F16_ozaki1_z3_isSome {x y : List ℚ} (hlen : x.length = y.length) (hk : x.length = z3K)
    (hx : ∀ a ∈ x, Rat.abs a ≤ 2 ^ (60 : ℤ)) (hy : ∀ a ∈ y, Rat.abs a ≤ 2 ^ (60 : ℤ)) :
    ∃ v, mcOzaki1 cdna3F16 z3SliceBits z3Slices x y = some v :=
  ozaki1_z3_isSome (cdna3F16_exactMultiplier (by decide)) hlen hk hx hy

/-- The Z3 Ozaki-II model returns a value on CDNA 3 fp16 for entries at most `2^60`. -/
theorem cdna3F16_ozaki2_z3_isSome {x y : List ℚ} (hlen : x.length = y.length) (hk : x.length = z3K)
    (hx : ∀ a ∈ x, Rat.abs a ≤ 2 ^ (60 : ℤ)) (hy : ∀ a ∈ y, Rat.abs a ≤ 2 ^ (60 : ℤ)) :
    ∃ v, mcOzaki2 cdna3F16 z3Basis z3Bits x y = some v :=
  ozaki2_z3_isSome (cdna3F16_exactMultiplier (by decide)) hlen hk hx hy

end Ozaki.MC
