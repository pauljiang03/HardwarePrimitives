import OzakiTC.Schemes
import Ozaki.Success

/-! # The Tensor Core pipelines return a value

The Z3 models check that no NaN or infinity ever appears (`[H.1]` of both models). On the Tensor
Core model the schemes return `none` only when a binary32 rounding overflows, and TC-EFT's
binary32 converter succeeds on every value of magnitude at most `maxFinite32`
(`round32Value_succeeds`). With an exact engine:

* `tcOzaki1_isSome`: Ozaki-I returns a value when
  `(1 + 2^-24)^n · n k 2^(E+F) + n (1 + 2^-24)^n 2^-150 ≤ maxFinite32`;
* `tcOzaki2_isSome`: Ozaki-II returns a value when `k 2^((P − sₓ) + (P − s_y)) ≤ maxFinite32`;
* `ozaki1_z3_isSome`, `ozaki2_z3_isSome`: in the Z3 configuration (`k = 4`), on any path exact on
  `11`-bit slices, both return a value whenever every entry of `x` and `y` is at most `2^60` in
  magnitude; `v100_ozaki1_z3_isSome` and `v100_ozaki2_z3_isSome` are the V100 instances. -/

open TensorCore

namespace Ozaki.TC

/-- **Binary32 rounding succeeds in range.** `round32Value` returns a value for every rational of
magnitude at most `maxFinite32`. -/
theorem round32Value_succeeds : RoundSucceeds round32Value maxFinite32 := by
  intro q hq
  have h := roundRNE_isSome (p := 24) (emin := -126) (emax := 127) (q := q) (by decide) (by decide)
    (by rw [← maxFinite32_eq_maxFormat]; exact hq)
  obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp h
  exact ⟨v, hv⟩

theorem add32_succeeds : AddSucceeds add32 maxFinite32 := by
  rw [add32_eq_addOfRound]; exact addOfRound_succeeds round32Value_succeeds

/-- **Ozaki-I returns a value on the Tensor Core** (`[H.1]`). -/
theorem tcOzaki1_isSome {p : Model} {b : ℕ} (hmult : (tcMultiplier p).ExactOn b (2 ^ 24)) (s : ℕ)
    {x y : List ℚ} (hlen : x.length = y.length) (hk : x.length * (2 ^ b * 2 ^ b) ≤ 2 ^ 24)
    (hL : (1 + 2 ^ (-24 : ℤ)) ^ (trianglePairs s).length *
        ((trianglePairs s).length * (x.length * 2 ^ (splitExp b x + splitExp b y))) +
      (trianglePairs s).length * (1 + 2 ^ (-24 : ℤ)) ^ (trianglePairs s).length * 2 ^ (-150 : ℤ) ≤
        maxFinite32) :
    ∃ v, tcOzaki1 p b s x y = some v :=
  ozaki1_isSome hmult (Rat.le_of_lt (two_pow_pos _)) (Rat.le_of_lt (two_pow_pos _)) add32_within
    add32_succeeds hlen hk hL

/-- **Ozaki-II returns a value on the Tensor Core** (`[H.1]`). -/
theorem tcOzaki2_isSome {p : Model} {b : ℕ} (hmult : (tcMultiplier p).ExactOn b (2 ^ 24))
    {B : CRTBasis} (hB : B.Valid) (hmb : ∀ m ∈ B.moduli, m ≤ 2 ^ (b + 1)) (P : ℕ) {x y : List ℚ}
    (hlen : x.length = y.length) (hk : x.length * (2 ^ b * 2 ^ b) ≤ 2 ^ 24)
    (hrange : 2 * x.length * (2 ^ P * 2 ^ P) < B.modulus)
    (hL : x.length * (2 : ℚ) ^ ((P - scaleShift P x) + (P - scaleShift P y)) ≤ maxFinite32) :
    ∃ v, tcOzaki2 p B P x y = some v :=
  ozaki2_isSome hmult round32Value_succeeds hB hmb P hlen hk hrange hL

/-! ## The Z3 configuration -/

/-- The overflow condition of `tcOzaki1_isSome` for `k = 4`, four slices, and `E + F ≤ 120`. -/
theorem z3_ozaki1_range : (1 + (2 : ℚ) ^ (-24 : ℤ)) ^ 10 * (10 * (4 * 2 ^ (120 : ℤ))) +
    10 * (1 + (2 : ℚ) ^ (-24 : ℤ)) ^ 10 * 2 ^ (-150 : ℤ) ≤ maxFinite32 := by decide +kernel

/-- The overflow condition of `tcOzaki2_isSome` for `k = 4` and exponents summing to `120`. -/
theorem z3_ozaki2_range : 4 * (2 : ℚ) ^ (120 : ℤ) ≤ maxFinite32 := by decide +kernel

/-- **The Z3 Ozaki-I model returns a value** on any path exact on `11`-bit slices, whenever every
entry of `x` and `y` is at most `2^60` in magnitude. -/
theorem ozaki1_z3_isSome {p : Model} (hmult : (tcMultiplier p).ExactOn z3SliceBits (2 ^ 24))
    {x y : List ℚ} (hlen : x.length = y.length) (hk : x.length = z3K)
    (hx : ∀ a ∈ x, Rat.abs a ≤ 2 ^ (60 : ℤ)) (hy : ∀ a ∈ y, Rat.abs a ≤ 2 ^ (60 : ℤ)) :
    ∃ v, tcOzaki1 p z3SliceBits z3Slices x y = some v := by
  refine tcOzaki1_isSome hmult z3Slices hlen (by rw [hk]; decide) ?_
  have hE := splitExp_le z3SliceBits hx (by decide)
  have hF := splitExp_le z3SliceBits hy (by decide)
  have hX := two_pow_le (show splitExp z3SliceBits x + splitExp z3SliceBits y ≤ 120 by omega)
  rw [z3_slice_products, hk]
  generalize (2 : ℚ) ^ (splitExp z3SliceBits x + splitExp z3SliceBits y) = X at hX
  have hP : (0 : ℚ) ≤ (1 + 2 ^ (-24 : ℤ)) ^ 10 := Rat.pow_nonneg (by have := two_pow_pos (-24); grind)
  have h1 : ((10 : ℕ) : ℚ) * (((z3K : ℕ) : ℚ) * X) ≤ 10 * (4 * 2 ^ (120 : ℤ)) := by
    have : ((z3K : ℕ) : ℚ) = 4 := rfl
    rw [this]; have : ((10 : ℕ) : ℚ) = 10 := rfl
    rw [this]; grind
  have h2 := Rat.mul_le_mul_of_nonneg_left h1 hP
  have h3 : ((10 : ℕ) : ℚ) = 10 := rfl
  rw [h3]
  have := z3_ozaki1_range
  grind

/-- **The Z3 Ozaki-II model returns a value** on any path exact on `11`-bit slices, whenever every
entry of `x` and `y` is at most `2^60` in magnitude. -/
theorem ozaki2_z3_isSome {p : Model} (hmult : (tcMultiplier p).ExactOn z3SliceBits (2 ^ 24))
    {x y : List ℚ} (hlen : x.length = y.length) (hk : x.length = z3K)
    (hx : ∀ a ∈ x, Rat.abs a ≤ 2 ^ (60 : ℤ)) (hy : ∀ a ∈ y, Rat.abs a ≤ 2 ^ (60 : ℤ)) :
    ∃ v, tcOzaki2 p z3Basis z3Bits x y = some v := by
  refine tcOzaki2_isSome hmult z3Basis_valid z3Moduli_le z3Bits hlen (by rw [hk]; decide)
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

/-- The Z3 Ozaki-I model returns a value on V100 for entries at most `2^60`. -/
theorem v100_ozaki1_z3_isSome {x y : List ℚ} (hlen : x.length = y.length) (hk : x.length = z3K)
    (hx : ∀ a ∈ x, Rat.abs a ≤ 2 ^ (60 : ℤ)) (hy : ∀ a ∈ y, Rat.abs a ≤ 2 ^ (60 : ℤ)) :
    ∃ v, tcOzaki1 v100F16F32 z3SliceBits z3Slices x y = some v :=
  ozaki1_z3_isSome v100_exactOn hlen hk hx hy

/-- The Z3 Ozaki-II model returns a value on V100 for entries at most `2^60`. -/
theorem v100_ozaki2_z3_isSome {x y : List ℚ} (hlen : x.length = y.length) (hk : x.length = z3K)
    (hx : ∀ a ∈ x, Rat.abs a ≤ 2 ^ (60 : ℤ)) (hy : ∀ a ∈ y, Rat.abs a ≤ 2 ^ (60 : ℤ)) :
    ∃ v, tcOzaki2 v100F16F32 z3Basis z3Bits x y = some v :=
  ozaki2_z3_isSome v100_exactOn hlen hk hx hy

end Ozaki.TC
