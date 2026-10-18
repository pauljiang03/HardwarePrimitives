import MatrixCore
import MCFloat.Model
import FloatLib.Floats.Formats.BinaryInterchange.DirectedSemantics.Rational.Logarithm

/-! # Arithmetic bridges

The `MatrixCore` exact-arithmetic helpers (written without mathlib) equal their mathlib and
FloatLib counterparts. -/

namespace MCFloat.Equivalence
open FloatLib.Floats.Formats.BinaryInterchange
open FloatLib.Numerics

@[simp] theorem pow2_eq (e : ℤ) : MatrixCore.pow2 e = MCFloat.pow2 e := rfl

@[simp] theorem abs_eq (x : ℚ) : MatrixCore.absQ x = |x| := by
  unfold MatrixCore.absQ
  split <;> rename_i h
  · exact (abs_of_neg h).symm
  · exact (abs_of_nonneg (le_of_not_gt h)).symm

@[simp] theorem sumQ_eq (xs : List ℚ) : MatrixCore.sumQ xs = xs.sum := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [MatrixCore.sumQ, ih]

theorem floor_eq (x : ℚ) : x.floor = ⌊x⌋ := rfl

@[simp] theorem rdGrid_eq (x : ℚ) (g : ℤ) : MatrixCore.rdGrid x g = MCFloat.rdGrid x g := rfl

@[simp] theorem truncGrid_eq (x : ℚ) (g : ℤ) :
    MatrixCore.truncGrid x g = MCFloat.truncGrid x g := rfl

theorem pow2_pos (e : ℤ) : 0 < MCFloat.pow2 e := MatrixCore.pow2_pos e

theorem abs_ratio (x : ℚ) : (x.num.natAbs : ℚ) / x.den = |x| := by
  calc
    _ = |(x.num : ℚ) / x.den| := by simp [abs_div]
    _ = |x| := congrArg abs (Rat.num_div_den x)

theorem real_ratio (x : ℚ) : (x.num.natAbs : ℝ) / x.den = ((|x| : ℚ) : ℝ) := by
  simpa only [Rat.cast_div, Rat.cast_natCast] using congrArg (fun q : ℚ => (q : ℝ)) (abs_ratio x)

theorem cast_pow2 (e : ℤ) : ((MCFloat.pow2 e : ℚ) : ℝ) = (2 : ℝ) ^ e := by
  simp [MCFloat.pow2]

theorem floorLog2_eq (x : ℚ) (hx : x ≠ 0) :
    RationalBinary.floorLog2 x.num.natAbs x.den = MatrixCore.log2Floor |x| := by
  obtain ⟨hl, hu⟩ := MatrixCore.log2Floor_spec (x := |x|) (abs_pos.mpr hx)
  apply Model.floorLog2_eq_of_bounds
  · exact fun h => hx (Rat.num_eq_zero.mp (Int.natAbs_eq_zero.mp h))
  · exact x.den_nz
  · change (2 : ℝ) ^ (MatrixCore.log2Floor |x|) ≤ (x.num.natAbs : ℝ) / x.den
    rw [real_ratio]
    have h := (Rat.cast_le (K := ℝ)).mpr hl
    simpa only [pow2_eq, cast_pow2] using h
  · change (x.num.natAbs : ℝ) / x.den < (2 : ℝ) ^ (MatrixCore.log2Floor |x| + 1)
    rw [real_ratio]
    have h := (Rat.cast_lt (K := ℝ)).mpr hu
    simpa only [pow2_eq, cast_pow2] using h

theorem normExp_eq (x : ℚ) (hx : x ≠ 0) :
    MCFloat.normExp x = MatrixCore.normExp (MatrixCore.absQ x) := by
  simp only [MCFloat.normExp, MatrixCore.normExp, floorLog2_eq x hx, abs_eq]

end MCFloat.Equivalence
