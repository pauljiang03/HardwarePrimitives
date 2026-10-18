import TensorCore.Numerics.Sum
import TensorCore.TC.Accumulator

/-! Fixed-width accumulation is exact at adequate width. -/

namespace TensorCore

theorem machineAccumulate_eq (w : ℕ) (initial : ℤ) (zs : List ℤ) :
    machineAccumulate w (BitVec.ofInt w initial) zs = BitVec.ofInt w (initial + sumZ zs) := by
  induction zs generalizing initial with
  | nil => simp [machineAccumulate, sumZ]
  | cons z zs ih =>
    simp only [machineAccumulate, ← BitVec.ofInt_add, ih, sumZ]
    congr 1
    omega

/-- Final signed value is exact whenever total absolute support fits the positive range. -/
theorem machineAccumulate_exact (w : ℕ) (zs : List ℤ) (hw : 0 < w)
    (h : magnitudeSum zs < 2 ^ (w - 1)) :
    (machineAccumulate w 0 zs).toInt = sumZ zs := by
  have hs := sumZ_natAbs_le zs
  have hp : ((2 ^ (w - 1) : ℕ) : ℤ) = (2 : ℤ) ^ (w - 1) := by simp
  have hb : (machineAccumulate w 0 zs) = BitVec.ofInt w (sumZ zs) := by
    simpa using machineAccumulate_eq w 0 zs
  rw [hb]
  apply BitVec.toInt_ofInt_eq_self hw <;> omega

/-- Every prefix is exact under the same support condition, even with cancellation. -/
theorem machineAccumulate_prefix_exact (w : ℕ) (xs ys : List ℤ) (hw : 0 < w)
    (h : magnitudeSum (xs ++ ys) < 2 ^ (w - 1)) :
    (machineAccumulate w 0 xs).toInt = sumZ xs := by
  apply machineAccumulate_exact w xs hw
  rw [magnitudeSum_append] at h
  omega

theorem machineAccumulate_of_coefficient_bound (zs : List ℤ) (B c : ℕ)
    (hterm : ∀ z ∈ zs, z.natAbs < 2 ^ B) (hcount : zs.length ≤ 2 ^ c) :
    (machineAccumulate (B + c + 1) 0 zs).toInt = sumZ zs :=
  machineAccumulate_exact _ zs (by omega) (coefficient_width_sufficient zs B c hterm hcount)

theorem machineAccumulator_eq (b : PreparedBlock) (w : ℕ) (hw : 0 < w)
    (h : magnitudeSum b.alignedBits < 2 ^ (w - 1)) :
    b.machineAccumulator w = b.accumulator := by
  unfold PreparedBlock.machineAccumulator PreparedBlock.accumulator
  rw [machineAccumulate_exact w b.alignedBits hw h]

end TensorCore
