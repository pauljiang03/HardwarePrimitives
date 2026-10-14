import MatrixCore.MC.Accumulator

/-! # Fixed-width accumulation is exact at adequate width -/

namespace MatrixCore

theorem machineAccumulate_eq (w : ℕ) (initial : ℤ) (zs : List ℤ) :
    machineAccumulate w (BitVec.ofInt w initial) zs = BitVec.ofInt w (initial + sumZ zs) := by
  induction zs generalizing initial with
  | nil => simp [machineAccumulate, sumZ]
  | cons z zs ih =>
    simp only [machineAccumulate, ← BitVec.ofInt_add, ih, sumZ]
    congr 1
    omega

/-- The final signed value is exact whenever the total magnitude fits the positive range. -/
theorem machineAccumulate_exact (w : ℕ) (zs : List ℤ) (hw : 0 < w)
    (h : magnitudeSum zs < 2 ^ (w - 1)) :
    (machineAccumulate w 0 zs).toInt = sumZ zs := by
  have hs := sumZ_natAbs_le zs
  have hp : ((2 ^ (w - 1) : ℕ) : ℤ) = (2 : ℤ) ^ (w - 1) := by simp
  have hb : (machineAccumulate w 0 zs) = BitVec.ofInt w (sumZ zs) := by
    simpa using machineAccumulate_eq w 0 zs
  rw [hb]
  apply BitVec.toInt_ofInt_eq_self hw <;> omega

/-- Every prefix is exact under the same condition, even with cancellation. -/
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

/-- A `w`-bit sum of two registers is exact when the exact sum fits. -/
theorem bitVec_add_toInt (x y : BitVec w) (hw : 0 < w)
    (h : (x.toInt + y.toInt).natAbs < 2 ^ (w - 1)) : (x + y).toInt = x.toInt + y.toInt := by
  have hp : ((2 ^ (w - 1) : ℕ) : ℤ) = (2 : ℤ) ^ (w - 1) := by simp
  have hs : x + y = BitVec.ofInt w (x.toInt + y.toInt) := by
    rw [BitVec.ofInt_add, BitVec.ofInt_toInt, BitVec.ofInt_toInt]
  rw [hs]
  apply BitVec.toInt_ofInt_eq_self hw <;> omega

/-- The exact sum of the aligned products is the integer sum placed on the alignment grid. -/
theorem sumQ_truncMantissa_eq (padding : ℕ) (e : ℤ) (ps : List Unpacked) :
    sumQ (ps.map fun p => truncMantissa p.value e (23 + padding)) =
      (sumZ (alignedBits padding e ps) : ℚ) * pow2 (e - (23 + padding : ℕ)) := by
  rw [← sumQ_map_intCast_mul, alignedBits, List.map_map]
  congr 1
  apply List.map_congr_left
  intro p _
  exact truncGrid_eq_truncBits _ _

end MatrixCore
