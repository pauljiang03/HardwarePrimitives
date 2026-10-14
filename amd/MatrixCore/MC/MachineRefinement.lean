import MatrixCore.MC.AccumulatorWidth
import MatrixCore.MC.Prepared

/-! # Fixed-width and exact accumulation give the same output

Every decoded operand has a significand below 2, so every product is below 4: a product aligned
to `e_max` with `23 + padding` mantissa bits fits in `23 + padding + 2` bits. With
`N_FMA ≤ 2^carryBits` products and a sign bit, a register of `23 + padding + 2 + carryBits + 1`
bits never wraps, on any prefix of the sum and in either grouping. -/

namespace MatrixCore

/-! ## Significand bounds -/

/-! ## Aligned products as integers -/

theorem truncBits_zero (g : ℤ) : truncBits 0 g = 0 := by
  have h := truncGrid_eq_truncBits 0 g
  rw [truncGrid_zero] at h
  have hp := pow2_ne_zero g
  have : ((truncBits 0 g : ℤ) : ℚ) = 0 := by
    rcases Rat.mul_eq_zero.mp h.symm with h | h
    · exact h
    · exact absurd h hp
  exact_mod_cast this

/-- An aligned product fits in `23 + padding + 2` bits. -/
theorem alignedBits_bound {padding : ℕ} {ps : List Unpacked} {e : ℤ} (he : maxExp ps = some e)
    (hb : ∀ p ∈ ps, p.m < 2 ^ (p.t + 2)) :
    ∀ z ∈ alignedBits padding e ps, z.natAbs < 2 ^ (23 + padding + 2) := by
  intro z hz
  simp only [alignedBits, List.mem_map] at hz
  obtain ⟨p, hp, rfl⟩ := hz
  by_cases hm : p.m = 0
  · rw [(Unpacked.value_eq_zero_iff p).mpr hm, truncBits_zero]
    exact Nat.two_pow_pos _
  · have hle := maxExp_le he p hp hm
    generalize hg : e - ((23 + padding : ℕ) : ℤ) = g
    have h1 := truncBits_natAbs_le p.value g
    rw [Unpacked.absQ_value] at h1
    have hmq : (p.m : ℚ) < pow2 ((p.t + 2 : ℕ) : ℤ) := by
      rw [pow2_natCast]; exact_mod_cast hb p hp
    have h2 : (p.m : ℚ) * pow2 (p.e - p.t) < pow2 (p.e + 2) := by
      have := Rat.mul_lt_mul_of_pos_right hmq (pow2_pos (p.e - p.t))
      rwa [← pow2_add, show ((p.t + 2 : ℕ) : ℤ) + (p.e - p.t) = p.e + 2 by omega] at this
    have h3 : pow2 (p.e + 2) ≤ pow2 (e + 2) := pow2_le_of_le (by omega)
    have h4 : pow2 (e + 2) = ((2 ^ (23 + padding + 2) : ℕ) : ℚ) * pow2 g := by
      rw [← pow2_natCast, ← pow2_add]; congr 1; omega
    have h5 : ((truncBits p.value g).natAbs : ℚ) * pow2 g <
        ((2 ^ (23 + padding + 2) : ℕ) : ℚ) * pow2 g := by
      rw [← h4]; grind
    have h6 : ((truncBits p.value g).natAbs : ℚ) < ((2 ^ (23 + padding + 2) : ℕ) : ℚ) := by
      apply Rat.not_le.mp
      intro hc
      exact Rat.not_le.mpr h5 (Rat.mul_le_mul_of_nonneg_right hc (Rat.le_of_lt (pow2_pos g)))
    exact_mod_cast h6

theorem alignedBits_magnitude {padding : ℕ} {ps : List Unpacked} {e : ℤ} (he : maxExp ps = some e)
    (hb : ∀ p ∈ ps, p.m < 2 ^ (p.t + 2)) :
    magnitudeSum (alignedBits padding e ps) ≤ ps.length * (2 ^ (23 + padding + 2) - 1) := by
  have := magnitudeSum_le_length_mul (alignedBits padding e ps) (2 ^ (23 + padding + 2) - 1)
    (fun z hz => by have := alignedBits_bound he hb z hz; omega)
  simpa [alignedBits] using this

/-- `ps.length` terms of at most `2^B − 1` fit below `2^(B + c)` when `ps.length ≤ 2^c`. -/
theorem count_mul_lt (n B c : ℕ) (h : n ≤ 2 ^ c) : n * (2 ^ B - 1) < 2 ^ (B + c) := by
  have hB := Nat.two_pow_pos B
  have hc := Nat.two_pow_pos c
  have h1 := Nat.mul_le_mul_right (2 ^ B - 1) h
  have h2 : 2 ^ c * (2 ^ B - 1) < 2 ^ c * 2 ^ B := Nat.mul_lt_mul_of_pos_left (by omega) hc
  rw [Nat.pow_add, Nat.mul_comm (2 ^ B)]
  omega

/-! ## One group in a register -/

/-- A group register holds the group's aligned sum exactly, and its magnitude is bounded by the
group size. -/
theorem machineAlignedSum_spec (w padding : ℕ) (ps : List Unpacked) (hw : 0 < w)
    (hb : ∀ p ∈ ps, p.m < 2 ^ (p.t + 2))
    (hcap : ps.length * (2 ^ (23 + padding + 2) - 1) < 2 ^ (w - 1)) :
    alignedSum padding ps = ((machineAlignedSum w padding ps).1,
      ((machineAlignedSum w padding ps).2.toInt : ℚ) *
        pow2 ((machineAlignedSum w padding ps).1.getD 0 - (23 + padding : ℕ))) ∧
    ((machineAlignedSum w padding ps).2.toInt).natAbs ≤ ps.length * (2 ^ (23 + padding + 2) - 1) ∧
    ((machineAlignedSum w padding ps).1 = none → (machineAlignedSum w padding ps).2.toInt = 0) := by
  unfold alignedSum machineAlignedSum
  cases he : maxExp ps with
  | none => simp
  | some e =>
    have hm := alignedBits_magnitude (padding := padding) he hb
    have hx := machineAccumulate_exact w (alignedBits padding e ps) hw (by omega)
    simp only [Option.getD_some, reduceCtorEq, false_implies, and_true]
    rw [hx, sumQ_truncMantissa_eq]
    exact ⟨rfl, by have := sumZ_natAbs_le (alignedBits padding e ps); omega⟩

/-- Moving a register to a coarser exponent by an arithmetic right shift is the RD of the
model. -/
theorem shiftRegister_spec {w : ℕ} (F : ℕ) (e : ℤ) (s : Option ℤ × BitVec w)
    (hle : ∀ v, s.1 = some v → v ≤ e) (hz : s.1 = none → s.2.toInt = 0) :
    rdMantissa ((s.2.toInt : ℚ) * pow2 (s.1.getD 0 - F)) e F =
        ((shiftRegister e s).toInt : ℚ) * pow2 (e - F) ∧
      ((shiftRegister e s).toInt).natAbs ≤ (s.2.toInt).natAbs := by
  obtain ⟨o, r⟩ := s
  unfold shiftRegister
  simp only [BitVec.toInt_sshiftRight, Int.shiftRight_eq_div_pow] at *
  refine ⟨?_, Int.natAbs_ediv_le_natAbs _ _⟩
  cases o with
  | none =>
    have h0 := hz rfl
    simp only [h0, Int.zero_ediv, Rat.intCast_zero, Rat.zero_mul]
    exact rdGrid_zero _
  | some v =>
    have hv := hle v rfl
    simp only [Option.getD_some]
    have hg : e - (F : ℤ) = (v - F) + (((e - v).toNat : ℕ) : ℤ) := by omega
    rw [show rdMantissa ((r.toInt : ℚ) * pow2 (v - F)) e F =
        rdGrid ((r.toInt : ℚ) * pow2 (v - F)) (e - F) from rfl, hg, rdGrid_eq_rdBits,
      rdBits_intCast_mul, Int.shiftRight_eq_div_pow]

/-! ## The configuration -/

/-- With `|ps| ≤ 2^carryBits` products of significand below 4, `w`-bit registers give the model's
`(e_max, S_{p_i,sum})` in both groupings. -/
theorem machineProductSum_eq (w carryBits : ℕ) (P : Model) (ps : List Unpacked)
    (hb : ∀ p ∈ ps, p.m < 2 ^ (p.t + 2)) (hcount : ps.length ≤ 2 ^ carryBits)
    (hw : P.alignMantissaBits + 2 + carryBits + 1 ≤ w) :
    machineProductSum w P ps = productSum P ps := by
  have hw0 : 0 < w := by omega
  have hcap : ps.length * (2 ^ (23 + P.padding + 2) - 1) < 2 ^ (w - 1) :=
    Nat.lt_of_lt_of_le (count_mul_lt _ _ _ hcount)
      (Nat.pow_le_pow_right (by decide) (by simp only [Model.alignMantissaBits] at hw; omega))
  unfold machineProductSum productSum
  cases hacc : P.accumulation
  case oddEvenGrouping =>
    simp only
    obtain ⟨hsum, hlen⟩ := sumQ_odd_even Unpacked.value ps
    have hbo : ∀ p ∈ oddIndexed ps, p.m < 2 ^ (p.t + 2) := fun p hp => hb p (oddIndexed_subset ps p hp)
    have hbe : ∀ p ∈ evenIndexed ps, p.m < 2 ^ (p.t + 2) := fun p hp => hb p (evenIndexed_subset ps p hp)
    have hmul := Nat.add_mul (oddIndexed ps).length (evenIndexed ps).length (2 ^ (23 + P.padding + 2) - 1)
    rw [hlen] at hmul
    obtain ⟨ho, hmo, hzo⟩ := machineAlignedSum_spec w P.padding (oddIndexed ps) hw0 hbo (by omega)
    obtain ⟨he, hme, hze⟩ := machineAlignedSum_spec w P.padding (evenIndexed ps) hw0 hbe (by omega)
    rw [ho, he]
    generalize machineAlignedSum w P.padding (oddIndexed ps) = O at *
    generalize machineAlignedSum w P.padding (evenIndexed ps) = E at *
    simp only
    cases hj : joinExp O.1 E.1 with
    | none => rfl
    | some e =>
      simp only
      have hleo : ∀ v, O.1 = some v → v ≤ e := by
        intro v hv; rw [hv] at hj; cases hE : E.1 <;> rw [hE] at hj <;> simp [joinExp] at hj <;> omega
      have hlee : ∀ v, E.1 = some v → v ≤ e := by
        intro v hv; rw [hv] at hj; cases hO : O.1 <;> rw [hO] at hj <;> simp [joinExp] at hj <;> omega
      obtain ⟨rdo, so⟩ := shiftRegister_spec (23 + P.padding) e O hleo hzo
      obtain ⟨rde, se⟩ := shiftRegister_spec (23 + P.padding) e E hlee hze
      rw [rdo, rde, bitVec_add_toInt _ _ hw0 (by
        have := Int.natAbs_add_le (shiftRegister e O).toInt (shiftRegister e E).toInt; omega),
        Rat.intCast_add, Rat.add_mul]
  all_goals
    simp only
    exact (machineAlignedSum_spec w P.padding ps hw0 hb hcap).1.symm

theorem accumulateMachine_eq (w : ℕ) (P : Model) (x : Prepared)
    (h : machineProductSum w P x.p = productSum P x.p) :
    accumulateMachine w P x = accumulate P x := by
  unfold accumulateMachine accumulate machineAlignedAccumulation alignedAccumulation
  rw [h]
  split
  · rfl
  · cases P.accumulation <;> rfl

/-- **Fixed-width refinement.** For every model and every input, accumulating the products in
`w`-bit registers gives the model's result, whenever `N_FMA ≤ 2^carryBits` and
`23 + padding + 2 + carryBits + 1 ≤ w`. -/
theorem evalBlockMachine_eq {P : Model} (x : BlockInput P) (w carryBits : ℕ)
    (hcount : P.nfma ≤ 2 ^ carryBits) (hw : P.alignMantissaBits + 2 + carryBits + 1 ≤ w) :
    evalBlockMachine w x = evalBlock x := by
  unfold evalBlockMachine evalBlock
  split
  · rfl
  · rename_i hlen
    cases hp : prepare x with
    | none => rfl
    | some px =>
      obtain ⟨hla, ha, hb⟩ := prepare_bounded hp
      have hpl : px.p.length ≤ 2 ^ carryBits := by
        have := Prepared.p_length px
        simp only [not_or, Decidable.not_not] at hlen
        omega
      simp only
      rw [accumulateMachine_eq w P px
        (machineProductSum_eq w carryBits P px.p (products_bounded ha hb) hpl hw)]
      cases accumulate P px with
      | error e => rfl
      | ok s => cases fl32 (!P.subnormals) s <;> rfl

/-- Every prefix of the aligned products, in any order, is exact in the register. -/
theorem machinePrefix_exact (w carryBits padding : ℕ) {ps : List Unpacked} {e : ℤ}
    (he : maxExp ps = some e) (hb : ∀ p ∈ ps, p.m < 2 ^ (p.t + 2))
    (hcount : ps.length ≤ 2 ^ carryBits) (hw : 23 + padding + 2 + carryBits + 1 ≤ w)
    (xs ys : List ℤ) (hperm : (xs ++ ys).Perm (alignedBits padding e ps)) :
    (machineAccumulate w 0 xs).toInt = sumZ xs := by
  apply machineAccumulate_prefix_exact w xs ys (by omega)
  rw [magnitudeSum_perm hperm]
  have := alignedBits_magnitude (padding := padding) he hb
  have := count_mul_lt ps.length (23 + padding + 2) carryBits hcount
  have := Nat.pow_le_pow_right (show 0 < 2 by decide) (show 23 + padding + 2 + carryBits ≤ w - 1 by omega)
  omega

/-! ## CDNA 3 register widths -/

/-- CDNA 3 fp16: 26 bits per aligned product, 3 carry bits for 8 products, and a sign bit. -/
theorem cdna3F16_machine_eq (x : BlockInput cdna3F16) : evalBlockMachine 30 x = evalBlock x :=
  evalBlockMachine_eq x 30 3 (by decide) (by decide)

theorem cdna3BF16_machine_eq (x : BlockInput cdna3BF16) : evalBlockMachine 30 x = evalBlock x :=
  evalBlockMachine_eq x 30 3 (by decide) (by decide)

/-- CDNA 3 XF32: 4 products, so 2 carry bits. -/
theorem cdna3XF32_machine_eq (x : BlockInput cdna3XF32) : evalBlockMachine 29 x = evalBlock x :=
  evalBlockMachine_eq x 29 2 (by decide) (by decide)

/-- CDNA 3 binary8: 16 products in two groups of eight; one more carry bit holds the combined
odd and even sums. -/
theorem cdna3FP8_machine_eq (fa fb : Format) (x : BlockInput (cdna3FP8 fa fb)) :
    evalBlockMachine 31 x = evalBlock x :=
  evalBlockMachine_eq x 31 4 (by simp [cdna3FP8]) (by simp [cdna3FP8, Model.alignMantissaBits])

end MatrixCore
