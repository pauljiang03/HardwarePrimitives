import TensorCore.TC.Monotonicity

/-! TC-EFT Theorem III.5: range and effect of the non-monotonic perturbation. -/

namespace TensorCore

/-- `c_j = 1 − j·2^-24` in decoded form: significand `2^24 − j` on exponent `−1`. -/
def belowDecoded (j : ℕ) : Decoded := ⟨((16777216 - j : ℕ) : ℤ), -1, 23⟩

theorem belowDecoded_one : belowDecoded 1 = belowOneDecoded := rfl

theorem belowDecoded_value (j : ℕ) (hj : j ≤ 16777216) :
    (belowDecoded j).value = 1 - (j : ℚ) * pow2 (-24) := by
  have h : ((16777216 - j : ℕ) : ℚ) + (j : ℚ) = ((16777216 : ℕ) : ℚ) := by
    rw [← Rat.natCast_add, Nat.sub_add_cancel hj]
  have h24 : ((16777216 : ℕ) : ℚ) * pow2 (-24) = 1 := by decide +kernel
  show (((16777216 - j : ℕ) : ℤ) : ℚ) * pow2 (-1 - 23) = _
  rw [Rat.intCast_natCast, show (-1 - 23 : ℤ) = -24 by decide]
  grind

theorem floor_eq_of_bounds (x : ℚ) (z : ℤ) (h1 : (z : ℚ) ≤ x) (h2 : x < (z : ℚ) + 1) :
    x.floor = z := by
  have a : z ≤ x.floor := Rat.le_floor_iff.mpr h1
  have b : x.floor < z + 1 := Rat.floor_lt_iff.mpr (by rw [Rat.intCast_add, Rat.intCast_one]; exact h2)
  omega

/-- The floor of a natural number scaled by `2^-d` is its quotient by `2^d`. -/
theorem floor_natCast_mul_pow2_neg (N d : ℕ) :
    ((N : ℚ) * pow2 (-(d : ℤ))).floor = ((N / 2 ^ d : ℕ) : ℤ) := by
  have hnd := pow2_pos (-(d : ℤ))
  have hcancel : pow2 (d : ℤ) * pow2 (-(d : ℤ)) = 1 := by
    rw [← pow2_add]
    have : (d : ℤ) + -(d : ℤ) = 0 := by omega
    rw [this, pow2_zero]
  apply floor_eq_of_bounds
  · have h : ((N / 2 ^ d * 2 ^ d : ℕ) : ℚ) ≤ (N : ℚ) :=
      Rat.natCast_le_natCast.mpr (Nat.div_mul_le_self N (2 ^ d))
    have := Rat.mul_le_mul_of_nonneg_right h (Rat.le_of_lt hnd)
    rw [Rat.natCast_mul, ← pow2_natCast, Rat.mul_assoc, hcancel, Rat.mul_one] at this
    rw [Rat.intCast_natCast]
    exact this
  · have h : (N : ℚ) < ((2 ^ d * (N / 2 ^ d + 1) : ℕ) : ℚ) :=
      Rat.natCast_lt_natCast.mpr (Nat.lt_mul_div_succ N (Nat.two_pow_pos d))
    have := Rat.mul_lt_mul_of_pos_right h hnd
    rw [Rat.natCast_mul, ← pow2_natCast, Rat.mul_comm (pow2 _), Rat.mul_assoc, hcancel,
      Rat.mul_one, Rat.natCast_add] at this
    rw [Rat.intCast_natCast]
    simpa using this

/-- Accumulator with `c_j`: every product is retained and `A_j = 1 + (K − j·2^p)·2^-(24+p)`, written as a natural coefficient on the grid `2^-(24+p)`. -/
theorem construction_accumulator_range (prof : Model) (p K j : ℕ) (da db : Decoded)
    (hF : prof.alignMantissaBits = 23 + p) (hfl : ∀ f ∈ prof.eAlignMin, f ≤ -1)
    (hval : (denormalizedMul da db).value = pow2 (-(24 + p))) (hscale : (denormalizedMul da db).exponent ≤ -1)
    (hj : j ≤ 2 ^ 23) :
    (PreparedBlock.mk prof (List.replicate K (da, db)) (belowDecoded j)).accumulator =
      (((16777216 - j) * 2 ^ p + K : ℕ) : ℚ) * pow2 (-(24 + p)) := by
  have hu := denormalizedMul_significand_ne_zero da db p hval
  have hsig : (belowDecoded j).significand ≠ 0 := by
    show ((16777216 - j : ℕ) : ℤ) ≠ 0
    omega
  have heta := construction_alignExp prof K da db (belowDecoded j) hsig hu hscale hfl
  have hq : (PreparedBlock.mk prof (List.replicate K (da, db)) (belowDecoded j)).alignGridExponent =
      -(24 + p) := by
    unfold PreparedBlock.alignGridExponent
    rw [heta]
    change (belowDecoded j).exponent - prof.alignMantissaBits = _
    rw [hF]
    simp only [belowDecoded]
    omega
  have hcoef := construction_alignedBits prof K da db (belowDecoded j)
  rw [hq] at hcoef
  have hc : truncBits (belowDecoded j).value (-(24 + p)) =
      (((16777216 - j) * 2 ^ p : ℕ) : ℤ) := by
    have h1 : (belowDecoded j).value =
        ((((16777216 - j) * 2 ^ p : ℕ) : ℤ) : ℚ) * pow2 (-(24 + p)) := by
      show (((16777216 - j : ℕ) : ℤ) : ℚ) * pow2 (-1 - 23) = _
      rw [Rat.intCast_natCast, Rat.intCast_natCast, Rat.natCast_mul, ← pow2_natCast,
        Rat.mul_assoc, ← pow2_add]
      congr 2
      omega
    rw [h1, truncBits_of_grid]
  have hp : truncBits (denormalizedMul da db).value (-(24 + p)) = 1 := by
    rw [hval]
    have h1 : pow2 (-(24 + p)) = ((1 : ℤ) : ℚ) * pow2 (-(24 + p)) := by simp
    rw [h1, truncBits_of_grid]
  unfold PreparedBlock.accumulator
  rw [hcoef, hq]
  simp only [sumZ, hc, hp, sumZ_replicate, Int.mul_one]
  congr 1
  all_goals rw [Rat.intCast_add, Rat.intCast_natCast, Rat.intCast_natCast, Rat.natCast_add]

/-- TC-EFT Theorem III.5 on prepared blocks. -/
theorem nonmonotone_range (prof : Model) (p K j : ℕ) (da db : Decoded)
    (hF : prof.alignMantissaBits = 23 + p) (hfl : ∀ f ∈ prof.eAlignMin, f ≤ -1)
    (hw : 23 ≤ prof.outputMantissaBits)
    (hval : (denormalizedMul da db).value = pow2 (-(24 + p))) (hscale : (denormalizedMul da db).exponent ≤ -1)
    (hK : K < 2 ^ (24 + p)) (hj1 : 1 ≤ j) (hj2 : j ≤ 2 ^ 23) :
    ∃ t : BlockTrace,
      evalPrepared ⟨prof, List.replicate K (da, db), belowDecoded j⟩ = .ok t ∧
      (1 < t.output.value ↔ (j + 2) * 2 ^ p ≤ K) ∧
      (j * 2 ^ p ≤ K →
        t.output.value = 1 + (((K - j * 2 ^ p) / 2 ^ (p + 1) : ℕ) : ℚ) * pow2 (-23)) ∧
      t.output.value ≤ 1 + (((K - 2 ^ p) / 2 ^ (p + 1) : ℕ) : ℚ) * pow2 (-23) := by
  have hA := construction_accumulator_range prof p K j da db hF hfl hval hscale hj2
  have hq := pow2_pos (-(24 + p))
  have hq23 := pow2_pos (-23)
  have hPpos := Nat.two_pow_pos p
  have h2p24 : 2 ^ (24 + p) = 16777216 * 2 ^ p := by
    rw [Nat.pow_add]
    all_goals simp
  have h2p25 : 2 ^ (25 + p) = 2 * (16777216 * 2 ^ p) := by
    rw [show 25 + p = 1 + (24 + p) by omega, Nat.pow_add, Nat.pow_add]
    all_goals simp
  have h2p1 : 2 ^ (p + 1) = 2 ^ p * 2 := Nat.pow_succ 2 p
  have hjP : j * 2 ^ p ≤ 8388608 * 2 ^ p := Nat.mul_le_mul_right _ hj2
  have hjP1 : 2 ^ p ≤ j * 2 ^ p := by
    have := Nat.mul_le_mul_right (2 ^ p) hj1
    simpa using this
  have hsub : (16777216 - j) * 2 ^ p = 16777216 * 2 ^ p - j * 2 ^ p := Nat.sub_mul _ _ _
  have hM : ∀ m : ℕ, (0 : ℚ) ≤ (m : ℚ) * pow2 (-23) := fun m =>
    Rat.mul_nonneg Rat.natCast_nonneg (Rat.le_of_lt hq23)
  have hMle : (K - j * 2 ^ p) / 2 ^ (p + 1) ≤ (K - 2 ^ p) / 2 ^ (p + 1) :=
    Nat.div_le_div_right (Nat.sub_le_sub_left hjP1 K)
  have hMle' : (((K - j * 2 ^ p) / 2 ^ (p + 1) : ℕ) : ℚ) * pow2 (-23) ≤
      (((K - 2 ^ p) / 2 ^ (p + 1) : ℕ) : ℚ) * pow2 (-23) :=
    Rat.mul_le_mul_of_nonneg_right (Rat.natCast_le_natCast.mpr hMle) (Rat.le_of_lt hq23)
  generalize hN : (16777216 - j) * 2 ^ p + K = N at hA
  generalize hA' : (N : ℚ) * pow2 (-(24 + p)) = A at hA
  have hNpos : (0 : ℚ) < (N : ℚ) := Rat.natCast_pos.mpr (by omega)
  have hApos : 0 < A := by
    rw [← hA']
    have := Rat.mul_lt_mul_of_pos_right hNpos hq
    simpa using this
  have hA2lt : A < 2 := by
    rw [← hA']
    have hlt : (N : ℚ) < ((2 ^ (25 + p) : ℕ) : ℚ) := by
      apply Rat.natCast_lt_natCast.mpr
      omega
    have := Rat.mul_lt_mul_of_pos_right hlt hq
    rw [← pow2_natCast, ← pow2_add] at this
    have h25 : ((25 + p : ℕ) : ℤ) + -(24 + p) = 1 := by omega
    rw [h25, pow2_one] at this
    exact this
  have hrange : absQ A ≤ maxFinite32 := by
    rw [absQ_of_nonneg (Rat.le_of_lt hApos)]
    have : (2 : ℚ) ≤ maxFinite32 := by decide +kernel
    grind
  obtain ⟨b, hb, hv, _, _⟩ := round32_nonzero_spec .truncate A (Rat.ne_of_gt hApos) hrange
  obtain ⟨f, hf, _, hfv⟩ := finite32_of_value32 _ _ hv
  refine ⟨⟨⟨prof, List.replicate K (da, db), belowDecoded j⟩, f⟩, ?_, ?_⟩
  · simp only [evalPrepared, hA, hb, truncateMantissa32_of_le hw, hf]
  · change (1 < f.value ↔ _) ∧ (_ → f.value = _) ∧ f.value ≤ _
    rw [hfv]
    unfold signedRounded
    rw [if_neg (by grind), absQ_of_nonneg (Rat.le_of_lt hApos)]
    unfold magnitudeRounded roundedSignificand roundSignificand
    dsimp only
    by_cases hjK : j * 2 ^ p ≤ K
    · have hAge : 1 ≤ A := by
        rw [← hA']
        have hle : ((2 ^ (24 + p) : ℕ) : ℚ) ≤ (N : ℚ) := by
          apply Rat.natCast_le_natCast.mpr
          omega
        have := Rat.mul_le_mul_of_nonneg_right hle (Rat.le_of_lt hq)
        rw [← pow2_natCast, ← pow2_add] at this
        have h24 : ((24 + p : ℕ) : ℤ) + -(24 + p) = 0 := by omega
        rw [h24, pow2_zero] at this
        exact this
      have hexp : normExp A = 0 := by
        unfold normExp emin32
        rw [magnitudeExponent_eq_of_bounds A 0 (by rw [pow2_zero]; exact hAge)
          (by rw [show (0 : ℤ) + 1 = 1 by omega, pow2_one]; exact hA2lt)]
        decide
      rw [hexp]
      simp only [Int.zero_sub]
      rw [div_pow2, Int.neg_neg]
      have hA23 : A * pow2 23 = (N : ℚ) * pow2 (-((1 + p : ℕ) : ℤ)) := by
        rw [← hA', Rat.mul_assoc, ← pow2_add]
        congr 2
        omega
      rw [hA23, floor_natCast_mul_pow2_neg]
      have hdiv : N / 2 ^ (1 + p) = 8388608 + (K - j * 2 ^ p) / 2 ^ (p + 1) := by
        have h1 : N = 2 ^ (p + 1) * 8388608 + (K - j * 2 ^ p) := by
          rw [h2p1]
          omega
        rw [Nat.add_comm 1 p, h1, Nat.mul_add_div (Nat.two_pow_pos _)]
      rw [hdiv]
      have hval' : (((8388608 + (K - j * 2 ^ p) / 2 ^ (p + 1) : ℕ) : ℤ) : ℚ) * pow2 (-23) =
          1 + (((K - j * 2 ^ p) / 2 ^ (p + 1) : ℕ) : ℚ) * pow2 (-23) := by
        rw [Rat.intCast_natCast, Rat.natCast_add, Rat.add_mul]
        have : ((8388608 : ℕ) : ℚ) * pow2 (-23) = 1 := by decide +kernel
        rw [this]
      refine ⟨?_, fun _ => hval', ?_⟩
      · rw [hval']
        have hpos : 1 ≤ (K - j * 2 ^ p) / 2 ^ (p + 1) ↔ 1 * 2 ^ (p + 1) ≤ K - j * 2 ^ p :=
          Nat.le_div_iff_mul_le (Nat.two_pow_pos _)
        generalize hm : (K - j * 2 ^ p) / 2 ^ (p + 1) = m at hpos
        constructor
        · intro h
          have h1 : 1 ≤ m := by
            rcases Nat.eq_zero_or_pos m with hm0 | hm0
            · subst hm0
              have h0 : ((0 : ℕ) : ℚ) * pow2 (-23) = 0 := by simp
              rw [h0, Rat.add_zero] at h
              exact absurd h Rat.lt_irrefl
            · exact hm0
          rw [Nat.add_mul]
          omega
        · intro h
          rw [Nat.add_mul] at h
          have h1 : 1 ≤ m := hpos.mpr (by omega)
          have : (1 : ℚ) ≤ (m : ℚ) := by
            have := Rat.natCast_le_natCast.mpr h1
            simpa using this
          have := Rat.mul_le_mul_of_nonneg_right this (Rat.le_of_lt hq23)
          rw [Rat.one_mul] at this
          grind
      · rw [hval']
        grind
    · have hAlt : A < 1 := by
        rw [← hA']
        have hlt : (N : ℚ) < ((2 ^ (24 + p) : ℕ) : ℚ) := by
          apply Rat.natCast_lt_natCast.mpr
          omega
        have := Rat.mul_lt_mul_of_pos_right hlt hq
        rw [← pow2_natCast, ← pow2_add] at this
        have h24 : ((24 + p : ℕ) : ℤ) + -(24 + p) = 0 := by omega
        rw [h24, pow2_zero] at this
        exact this
      have hqe := pow2_pos (normExp A - 23)
      have hle : (((A / pow2 (normExp A - 23)).floor : ℤ) : ℚ) * pow2 (normExp A - 23) ≤ A := by
        have := Rat.mul_le_mul_of_nonneg_right (Rat.floor_le (A / pow2 (normExp A - 23)))
          (Rat.le_of_lt hqe)
        rwa [Rat.div_mul_cancel (Rat.ne_of_gt hqe)] at this
      refine ⟨⟨fun h => ?_, fun h => ?_⟩, fun h => absurd h hjK, ?_⟩
      · exfalso; grind
      · exfalso; rw [Nat.add_mul] at h; omega
      · have := hM ((K - 2 ^ p) / 2 ^ (p + 1))
        grind

/-- Equation 9: with `1 ≤ j`, the witness condition `j ≤ 2^23 ∧ (j + 2)·2^p ≤ K` is `j ≤ min(2^23, ⌊K/2^p⌋ − 2)`. -/
theorem nonmonotone_range_iff (p K j : ℕ) (hj1 : 1 ≤ j) :
    (j ≤ 2 ^ 23 ∧ (j + 2) * 2 ^ p ≤ K) ↔ j ≤ min (2 ^ 23) (K / 2 ^ p - 2) := by
  have h : j + 2 ≤ K / 2 ^ p ↔ (j + 2) * 2 ^ p ≤ K := Nat.le_div_iff_mul_le (Nat.two_pow_pos p)
  rw [← h]
  omega

/-- The FP32 encoding `3f800000 − j` decodes to `c_j` for `1 ≤ j ≤ 2^23`. -/
theorem decode32_below (j : ℕ) (hj1 : 1 ≤ j) (hj2 : j ≤ 2 ^ 23) :
    decode32 (BitVec.ofNat 32 (0x3f800000 - j)) = some (belowDecoded j) := by
  rw [decode32_eq, BitVec.toNat_ofNat, classifyNat_fp32]
  have hmod : (0x3f800000 - j) % 2 ^ 32 = 0x3f800000 - j := Nat.mod_eq_of_lt (by omega)
  rw [hmod, if_neg (by omega), if_neg (by omega)]
  have hs : ((0x3f800000 - j) / 2147483648 != 0) = false := by
    have : (0x3f800000 - j) / 2147483648 = 0 := by omega
    rw [this]
    rfl
  simp only [Classification.finite, Option.some.injEq, hs, Bool.false_eq_true, if_false]
  unfold belowDecoded
  congr 1
  · omega
  · omega


/-- For C = 1 − j·2^-24: which j raise the output, the resulting output, and its maximum. -/
theorem nonmonotone_range_encoded (K p j : ℕ) (eAlignMin : Option ℤ)
    (hfl : ∀ f ∈ eAlignMin, f ≤ -1)
    (a b : (fp16Fp32Model K p eAlignMin).Word) (da db : Decoded)
    (ha : (fp16Fp32Model K p eAlignMin).decode a = some da)
    (hb : (fp16Fp32Model K p eAlignMin).decode b = some db)
    (hval : (denormalizedMul da db).value = pow2 (-(24 + p))) (hscale : (denormalizedMul da db).exponent ≤ -1)
    (hK : K < 2 ^ (24 + p)) (hj1 : 1 ≤ j) (hj2 : j ≤ 2 ^ 23) :
    ∃ t : BlockTrace,
      evalBlock (⟨List.replicate K (a, b), BitVec.ofNat 32 (0x3f800000 - j)⟩ :
        BlockInput (fp16Fp32Model K p eAlignMin)) = .ok t ∧
      (1 < t.output.value ↔ j ≤ min (2 ^ 23) (K / 2 ^ p - 2)) ∧
      (j * 2 ^ p ≤ K →
        t.output.value = 1 + (((K - j * 2 ^ p) / 2 ^ (p + 1) : ℕ) : ℚ) * pow2 (-23)) ∧
      t.output.value ≤ 1 + (((K - 2 ^ p) / 2 ^ (p + 1) : ℕ) : ℚ) * pow2 (-23) := by
  have hF : (fp16Fp32Model K p eAlignMin).alignMantissaBits = 23 + p := by
    show ((23 + p : ℕ) : ℤ) = 23 + (p : ℤ)
    omega
  obtain ⟨t, h1, hiff, hform, hbound⟩ :=
    nonmonotone_range (fp16Fp32Model K p eAlignMin) p K j da db hF hfl (Nat.le_refl 23) hval hscale
      hK hj1 hj2
  have hc := decode32_below j hj1 hj2
  have hps := prepareProducts_replicate _ a b da db K ha hb
  have hlen : ¬ ((List.replicate K (a, b)).length != (fp16Fp32Model K p eAlignMin).nfma) = true := by
    simp [fp16Fp32Model]
  refine ⟨t, ?_, ?_, hform, hbound⟩
  · unfold evalBlock
    rw [if_neg hlen]
    simp only [prepare, hc, hps]
    exact h1
  · rw [hiff, ← nonmonotone_range_iff p K j hj1]
    exact ⟨fun h => ⟨hj2, h⟩, fun h => h.2⟩

end TensorCore
