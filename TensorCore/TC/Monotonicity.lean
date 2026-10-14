import TensorCore.Numerics.CorrectRounding
import TensorCore.TC.StageResiduals
import TensorCore.TC.AlignmentExponent
import TensorCore.TC.Padding

/-! Non-monotonicity of the model under a smaller C. -/

namespace TensorCore

def oneDecoded : Decoded := ⟨8388608, 0, 23⟩
def belowOneDecoded : Decoded := ⟨16777215, -1, 23⟩

theorem oneDecoded_value : oneDecoded.value = 1 := by decide +kernel
theorem belowOneDecoded_value : belowOneDecoded.value = 16777215 * pow2 (-24) := by
  decide +kernel

/-- In the construction, the alignment exponent is C's exponent when no product's exponent exceeds it. -/
theorem construction_alignExp (prof : Model) (K : ℕ) (da db c : Decoded)
    (hc : c.significand ≠ 0) (_hu : (denormalizedMul da db).significand ≠ 0)
    (hs : (denormalizedMul da db).exponent ≤ c.exponent) (hfl : ∀ f ∈ prof.eAlignMin, f ≤ c.exponent) :
    (PreparedBlock.mk prof (List.replicate K (da, db)) c).alignExp = some c.exponent := by
  have hterms : (PreparedBlock.mk prof (List.replicate K (da, db)) c).terms =
      ⟨c.significand, c.exponent, c.mantissaBits⟩ :: List.replicate K (denormalizedMul da db) := by
    simp [PreparedBlock.terms, List.map_replicate]
  have hmem : (⟨c.significand, c.exponent, c.mantissaBits⟩ : DenormalizedProduct) ∈
      (PreparedBlock.mk prof (List.replicate K (da, db)) c).terms := by
    rw [hterms]; simp
  obtain ⟨e, he, hle⟩ := maxTermExp_term _ _ hmem hc
  have hle' : c.exponent ≤ e := hle
  have hup := maxTermExp_upper (PreparedBlock.mk prof (List.replicate K (da, db)) c).terms
    c.exponent (by
      intro t ht _
      rw [hterms] at ht
      simp only [List.mem_cons, List.mem_replicate] at ht
      rcases ht with rfl | ⟨_, rfl⟩
      · exact Int.le_refl _
      · exact hs) e (by rw [he]; simp)
  have heq : e = c.exponent := by omega
  subst heq
  unfold PreparedBlock.alignExp
  rw [he]
  show prof.applyEAlignMin (some c.exponent) = some c.exponent
  unfold Model.applyEAlignMin
  cases hf : prof.eAlignMin with
  | none => rfl
  | some f =>
    have := hfl f (by rw [hf]; simp)
    simp [Int.max_eq_left this]

theorem denormalizedMul_significand_ne_zero (da db : Decoded) (p : ℕ)
    (hval : (denormalizedMul da db).value = pow2 (-(24 + p))) : (denormalizedMul da db).significand ≠ 0 := by
  intro h
  unfold DenormalizedProduct.value at hval
  rw [h] at hval
  have := pow2_pos (-(24 + p))
  simp at hval
  grind

/-- Accumulator with `c = 1`: every product truncates to zero. -/
theorem construction_accumulator_one (prof : Model) (p K : ℕ) (da db : Decoded)
    (hF : prof.alignMantissaBits = 23 + p) (hfl : ∀ f ∈ prof.eAlignMin, f ≤ -1)
    (hval : (denormalizedMul da db).value = pow2 (-(24 + p))) (hscale : (denormalizedMul da db).exponent ≤ -1) :
    (PreparedBlock.mk prof (List.replicate K (da, db)) oneDecoded).accumulator = 1 := by
  have hu := denormalizedMul_significand_ne_zero da db p hval
  have heta := construction_alignExp prof K da db oneDecoded (by decide) hu
    (by change (denormalizedMul da db).exponent ≤ 0; omega)
    (by intro f hf; have := hfl f hf; change f ≤ 0; omega)
  have hq : (PreparedBlock.mk prof (List.replicate K (da, db)) oneDecoded).alignGridExponent =
      -(23 + p) := by
    unfold PreparedBlock.alignGridExponent
    rw [heta]
    change oneDecoded.exponent - prof.alignMantissaBits = _
    rw [hF]
    simp only [oneDecoded]
    omega
  have hcoef := construction_alignedBits prof K da db oneDecoded
  rw [hq] at hcoef
  have hc : truncBits oneDecoded.value (-(23 + p)) = ((2 ^ (23 + p) : ℕ) : ℤ) := by
    rw [oneDecoded_value]
    have h1 : (1 : ℚ) = (((2 ^ (23 + p) : ℕ) : ℤ) : ℚ) * pow2 (-(23 + p)) := by
      rw [Rat.intCast_natCast, ← pow2_natCast, ← pow2_add]
      have : ((23 + p : ℕ) : ℤ) + -(23 + p) = 0 := by omega
      rw [this, pow2_zero]
    rw [h1, truncBits_of_grid]
  have hp : truncBits (denormalizedMul da db).value (-(23 + p)) = 0 := by
    rw [hval]
    unfold truncBits
    have hpos := pow2_pos (-(24 + p))
    rw [if_neg (by grind), pow2_div]
    have : (-(24 + p) : ℤ) - -(23 + p) = -1 := by omega
    rw [this]
    decide +kernel
  unfold PreparedBlock.accumulator
  rw [hcoef, hq]
  simp only [sumZ, hc, hp, sumZ_replicate, Int.mul_zero, Int.add_zero]
  rw [Rat.intCast_natCast, ← pow2_natCast, ← pow2_add]
  have : ((23 + p : ℕ) : ℤ) + -(23 + p) = 0 := by omega
  rw [this, pow2_zero]

/-- Accumulator with `c' = 1 − 2^-24`: every product is retained. -/
theorem construction_accumulator_below (prof : Model) (p K : ℕ) (da db : Decoded)
    (hF : prof.alignMantissaBits = 23 + p) (hfl : ∀ f ∈ prof.eAlignMin, f ≤ -1)
    (hval : (denormalizedMul da db).value = pow2 (-(24 + p))) (hscale : (denormalizedMul da db).exponent ≤ -1) :
    (PreparedBlock.mk prof (List.replicate K (da, db)) belowOneDecoded).accumulator =
      ((16777215 * 2 ^ p + K : ℕ) : ℚ) * pow2 (-(24 + p)) := by
  have hu := denormalizedMul_significand_ne_zero da db p hval
  have heta := construction_alignExp prof K da db belowOneDecoded (by decide) hu hscale hfl
  have hq : (PreparedBlock.mk prof (List.replicate K (da, db)) belowOneDecoded).alignGridExponent =
      -(24 + p) := by
    unfold PreparedBlock.alignGridExponent
    rw [heta]
    change belowOneDecoded.exponent - prof.alignMantissaBits = _
    rw [hF]
    simp only [belowOneDecoded]
    omega
  have hcoef := construction_alignedBits prof K da db belowOneDecoded
  rw [hq] at hcoef
  have hc : truncBits belowOneDecoded.value (-(24 + p)) = ((16777215 * 2 ^ p : ℕ) : ℤ) := by
    rw [belowOneDecoded_value]
    have h1 : (16777215 : ℚ) * pow2 (-24) =
        (((16777215 * 2 ^ p : ℕ) : ℤ) : ℚ) * pow2 (-(24 + p)) := by
      rw [Rat.intCast_natCast, Rat.natCast_mul, ← pow2_natCast, Rat.mul_assoc, ← pow2_add]
      have : (p : ℤ) + -(24 + p) = -24 := by omega
      rw [this]
      all_goals simp
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

/-- TC-EFT Theorem III.4. -/
theorem nonmonotone_perturbation (prof : Model) (p K : ℕ) (da db : Decoded)
    (hF : prof.alignMantissaBits = 23 + p) (hfl : ∀ f ∈ prof.eAlignMin, f ≤ -1)
    (hw : 23 ≤ prof.outputMantissaBits)
    (hval : (denormalizedMul da db).value = pow2 (-(24 + p))) (hscale : (denormalizedMul da db).exponent ≤ -1)
    (hK : K < 2 ^ (24 + p)) :
    ∃ t t' : BlockTrace,
      evalPrepared ⟨prof, List.replicate K (da, db), oneDecoded⟩ = .ok t ∧
      evalPrepared ⟨prof, List.replicate K (da, db), belowOneDecoded⟩ = .ok t' ∧
      t.output.value = 1 ∧ (1 < t'.output.value ↔ 3 * 2 ^ p ≤ K) := by
  have hA1 := construction_accumulator_one prof p K da db hF hfl hval hscale
  have hA2 := construction_accumulator_below prof p K da db hF hfl hval hscale
  have hr1 : round32 .truncate 1 = some (BitVec.ofNat 32 0x3f800000) := by decide +kernel
  have hv1 : value32 (BitVec.ofNat 32 0x3f800000) = some 1 := by decide +kernel
  obtain ⟨f1, hf1, _, hf1v⟩ := finite32_of_value32 _ _ hv1
  have hq := pow2_pos (-(24 + p))
  have h2p24 : 2 ^ (24 + p) = 16777216 * 2 ^ p := by
    rw [Nat.pow_add]
    all_goals simp
  have hPpos := Nat.two_pow_pos p
  generalize hN : 16777215 * 2 ^ p + K = N at hA2
  generalize hA : (N : ℚ) * pow2 (-(24 + p)) = A at hA2
  have hNpos : (0 : ℚ) < (N : ℚ) := Rat.natCast_pos.mpr (by omega)
  have hApos : 0 < A := by
    rw [← hA]
    have := Rat.mul_lt_mul_of_pos_right hNpos hq
    simpa using this
  have hA2lt : A < 2 := by
    rw [← hA]
    have hlt : (N : ℚ) < ((2 ^ (25 + p) : ℕ) : ℚ) := by
      apply Rat.natCast_lt_natCast.mpr
      have h1 : 2 ^ (25 + p) = 2 * (16777216 * 2 ^ p) := by
        rw [show 25 + p = 1 + (24 + p) by omega, Nat.pow_add, Nat.pow_add]
        all_goals simp
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
  obtain ⟨b2, hb2, hv2, _, _⟩ := round32_nonzero_spec .truncate A (Rat.ne_of_gt hApos) hrange
  obtain ⟨f2, hf2, _, hf2v⟩ := finite32_of_value32 _ _ hv2
  refine ⟨⟨⟨prof, List.replicate K (da, db), oneDecoded⟩, f1⟩,
    ⟨⟨prof, List.replicate K (da, db), belowOneDecoded⟩, f2⟩, ?_, ?_, hf1v, ?_⟩
  · simp only [evalPrepared, hA1, hr1, truncateMantissa32_of_le hw, hf1]
  · simp only [evalPrepared, hA2, hb2, truncateMantissa32_of_le hw, hf2]
  · change 1 < f2.value ↔ _
    rw [hf2v]
    unfold signedRounded
    rw [if_neg (by grind), absQ_of_nonneg (Rat.le_of_lt hApos)]
    unfold magnitudeRounded roundedSignificand roundSignificand
    dsimp only
    by_cases hKp : K < 2 ^ p
    · have hAlt : A < 1 := by
        rw [← hA]
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
      constructor
      · intro h; exfalso; grind
      · intro h; exfalso; omega
    · have hAge : 1 ≤ A := by
        rw [← hA]
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
      have hA23 : A * pow2 23 = (N : ℚ) * pow2 (-(1 + p)) := by
        rw [← hA, Rat.mul_assoc, ← pow2_add]
        congr 2
        omega
      rw [hA23]
      have hq1 := pow2_pos (-(1 + p))
      have hq23 := pow2_pos (-23)
      have hcmp : ∀ m : ℤ, (1 < (m : ℚ) * pow2 (-23) ↔ 8388608 < m) := by
        intro m
        have h1 : (1 : ℚ) = ((8388608 : ℤ) : ℚ) * pow2 (-23) := by decide +kernel
        rw [h1, Rat.mul_lt_mul_right hq23]
        exact Rat.intCast_lt_intCast
      rw [hcmp]
      have hfloor : (8388608 < ((N : ℚ) * pow2 (-(1 + p))).floor) ↔
          ((8388609 : ℤ) : ℚ) * pow2 ((1 + p : ℕ) : ℤ) ≤ (N : ℚ) := by
        rw [Int.lt_iff_add_one_le, Rat.le_floor_iff]
        have hz : -(1 + (p : ℤ)) + ((1 + p : ℕ) : ℤ) = 0 := by omega
        have hz' : ((1 + p : ℕ) : ℤ) + -(1 + (p : ℤ)) = 0 := by omega
        constructor
        · intro h
          have := Rat.mul_le_mul_of_nonneg_right h (Rat.le_of_lt (pow2_pos ((1 + p : ℕ) : ℤ)))
          rw [Rat.mul_assoc, ← pow2_add, hz, pow2_zero, Rat.mul_one] at this
          exact this
        · intro h
          have := Rat.mul_le_mul_of_nonneg_right h (Rat.le_of_lt hq1)
          rw [Rat.mul_assoc, ← pow2_add, hz', pow2_zero, Rat.mul_one] at this
          exact this
      rw [hfloor]
      have hcast : ((8388609 : ℤ) : ℚ) * pow2 ((1 + p : ℕ) : ℤ) =
          ((8388609 * 2 ^ (1 + p) : ℕ) : ℚ) := by
        rw [pow2_natCast, Rat.natCast_mul]
        simp
      rw [hcast, Rat.natCast_le_natCast]
      have h2p : 2 ^ (1 + p) = 2 * 2 ^ p := by
        rw [Nat.pow_add]
        all_goals simp
      subst hN
      rw [h2p]
      constructor
      · intro h; omega
      · intro h; omega


/-- Lowering C from 1 to its FP32 predecessor raises the output exactly when K ≥ 3·2^p. -/
theorem nonmonotone_encoded (K p : ℕ) (eAlignMin : Option ℤ) (hfl : ∀ f ∈ eAlignMin, f ≤ -1)
    (a b : (fp16Fp32Model K p eAlignMin).Word) (da db : Decoded)
    (ha : (fp16Fp32Model K p eAlignMin).decode a = some da)
    (hb : (fp16Fp32Model K p eAlignMin).decode b = some db)
    (hval : (denormalizedMul da db).value = pow2 (-(24 + p))) (hscale : (denormalizedMul da db).exponent ≤ -1)
    (hK : K < 2 ^ (24 + p)) :
    ∃ t t' : BlockTrace,
      evalBlock (⟨List.replicate K (a, b), 0x3f800000⟩ : BlockInput (fp16Fp32Model K p eAlignMin)) =
        .ok t ∧
      evalBlock (⟨List.replicate K (a, b), 0x3f7fffff⟩ : BlockInput (fp16Fp32Model K p eAlignMin)) =
        .ok t' ∧
      t.output.value = 1 ∧ (1 < t'.output.value ↔ 3 * 2 ^ p ≤ K) := by
  have hF : (fp16Fp32Model K p eAlignMin).alignMantissaBits = 23 + p := by
    show ((23 + p : ℕ) : ℤ) = 23 + (p : ℤ)
    omega
  obtain ⟨t, t', h1, h2, hv, hiff⟩ :=
    nonmonotone_perturbation (fp16Fp32Model K p eAlignMin) p K da db hF hfl (Nat.le_refl 23) hval
      hscale hK
  have hc1 : decode32 (0x3f800000 : F32) = some oneDecoded := by decide +kernel
  have hc2 : decode32 (0x3f7fffff : F32) = some belowOneDecoded := by decide +kernel
  have hps := prepareProducts_replicate _ a b da db K ha hb
  have hlen : ¬ ((List.replicate K (a, b)).length != (fp16Fp32Model K p eAlignMin).nfma) = true := by
    simp [fp16Fp32Model]
  refine ⟨t, t', ?_, ?_, hv, hiff⟩
  · unfold evalBlock
    rw [if_neg hlen]
    simp only [prepare, hc1, hps]
    exact h1
  · unfold evalBlock
    rw [if_neg hlen]
    simp only [prepare, hc2, hps]
    exact h2

end TensorCore
