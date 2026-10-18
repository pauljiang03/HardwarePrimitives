import TensorCore.Numerics.RoundTrip
import TensorCore.Numerics.Binary.Bijection

/-! Exact representability and bitwise round trips. -/

namespace TensorCore

theorem binaryCoefficient_intCast (mode : BinaryRoundingMode) (negative : Bool) (k : ℤ) :
    binaryCoefficient mode negative (k : ℚ) = k := by
  have hr := roundSignificand_intCast .nearestEven k
  change rneInt (k : ℚ) = k at hr
  cases mode <;> cases negative <;> simp [binaryCoefficient, Rat.floor_intCast, Rat.ceil_intCast, hr]

theorem BinaryRep.finiteValue {f : Format} (r : BinaryRep f) : f.FiniteValue r.value := by
  refine ⟨if r.negative then -(r.significand : ℤ) else r.significand, r.exponent,
    r.exponent_min, r.exponent_max, ?_, ?_⟩
  · cases r.negative <;> simpa using r.significand_lt
  · unfold BinaryRep.value
    cases r.negative <;> simp [Rat.intCast_natCast]

theorem BinaryRep.value_eq_zero_iff {f : Format} (r : BinaryRep f) :
    r.value = 0 ↔ r.significand = 0 := by
  have hq := pow2_pos (r.exponent - f.mantissaBits)
  unfold BinaryRep.value
  cases r.negative <;> simp only [Bool.false_eq_true, ↓reduceIte, Rat.neg_mul]
  · rw [Rat.mul_eq_zero]; simp [Rat.ne_of_gt hq]
  · have h : -(r.significand : ℚ) * pow2 (r.exponent - f.mantissaBits) = 0 ↔
        (r.significand : ℚ) * pow2 (r.exponent - f.mantissaBits) = 0 := by grind
    rw [Rat.neg_mul] at h
    rw [h, Rat.mul_eq_zero]; simp [Rat.ne_of_gt hq]

/-- All four modes fix every nonzero canonical finite encoding. -/
theorem roundBinary_canonical (f : Format) (hf : f.WellFormed) (mode : BinaryRoundingMode)
    (r : BinaryRep f) (hk : r.significand ≠ 0) :
    roundBinary f mode r.value = some r.encode := by
  have hq := pow2_pos (r.exponent - f.mantissaBits)
  have hkR : (0 : ℚ) < (r.significand : ℚ) := Rat.natCast_pos.mpr (by omega)
  have hpos := Rat.mul_pos hkR hq
  have hmag : absQ r.value = (r.significand : ℚ) * pow2 (r.exponent - f.mantissaBits) := by
    unfold BinaryRep.value
    cases r.negative <;> simp only [Bool.false_eq_true, ↓reduceIte]
    · exact absQ_of_nonneg (Rat.le_of_lt hpos)
    · rw [Rat.neg_mul, absQ_neg, absQ_of_nonneg (Rat.le_of_lt hpos)]
  have hrange := f.finiteValue_abs_le r.finiteValue
  have hne : r.value ≠ 0 := by simpa [r.value_eq_zero_iff] using hk
  have hexp : binaryNormExp f ((r.significand : ℚ) * pow2 (r.exponent - f.mantissaBits)) =
      r.exponent := by
    unfold binaryNormExp
    by_cases hnormal : 2 ^ f.mantissaBits ≤ r.significand
    · have hlo : pow2 r.exponent ≤ (r.significand : ℚ) * pow2 (r.exponent - f.mantissaBits) := by
        rw [f.binade_grid]
        exact Rat.mul_le_mul_of_nonneg_right (Rat.natCast_le_natCast.mpr hnormal) (Rat.le_of_lt hq)
      have hhi : (r.significand : ℚ) * pow2 (r.exponent - f.mantissaBits) < pow2 (r.exponent + 1) := by
        rw [f.next_binade_grid]
        exact Rat.mul_lt_mul_of_pos_right (Rat.natCast_lt_natCast.mpr r.significand_lt) hq
      rw [magnitudeExponent_eq_of_bounds _ r.exponent hlo hhi]
      exact Int.max_eq_left r.exponent_min
    · have he : r.exponent = f.emin := by have := r.normalized; omega
      have hsmall : (r.significand : ℚ) * pow2 (r.exponent - f.mantissaBits) < pow2 r.exponent := by
        rw [f.binade_grid r.exponent]
        exact Rat.mul_lt_mul_of_pos_right
          (Rat.natCast_lt_natCast.mpr (show r.significand < 2 ^ f.mantissaBits by omega)) hq
      have hme : magnitudeExponent ((r.significand : ℚ) * pow2 (r.exponent - f.mantissaBits)) <
          r.exponent := by
        apply Classical.byContradiction
        intro hn
        have h1 := (magnitudeExponent_spec _ hpos).1
        have h2 := pow2_le_of_le (show r.exponent ≤ magnitudeExponent
          ((r.significand : ℚ) * pow2 (r.exponent - f.mantissaBits)) by omega)
        grind
      rw [he] at hme ⊢
      exact Int.max_eq_right (by omega)
  have hsign : decide (r.value < 0) = r.negative := by
    unfold BinaryRep.value
    cases r.negative <;> simp only [Bool.false_eq_true, ↓reduceIte, decide_eq_true_eq,
      decide_eq_false_iff_not]
    · exact Rat.not_lt.mpr (Rat.le_of_lt hpos)
    · rw [Rat.neg_mul]; grind
  unfold roundBinary
  rw [if_neg (by exact fun h => h hf), if_neg (Rat.not_lt.mpr hrange), if_neg hne,
    hsign, hmag, hexp]
  dsimp only
  rw [Rat.mul_div_cancel (Rat.ne_of_gt hq)]
  rw [show (r.significand : ℚ) = ((r.significand : ℤ) : ℚ) from rfl,
    binaryCoefficient_intCast]
  have hcarry : binaryCarry f r.exponent r.significand = (r.exponent, (r.significand : ℤ)) := by
    unfold binaryCarry
    rw [if_neg (by have := r.significand_lt; omega)]
  rw [hcarry]
  dsimp only
  rw [if_neg (Int.not_lt.mpr r.exponent_max)]
  rfl

theorem binaryValue_roundBinary (f : Format) (hf : f.WellFormed) (mode : BinaryRoundingMode)
    (b : BitVec f.width) (v : ℚ) (hv : binaryValue f b = some v) (hnz : v ≠ 0) :
    roundBinary f mode v = some b := by
  have hb : ∃ d, (classify f b).finite = some d := by
    unfold binaryValue at hv
    cases hd : (classify f b).finite with
    | none => simp [hd] at hv
    | some d => exact ⟨d, rfl⟩
  let w : FiniteBinaryWord f := ⟨b, hb⟩
  let r := decodeBinaryRep f hf w
  have hval : r.value = v := Option.some.inj ((decodeBinaryRep_value f hf w).symm.trans hv)
  have hbits := congrArg Subtype.val (encode_decodeBinaryRep f hf w)
  have hround := roundBinary_canonical f hf mode r
    (by intro hz; exact hnz (hval.symm.trans (r.value_eq_zero_iff.mpr hz)))
  change r.encode = b at hbits
  rwa [hval, hbits] at hround

theorem binaryValue_injective_nonzero (f : Format) (hf : f.WellFormed)
    (b₁ b₂ : BitVec f.width) (v : ℚ) (h₁ : binaryValue f b₁ = some v)
    (h₂ : binaryValue f b₂ = some v) (hnz : v ≠ 0) : b₁ = b₂ := by
  have r₁ := binaryValue_roundBinary f hf .truncate b₁ v h₁ hnz
  have r₂ := binaryValue_roundBinary f hf .truncate b₂ v h₂ hnz
  exact Option.some.inj (r₁.symm.trans r₂)

end TensorCore
