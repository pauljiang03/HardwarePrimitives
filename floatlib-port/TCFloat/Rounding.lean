import TCFloat.Theory
import FloatLib.Floats.Formats.BinaryInterchange.DirectedSemantics.Rational.RoundingSemantics.Executable
import FloatLib.Floats.Formats.BinaryInterchange.DirectedSemantics.Exact

namespace TCFloat
open FloatLib.Floats.Formats.BinaryInterchange
open FloatLib.Floats.Formats.Flocq

private theorem signed_rat_real (q : ℚ) :
    Model.signedScaledRatToReal (q.num < 0) q.num.natAbs q.den 0 = (q : ℝ) := by
  rw [Rat.cast_def]
  simp only [Model.signedScaledRatToReal, Model.scaledRatToReal]
  by_cases h : q.num < 0
  · simp [h, abs_of_neg h, Model.bpow]; ring
  · simp [h, abs_of_nonneg (le_of_not_gt h), Model.bpow]

private theorem max_real : (maxFinite32 : ℝ) = Model.toReal (Model.posMaxFinite .binary32) := by
  rw [Model.toReal_posMaxFinite]
  norm_num [maxFinite32, pow2, FloatFormat.binary32, FloatFormat.ieee,
    FloatFormat.maxNormalExponent, FloatFormat.exponentBias, FloatFormat.fracWidth,
    bpow, Model.bpow, Model.pow2, FloatFormat.maxFiniteFracField, FloatFormat.maxFiniteExpField,
    FloatFormat.expAllOnesNat, FloatFormat.fracMaskNat, FloatFormat.Encoding.maxFiniteExponent, FloatLib.Numerics.binaryRadix, FloatLib.Numerics.Radix.toReal]

private theorem rat_decode_real {f : FloatFormat} (x : Model f) (q : ℚ)
    (h : x.toRat? = some q) : Model.toReal x = (q : ℝ) := by
  unfold Model.toRat? at h
  cases hd : x.toDyadic? with
  | none => simp [hd] at h
  | some d =>
    simp only [hd, Option.map_some, Option.some.injEq] at h
    rw [Model.toReal_eq, hd]
    exact (FloatLib.Numerics.Dyadic.cast_toRat d).symm.trans (congrArg (fun z : ℚ => (z : ℝ)) h)

/-- Bridge to FloatLib's mathematical nearest-even rounding, including zero. -/
theorem round32_nearest_real (x : ℚ) (hx : |x| ≤ maxFinite32) :
    ∃ bits y, round32 .nearestEven x = some bits ∧ value32 bits = some y ∧
      (y : ℝ) = Model.roundAt .binary32 (x : ℝ) := by
  let r := Model.roundRatScaled .binary32 (x.num < 0) x.num.natAbs x.den 0
  have hb : |Model.signedScaledRatToReal (x.num < 0) x.num.natAbs x.den 0| ≤
      Model.toReal (Model.posMaxFinite .binary32) := by
    rw [signed_rat_real, ← max_real]
    exact_mod_cast hx
  have hf : Model.isFinite r = true :=
    Model.isFinite_roundRatScaled_of_abs_le_posMaxFinite _ _ _ _ _ (by decide) x.den_nz hb
  obtain ⟨d, hd⟩ := Model.exists_toDyadic?_of_isFinite hf
  have hv : r.toRat? = some d.toRat := by simp [Model.toRat?, hd]
  refine ⟨r.bits.toNat, d.toRat, ?_, ?_, ?_⟩
  · simp [round32, not_lt.mpr hx, r, Model.roundRatWithRounding, Model.roundRatWithRoundingScaled]
  · simpa [value32, ofNat, Model.ofBits, BitVec.ofNat_toNat] using hv
  · rw [← rat_decode_real r d.toRat hv]
    by_cases hz : x = 0
    · subst x
      simp [r]
    · have hn : x.num.natAbs ≠ 0 := by simp [hz]
      exact (Model.toReal_roundRatScaled_eq_roundAt _ _ _ _ _ (by decide) hn x.den_nz hf).trans
        (congrArg (Model.roundAt .binary32) (signed_rat_real x))

/-- Mathematical IEEE grid representation, expressed independently of the executable rounder. -/
def Grid32 (x : ℚ) : Prop :=
  genericFormat FloatLib.Numerics.binaryRadix (Model.fexpOf .binary32) (x : ℝ)

theorem representable_of_grid (x : ℚ) (hg : Grid32 x) (hx : |x| ≤ maxFinite32) :
    representable x = true := by
  obtain ⟨bits,y,hr,hv,hy⟩ := round32_nearest_real x hx
  have he : y = x := by
    have hh : Model.roundAt .binary32 (x : ℝ) = (x : ℝ) :=
      round_preserves_generic nearestEven _ hg
    exact_mod_cast hy.trans hh
  subst y
  simp [representable, hr, hv]

/-- Common-grid coefficient bound used by the source scalar EFT predicate. -/
theorem grid_representable (z : Int) (e : Int) (hmin : -149 ≤ e) (hmax : e ≤ 104)
    (hz : z.natAbs < 2^24) : representable ((z : ℚ)*pow2 e) = true := by
  apply representable_of_grid
  · let d := FloatLib.Numerics.Dyadic.ofScaledInt z e
    have hs : d.significand < 2^(FloatFormat.binary32.fracWidth+1) := hz
    have he : FloatFormat.binary32.minSubnormalExponent ≤ d.exponent := hmin
    have hg := Model.Dyadic.genericFormat_of_significand_lt .binary32 d hs he
    have hd : d.toReal = (((z : ℚ)*pow2 e : ℚ) : ℝ) := by
      rw [← FloatLib.Numerics.Dyadic.cast_toRat, FloatLib.Numerics.Dyadic.ofScaledInt_toRat]
      rfl
    rwa [hd] at hg
  · have he : pow2 e ≤ pow2 104 := by
      exact zpow_le_zpow_right₀ (by norm_num : (1 : ℚ) ≤ 2) hmax
    have hz' : |(z : ℚ)| ≤ (2^24-1 : ℕ) := by
      have h : (z.natAbs : ℚ) ≤ (2^24-1 : ℕ) := by exact_mod_cast (show z.natAbs ≤ 2^24-1 by omega)
      simpa using h
    rw [abs_mul, abs_of_pos (show 0 < pow2 e from zpow_pos (by norm_num) _)]
    exact mul_le_mul hz' he (le_of_lt (zpow_pos (by norm_num) _)) (by positivity)

end TCFloat
