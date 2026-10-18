import TCFloat.Behavior
import FloatLib.Floats.Formats.BinaryInterchange.DirectedSemantics.Rational.Bounds

namespace TCFloat
open FloatLib.Floats.Formats.BinaryInterchange

private theorem positive_ratio (x : ℚ) (hx : 0 < x) :
    (x.num.natAbs : ℝ) / (x.den : ℝ) = (x : ℝ) := by
  rw [Rat.cast_def]
  have hn : 0 ≤ x.num := (Rat.num_nonneg.mpr hx.le)
  simp [abs_of_nonneg hn]

private theorem decode_real {f : FloatFormat} (r : Model f) (y : ℚ)
    (h : r.toRat? = some y) : Model.toReal r = (y : ℝ) := by
  unfold Model.toRat? at h
  cases hd : r.toDyadic? with
  | none => simp [hd] at h
  | some d =>
    simp only [hd, Option.map_some, Option.some.injEq] at h
    rw [Model.toReal_eq, hd]
    exact (FloatLib.Numerics.Dyadic.cast_toRat d).symm.trans (congrArg (fun z : ℚ => (z : ℝ)) h)

private theorem cast_pow2 (e : Int) : ((pow2 e : ℚ) : ℝ) = (2:ℝ)^e := by
  simp only [pow2, Rat.cast_zpow, Rat.cast_ofNat]

private theorem cast_div_pow2 (x : ℚ) (e : Int) :
    ((x / pow2 e : ℚ) : ℝ) = (x:ℝ)/(2:ℝ)^e := by
  simp only [pow2, Rat.cast_div, Rat.cast_zpow, Rat.cast_ofNat]

/-- Exact executable RTZ behavior within a normal binary interval. -/
theorem round32_rtz_normal (x : ℚ) (e : Int) (hmin : -126 ≤ e) (hmax : e ≤ 127)
    (hlow : pow2 e ≤ x) (hhigh : x < pow2 (e+1)) (hrange : |x| ≤ maxFinite32) :
    ∃ bits y, round32 .towardZero x = some bits ∧ value32 bits = some y ∧
      y = truncGrid x (e-23) := by
  have hx : 0 < x := lt_of_lt_of_le (zpow_pos (by norm_num) e) hlow
  have hn : x.num.natAbs ≠ 0 := by simp [ne_of_gt hx]
  have hs : (x.num < 0) = False := propext (by simp [not_lt.mpr (Rat.num_nonneg.mpr hx.le)])
  have he : FloatLib.Numerics.RationalBinary.floorLog2 x.num.natAbs x.den = e := by
    apply Model.floorLog2_eq_of_bounds _ _ _ hn x.den_nz
    · rw [positive_ratio x hx]
      change (2:ℝ)^e ≤ (x:ℝ)
      have hh := (Rat.cast_le (K := ℝ)).mpr hlow
      simpa only [cast_pow2] using hh
    · rw [positive_ratio x hx]
      change (x:ℝ) < (2:ℝ)^(e+1)
      have hh := (Rat.cast_lt (K := ℝ)).mpr hhigh
      simpa only [cast_pow2] using hh
  let scaled := FloatLib.Numerics.RationalBinary.scaleByPowerOfTwo x.num.natAbs x.den (23-e)
  let m := Model.roundQuotDirected false scaled.1 scaled.2
  let r := Model.roundRatMagnitudeDirectedScaled .binary32 false false x.num.natAbs x.den 0
  have hp := Model.roundRatMagnitudeDirectedScaled_pos_eq_normal_down .binary32
    x.num.natAbs x.den 0 (by decide) hn x.den_nz
    (by change -126 ≤ _; rw [he, add_zero]; exact hmin) (by change _ ≤ 127; rw [he, add_zero]; exact hmax)
  have hlo := (Model.roundQuotDirected_normal_bounds .binary32 false _ _ hn x.den_nz).1
  have hhi := Model.roundQuotDirected_false_normal_lt_pow2_succ .binary32 _ _ hn x.den_nz
  have hp' : r = Model.ofFields .binary32 false (Int.toNat (e+127)) (m-Model.pow2 23) := by
    simpa [r, scaled, m, he, show FloatFormat.binary32.fracWidth = 23 from rfl, show FloatFormat.binary32.exponentBias = 127 from rfl] using hp
  have hf := (Model.roundRatMagnitudeDirectedScaled_pos_down_finite_le .binary32
    _ _ 0 (by decide) hn x.den_nz).1
  change Model.isFinite r = true at hf
  have hv : Model.toReal r = (m : ℝ) * (2:ℝ)^(e-23) := by
    rw [hp'] at hf ⊢
    exact Model.toReal_ofFields_normalized .binary32 m e
      (by simpa [m, scaled, he, show FloatFormat.binary32.fracWidth = 23 from rfl] using hlo) (by simpa [m, scaled, he, show FloatFormat.binary32.fracWidth = 23 from rfl] using hhi) hmin hmax hf
  have hm : (m : Int) = ⌊x / pow2 (e-23)⌋ := by
    have hsc := Model.scaleByPowerOfTwo_real x.num.natAbs x.den (23-e)
    have hsc' : (scaled.1 : ℝ)/(scaled.2 : ℝ) = ((x / pow2 (e-23) : ℚ) : ℝ) := by
      rw [Model.scaledRatToReal, positive_ratio x hx] at hsc
      change (scaled.1 : ℝ)/(scaled.2 : ℝ) = (x:ℝ)*(2:ℝ)^(23-e) at hsc
      rw [show 23-e = -(e-23) by omega, zpow_neg] at hsc
      rw [cast_div_pow2]
      exact hsc
    have hh := congrArg Int.floor hsc'
    rw [Int.floor_div_natCast, Int.floor_natCast] at hh
    simpa only [m, Model.roundQuotDirected, Bool.false_eq_true, ite_false, Int.natCast_ediv,
      Rat.floor_cast] using hh

  obtain ⟨d,hd⟩ := Model.exists_toDyadic?_of_isFinite hf
  have hrat : r.toRat? = some d.toRat := by simp [Model.toRat?, hd]
  refine ⟨r.bits.toNat,d.toRat,?_,?_,?_⟩
  · simp [round32, not_lt.mpr hrange, Model.roundRatWithRounding,
      Model.roundRatWithRoundingScaled, hs, r]
  · simpa [value32, ofNat, Model.ofBits, BitVec.ofNat_toNat] using hrat
  · rw [decode_real r d.toRat hrat] at hv
    have hv' : d.toRat = (m : ℚ)*pow2 (e-23) := by
      apply Rat.cast_injective (α := ℝ)
      simpa only [pow2, Rat.cast_mul, Rat.cast_natCast, Rat.cast_zpow, Rat.cast_ofNat] using hv
    rw [hv']
    simp only [truncGrid, truncCoeff, not_lt.mpr hx.le, ite_false]
    exact congrArg (fun z : Int => (z : ℚ)*pow2 (e-23)) hm

end TCFloat
