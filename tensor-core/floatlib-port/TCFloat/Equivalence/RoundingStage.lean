import TCFloat.Equivalence.Packing

set_option maxRecDepth 2048
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
namespace TCFloat.Equivalence
open FloatLib.Floats.Formats.BinaryInterchange
open FloatLib.Numerics

def quotient (m : TensorCore.RoundingMode) (n d : Nat) : Nat :=
  match m with
  | .nearestEven => roundQuotientEven n d
  | .truncate => Model.roundQuotDirected false n d

theorem scaled_coefficient (m : TensorCore.RoundingMode) (x : Rat) (e : Int) :
    (quotient m (RationalBinary.scaleByPowerOfTwo x.num.natAbs x.den (-e)).1
      (RationalBinary.scaleByPowerOfTwo x.num.natAbs x.den (-e)).2 : Int) =
      TensorCore.roundSignificand m (|x| / TCFloat.pow2 e) := by
  have hd := RationalBinary.scaleByPowerOfTwo_snd_ne_zero x.num.natAbs x.den (-e) x.den_nz
  have hq : ((RationalBinary.scaleByPowerOfTwo x.num.natAbs x.den (-e)).1 : Rat) /
      (RationalBinary.scaleByPowerOfTwo x.num.natAbs x.den (-e)).2 = |x| / TCFloat.pow2 e := by
    rw [scale_ratio,abs_ratio]
    simp [TCFloat.pow2,zpow_neg,div_eq_mul_inv]
  cases m
  · simp only [quotient,quotient_rtz,hq,TensorCore.roundSignificand]
  · simp only [quotient,quotient_rne _ _ hd,hq,TensorCore.roundSignificand]

theorem coefficient_tiny (m : TensorCore.RoundingMode) (x : Rat)
    (hl : 0 ≤ x) (hh : x < 1/2) : TensorCore.roundSignificand m x = 0 := by
  have hf : x.floor = 0 := by
    change ⌊x⌋ = 0
    apply Int.floor_eq_iff.mpr
    norm_num
    constructor <;> linarith
  cases m
  · exact hf
  · simp only [TensorCore.roundSignificand,TensorCore.rneInt,hf,Int.cast_zero]
    have hn : ¬(1 < 2*(x-0) ∨ 2*(x-0)=1 ∧ (0:Int)%2=1) := by
      norm_num; linarith
    simp
    linarith

theorem source_round_nonzero (m : TensorCore.RoundingMode) (x : Rat)
    (hx : x ≠ 0) (hr : |x| ≤ TCFloat.maxFinite32) :
    TensorCore.round32 m x =
      some (TensorCore.encode32 (decide (x<0))
        (TensorCore.carry (TensorCore.normExp |x|) (TensorCore.roundedSignificand m |x|)).1
        (TensorCore.carry (TensorCore.normExp |x|) (TensorCore.roundedSignificand m |x|)).2) := by
  have hp := abs_pos.mpr hx
  have he := TensorCore.normExp_bounds |x| hp hr
  have hk := TensorCore.roundedSignificand_bounds m |x| hp hr
  have hc := TensorCore.carry_spec _ _ he.1 he.2.1 hk.1 hk.2.1 hk.2.2.1 hk.2.2.2
  simp only [TensorCore.round32,TensorCore.round32Core,abs_eq,maxFinite_eq,
    not_lt.mpr hr,ite_false,hx,not_lt.mpr hc.2.1]

theorem normExp_subnormal (x : Rat) (h : TensorCore.magnitudeExponent |x| < -126) :
    TensorCore.normExp |x| = -126 := by
  unfold TensorCore.normExp TensorCore.emin32
  omega

theorem roundedCoeff_subnormal (m : TensorCore.RoundingMode) (x : Rat) (hx : x ≠ 0)
    (h : TensorCore.magnitudeExponent |x| < -126) :
    TensorCore.roundedSignificand m |x| ≤ 2^23 := by
  obtain ⟨_,hu⟩ := TensorCore.magnitudeExponent_spec |x| (abs_pos.mpr hx)
  have hm : |x| < TensorCore.pow2 (-126) := lt_of_lt_of_le hu (TensorCore.pow2_le_of_le (by omega))
  unfold TensorCore.roundedSignificand
  rw [normExp_subnormal x h]
  apply TensorCore.roundSignificand_le_integer
  apply (div_le_iff₀ (TensorCore.pow2_pos _)).mpr
  have hg := TensorCore.binade_grid (-126)
  norm_num only at hg ⊢
  linarith

theorem roundedCoeff_tiny_rtz (x : Rat) (hx : x ≠ 0)
    (h : TensorCore.magnitudeExponent |x| < -149) :
    TensorCore.roundedSignificand .truncate |x| = 0 := by
  obtain ⟨_,hu⟩ := TensorCore.magnitudeExponent_spec |x| (abs_pos.mpr hx)
  have hm : |x| < TensorCore.pow2 (-149) := lt_of_lt_of_le hu (TensorCore.pow2_le_of_le (by omega))
  unfold TensorCore.roundedSignificand
  rw [normExp_subnormal x (by omega)]
  change ⌊|x| / TensorCore.pow2 (-149)⌋ = 0
  apply Int.floor_eq_iff.mpr
  norm_num only [Int.cast_zero,zero_add]
  exact ⟨div_nonneg (abs_nonneg _) (TensorCore.pow2_pos _).le,
    (div_lt_one (TensorCore.pow2_pos _)).mpr hm⟩

theorem roundedCoeff_tiny_rne (x : Rat) (hx : x ≠ 0)
    (h : TensorCore.magnitudeExponent |x| < -150) :
    TensorCore.roundedSignificand .nearestEven |x| = 0 := by
  obtain ⟨_,hu⟩ := TensorCore.magnitudeExponent_spec |x| (abs_pos.mpr hx)
  have hm : |x| < TensorCore.pow2 (-150) := lt_of_lt_of_le hu (TensorCore.pow2_le_of_le (by omega))
  unfold TensorCore.roundedSignificand
  rw [normExp_subnormal x (by omega)]
  apply coefficient_tiny
  · exact div_nonneg (abs_nonneg _) (TensorCore.pow2_pos _).le
  · apply (div_lt_iff₀ (TensorCore.pow2_pos _)).mpr
    have hg := TensorCore.pow2_succ (-150)
    norm_num only at hg ⊢
    linarith

theorem round32_rtz_nonzero (s : Bool) (x : Rat) (hx : x ≠ 0) (hr : |x| ≤ TCFloat.maxFinite32) :
    (Model.roundRatWithRounding .binary32 .towardZero s x.num.natAbs x.den).bits.toNat =
      (TensorCore.encode32 s
        (TensorCore.carry (TensorCore.normExp |x|) (TensorCore.roundedSignificand .truncate |x|)).1
        (TensorCore.carry (TensorCore.normExp |x|) (TensorCore.roundedSignificand .truncate |x|)).2).toNat := by
  have hn : x.num.natAbs ≠ 0 := by simp [hx]
  have he := TensorCore.normExp_bounds |x| (abs_pos.mpr hx) hr
  have hk := TensorCore.roundedSignificand_bounds .truncate |x| (abs_pos.mpr hx) hr
  have hlmax : TensorCore.magnitudeExponent |x| ≤ 127 := by
    have hm : TensorCore.magnitudeExponent |x| ≤ TensorCore.normExp |x| := le_max_left _ _
    omega
  simp only [Model.roundRatWithRounding,Model.roundRatWithRoundingScaled,
    Model.roundRatMagnitudeDirectedScaled,beq_iff_eq,x.den_nz,hn,ite_false,
    floorLog2_eq x hx,add_zero,
    show FloatFormat.binary32.maxNormalExponent=127 from rfl,
    not_lt.mpr hlmax,
    show FloatFormat.binary32.minSubnormalExponent= -149 from rfl,
    show FloatFormat.binary32.minNormalExponent= -126 from rfl,
    show FloatFormat.binary32.exponentBias=127 from rfl,
    show FloatFormat.binary32.fracWidth=23 from rfl,
    show (0:Int)+Int.ofNat (127+23-1)=(149:Int) from rfl,
    show Int.ofNat 23=(23:Int) from rfl]
  by_cases hsmall : TensorCore.magnitudeExponent |x| < -149
  · rw [ite_eq_left hsmall,normExp_subnormal x (by omega),roundedCoeff_tiny_rtz x hx hsmall]
    exact zero_bits s
  · rw [ite_eq_right hsmall]
    by_cases hsub : TensorCore.magnitudeExponent |x| < -126
    · rw [ite_eq_left hsub]
      have hc := scaled_coefficient .truncate x (-149)
      change (Model.roundQuotDirected false
        (RationalBinary.scaleByPowerOfTwo x.num.natAbs x.den 149).1
        (RationalBinary.scaleByPowerOfTwo x.num.natAbs x.den 149).2 : Int) =
          TensorCore.roundSignificand .truncate (|x| / TCFloat.pow2 (-149)) at hc
      have heq := normExp_subnormal x hsub
      have hce : TensorCore.roundedSignificand .truncate |x| =
        TensorCore.roundSignificand .truncate (|x|/TCFloat.pow2 (-149)) := by
        rw [TensorCore.roundedSignificand,heq]
        rfl
      rw [← hce] at hc
      have hcn := congrArg Int.toNat hc
      simp only [Int.toNat_natCast] at hcn
      change (Model.packRoundedSubnormal .binary32 s (Model.zero .binary32 s)
        (Model.roundQuotDirected false _ _)).bits.toNat = _
      rw [hcn,heq]
      have hb := roundedCoeff_subnormal .truncate x hx hsub
      have hcarry : TensorCore.carry (-126) (TensorCore.roundedSignificand .truncate |x|) =
          (-126,TensorCore.roundedSignificand .truncate |x|) := by
        unfold TensorCore.carry
        split
        · omega
        · rfl
      rw [hcarry]
      exact subnormal_pack s _ hk.1 hb
    · rw [ite_eq_right hsub]
      have heq : TensorCore.normExp |x| = TensorCore.magnitudeExponent |x| := by
        unfold TensorCore.normExp TensorCore.emin32; omega
      have hc := scaled_coefficient .truncate x (TensorCore.normExp |x|-23)
      have hs : -(TensorCore.normExp |x|-23) = 23-TensorCore.magnitudeExponent |x| := by omega
      rw [hs] at hc
      change (Model.roundQuotDirected false _ _ : Int) = TensorCore.roundedSignificand .truncate |x| at hc
      have hcn := congrArg Int.toNat hc
      simp only [Int.toNat_natCast] at hcn
      change (Model.packRoundedNormal .binary32 s _ (TensorCore.magnitudeExponent |x|)
        (Model.roundQuotDirected false _ _)).bits.toNat = _
      rw [hcn,← heq]
      have hlo := (Model.roundQuotDirected_normal_bounds .binary32 false _ _ hn x.den_nz).1
      simp only [show FloatFormat.binary32.fracWidth=23 from rfl,
        Model.pow2_eq_two_pow,floorLog2_eq x hx,show Int.ofNat 23=(23:Int) from rfl,hcn] at hlo
      exact normal_pack s _ _ _ he.1 he.2.1 (by omega) hk.2.1 hk.2.2.2

theorem round32_rne_nonzero (s : Bool) (x : Rat) (hx : x ≠ 0) (hr : |x| ≤ TCFloat.maxFinite32) :
    (Model.roundRatWithRounding .binary32 .nearestEven s x.num.natAbs x.den).bits.toNat =
      (TensorCore.encode32 s
        (TensorCore.carry (TensorCore.normExp |x|) (TensorCore.roundedSignificand .nearestEven |x|)).1
        (TensorCore.carry (TensorCore.normExp |x|) (TensorCore.roundedSignificand .nearestEven |x|)).2).toNat := by
  have hn : x.num.natAbs ≠ 0 := by simp [hx]
  have he := TensorCore.normExp_bounds |x| (abs_pos.mpr hx) hr
  have hk := TensorCore.roundedSignificand_bounds .nearestEven |x| (abs_pos.mpr hx) hr
  have hlmax : TensorCore.magnitudeExponent |x| ≤ 127 := by
    have hm : TensorCore.magnitudeExponent |x| ≤ TensorCore.normExp |x| := le_max_left _ _
    omega
  simp only [Model.roundRatWithRounding,Model.roundRatWithRoundingScaled,
    Model.roundRatScaled,FloatFormat.isIEEE_binary32,dite_true,Model.ieeeRoundRatScaled,
    beq_iff_eq,x.den_nz,hn,ite_false,floorLog2_eq x hx,add_zero,
    show FloatFormat.ieeeMaxNormalExponent .binary32=127 from rfl,
    show Int.ofNat 127=(127:Int) from rfl,not_lt.mpr hlmax,
    show FloatFormat.ieeeMinNormalExponent .binary32= -126 from rfl,
    show FloatFormat.normalMantissaExpOffset .binary32=150 from rfl,
    show -Int.ofNat 150=(-150:Int) from rfl,
    show FloatFormat.subnormalAlignExp .binary32=149 from rfl,
    show (0:Int)+Int.ofNat 149=(149:Int) from rfl,
    show FloatFormat.binary32.fracWidth=23 from rfl,
    show Int.ofNat 23=(23:Int) from rfl,
    show FloatFormat.binary32.bias=127 from rfl]
  by_cases hsmall : TensorCore.magnitudeExponent |x| < -150
  · rw [ite_eq_left hsmall,normExp_subnormal x (by omega),roundedCoeff_tiny_rne x hx hsmall]
    cases s
    · exact zero_bits false
    · exact zero_bits true
  · rw [ite_eq_right hsmall]
    by_cases hsub : TensorCore.magnitudeExponent |x| < -126
    · rw [ite_eq_left hsub]
      have hc := scaled_coefficient .nearestEven x (-149)
      have heq := normExp_subnormal x hsub
      have hce : TensorCore.roundedSignificand .nearestEven |x| =
        TensorCore.roundSignificand .nearestEven (|x|/TCFloat.pow2 (-149)) := by
        rw [TensorCore.roundedSignificand,heq]; rfl
      change (roundQuotientEven
        (RationalBinary.scaleByPowerOfTwo x.num.natAbs x.den 149).1
        (RationalBinary.scaleByPowerOfTwo x.num.natAbs x.den 149).2 : Int) = _ at hc
      rw [← hce] at hc
      have hcn := congrArg Int.toNat hc
      simp only [Int.toNat_natCast] at hcn
      rw [heq]
      have hb := roundedCoeff_subnormal .nearestEven x hx hsub
      have hcarry : TensorCore.carry (-126) (TensorCore.roundedSignificand .nearestEven |x|) =
          (-126,TensorCore.roundedSignificand .nearestEven |x|) := by
        unfold TensorCore.carry
        split
        · omega
        · rfl
      rw [hcarry]
      split
      · rename_i hz
        have hkz : TensorCore.roundedSignificand .nearestEven |x| = 0 := by rw [hz] at hc; simpa using hc.symm
        rw [hkz]
        cases s
        · exact zero_bits false
        · exact zero_bits true
      · split
        · rename_i hle _
          have hqge : 2^23 ≤ (TensorCore.roundedSignificand .nearestEven |x|).toNat := by
            change 2^23 ≤ roundQuotientEven
              (RationalBinary.scaleByPowerOfTwo x.num.natAbs x.den 149).1
              (RationalBinary.scaleByPowerOfTwo x.num.natAbs x.den 149).2 at hle
            rwa [hcn] at hle
          have hkeq : TensorCore.roundedSignificand .nearestEven |x| = 8388608 := by omega
          rw [hkeq]
          have hp := encode_normal s (-126) 8388608 (by decide) (by decide) (by decide) (by decide)
          norm_num at hp
          exact hp
        · rename_i hlt _
          have hqlt : ¬2^23 ≤ (TensorCore.roundedSignificand .nearestEven |x|).toNat := by
            change ¬2^23 ≤ roundQuotientEven
              (RationalBinary.scaleByPowerOfTwo x.num.natAbs x.den 149).1
              (RationalBinary.scaleByPowerOfTwo x.num.natAbs x.den 149).2 at hlt
            rwa [hcn] at hlt
          rw [hcn]
          exact encode_subnormal s _ hk.1 (by omega)
    · rw [ite_eq_right hsub]
      have heq : TensorCore.normExp |x| = TensorCore.magnitudeExponent |x| := by
        unfold TensorCore.normExp TensorCore.emin32; omega
      have hc := scaled_coefficient .nearestEven x (TensorCore.normExp |x|-23)
      have hs : -(TensorCore.normExp |x|-23) = 23-TensorCore.magnitudeExponent |x| := by omega
      rw [hs] at hc
      change (roundQuotientEven _ _ : Int) = TensorCore.roundedSignificand .nearestEven |x| at hc
      have hcn := congrArg Int.toNat hc
      simp only [Int.toNat_natCast] at hcn
      rw [hcn,← heq]
      have hlo := (Model.roundQuotientEven_normal_bounds .binary32 _ _ hn x.den_nz).1
      simp only [show FloatFormat.binary32.fracWidth=23 from rfl,
        Model.pow2_eq_two_pow,floorLog2_eq x hx,show Int.ofNat 23=(23:Int) from rfl,hcn] at hlo
      have hlok : 2^23 ≤ TensorCore.roundedSignificand .nearestEven |x| := by omega
      by_cases hcarry : TensorCore.roundedSignificand .nearestEven |x| = 2^24
      · have hetop : TensorCore.normExp |x|+1 ≤127 := by omega
        rw [hcarry]
        change (if TensorCore.normExp |x|+1 > 127 then _ else
          Model.ofFields .binary32 s (TensorCore.normExp |x|+1+127).toNat 0).bits.toNat = _
        rw [ite_eq_right (not_lt.mpr hetop)]
        have hcarryeq : TensorCore.carry (TensorCore.normExp |x|) (2^24) =
            (TensorCore.normExp |x|+1,8388608) := by norm_num [TensorCore.carry]
        rw [hcarryeq]
        have h := encode_normal s (TensorCore.normExp |x|+1) 8388608 (by omega) hetop (by decide) (by decide)
        norm_num at h
        exact h
      · have hcarryN : (TensorCore.roundedSignificand .nearestEven |x|).toNat ≠ 2^24 := by omega
        simp only [Model.pow2_eq_two_pow,hcarryN,ite_false,
          not_lt.mpr he.2.1,TensorCore.carry,hcarry]
        exact encode_normal s _ _ he.1 he.2.1 hlok (by omega)

/-- Bit-for-bit FP32 rounding equivalence, for every rational and rounding mode. -/
theorem round32_eq (m : TensorCore.RoundingMode) (x : Rat) :
    TCFloat.round32 (mode m) x = (TensorCore.round32 m x).map BitVec.toNat := by
  by_cases hr : |x| ≤ TCFloat.maxFinite32
  · by_cases hz : x = 0
    · subst x
      cases m <;> decide +kernel
    · rw [source_round_nonzero m x hz hr]
      simp only [TCFloat.round32,not_lt.mpr hr,ite_false,Option.map_some]
      have hs : decide (x.num<0) = decide (x<0) := by
        congr 1
        exact propext (by simpa only [not_le] using not_congr (Rat.num_nonneg (q := x)))
      rw [hs]
      apply congrArg some
      cases m
      · exact round32_rtz_nonzero _ x hz hr
      · exact round32_rne_nonzero _ x hz hr
  · have ho : |x| > TCFloat.maxFinite32 := lt_of_not_ge hr
    simp only [TCFloat.round32,TensorCore.round32,abs_eq,maxFinite_eq,ho,ite_true,Option.map_none]

theorem round32_rne_eq (x : Rat) :
    TCFloat.round32 .nearestEven x = (TensorCore.round32 .nearestEven x).map BitVec.toNat :=
  round32_eq .nearestEven x

theorem round32_rtz_eq (x : Rat) :
    TCFloat.round32 .towardZero x = (TensorCore.round32 .truncate x).map BitVec.toNat :=
  round32_eq .truncate x

end TCFloat.Equivalence
