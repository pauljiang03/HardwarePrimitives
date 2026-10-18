import TCFloat.Equivalence.Base

namespace TCFloat.Equivalence
open FloatLib.Floats.Formats.BinaryInterchange
open FloatLib.Numerics

theorem abs_ratio (x : Rat) : (x.num.natAbs : Rat) / x.den = |x| := by
  calc
    _ = |(x.num : Rat) / x.den| := by simp [abs_div]
    _ = |x| := congrArg abs (Rat.num_div_den x)

theorem cast_pow2 (e : Int) : ((TCFloat.pow2 e : Rat) : ℝ) = (2:ℝ)^e := by
  simp [TCFloat.pow2]

theorem floorLog2_eq (x : Rat) (hx : x ≠ 0) :
    RationalBinary.floorLog2 x.num.natAbs x.den = TensorCore.magnitudeExponent |x| := by
  have hp : 0 < |x| := abs_pos.mpr hx
  obtain ⟨hl,hu⟩ := TensorCore.magnitudeExponent_spec |x| hp
  apply Model.floorLog2_eq_of_bounds
  · exact fun h => hx (Rat.num_eq_zero.mp (Int.natAbs_eq_zero.mp h))
  · exact x.den_nz
  · change (2:ℝ)^(TensorCore.magnitudeExponent |x|) ≤ (x.num.natAbs:ℝ)/x.den
    have hr : (x.num.natAbs:ℝ)/x.den = ((|x|:Rat):ℝ) := by
      simpa only [Rat.cast_div,Rat.cast_natCast] using congrArg (fun q : Rat => (q:ℝ)) (abs_ratio x)
    rw [hr]
    have h := (Rat.cast_le (K := ℝ)).mpr hl
    simpa only [pow2_eq,cast_pow2] using h
  · change (x.num.natAbs:ℝ)/x.den < (2:ℝ)^(TensorCore.magnitudeExponent |x|+1)
    have hr : (x.num.natAbs:ℝ)/x.den = ((|x|:Rat):ℝ) := by
      simpa only [Rat.cast_div,Rat.cast_natCast] using congrArg (fun q : Rat => (q:ℝ)) (abs_ratio x)
    rw [hr]
    have h := (Rat.cast_lt (K := ℝ)).mpr hu
    simpa only [pow2_eq,cast_pow2] using h

theorem scale_ratio (n d : Nat) (e : Int) :
    ((RationalBinary.scaleByPowerOfTwo n d e).1 : Rat) /
        (RationalBinary.scaleByPowerOfTwo n d e).2 = (n:Rat)/d * TCFloat.pow2 e := by
  apply Rat.cast_injective (α := ℝ)
  simpa [TCFloat.pow2, Model.scaledRatToReal, Model.bpow, FloatLib.Floats.Formats.Flocq.bpow, binaryRadix, Radix.toReal] using Model.scaleByPowerOfTwo_real n d e

theorem rneInt_real (x : Rat) :
    TensorCore.rneInt x = FloatLib.Floats.Formats.Flocq.nearestEven (x : ℝ) := by
  have hf : (⌊(x:ℝ)⌋ : Int) = x.floor := Rat.floor_cast x
  have hc : ((x - (x.floor : Rat) : Rat) : ℝ) = (x:ℝ) - x.floor := by simp
  have hl : (x:ℝ) - x.floor < 1/2 ↔ 2*(x - (x.floor:Rat)) < 1 := by
    rw [← hc, ← Rat.cast_one, ← Rat.cast_ofNat (n := 2), ← Rat.cast_div, Rat.cast_lt]
    constructor <;> intro h <;> linarith
  have hg : (1:ℝ)/2 < (x:ℝ) - x.floor ↔ 1 < 2*(x - (x.floor:Rat)) := by
    rw [← hc, ← Rat.cast_one, ← Rat.cast_ofNat (n := 2), ← Rat.cast_div, Rat.cast_lt]
    constructor <;> intro h <;> linarith
  unfold TensorCore.rneInt FloatLib.Floats.Formats.Flocq.nearestEven
  simp only [hf]
  simp only [hl,hg,Int.even_iff]
  split_ifs <;> grind

theorem quotient_rne (n d : Nat) (hd : d ≠ 0) :
    (roundQuotientEven n d : Int) = TensorCore.rneInt ((n:Rat)/d) := by
  rw [rneInt_real]
  simpa using (Model.nearestEven_div_eq_roundQuotientEven n d hd).symm

theorem quotient_rtz (n d : Nat) :
    (Model.roundQuotDirected false n d : Int) = ((n:Rat)/d).floor := by
  change (n/d : Nat) = ⌊(n:Rat)/d⌋
  rw [Rat.floor_natCast_div_natCast]
  rfl

end TCFloat.Equivalence
