import TCFloat.Equivalence.Quotient
import TCFloat.Equivalence.Decode

set_option maxRecDepth 2048
set_option backward.isDefEq.respectTransparency false
namespace TCFloat.Equivalence
open FloatLib.Floats.Formats.BinaryInterchange

theorem fields_nat (fmt : FloatFormat) (s : Bool) (e f : Nat)
    (he : e < 2^fmt.expWidth) (hf : f < 2^fmt.fracWidth) :
    (Model.ofFields fmt s e f).bits.toNat =
      (if s then 2^(fmt.expWidth+fmt.fracWidth) else 0) + e*2^fmt.fracWidth + f := by
  unfold Model.ofFields
  rw [Model.mkBits_eq_mkBitsImpl_apply]
  simp only [Model.ofBits,Model.mkBitsImpl,BitVec.toNat_ofNatLT,
    FloatFormat.expAllOnesNat,FloatFormat.fracMaskNat]
  have shift_or (a i b : Nat) (hb : b < 2^i) :
      Nat.shiftLeft a i ||| b = a*2^i+b := by
    calc
      _ = (a <<< i) ||| b := rfl
      _ = (a <<< i) + b := (Nat.shiftLeft_add_eq_or_of_lt hb a).symm
      _ = a*2^i+b := by rw [Nat.shiftLeft_eq]
  rw [Nat.and_two_pow_sub_one_eq_mod,Nat.and_two_pow_sub_one_eq_mod,
    Nat.mod_eq_of_lt he,Nat.mod_eq_of_lt hf,Nat.or_assoc,shift_or e _ f hf]
  have hl : e*2^fmt.fracWidth + f < 2^(fmt.expWidth+fmt.fracWidth) := by
    rw [pow_add]
    nlinarith
  cases s
  · simp
  · simp only [ite_true]
    rw [shift_or 1 _ _ hl]
    simp only [one_mul,Nat.add_assoc]

theorem encode_subnormal (s : Bool) (k : Int) (hk : 0 ≤ k) (hu : k < 2^23) :
    (Model.ofFields .binary32 s 0 k.toNat).bits.toNat =
      (TensorCore.encode32 s (-126) k).toNat := by
  rw [fields_nat _ s 0 k.toNat (by decide) (by change k.toNat < 2^23; omega)]
  have hword : (if s then 2^31 else 0) + k.toNat < 2^32 := by cases s <;> simp <;> omega
  norm_num at hu
  simp only [TensorCore.encode32,BitVec.toNat_ofNat]
  change (if s then 2^31 else 0) + 0*2^23 + k.toNat =
    ((if s then 2^31 else 0) + if k < 2^23 then k.toNat else _) % 2^32
  rw [ite_eq_left (show k < 2^23 by exact hu),Nat.mod_eq_of_lt hword]
  omega

theorem encode_normal (s : Bool) (e k : Int)
    (he : -126 ≤ e) (he' : e ≤ 127) (hk : 2^23 ≤ k) (hk' : k < 2^24) :
    (Model.ofFields .binary32 s (e+127).toNat (k.toNat-2^23)).bits.toNat =
      (TensorCore.encode32 s e k).toNat := by
  rw [fields_nat _ s (e+127).toNat (k.toNat-2^23)
    (by change (e+127).toNat < 2^8; omega) (by change k.toNat-2^23 < 2^23; omega)]
  have ht : k.toNat-2^23 = (k-2^23).toNat := by omega
  simp only [TensorCore.encode32,BitVec.toNat_ofNat,not_lt.mpr hk,ite_false]
  change (if s then 2^31 else 0) + (e+127).toNat*2^23 + (k.toNat-2^23) =
    ((if s then 2^31 else 0) + ((e+127).toNat*2^23 + (k-2^23).toNat)) % 2^32
  rw [ht,Nat.mod_eq_of_lt (by cases s <;> simp <;> omega)]
  omega

theorem zero_bits (s : Bool) :
    (Model.zero .binary32 s).bits.toNat = (TensorCore.encode32 s (-126) 0).toNat := by
  cases s <;> decide +kernel

theorem subnormal_pack (s : Bool) (k : Int) (hk : 0 ≤ k) (hu : k ≤ 2^23) :
    (Model.packRoundedSubnormal .binary32 s (Model.zero .binary32 s) k.toNat).bits.toNat =
      (TensorCore.encode32 s (-126) k).toNat := by
  by_cases hz : k = 0
  · subst k; exact zero_bits s
  · by_cases ht : k = 2^23
    · subst k
      have h := encode_normal s (-126) (2^23) (by decide) (by decide) (by decide) (by decide)
      change (Model.ofFields .binary32 s 1 0).bits.toNat = _ at h
      exact h
    · have hlt : k < 2^23 := by omega
      simpa only [Model.packRoundedSubnormal,
        show FloatFormat.binary32.fracWidth=23 from rfl,Model.pow2_eq_two_pow,
        beq_iff_eq,show k.toNat ≠ 0 by omega,show ¬ (2^23 ≤ k.toNat) by omega,
        ite_false] using encode_subnormal s k hk hlt

theorem normal_pack (s : Bool) (overflow : Model .binary32) (e k : Int)
    (he : -126 ≤ e) (he' : e ≤ 127) (hk : 2^23 ≤ k) (hk' : k ≤ 2^24)
    (htop : e = 127 → k ≤ 16777215) :
    (Model.packRoundedNormal .binary32 s overflow e k.toNat).bits.toNat =
      (TensorCore.encode32 s (TensorCore.carry e k).1 (TensorCore.carry e k).2).toNat := by
  have hf : FloatFormat.binary32.fracWidth = 23 := rfl
  have hb : FloatFormat.binary32.exponentBias = 127 := rfl
  have hm : FloatFormat.binary32.maxNormalExponent = 127 := rfl
  have hme : FloatFormat.binary32.maxFiniteExpField = 254 := rfl
  have hmf : FloatFormat.binary32.maxFiniteFracField = 8388607 := rfl
  by_cases hc : k = 2^24
  · have hen : e + 1 ≤ 127 := by omega
    have hex : (e+1+127).toNat ≤ 254 := by omega
    subst k
    simp only [Model.packRoundedNormal,hf,hb,hm,hme,hmf,Model.pow2_eq_two_pow,show Int.ofNat 127=(127:Int) from rfl]
    norm_num only
    have h := encode_normal s (e+1) (2^23) (by omega) hen (by decide) (by decide)
    change (Model.ofFields .binary32 s (e+1+127).toNat 0).bits.toNat =
      (TensorCore.encode32 s (e+1) 8388608).toNat at h
    simp only [show Int.toNat (16777216:Int)=16777216 from rfl,
      show ((16777216:Nat)==16777216)=true from rfl,ite_true,not_lt.mpr hen,ite_false,
      show (8388608:Nat)-8388608=0 from rfl,
      show decide ((e+1+127).toNat >254)=false from decide_eq_false (not_lt.mpr hex),
      show decide ((0:Nat)>8388607)=false from rfl,Bool.and_false,Bool.or_self]
    exact h
  · have hcN : k.toNat ≠ 2^24 := by omega
    have hex : (e+127).toNat ≤ 254 := by omega
    have hmant : k.toNat-2^23 ≤ 8388607 := by omega
    simp only [Model.packRoundedNormal,hf,hb,hm,hme,hmf,Model.pow2_eq_two_pow,
      beq_iff_eq,hcN,ite_false,not_lt.mpr he',TensorCore.carry,hc,show Int.ofNat 127=(127:Int) from rfl]
    simp only [show ¬(e+127).toNat > 254 by omega,decide_false,
      show ¬k.toNat-2^23 > 8388607 by omega,Bool.and_false,Bool.or_self]
    exact encode_normal s e k he he' hk (by omega)

theorem ieee_subnormal_pack (s : Bool) (k : Nat) :
    (if k == 0 then (if s then Model.negZero .binary32 else Model.posZero .binary32)
      else match Nat.decLe (2^23) k with
        | isTrue _ => Model.ofFields .binary32 s 1 0
        | isFalse _ => Model.ofFields .binary32 s 0 k) =
      Model.packRoundedSubnormal .binary32 s (Model.zero .binary32 s) k := by
  have hz : (if s then Model.negZero .binary32 else Model.posZero .binary32) =
      Model.zero .binary32 s := by cases s <;> rfl
  rw [hz]
  unfold Model.packRoundedSubnormal
  change (if k==0 then _ else match Nat.decLe (2^23) k with | isTrue _ => _ | isFalse _ => _) =
    (if k==0 then _ else if k ≥ 2^23 then _ else _)
  by_cases hk : k = 0
  · simp [hk]
  · simp only [hk,beq_iff_eq,ite_false]
    split <;> simp_all <;> intro h <;> omega

end TCFloat.Equivalence
