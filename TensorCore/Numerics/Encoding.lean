import TensorCore.Numerics.Defs

/-! Classification and decoding of binary words. -/

namespace TensorCore

/-- Classification of a bit pattern given as a natural number below `2 ^ f.width`. -/
def classifyNat (f : Format) (n : ℕ) : Classification :=
  let mantissa := n % 2 ^ f.mantissaBits
  let exponent := n / 2 ^ f.mantissaBits % 2 ^ f.exponentBits
  let negative := n / 2 ^ (f.mantissaBits + f.exponentBits) != 0
  let signed (m : ℕ) : ℤ := if negative then -(m : ℤ) else m
  if exponent = 2 ^ f.exponentBits - 1 then
    if mantissa = 0 then .infinity negative else .nan
  else if exponent = 0 then
    if mantissa = 0 then .zero negative
    else .subnormal ⟨signed mantissa, 1 - f.bias, f.mantissaBits⟩
  else .normal ⟨signed (2 ^ f.mantissaBits + mantissa),
    (exponent : ℤ) - f.bias, f.mantissaBits⟩

def classify (f : Format) (bits : BitVec f.width) : Classification := classifyNat f bits.toNat

def Classification.finite : Classification → Option Decoded
  | .zero _ => some ⟨0, 0, 0⟩
  | .subnormal x | .normal x => some x
  | .infinity _ | .nan => none

@[implicit_reducible] def decode16 (x : F16) : Option Decoded := (classify fp16 x).finite
@[implicit_reducible] def decode32 (x : F32) : Option Decoded := (classify fp32 x).finite

theorem decode32_eq (x : F32) : decode32 x = (classifyNat fp32 x.toNat).finite := rfl

def value32 (x : F32) : Option ℚ := (decode32 x).map Decoded.value

structure Finite32 where
  bits : F32
  decoded : Decoded
  valid : decode32 bits = some decoded
  deriving Repr, DecidableEq

def finite32 (bits : F32) : Option Finite32 :=
  match h : decode32 bits with
  | none => none
  | some d => some ⟨bits, d, h⟩

def Finite32.value (x : Finite32) : ℚ := x.decoded.value

theorem finite32_of_value32 (b : F32) (v : ℚ) (h : value32 b = some v) :
    ∃ f : Finite32, finite32 b = some f ∧ f.bits = b ∧ f.value = v := by
  unfold value32 at h
  cases hd : decode32 b with
  | none => simp [hd] at h
  | some d =>
    simp only [hd, Option.map_some, Option.some.injEq] at h
    refine ⟨⟨b, d, hd⟩, ?_, rfl, h⟩
    unfold finite32
    split
    · rename_i h'; rw [hd] at h'; contradiction
    · rename_i d' h'; rw [hd] at h'; cases Option.some.inj h'; rfl

end TensorCore
