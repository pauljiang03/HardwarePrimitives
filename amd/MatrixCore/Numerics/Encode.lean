import MatrixCore.Numerics.Format

/-! # Exact encoding

Encodes a rational that the format represents exactly; any other value gives `none`. -/

namespace MatrixCore

/-- Word with the given sign, biased exponent field, and mantissa field. -/
def Format.pack (f : Format) (negative : Bool) (E M : ℕ) : BitVec f.width :=
  BitVec.ofNat f.width ((if negative then 2 ^ (f.mantissaBits + f.exponentBits) else 0) +
    E * 2 ^ f.mantissaBits + M)

/-- The word whose decoded value is exactly `v`, if one exists (`+0` for zero). -/
def Format.encodeExact (f : Format) (v : ℚ) : Option (BitVec f.width) :=
  if v = 0 then some 0
  else
    let a := absQ v
    let e := max (log2Floor a) f.emin
    let t := a / pow2 (e - f.mantissaBits)
    if t.den ≠ 1 then none
    else
      let m := t.num.toNat
      let E := if m < 2 ^ f.mantissaBits then 0 else (e + f.bias).toNat
      let w := f.pack (decide (v < 0)) E (m % 2 ^ f.mantissaBits)
      if (f.decode w).toFinite.map Unpacked.value = some v then some w else none

def fp32Exact (v : ℚ) : Option F32 := fp32.encodeExact v

def InputFormat.encodeExact : (i : InputFormat) → ℚ → Option i.Word
  | .packed f, v => f.encodeExact v
  | .xf32, v => fp32.encodeExact v

end MatrixCore
