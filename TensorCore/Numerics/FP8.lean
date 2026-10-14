import TensorCore.Numerics.Format

/-! The 8-bit formats E4M3 and E5M2, as NVIDIA Ada, Hopper and Blackwell Tensor Cores take them.

E5M2 follows IEEE 754: its all-ones exponent encodes the infinities and NaNs. E4M3 is the "fn"
variant: it has no infinities, its all-ones exponent holds finite values up to 448, and its only
NaNs are `S.1111.111`. Both use the existing decoders: E5M2 the IEEE classification, E4M3 the
`finiteTopNaN` rule of `ValueFormat`.

The block model decodes its operands with the IEEE classification, so it takes E4M3 values in a
9-bit layout, `e4m3x`, whose exponent field has one more bit: E4M3's top binade is then an ordinary
binade, and the bias, the minimum exponent and the subnormals are E4M3's. `widenE4M3` maps each E4M3
word to its `e4m3x` word, and `e4m3_decode_widen` proves, for all 256 words, that the two decodings
agree (as `tf32Unpack` does for TF32 register words and the `tf19` layout). -/

namespace TensorCore

/-- E5M2: two mantissa bits, five exponent bits, bias 15; IEEE classification. -/
@[implicit_reducible] def e5m2 : Format := ⟨2, 5, 15⟩

/-- The bit layout of E4M3: three mantissa bits, four exponent bits, bias 7. -/
@[implicit_reducible] def e4m3 : Format := ⟨3, 4, 7⟩

/-- E4M3 values: the all-ones exponent is finite except `S.1111.111`, the only NaNs. -/
def e4m3Values : ValueFormat := ⟨e4m3, .finiteTopNaN⟩

/-- E4M3 operands as 8-bit words. -/
def e4m3Encoding : OperandEncoding := ⟨e4m3Values, 0⟩

/-- E5M2 operands as 8-bit words. -/
def e5m2Encoding : OperandEncoding := packedIEEE e5m2

/-- E4M3 values in a 9-bit layout with IEEE classification: E4M3's bias and fields, with one more
exponent bit. -/
@[implicit_reducible] def e4m3x : Format := ⟨3, 5, 7⟩

/-- The `e4m3x` word of an E4M3 word: the sign moves to bit 8, the exponent and mantissa fields are
unchanged, and the NaNs `S.1111.111` become the NaNs `S.11111.111`. -/
def widenE4M3 (w : BitVec 8) : BitVec 9 :=
  BitVec.ofNat 9 (w.toNat / 128 * 256 + if w.toNat % 128 = 127 then 255 else w.toNat % 128)

/-- The E4M3 decoding of every word is the IEEE decoding of its `e4m3x` word. -/
theorem e4m3_decode_widen (w : BitVec 8) :
    e4m3Encoding.decode w = (classify e4m3x (widenE4M3 w)).finite := by
  have h : ∀ n : ℕ, n < 256 → e4m3Encoding.decode (BitVec.ofNat 8 n) =
      (classify e4m3x (widenE4M3 (BitVec.ofNat 8 n))).finite := by
    decide +kernel
  have hw := h w.toNat w.isLt
  rwa [BitVec.ofNat_toNat, BitVec.setWidth_eq] at hw

/-- The E5M2 decoding of a word is its IEEE decoding. -/
theorem e5m2_decode (w : BitVec 8) : e5m2Encoding.decode w = (classify e5m2 w).finite :=
  packedIEEE_decode e5m2 w

/-! ## Special and boundary encodings -/

/-- E4M3 has no infinities, and exactly two NaN words, `0x7f` and `0xff`. -/
theorem e4m3_specials :
    (∀ n : ℕ, n < 256 → ∀ s, e4m3Values.classifyNat n ≠ .infinity s) ∧
    (∀ n : ℕ, n < 256 → (e4m3Values.classifyNat n = .nan ↔ n = 0x7f ∨ n = 0xff)) := by
  decide +kernel

/-- E5M2 has the infinities `0x7c` and `0xfc` and the NaNs `0x7d`–`0x7f` and `0xfd`–`0xff`. -/
theorem e5m2_specials :
    classifyNat e5m2 0x7c = .infinity false ∧ classifyNat e5m2 0xfc = .infinity true ∧
    (∀ n : ℕ, n < 256 → (classifyNat e5m2 n = .nan ↔
      n = 0x7d ∨ n = 0x7e ∨ n = 0x7f ∨ n = 0xfd ∨ n = 0xfe ∨ n = 0xff)) := by
  decide +kernel

/-- Every finite E4M3 value has magnitude at most 448, attained by `0x7e` and `0xfe`. -/
theorem e4m3_max :
    (∀ n : ℕ, n < 256 → (e4m3Values.classifyNat n).finite.all (fun d => absQ d.value ≤ 448)) ∧
    (e4m3Encoding.decode 0x7e).map Decoded.value = some 448 ∧
    (e4m3Encoding.decode 0xfe).map Decoded.value = some (-448) := by
  decide +kernel

/-- Every finite E5M2 value has magnitude at most 57344, attained by `0x7b` and `0xfb`. -/
theorem e5m2_max :
    (∀ n : ℕ, n < 256 → (classifyNat e5m2 n).finite.all (fun d => absQ d.value ≤ 57344)) ∧
    (e5m2Encoding.decode 0x7b).map Decoded.value = some 57344 ∧
    (e5m2Encoding.decode 0xfb).map Decoded.value = some (-57344) := by
  decide +kernel

end TensorCore
