import TensorCore.Numerics.Format

/-! The 8-bit formats E4M3 and E5M2, as NVIDIA Ada, Hopper and Blackwell Tensor Cores take them.

E5M2 follows IEEE 754; E4M3 has no infinities and its only NaNs are `S.1111.111`. The block model
takes E4M3 values in the 9-bit IEEE layout `e4m3x`, which decodes them identically. -/

namespace TensorCore

/-- E5M2: two mantissa bits, five exponent bits, bias 15; IEEE classification. -/
@[implicit_reducible] def e5m2 : Format := ⟨2, 5, 15⟩

/-- The bit layout of E4M3: three mantissa bits, four exponent bits, bias 7. -/
@[implicit_reducible] def e4m3 : Format := ⟨3, 4, 7⟩

/-- E4M3 values: the all-ones exponent is finite except `S.1111.111`, the only NaNs. -/
def e4m3Values : ValueFormat := ⟨e4m3, .finiteTopNaN⟩

def e4m3Encoding : OperandEncoding := ⟨e4m3Values, 0⟩

def e5m2Encoding : OperandEncoding := packedIEEE e5m2

/-- E4M3 values in a 9-bit IEEE layout: E4M3's bias and fields, with one more exponent bit. -/
@[implicit_reducible] def e4m3x : Format := ⟨3, 5, 7⟩

/-- The `e4m3x` word of an E4M3 word: the sign moves to bit 8 and the NaNs become `S.11111.111`. -/
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

/-! ## Conversion to FP16 -/

/-- The FP16 word of an E5M2 word: the E5M2 word followed by eight zero bits. -/
def e5m2ToF16 (w : BitVec 8) : F16 := BitVec.ofNat 16 (w.toNat * 256)

/-- The FP16 word with the value of an E4M3 word; E4M3 subnormals become FP16 normals. -/
def e4m3ToF16 (w : BitVec 8) : F16 :=
  let n := w.toNat
  let s := n / 128 * 32768
  let E := n / 8 % 16
  let M := n % 8
  BitVec.ofNat 16 <|
    if E = 15 ∧ M = 7 then s + 0x7e00
    else if E ≠ 0 then s + (E + 8) * 1024 + M * 128
    else if M = 0 then s
    else if M = 1 then s + 6 * 1024
    else if M < 4 then s + 7 * 1024 + (M - 2) * 512
    else s + 8 * 1024 + (M - 4) * 256

/-- Converting E4M3 to FP16 keeps every value, every NaN and the sign bit. -/
theorem e4m3ToF16_exact (w : BitVec 8) :
    (decode16 (e4m3ToF16 w)).map Decoded.value = (e4m3Encoding.decode w).map Decoded.value ∧
    (classify fp16 (e4m3ToF16 w) = .nan ↔ e4m3Values.classifyNat w.toNat = .nan) ∧
    (e4m3ToF16 w).toNat / 2 ^ 15 = w.toNat / 2 ^ 7 := by
  have h : ∀ n : ℕ, n < 256 →
      ((decode16 (e4m3ToF16 (BitVec.ofNat 8 n))).map Decoded.value =
        (e4m3Encoding.decode (BitVec.ofNat 8 n)).map Decoded.value ∧
      (classify fp16 (e4m3ToF16 (BitVec.ofNat 8 n)) = .nan ↔
        e4m3Values.classifyNat (BitVec.ofNat 8 n).toNat = .nan) ∧
      (e4m3ToF16 (BitVec.ofNat 8 n)).toNat / 2 ^ 15 = (BitVec.ofNat 8 n).toNat / 2 ^ 7) := by
    decide +kernel
  have hw := h w.toNat w.isLt
  rwa [BitVec.ofNat_toNat, BitVec.setWidth_eq] at hw

/-- Converting E5M2 to FP16 keeps every value, every infinity and NaN, and the sign bit. -/
theorem e5m2ToF16_exact (w : BitVec 8) :
    (decode16 (e5m2ToF16 w)).map Decoded.value = (e5m2Encoding.decode w).map Decoded.value ∧
    (classify fp16 (e5m2ToF16 w) = .nan ↔ classify e5m2 w = .nan) ∧
    (∀ s, classify fp16 (e5m2ToF16 w) = .infinity s ↔ classify e5m2 w = .infinity s) ∧
    (e5m2ToF16 w).toNat / 2 ^ 15 = w.toNat / 2 ^ 7 := by
  have h : ∀ n : ℕ, n < 256 →
      ((decode16 (e5m2ToF16 (BitVec.ofNat 8 n))).map Decoded.value =
        (e5m2Encoding.decode (BitVec.ofNat 8 n)).map Decoded.value ∧
      (classify fp16 (e5m2ToF16 (BitVec.ofNat 8 n)) = .nan ↔ classify e5m2 (BitVec.ofNat 8 n) = .nan) ∧
      (∀ s, classify fp16 (e5m2ToF16 (BitVec.ofNat 8 n)) = .infinity s ↔
        classify e5m2 (BitVec.ofNat 8 n) = .infinity s) ∧
      (e5m2ToF16 (BitVec.ofNat 8 n)).toNat / 2 ^ 15 = (BitVec.ofNat 8 n).toNat / 2 ^ 7) := by
    intro n hn
    have h1 : ∀ n : ℕ, n < 256 →
        ((decode16 (e5m2ToF16 (BitVec.ofNat 8 n))).map Decoded.value =
          (e5m2Encoding.decode (BitVec.ofNat 8 n)).map Decoded.value ∧
        (classify fp16 (e5m2ToF16 (BitVec.ofNat 8 n)) = .nan ↔
          classify e5m2 (BitVec.ofNat 8 n) = .nan) ∧
        (classify fp16 (e5m2ToF16 (BitVec.ofNat 8 n)) = .infinity false ↔
          classify e5m2 (BitVec.ofNat 8 n) = .infinity false) ∧
        (classify fp16 (e5m2ToF16 (BitVec.ofNat 8 n)) = .infinity true ↔
          classify e5m2 (BitVec.ofNat 8 n) = .infinity true) ∧
        (e5m2ToF16 (BitVec.ofNat 8 n)).toNat / 2 ^ 15 = (BitVec.ofNat 8 n).toNat / 2 ^ 7) := by
      decide +kernel
    obtain ⟨a, b, c, d, e⟩ := h1 n hn
    exact ⟨a, b, fun s => by cases s <;> assumption, e⟩
  have hw := h w.toNat w.isLt
  rwa [BitVec.ofNat_toNat, BitVec.setWidth_eq] at hw

end TensorCore
