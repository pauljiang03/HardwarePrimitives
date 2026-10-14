import TensorCore

/-! FP8 encodings and block FMAs: every special and boundary encoding of E4M3 and E5M2, the
widened E4M3 layout, the 13-bit block output, recursive summation and the B200 recording
convention. -/

namespace TensorCoreTests.FP8

open TensorCore

/-! ## E4M3: no infinities, NaN only at `S.1111.111`, largest value 448 -/

example : e4m3Values.classifyNat 0x00 = .zero false ∧ e4m3Values.classifyNat 0x80 = .zero true := by
  decide +kernel

example : (e4m3Encoding.decode 0x01).map Decoded.value = some (1 / 512) ∧
    (e4m3Encoding.decode 0x07).map Decoded.value = some (7 / 512) ∧
    (e4m3Encoding.decode 0x08).map Decoded.value = some (1 / 64) ∧
    (e4m3Encoding.decode 0x38).map Decoded.value = some 1 ∧
    (e4m3Encoding.decode 0x77).map Decoded.value = some 240 ∧
    (e4m3Encoding.decode 0x78).map Decoded.value = some 256 ∧
    (e4m3Encoding.decode 0x7e).map Decoded.value = some 448 ∧
    (e4m3Encoding.decode 0xf8).map Decoded.value = some (-256) ∧
    (e4m3Encoding.decode 0xfe).map Decoded.value = some (-448) ∧
    (e4m3Encoding.decode 0x81).map Decoded.value = some (-1 / 512) := by
  decide +kernel

/-- `0x78` is a normal value, not an infinity; `0x7f` and `0xff` are NaNs. -/
example : e4m3Values.classifyNat 0x78 = .normal ⟨8, 8, 3⟩ ∧
    e4m3Values.classifyNat 0x7f = .nan ∧ e4m3Values.classifyNat 0xff = .nan ∧
    e4m3Encoding.decode 0x7f = none ∧ e4m3Encoding.decode 0xff = none := by
  decide +kernel

/-- The IEEE decoding of the E4M3 layout would wrongly make `0x78` an infinity: E4M3 needs its own
rule. -/
example : classifyNat e4m3 0x78 = .infinity false ∧ e4m3Values.classifyNat 0x78 ≠ .infinity false := by
  decide +kernel

/-- Subnormal E4M3 values keep the minimum exponent −6, normal ones their own. -/
example : e4m3Encoding.decode 0x07 = some ⟨7, -6, 3⟩ ∧ e4m3Encoding.decode 0x08 = some ⟨8, -6, 3⟩ ∧
    e4m3Encoding.decode 0x7e = some ⟨14, 8, 3⟩ := by
  decide +kernel

/-! ## The widened E4M3 layout -/

example : widenE4M3 0x7e = 0x07e ∧ widenE4M3 0xfe = 0x17e ∧ widenE4M3 0x7f = 0x0ff ∧
    widenE4M3 0xff = 0x1ff ∧ widenE4M3 0x80 = 0x100 ∧ widenE4M3 0x01 = 0x001 := by
  decide +kernel

example : classify e4m3x 0x0ff = .nan ∧ (classify e4m3x 0x078).finite = some ⟨8, 8, 3⟩ := by
  decide +kernel

/-! ## E5M2: IEEE-like, largest value 57344 -/

example : classifyNat e5m2 0x00 = .zero false ∧ classifyNat e5m2 0x80 = .zero true ∧
    classifyNat e5m2 0x7c = .infinity false ∧ classifyNat e5m2 0xfc = .infinity true ∧
    classifyNat e5m2 0x7d = .nan ∧ classifyNat e5m2 0x7e = .nan ∧ classifyNat e5m2 0x7f = .nan ∧
    classifyNat e5m2 0xfd = .nan ∧ classifyNat e5m2 0xfe = .nan ∧ classifyNat e5m2 0xff = .nan := by
  decide +kernel

example : (e5m2Encoding.decode 0x01).map Decoded.value = some (1 / 65536) ∧
    (e5m2Encoding.decode 0x03).map Decoded.value = some (3 / 65536) ∧
    (e5m2Encoding.decode 0x04).map Decoded.value = some (1 / 16384) ∧
    (e5m2Encoding.decode 0x3c).map Decoded.value = some 1 ∧
    (e5m2Encoding.decode 0x7b).map Decoded.value = some 57344 ∧
    (e5m2Encoding.decode 0xfb).map Decoded.value = some (-57344) ∧
    e5m2Encoding.decode 0x7c = none ∧ e5m2Encoding.decode 0xfc = none ∧
    e5m2Encoding.decode 0x7f = none := by
  decide +kernel

/-! ## The 13-bit block output of Ada and Hopper FP8 -/

/-- `1·1 + 1·1 + 2^-9·2^-4 = 2 + 2^-13`: the 13-bit block output keeps `2`, a binary32 output
would keep `2 + 2^-13`. -/
def narrowCase : List (BitVec 9 × BitVec 9) :=
  [(widenE4M3 0x38, widenE4M3 0x38), (widenE4M3 0x38, widenE4M3 0x38),
    (widenE4M3 0x01, widenE4M3 0x18)] ++ List.replicate 13 (0, 0)

example : (evalBlock (⟨narrowCase, 0⟩ : BlockInput adaE4M3F32)).toOption.map (·.output.bits) =
    some 0x40000000 := by
  decide +kernel

/-- Ada E4M3 with a binary32 block output instead. -/
@[implicit_reducible] def adaE4M3Binary32 : Model := ⟨e4m3x, 16, 13, none, 23⟩

example : (evalBlock (⟨narrowCase, 0⟩ : BlockInput adaE4M3Binary32)).toOption.map (·.output.bits) =
    some 0x40000200 := by
  decide +kernel

/-! ## Recursive summation and the B200 recording convention -/

/-- Thirty-two products of one on Ada: two block FMAs of sixteen, `16 + 16 = 32`. -/
example : adaE4M3F32.dot 0 (List.replicate 32 (widenE4M3 0x38, widenE4M3 0x38)) = some 0x42000000 := by
  decide +kernel

/-- `c = 2^24 + 2` and one product of one on B200: inside the block FMA the sum `2^24 + 3` is
truncated to `2^24 + 2`; added after it, `2^24 + 3` rounds to the even `2^24 + 4`. -/
example :
    blackwellE4M3F32.dot 0x4b800001 ((widenE4M3 0x38, widenE4M3 0x38) :: List.replicate 31 (0, 0)) =
      some 0x4b800001 ∧
    blackwellE4M3F32.dotThenAdd 0x4b800001
      ((widenE4M3 0x38, widenE4M3 0x38) :: List.replicate 31 (0, 0)) = some 0x4b800002 := by
  decide +kernel

/-- The descriptors agree on the same cases, with E4M3 decoded by its own rule. -/
example : invocationBits (p := adaE4M3Invocation)
    ⟨[(0x38, 0x38), (0x38, 0x38), (0x01, 0x18)] ++ List.replicate 13 (0, 0), 0⟩ = some 0x40000000 ∧
    invocationBits (p := blackwellE4M3ThenAddInvocation)
      ⟨(0x38, 0x38) :: List.replicate 31 (0, 0), 0x4b800001⟩ = some 0x4b800002 := by
  decide +kernel

end TensorCoreTests.FP8
