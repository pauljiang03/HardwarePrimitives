import MatrixCoreTests.Support

/-! # Table 1 formats and binary32 rounding

Decoded extreme words of each input format, the FNUZ conventions, XF32 truncation, and the RNE
overflow threshold. -/

namespace MatrixCoreTests.Formats

open MatrixCore

def val (f : Format) (n : ℕ) : Option ℚ := (f.decodeNat n).toFinite.map Unpacked.value

/-- binary16: maximum `65504`, minimum normal `2^-14`, minimum subnormal `2^-24`. -/
example : val fp16 0x7BFF = some 65504 ∧ val fp16 0x0400 = some (p2 (-14)) ∧
    val fp16 0x0001 = some (p2 (-24)) ∧ fp16.decodeNat 0x7C00 = .infinity false := by
  decide +kernel

/-- bfloat16: maximum `(2 − 2^-7)·2^127`, minimum normal `2^-126`. -/
example : val bf16 0x7F7F = some ((2 - p2 (-7)) * p2 127) ∧
    val bf16 0x0080 = some (p2 (-126)) := by decide +kernel

/-- tf19: maximum `(2 − 2^-10)·2^127`. -/
example : val tf19 0x3FBFF = some ((2 - p2 (-10)) * p2 127) := by decide +kernel

/-- fp8-E4M3 FNUZ: maximum `240`, minimum normal `2^-7`, minimum subnormal `2^-10`; the
negative-zero word is NaN and there are no infinities. -/
example : val e4m3fnuz 0x7F = some 240 ∧ val e4m3fnuz 0x08 = some (p2 (-7)) ∧
    val e4m3fnuz 0x01 = some (p2 (-10)) ∧ e4m3fnuz.decodeNat 0x80 = .nan ∧
    val e4m3fnuz 0xFF = some (-240) := by decide +kernel

/-- fp8-E5M2 FNUZ: maximum `57344`, minimum normal `2^-15`, minimum subnormal `2^-17`. -/
example : val e5m2fnuz 0x7F = some 57344 ∧ val e5m2fnuz 0x04 = some (p2 (-15)) ∧
    val e5m2fnuz 0x01 = some (p2 (-17)) ∧ e5m2fnuz.decodeNat 0x80 = .nan := by decide +kernel

/-- binary32: maximum `(2 − 2^-23)·2^127`, the infinities and a NaN. -/
example : val fp32 0x7F7FFFFF = some ((2 - p2 (-23)) * p2 127) ∧
    fp32.decodeNat 0xFF800000 = .infinity true ∧ fp32.decodeNat 0x7FC00000 = .nan := by
  decide +kernel

/-- XF32 reads `1 + 2^-10 + 2^-11` (`0x3F803000`) as `1 + 2^-10`. -/
example : ((InputFormat.xf32.read (0x3F803000 : BitVec 32)).toFinite.map Unpacked.value) =
    some (1 + p2 (-10)) := by decide +kernel

/-- RNE overflows exactly at `2^128 − 2^103`; just below, it returns the largest finite value. -/
example : rne32 (p2 128 - p2 103) = none ∧
    rne32 (p2 128 - p2 103 - p2 90) = some 0x7F7FFFFF ∧
    rne32 (-(p2 128 - p2 103 - p2 90)) = some 0xFF7FFFFF := by decide +kernel

/-- Ties go to even, also into the subnormal range; tiny values keep their sign as zeros. -/
example : rne32 (1 + p2 (-24)) = some 0x3F800000 ∧ rne32 (1 + 3 * p2 (-24)) = some 0x3F800002 ∧
    rne32 (3 * p2 (-150)) = some 0x00000002 ∧ rne32 (-p2 (-151)) = some 0x80000000 := by
  decide +kernel

/-- Flush to zero keeps the sign. -/
example : fl32 true (-p2 (-130)) = some 0x80000000 ∧ fl32 false (-p2 (-130)) = some 0x80080000 := by
  decide +kernel

/-- Models by architecture and input format. -/
example : Architecture.model .cdna1 .fp16 = some cdna1F16 ∧
    Architecture.model .cdna2 .bf16_1k = some cdna2BF16_1k ∧
    Architecture.model .cdna3 (.fp8 e4m3fnuz e5m2fnuz) = some (cdna3FP8 e4m3fnuz e5m2fnuz) ∧
    Architecture.model .cdna1 .xf32 = none ∧ Architecture.ofDevice "MI300X" = some .cdna3 := by
  decide

end MatrixCoreTests.Formats
