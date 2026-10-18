import MatrixCore

/-! # The correction on CDNA 1–3

Kernel-evaluated blocks: the matrix core's output `D`, the correction from `D`, and its path. -/

namespace MatrixCoreTests.EFT

open MatrixCore

/-- RNE of the exact sum of a block's decoded inputs. -/
def target {P : Model} (x : BlockInput P) : Option (Option F32) :=
  (prepare x).map fun px => rne32 px.exact

/-- Cut-off `q`, `H`, overlap, sum of the low parts, and the part the matrix core kept. -/
def parts {P : Model} (x : BlockInput P) : Option (ℤ × ℚ × ℚ × ℚ × ℚ) :=
  match evalBlock x with
  | .ok t => some (t.split.q, t.split.H, t.split.overlap (wordValue t.d), sumQ t.split.lows,
      keptLow P t.prepared t.split.q)
  | .error _ => none

/-! ## CDNA 3 FP16: seven small products lost to alignment -/

def cdna3Lost : BlockInput cdna3F16 :=
  ⟨[0x4080] ++ List.replicate 7 0x0C00, [0x3C00] ++ List.replicate 7 0x0C00, 0⟩

example : blockBits cdna3Lost = .ok 0x40100000 := by decide +kernel
example : target cdna3Lost = some (some 0x40100002) := by decide +kernel

example : mcEft cdna3Lost 0x40100000 = .ok (.fast 0x40100002) := by decide +kernel

example : parts cdna3Lost = some (-22, 9 / 4, 0, 7 * pow2 (-24), 0) := by decide +kernel

/-- Any finite `D` gives the same word. -/
example : mcEft cdna3Lost 0 = .ok (.fast 0x40100002) ∧
    mcEft cdna3Lost 0xC0100000 = .ok (.fast 0x40100002) ∧
    mcEft cdna3Lost 0x7F7FFFFF = .ok (.exact 0x40100002) := by decide +kernel

/-! ## CDNA 3 FP16: the matrix core keeps part of a low part -/

def cdna3Kept : BlockInput cdna3F16 :=
  ⟨[0x3C00, 0x0E00] ++ List.replicate 6 0, [0x3C00, 0x1000] ++ List.replicate 6 0, 0⟩

example : blockBits cdna3Kept = .ok 0x3F800002 := by decide +kernel
example : parts cdna3Kept = some (-23, 1 + pow2 (-23), pow2 (-23), pow2 (-24), pow2 (-24)) := by
  decide +kernel
example : mcEft cdna3Kept 0x3F800002 = .ok (.fast 0x3F800002) := by decide +kernel

/-! ## CDNA 3 FP16: cancellation, where the final rounding is exact -/

def cdna3Cancel : BlockInput cdna3F16 :=
  ⟨[0x3C00, 0xBBFF, 0x0800] ++ List.replicate 5 0, [0x3C00, 0x3C00, 0x0C00] ++ List.replicate 5 0,
    0⟩

example : blockBits cdna3Cancel = .ok 0x3A000000 := by decide +kernel
example : parts cdna3Cancel = some (-24, pow2 (-11), 0, pow2 (-25), 0) := by decide +kernel
example : mcEft cdna3Cancel 0x3A000000 = .ok (.fast 0x3A000200) := by decide +kernel

/-! ## CDNA 3 FP16: the exact fallback is needed -/

def cdna3Fallback : BlockInput cdna3F16 :=
  ⟨[0x3C00, 0x0C00] ++ List.replicate 6 0, [0x3C00, 0x0C00] ++ List.replicate 6 0, 0x21800000⟩

example : blockBits cdna3Fallback = .ok 0x3F800000 := by decide +kernel
example : target cdna3Fallback = some (some 0x3F800001) := by decide +kernel
example : mcEft cdna3Fallback 0x3F800000 = .ok (.exact 0x3F800001) := by decide +kernel
example : (prepare cdna3Fallback).map (fun px =>
    ((eftSplit cdna3F16 px 1).guard 1, (eftSplit cdna3F16 px 1).fastPath 1)) =
      some (false, some 0x3F800000) := by decide +kernel

/-! ## CDNA 3 FP16: late `c` with `e_c > e_max` -/

def cdna3Late : BlockInput cdna3F16 :=
  ⟨[0x0C00, 0x0010] ++ List.replicate 6 0, [0x0C00, 0x0010] ++ List.replicate 6 0, 0x3F800000⟩

example : blockBits cdna3Late = .ok 0x3F800000 := by decide +kernel
example : (prepare cdna3Late).map (fun px =>
    (alignExp cdna3F16 px.p, cExp cdna3F16 px.c, hwGrid cdna3F16 px)) =
      some (some (-24), some 0, some (-32)) := by decide +kernel
example : parts cdna3Late = some (-23, 1, 0, pow2 (-24) + pow2 (-40), pow2 (-24)) := by
  decide +kernel
example : mcEft cdna3Late 0x3F800000 = .ok (.fast 0x3F800001) := by decide +kernel

/-! ## CDNA 3 FP8: odd and even groups -/

def cdna3FP8Odd : BlockInput (cdna3FP8 e5m2fnuz e5m2fnuz) :=
  ⟨[0xC0, 0, 0x92] ++ List.replicate 13 0, [0x40, 0, 0x10] ++ List.replicate 13 0, 0⟩

def cdna3FP8Even : BlockInput (cdna3FP8 e5m2fnuz e5m2fnuz) :=
  ⟨[0xC0, 0x92] ++ List.replicate 14 0, [0x40, 0x10] ++ List.replicate 14 0, 0⟩

example : blockBits cdna3FP8Odd = .ok 0xBF800000 := by decide +kernel
example : mcEft cdna3FP8Odd 0xBF800000 = .ok (.fast 0xBF800001) := by decide +kernel
example : parts cdna3FP8Odd = some (-23, -1, 0, -3 * pow2 (-25), -pow2 (-24)) := by decide +kernel
example : blockBits cdna3FP8Even = .ok 0xBF800001 := by decide +kernel
example : mcEft cdna3FP8Even 0xBF800001 = .ok (.fast 0xBF800001) := by decide +kernel

/-! ## CDNA 2 FP16: the order-dependence example -/

def cdna2Order : BlockInput cdna2F16 :=
  ⟨[0x3C00, 0x0E00, 0x0E00, 0], [0x3C00, 0x1000, 0x1000, 0], 0⟩

example : blockBits cdna2Order = .ok 0x3F800004 := by decide +kernel
example : target cdna2Order = some (some 0x3F800003) := by decide +kernel
example : mcEft cdna2Order 0x3F800004 = .ok (.fast 0x3F800003) := by decide +kernel

example : (match evalBlock cdna2Order with
    | .ok t => some (t.split.q, t.split.H, t.split.overlap (wordValue t.d), sumQ t.split.lows)
    | .error _ => none) = some (-23, 1 + pow2 (-22), pow2 (-22), pow2 (-23)) := by decide +kernel

example : (prepare cdna2Order).map (fun px =>
    (pairwiseRoundingErrors cdna2F16 px, flushLoss cdna2F16 px)) =
    some ([0, 0, 0, 0, pow2 (-24), 0, pow2 (-24)], 0) := by decide +kernel

/-! ## CDNA 1: the correction returns `D` -/

def cdna1Order : BlockInput cdna1F16 :=
  ⟨[0x3C00, 0x0E00, 0x0E00, 0], [0x3C00, 0x1000, 0x1000, 0], 0⟩

example : blockBits cdna1Order = .ok 0x3F800003 := by decide +kernel
example : mcEft cdna1Order 0x3F800003 = .ok (.fast 0x3F800003) := by decide +kernel

/-! ## Out of range and non-finite inputs -/

/-- CDNA 1 BF16 with exact sum `2^129`. -/
example : mcEft (P := cdna1BF16) ⟨[0x7F00, 0x7F00], [0x4000, 0x4000], 0⟩ 0 = .ok .outOfRange := by
  decide +kernel

example : mcEft cdna3Lost 0x7F800000 = .error .nonfiniteOutput := by decide +kernel
example : mcEft (P := cdna3F16) ⟨[0x7C00] ++ List.replicate 7 0, List.replicate 8 0, 0⟩ 0 =
    .error .nonfiniteInput := by decide +kernel
example : mcEft (P := cdna3F16) ⟨[0x3C00], [0x3C00], 0⟩ 0 = .error .wrongLength := by
  decide +kernel

end MatrixCoreTests.EFT
