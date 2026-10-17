import OzakiTC

/-! # The Z3 models' test matrices on the V100 Tensor Core

The two `4 × 4` cases of the Z3 models (`random.Random(2026)`, exponents in `[2^-1, 2^1]` and
`[2^-6, 2^6]`), with the outputs of the unmodified Z3 models recorded in
[`data/z3-reference.json`](../../data/z3-reference.json) by `scripts/z3_reference.py`. Every word is
binary32. The Lean pipelines on the V100 Tensor Core model return the same words: Ozaki-I with four
`11`-bit slices (ten slice products) and Ozaki-II with moduli `{4096, 4095, 4093, 4091}` and
`P = 22`. Each check is a kernel evaluation of the same definitions the theorems use. -/

open TensorCore Ozaki Ozaki.TC

namespace OzakiTCTests.Z3Matrices

/-- `A`, narrow case. -/
def A_narrow : List (List F32) :=
  [[0xBFC302B8, 0x3FE71660, 0x3EB851FF, 0x3FC4AB5A],
    [0x3E78CCA9, 0x3F911651, 0x3F2F4F48, 0x3F808679],
    [0xBD714660, 0x3DE9E3EF, 0xBE59DDB4, 0xBE4E36BC],
    [0xBC9F2463, 0xBF145D6F, 0xBE9BFF95, 0x3F9C3AC6]]

/-- `B`, narrow case. -/
def B_narrow : List (List F32) :=
  [[0x3C5E9E4D, 0x3E647777, 0x3DEB5141, 0xBE597EE1],
    [0x3FC0C14E, 0x3EDD9BFC, 0xBFF3555F, 0xBE864D9A],
    [0xBE1F4C6F, 0x3FC82D0E, 0xBACA7EC8, 0xBE98B12C],
    [0x3F4038D0, 0x3F5560DD, 0x3FB05F62, 0x3F5A3B3A]]

/-- The Z3 Ozaki-I model's `C`, narrow case. -/
def C1_narrow : List (List F32) :=
  [[0x4072ECA1, 0x40124038, 0xBFBECAD7, 0x3F86B6FE],
    [0x4016E3A9, 0x401CF8FC, 0xBF3E90AA, 0x3E9B092A],
    [0x3D595D7A, 0xBEEDB7E6, 0xBF004398, 0xBE00AE66],
    [0x3DBA1243, 0x3E9242A3, 0x403208D7, 0x3FA4CC56]]

/-- The Z3 Ozaki-II model's `C`, narrow case. -/
def C2_narrow : List (List F32) :=
  [[0x4072ECA0, 0x40124031, 0xBFBECAD6, 0x3F86B6FD],
    [0x4016E3A7, 0x401CF8F7, 0xBF3E90A2, 0x3E9B0929],
    [0x3D595D51, 0xBEEDB7E4, 0xBF004396, 0xBE00AE64],
    [0x3DBA1287, 0x3E9242A9, 0x403208D0, 0x3FA4CC50]]

/-- `A`, wide case. -/
def A_wide : List (List F32) :=
  [[0x3FD429CC, 0xBDF301E6, 0x3C081A63, 0x406CEA53],
    [0x3CC60DE2, 0x3EDE85DD, 0xBDF56DFF, 0x3CC4C3C7],
    [0x3F01B5EA, 0x41327C87, 0x405BE2CC, 0xBEFEF828],
    [0x3DADD3F9, 0x3FC53766, 0x3BF8FC6D, 0x3F1C1B1B]]

/-- `B`, wide case. -/
def B_wide : List (List F32) :=
  [[0xBD091442, 0x3C29E732, 0xC16F0C4D, 0x3FC39AF8],
    [0x3F9B6A81, 0xBD0F6CF9, 0xBF75A597, 0xC088939B],
    [0x42270037, 0xC006B2B0, 0x3E508533, 0xC1BBBE3D],
    [0xC1CDA1ED, 0x3FDDB703, 0xBCF6F4F7, 0x41EF3DB9]]

/-- The Z3 Ozaki-I model's `C`, wide case. -/
def C1_wide : List (List F32) :=
  [[0xC2BE0217, 0x40CD4F47, 0xC1C6151E, 0x42E3183F],
    [0xC0A3004A, 0x3E8EC63D, 0xBF4DAA00, 0x3FDB3860],
    [0x4329C520, 0xC107A9CD, 0xC18C7A45, 0xC30E5BCC],
    [0xC157D27A, 0x3F7CB7E2, 0xC030DB40, 0x4139C7A0]]

/-- The Z3 Ozaki-II model's `C`, wide case. -/
def C2_wide : List (List F32) :=
  [[0xC2BE0212, 0x40CD4F41, 0xC1C61516, 0x42E3183A],
    [0xC0A3003C, 0x3E8EC641, 0xBF4DA9E2, 0x3FDB3857],
    [0x4329C513, 0xC107A9BA, 0xC18C7A2A, 0xC30E5BC0],
    [0xC157D272, 0x3F7CB7F2, 0xC030DB15, 0x4139C7A2]]

example : (do
    let A ← decodeMatrix A_narrow; let B ← decodeMatrix B_narrow
    let C ← tcOzaki1Gemm v100F16F32 11 4 A B; encodeMatrix C) = some C1_narrow := by
  decide +kernel

example : (do
    let A ← decodeMatrix A_narrow; let B ← decodeMatrix B_narrow
    let C ← tcOzaki2Gemm v100F16F32 z3Basis 22 A B; encodeMatrix C) = some C2_narrow := by
  decide +kernel

example : (do
    let A ← decodeMatrix A_wide; let B ← decodeMatrix B_wide
    let C ← tcOzaki1Gemm v100F16F32 11 4 A B; encodeMatrix C) = some C1_wide := by
  decide +kernel

example : (do
    let A ← decodeMatrix A_wide; let B ← decodeMatrix B_wide
    let C ← tcOzaki2Gemm v100F16F32 z3Basis 22 A B; encodeMatrix C) = some C2_wide := by
  decide +kernel

/-! The slices computed with binary32 σ-trick operations, as the Z3 model computes them, are the
slices of the scheme library on every row of `A` and every column of `B` (`splitFrom32_eq`). -/

example : ((decodeMatrix A_narrow).map fun A => A.map (split32 11 4)) =
    ((decodeMatrix A_narrow).map fun A => A.map fun x => some (split 11 4 x)) := by decide +kernel

example : ((decodeMatrix B_narrow).map fun B => (transpose B).map (split32 11 4)) =
    ((decodeMatrix B_narrow).map fun B => (transpose B).map fun x => some (split 11 4 x)) := by
  decide +kernel

example : ((decodeMatrix A_wide).map fun A => A.map (split32 11 4)) =
    ((decodeMatrix A_wide).map fun A => A.map fun x => some (split 11 4 x)) := by decide +kernel

example : ((decodeMatrix B_wide).map fun B => (transpose B).map (split32 11 4)) =
    ((decodeMatrix B_wide).map fun B => (transpose B).map fun x => some (split 11 4 x)) := by
  decide +kernel

end OzakiTCTests.Z3Matrices
