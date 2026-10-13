import OzakiMC.Correct

/-! # Correct rounding on AMD matrix cores against an exact-arithmetic oracle

The correctly rounded schemes on the matrix-core model return the words that
`scripts/correct_reference.py` computes with exact fractions (recorded in
[`data/correct-reference.json`](../../data/correct-reference.json)), as on the
Tensor Core model: binary32 is binary32, whatever the matrix multiplier does inside. Ozaki-I tries
three then four `11`-bit slices; Ozaki-II five then six moduli; both fall back to the exact product.
Checked on the binary32 SFMA, CDNA 1, CDNA 2 and CDNA 3 fp16, and CDNA 3 XF32. -/

open MatrixCore Ozaki Ozaki.MC

namespace OzakiMCTests.Correct

/-- `narrow`: left operand. -/
def A_narrow : List (List F32) :=
  [[0xBFC302B8, 0x3FE71660, 0x3EB851FF, 0x3FC4AB5A],
    [0x3E78CCA9, 0x3F911651, 0x3F2F4F48, 0x3F808679],
    [0xBD714660, 0x3DE9E3EF, 0xBE59DDB4, 0xBE4E36BC],
    [0xBC9F2463, 0xBF145D6F, 0xBE9BFF95, 0x3F9C3AC6]]

/-- `narrow`: right operand. -/
def B_narrow : List (List F32) :=
  [[0x3C5E9E4D, 0x3E647777, 0x3DEB5141, 0xBE597EE1],
    [0x3FC0C14E, 0x3EDD9BFC, 0xBFF3555F, 0xBE864D9A],
    [0xBE1F4C6F, 0x3FC82D0E, 0xBACA7EC8, 0xBE98B12C],
    [0x3F4038D0, 0x3F5560DD, 0x3FB05F62, 0x3F5A3B3A]]

/-- `narrow`: correctly rounded product (oracle). -/
def C_narrow : List (List F32) :=
  [[0x4072ECA1, 0x40124038, 0xBFBECAD7, 0x3F86B6FE],
    [0x4016E3A9, 0x401CF8FC, 0xBF3E90AA, 0x3E9B092A],
    [0x3D595D7A, 0xBEEDB7E6, 0xBF004398, 0xBE00AE66],
    [0x3DBA1243, 0x3E9242A3, 0x403208D7, 0x3FA4CC56]]

/-- `wide`: left operand. -/
def A_wide : List (List F32) :=
  [[0x3FD429CC, 0xBDF301E6, 0x3C081A63, 0x406CEA53],
    [0x3CC60DE2, 0x3EDE85DD, 0xBDF56DFF, 0x3CC4C3C7],
    [0x3F01B5EA, 0x41327C87, 0x405BE2CC, 0xBEFEF828],
    [0x3DADD3F9, 0x3FC53766, 0x3BF8FC6D, 0x3F1C1B1B]]

/-- `wide`: right operand. -/
def B_wide : List (List F32) :=
  [[0xBD091442, 0x3C29E732, 0xC16F0C4D, 0x3FC39AF8],
    [0x3F9B6A81, 0xBD0F6CF9, 0xBF75A597, 0xC088939B],
    [0x42270037, 0xC006B2B0, 0x3E508533, 0xC1BBBE3D],
    [0xC1CDA1ED, 0x3FDDB703, 0xBCF6F4F7, 0x41EF3DB9]]

/-- `wide`: correctly rounded product (oracle). -/
def C_wide : List (List F32) :=
  [[0xC2BE0217, 0x40CD4F47, 0xC1C6151E, 0x42E3183F],
    [0xC0A3004A, 0x3E8EC63D, 0xBF4DAA00, 0x3FDB3860],
    [0x4329C520, 0xC107A9CD, 0xC18C7A45, 0xC30E5BCC],
    [0xC157D27A, 0x3F7CB7E2, 0xC030DB40, 0x4139C7A0]]

/-- `cancel`: left operand. -/
def A_cancel : List (List F32) :=
  [[0x3F800000, 0xBF800000, 0x2B800000, 0x00000000]]

/-- `cancel`: right operand. -/
def B_cancel : List (List F32) :=
  [[0x3F800000],
    [0x3F800000],
    [0x3F800000],
    [0x00000000]]

/-- `cancel`: correctly rounded product (oracle). -/
def C_cancel : List (List F32) :=
  [[0x2B800000]]

/-- `halfway`: left operand. -/
def A_halfway : List (List F32) :=
  [[0x3F800000, 0x33800000, 0x00000000, 0x00000000]]

/-- `halfway`: right operand. -/
def B_halfway : List (List F32) :=
  [[0x3F800000],
    [0x3F800000],
    [0x00000000],
    [0x00000000]]

/-- `halfway`: correctly rounded product (oracle). -/
def C_halfway : List (List F32) :=
  [[0x3F800000]]

def basis5 : CRTBasis := crtBasis [4096, 4095, 4093, 4091, 4087]
def basis6 : CRTBasis := crtBasis [4096, 4095, 4093, 4091, 4087, 4079]

/-- The configurations for Ozaki-II: `P = 28` and `P = 34` for `k = 4`. -/
def cfgs2 : List (CRTBasis × ℕ) := [(basis5, 28), (basis6, 34)]

/-- Ozaki-I and Ozaki-II, correctly rounded, on one variant: both cases equal the oracle. -/
def agrees (P : Model) : Bool :=
  [(A_narrow, B_narrow, C_narrow), (A_wide, B_wide, C_wide), (A_cancel, B_cancel, C_cancel),
    (A_halfway, B_halfway, C_halfway)].all fun (A, B, C) =>
    (do let A ← decodeMatrix A; let B ← decodeMatrix B
        let C1 ← mcOzaki1CRGemm P 11 [3, 4] A B; encodeMatrix C1) == some C &&
    (do let A ← decodeMatrix A; let B ← decodeMatrix B
        let C2 ← mcOzaki2CRGemm P cfgs2 A B; encodeMatrix C2) == some C

example : agrees sfmaF32 = true := by decide +kernel
example : agrees cdna1F16 = true := by decide +kernel
example : agrees cdna2F16 = true := by decide +kernel
example : agrees cdna3F16 = true := by decide +kernel
example : agrees cdna3XF32 = true := by decide +kernel

/-- The exact fallback alone on CDNA 3 fp16 (no slice counts to try), and the hard cases with it. -/
example : [(A_narrow, B_narrow, C_narrow), (A_cancel, B_cancel, C_cancel),
    (A_halfway, B_halfway, C_halfway)].all (fun (A, B, C) =>
    (do let A ← decodeMatrix A; let B ← decodeMatrix B
        let C1 ← A.mapM fun x => (transpose B).mapM fun y => mcOzaki1CRE cdna3F16 11 [] 24 x y
        encodeMatrix C1) == some C) = true := by
  decide +kernel

end OzakiMCTests.Correct
