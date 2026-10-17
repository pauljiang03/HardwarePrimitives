import OzakiTC.Correct

/-! # Correct rounding against an exact-arithmetic oracle

The correctly rounded schemes return, entry by entry, the words that `scripts/correct_reference.py`
computes with exact fractions and its own round to nearest even (recorded in
[`data/correct-reference.json`](../../data/correct-reference.json)). The Lean theorems
`tcOzaki1CR_eq`, `tcOzaki2CR_eq` and `adpCR_eq` say this holds for every input; these checks compare
the Lean definitions with an implementation that shares no code with them.

* binary32, V100: the Z3 models' two test cases, a product with heavy cancellation, and a product
  exactly halfway between two binary32 values; Ozaki-I tries three then four slices, Ozaki-II five
  then six moduli, and both fall back to the exact product;
* binary64, ADP on the INT8 matrix multiplier: two random `4 × 8` by `8 × 4` products of binary64
  values, trying `7`, `8`, then `9` slices of widths `54`, `62`, `70`.

The last group shows how often the fast path decides an entry: with four slices every Z3 entry is
decided without the exact product; with three, all but two. -/

open TensorCore Ozaki Ozaki.TC

namespace OzakiTCTests.Correct

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

/-- `narrow64`: left operand. -/
def A_narrow64 : List (List (BitVec 64)) :=
  [[0xBFB51C9B1E7EA419, 0xBFE99DD2E5121482, 0xBFED7A7A8C3D5F16, 0x3FC70EB996263AE6, 0xBFD1C59314AA4E71, 0xBFE02F0E731C9452, 0x3FD65B0035D14880, 0xBFDEDE7BFFB88309],
    [0xBFBBEF7EFFE976AB, 0x3FD8EB5116F44881, 0x3FDE060A24114258, 0x3FD5E6C9B5FB12E0, 0xBFE6616017371472, 0x3FE81A0B6CE9DA66, 0xBFE42367864FA3F3, 0xBFB7AAC3FB759E0F],
    [0xBFB21061C40D31B5, 0xBFBE306F85F184E0, 0x3FC785496DEDC86A, 0xBFBD98143A9AFA39, 0xBFEAC9F274F09AF5, 0xBFDFCBADF5A9CA5F, 0xBFDFF8B2AB74FE57, 0xBFE807C7A598D0DB],
    [0x3FC6EDD766E61127, 0x3FB025FF44DF8A13, 0xBFE98E6EE1CD7BE8, 0xBFD7D510ED4D19B8, 0x3FEB151542969A50, 0xBFED3801C446AB8C, 0xBFBA9F538ECE78B0, 0x3FB7528E511070A7]]

/-- `narrow64`: right operand. -/
def B_narrow64 : List (List (BitVec 64)) :=
  [[0x3FDC8FB4B76DC0C3, 0xBFE2EDC4F71BD135, 0xBFBF0ACD7AA95416, 0x3FD7F988E73C49EA],
    [0x3FEDB4C9BF5F85E2, 0x3FB0397AEA9E7AB5, 0xBFB8BED594A4D29C, 0xBFB3F72432E4034C],
    [0xBFD8BE40C07991D4, 0x3FC5B74CA2AA216A, 0xBFE9543CAA220078, 0x3FC22867F000E394],
    [0x3FDF551A219763C5, 0xBFC28FDBAB266981, 0xBFD96060EA3E7F73, 0xBFCCED8C63F1BBBC],
    [0xBFB6041F325ABDEC, 0x3FBE344F63AC4F14, 0xBFDA572158D62944, 0xBFB069A3F1F02F49],
    [0x3FDAECB953E81536, 0xBFE1F124E9F91484, 0x3FC9E5CF92559248, 0xBFE34FD0850567C2],
    [0xBFC9924E75750C2B, 0x3FE8C1F611CB4EA7, 0x3FCEBE48A5B0E526, 0x3FBEE5328B75D02A],
    [0x3FCA40EEC134A79B, 0x3FBE0B89ADBAFED0, 0x3FC37FE487A9EC13, 0x3FE2F9E0D828F123]]

/-- `narrow64`: correctly rounded product (oracle). -/
def C_narrow64 : List (List (BitVec 64)) :=
  [[0xBFE62EAAC9AAE01E, 0x3FD1ECD10FBB1D2F, 0x3FE88F4EB50E6366, 0xBFAF146337C13E4B],
    [0x3FE90BD5370C3CB1, 0xBFEC448D6FCBAA0F, 0xBFD0692C90E684F4, 0xBFE3EB949FF8D17D],
    [0xBFDD6DF3B479559F, 0xBFCB37DB02527A78, 0xBFB1EC4AF7314992, 0xBFBDFDEF9C86C097],
    [0xBFC3851B08B02E9A, 0x3FD6F317CBF74BF6, 0x3FCA99DB44DA22CA, 0x3FE248222522B33D]]

/-- `wide64`: left operand. -/
def A_wide64 : List (List (BitVec 64)) :=
  [[0x3F06A01988736737, 0x3F65814B2FEC4275, 0x405FFCE67F62DF26, 0x40C5366E2D4D6661, 0xC0C86F9F1EBF3DEB, 0x3F818357D0EF5C36, 0xC0817D6AF423F8BE, 0xBF68B8906872D96B],
    [0x3F5D8B6D5A1967D0, 0x40D92845AFE987C1, 0xBFCB74C99EEBBA4E, 0xBF8BB20E916B2B37, 0x40E44A239015B7C2, 0xBF14382AC8130637, 0xBEE1B2522BD8AF21, 0xBF6CD64AB8EC796E],
    [0x3FF81B241B37CA07, 0xBFD105CBD65F45B6, 0x3FB42C792950E9AE, 0x3FBDDD2869616452, 0x3F10EABF03F33851, 0xBF11F7E44F56D48F, 0x401FCF2C93944318, 0x4129B75174BF589B],
    [0x41150E986779082C, 0xBF26D167767187FD, 0x3FB8052BDC7E351E, 0x401D11ADF272C2EF, 0x3EC6FCE4B7158E9C, 0x3F24A205549ECC0A, 0xC1051A246AA8B0B5, 0x400F4F038ACACA45]]

/-- `wide64`: right operand. -/
def B_wide64 : List (List (BitVec 64)) :=
  [[0x3F2B8BFE0E5F8755, 0x3ED1E47C1F684C50, 0x3FE98D1E5AA26879, 0x4012055094002427],
    [0xC053D432608F02B1, 0xBF6200DAC6605AFB, 0xC0DB79ECA95C2C0B, 0xBFBE39F165988372],
    [0x3EC05FB03A6EF8D3, 0xBFB6AFA27A957971, 0x410F1B8E237F0DE0, 0xBED8D9032DE6C061],
    [0xC0BD2E38F6181E7C, 0xC0CA20CB5738F7C7, 0xBEB0E66C51478B93, 0xBEE7875A3E289120],
    [0xBF48234EADDC5401, 0xC04DF298E7F29366, 0xBF9F374B5C2472E5, 0x3F757FBE469855D2],
    [0xC08A3132759291D6, 0x410E5A34795C2B9B, 0x405A0C5B2885F868, 0xC01015C1E4CFED0E],
    [0xC0585F23D5C67EE3, 0x3F02C2DBA39D2086, 0x3FBBB2358BF6237B, 0xBEC19CADBD513018],
    [0x410D9452D98D4098, 0x404F49E70B6DBA44, 0xC0CF8993F6908F31, 0x40B28759A969BD91]]

/-- `wide64`: correctly rounded product (oracle). -/
def C_wide64 : List (List (BitVec 64)) :=
  [[0xC19354AEBB58F5BA, 0xC1A13B07CF9644EF, 0x417F189D4D207AFD, 0xC05408DFE120222F],
    [0xC13F3086135A8BD6, 0xC142FCCD65C5093D, 0xC1C59A4242260A9B, 0xC0A6307AC5367C08],
    [0x4247C5543BF1F7F2, 0x418924C97A6A900D, 0xC2095823489DCF67, 0x41EDC7C67F79E35D],
    [0x4170ECA1E029987F, 0xC0F7AAB29BC82A52, 0x410A8CA828C23160, 0x4137FFEDE8BFF513]]

/-- Decode binary64 words. -/
def decode64 (A : List (List (BitVec 64))) : Option (List (List ℚ)) :=
  A.mapM (·.mapM (binaryValue fp64))

/-- Encode binary64 values (exact for binary64 values). -/
def encode64 (C : List (List ℚ)) : Option (List (List (BitVec 64))) :=
  C.mapM (·.mapM (roundBinary fp64 .nearestEven))

/-- Five and six moduli: `P = 28` and `P = 34` for `k = 4`. -/
def basis5 : CRTBasis := crtBasis [4096, 4095, 4093, 4091, 4087]
def basis6 : CRTBasis := crtBasis [4096, 4095, 4093, 4091, 4087, 4079]

theorem basis5_valid : basis5.Valid := by decide +kernel
theorem basis6_valid : basis6.Valid := by decide +kernel

/-- The configurations for Ozaki-II. -/
def cfgs2 : List (CRTBasis × ℕ) := [(basis5, 28), (basis6, 34)]

theorem cfgs2_ok : ∀ c ∈ cfgs2, c.1.Valid ∧ (∀ m ∈ c.1.moduli, m ≤ 2 ^ (11 + 1)) ∧
    2 * 4 * (2 ^ c.2 * 2 ^ c.2) < c.1.modulus := by
  intro c hc
  simp only [cfgs2, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl
  · exact ⟨basis5_valid, by decide +kernel, by decide +kernel⟩
  · exact ⟨basis6_valid, by decide +kernel, by decide +kernel⟩

/-! ## Ozaki-I and Ozaki-II on V100, binary32 -/

example : (do
    let A ← decodeMatrix A_narrow; let B ← decodeMatrix B_narrow
    let C ← tcOzaki1CRGemm v100F16F32 11 [3, 4] A B; encodeMatrix C) = some C_narrow := by
  decide +kernel

example : (do
    let A ← decodeMatrix A_wide; let B ← decodeMatrix B_wide
    let C ← tcOzaki1CRGemm v100F16F32 11 [3, 4] A B; encodeMatrix C) = some C_wide := by
  decide +kernel

example : (do
    let A ← decodeMatrix A_narrow; let B ← decodeMatrix B_narrow
    let C ← tcOzaki2CRGemm v100F16F32 cfgs2 A B; encodeMatrix C) = some C_narrow := by
  decide +kernel

example : (do
    let A ← decodeMatrix A_wide; let B ← decodeMatrix B_wide
    let C ← tcOzaki2CRGemm v100F16F32 cfgs2 A B; encodeMatrix C) = some C_wide := by
  decide +kernel

example : (do
    let A ← decodeMatrix A_cancel; let B ← decodeMatrix B_cancel
    let C ← tcOzaki1CRGemm v100F16F32 11 [3, 4] A B; encodeMatrix C) = some C_cancel := by
  decide +kernel

example : (do
    let A ← decodeMatrix A_halfway; let B ← decodeMatrix B_halfway
    let C ← tcOzaki1CRGemm v100F16F32 11 [3, 4] A B; encodeMatrix C) = some C_halfway := by
  decide +kernel

/-! ## ADP on the INT8 matrix multiplier, binary64 -/

/-- The ADP configurations `(slices, width)`. -/
def cfgsADP : List (ℕ × ℕ) := [(7, 54), (8, 62), (9, 70)]

example : (do
    let A ← decode64 A_narrow64; let B ← decode64 B_narrow64
    let C ← adpCRGemm cfgsADP A B; encode64 C) = some C_narrow64 := by
  decide +kernel

example : (do
    let A ← decode64 A_wide64; let B ← decode64 B_wide64
    let C ← adpCRGemm cfgsADP A B; encode64 C) = some C_wide64 := by
  decide +kernel

/-! ## How often the fast path decides an entry -/

/-- Whether the rounding test succeeds on the enclosure from `s` slices. -/
def succeeds (s : ℕ) (x y : List ℚ) : Bool :=
  ((ozaki1Enclosure (tcMultiplier v100F16F32) 11 s x y).bind fun p =>
    roundEnclosure round32Value p.1 p.2).isSome

/-- On how many entries of `AB` the rounding test succeeds with the enclosure from `s` slices. -/
def successCount (s : ℕ) (A B : List (List F32)) : Option ℕ := do
  let A ← decodeMatrix A; let B ← decodeMatrix B
  pure ((A.flatMap fun x => (transpose B).map fun y => succeeds s x y).count true)

example : successCount 4 A_narrow B_narrow = some 16 ∧ successCount 4 A_wide B_wide = some 16 := by
  decide +kernel

example : successCount 3 A_narrow B_narrow = some 14 ∧ successCount 3 A_wide B_wide = some 16 := by
  decide +kernel

/-! ## The exact fallback on Tensor Core blocks

`tcOzaki1CRE` takes its exact fallback on V100 blocks too (all `s²` slice products at the smallest
slice count that leaves nothing over). With no slice counts to try, every entry takes the exact
fallback. -/

example : (do
    let A ← decodeMatrix A_narrow; let B ← decodeMatrix B_narrow
    let C ← A.mapM fun x => (transpose B).mapM fun y => tcOzaki1CRE v100F16F32 11 [] 24 x y
    encodeMatrix C) = some C_narrow := by
  decide +kernel

example : (do
    let A ← decodeMatrix A_cancel; let B ← decodeMatrix B_cancel
    let C ← A.mapM fun x => (transpose B).mapM fun y => tcOzaki1CRE v100F16F32 11 [3, 4] 24 x y
    encodeMatrix C) = some C_cancel := by
  decide +kernel

example : (do
    let A ← decodeMatrix A_halfway; let B ← decodeMatrix B_halfway
    let C ← A.mapM fun x => (transpose B).mapM fun y => tcOzaki1CRE v100F16F32 11 [3, 4] 24 x y
    encodeMatrix C) = some C_halfway := by
  decide +kernel

/-! ## How often Ozaki-II's and ADP's rounding tests decide an entry

The correctly rounded theorems hold whatever the tests do, because the last resort is exact. These
counts show how often the matrix multiplier's enclosure decides an entry by itself. Ozaki-II with
the Z3 models' four moduli (`P = 22`) decides none (its truncation error exceeds half a binary32
ulp), five moduli decide 12 and 9 of 16, six decide all. ADP decides every entry at the
configuration its own ESC rule picks for these inputs (`8` slices of width `56` for `narrow64`, `11`
of width `81` for `wide64`), and fewer with fewer slices. -/

/-- Whether the rounding test succeeds on the Ozaki-II enclosure of one configuration. -/
def succeeds2 (B : CRTBasis) (P : ℕ) (x y : List ℚ) : Bool :=
  ((ozaki2Enclosure (tcMultiplier v100F16F32) B P x y).bind fun p =>
    roundEnclosure round32Value p.1 p.2).isSome

def successCount2 (B : CRTBasis) (P : ℕ) (A Bm : List (List F32)) : Option ℕ := do
  let A ← decodeMatrix A; let Bm ← decodeMatrix Bm
  pure ((A.flatMap fun x => (transpose Bm).map fun y => succeeds2 B P x y).count true)

example : successCount2 z3Basis 22 A_narrow B_narrow = some 0 ∧
    successCount2 z3Basis 22 A_wide B_wide = some 0 := by decide +kernel
example : successCount2 basis5 28 A_narrow B_narrow = some 12 ∧
    successCount2 basis5 28 A_wide B_wide = some 9 := by decide +kernel
example : successCount2 basis6 34 A_narrow B_narrow = some 16 ∧
    successCount2 basis6 34 A_wide B_wide = some 16 := by decide +kernel

/-- Whether the rounding test succeeds on the ADP enclosure of `s` slices of width `W`. -/
def succeedsADP (s W : ℕ) (x y : List ℚ) : Bool :=
  (roundEnclosure fp64Round (adpEnclosure s W x y).1 (adpEnclosure s W x y).2).isSome

def successCountADP (s W : ℕ) (A Bm : List (List (BitVec 64))) : Option ℕ := do
  let A ← decode64 A; let Bm ← decode64 Bm
  pure ((A.flatMap fun x => (transpose Bm).map fun y => succeedsADP s W x y).count true)

example : successCountADP 8 56 A_narrow64 B_narrow64 = some 16 := by decide +kernel
example : successCountADP 11 81 A_wide64 B_wide64 = some 16 := by decide +kernel
example : successCountADP 8 62 A_wide64 B_wide64 = some 5 ∧
    successCountADP 9 70 A_wide64 B_wide64 = some 11 := by decide +kernel

end OzakiTCTests.Correct
