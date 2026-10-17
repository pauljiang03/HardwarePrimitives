import OzakiTCTests.Z3Matrices

/-! # The Z3 models' test matrices on every Tensor Core variant

`Z3Matrices` checks the V100 variant. Here the same `4 × 4` cases run on the other seven variants of
`TensorCore`:

* the A100 and H100 fp16 variants and the three tf32 variants hold `11`-bit slices, so both schemes
  in the Z3 configuration return exactly the Z3 models' binary32 words. With `k = 4` every block
  carries at most four nonzero products, within the exactness bound even where a block FMA takes
  eight or sixteen;
* the bf16 variants cannot hold `11`-bit slices (bf16 has eight significant bits), so the Z3
  configuration returns `none`. With `8`-bit slices, and for Ozaki-II moduli at most `2^9`, they
  return the same result as an exact matrix multiplier.

Each check is a kernel evaluation of the same definitions the theorems use. -/

open TensorCore Ozaki Ozaki.TC OzakiTCTests.Z3Matrices

namespace OzakiTCTests.AllVariants

/-- Ozaki-I on a variant, from binary32 words to binary32 words. -/
def runI (p : Model) (b s : ℕ) (A B : List (List F32)) : Option (List (List F32)) := do
  let A ← decodeMatrix A; let B ← decodeMatrix B
  let C ← tcOzaki1Gemm p b s A B; encodeMatrix C

/-- Ozaki-II on a variant, from binary32 words to binary32 words. -/
def runII (p : Model) (Bs : CRTBasis) (P : ℕ) (A B : List (List F32)) :
    Option (List (List F32)) := do
  let A ← decodeMatrix A; let B ← decodeMatrix B
  let C ← tcOzaki2Gemm p Bs P A B; encodeMatrix C

/-- Ozaki-I with an exact matrix multiplier, for comparison. -/
def runIExact (b s : ℕ) (A B : List (List F32)) : Option (List (List F32)) := do
  let A ← decodeMatrix A; let B ← decodeMatrix B
  let C ← ozaki1Gemm exactMultiplier fp32Add b s A B; encodeMatrix C

/-- Ozaki-II with an exact matrix multiplier, for comparison. -/
def runIIExact (Bs : CRTBasis) (P : ℕ) (A B : List (List F32)) : Option (List (List F32)) := do
  let A ← decodeMatrix A; let B ← decodeMatrix B
  let C ← ozaki2Gemm exactMultiplier round32Value Bs P A B; encodeMatrix C

/-! ## A100 fp16 (`K = 8`, `F = 24`) -/

example : runI ampereF16F32 11 4 A_narrow B_narrow = some C1_narrow := by decide +kernel
example : runII ampereF16F32 z3Basis 22 A_narrow B_narrow = some C2_narrow := by decide +kernel
example : runI ampereF16F32 11 4 A_wide B_wide = some C1_wide := by decide +kernel
example : runII ampereF16F32 z3Basis 22 A_wide B_wide = some C2_wide := by decide +kernel

/-! ## H100 fp16 (`K = 16`, `F = 25`) -/

example : runI hopperF16F32 11 4 A_narrow B_narrow = some C1_narrow := by decide +kernel
example : runII hopperF16F32 z3Basis 22 A_narrow B_narrow = some C2_narrow := by decide +kernel
example : runI hopperF16F32 11 4 A_wide B_wide = some C1_wide := by decide +kernel
example : runII hopperF16F32 z3Basis 22 A_wide B_wide = some C2_wide := by decide +kernel

/-! ## A100 tf32 (`K = 4`, `F = 24`) -/

example : runI a100TF32F32 11 4 A_narrow B_narrow = some C1_narrow := by decide +kernel
example : runII a100TF32F32 z3Basis 22 A_narrow B_narrow = some C2_narrow := by decide +kernel
example : runI a100TF32F32 11 4 A_wide B_wide = some C1_wide := by decide +kernel
example : runII a100TF32F32 z3Basis 22 A_wide B_wide = some C2_wide := by decide +kernel

/-! ## H100 tf32, `wmma` (`K = 4`, `F = 25`) -/

example : runI hopperTF32WmmaF32 11 4 A_narrow B_narrow = some C1_narrow := by decide +kernel
example : runII hopperTF32WmmaF32 z3Basis 22 A_narrow B_narrow = some C2_narrow := by
  decide +kernel
example : runI hopperTF32WmmaF32 11 4 A_wide B_wide = some C1_wide := by decide +kernel
example : runII hopperTF32WmmaF32 z3Basis 22 A_wide B_wide = some C2_wide := by decide +kernel

/-! ## H100 tf32, `mma` (`K = 8`, `F = 25`) -/

example : runI hopperTF32MmaF32 11 4 A_narrow B_narrow = some C1_narrow := by decide +kernel
example : runII hopperTF32MmaF32 z3Basis 22 A_narrow B_narrow = some C2_narrow := by
  decide +kernel
example : runI hopperTF32MmaF32 11 4 A_wide B_wide = some C1_wide := by decide +kernel
example : runII hopperTF32MmaF32 z3Basis 22 A_wide B_wide = some C2_wide := by decide +kernel

/-! ## The bf16 variants

The Z3 configuration needs `11`-bit slices and residues up to `2048`, which bf16 cannot hold. With
`8`-bit slices and the moduli `{512, 511, 509, 503}` (`M ≈ 2^35.9`, so `P = 16`), every call
to the matrix multiplier is exact and the result is that of an exact matrix multiplier. -/

/-- Four pairwise coprime moduli at most `2^9`: residues fit bf16. -/
def bf16Basis : CRTBasis := crtBasis [512, 511, 509, 503]

example : bf16Basis.Valid := by decide +kernel
example : ozaki2Bits 4 bf16Basis.modulus 64 = 16 := by decide +kernel

example : runI a100BF16F32 11 4 A_narrow B_narrow = none := by decide +kernel
example : runII a100BF16F32 z3Basis 22 A_narrow B_narrow = none := by decide +kernel
example : runI hopperBF16F32 11 4 A_wide B_wide = none := by decide +kernel
example : runII hopperBF16F32 z3Basis 22 A_wide B_wide = none := by decide +kernel

example : runI a100BF16F32 8 4 A_narrow B_narrow = runIExact 8 4 A_narrow B_narrow ∧
    (runIExact 8 4 A_narrow B_narrow).isSome := by decide +kernel
example : runII a100BF16F32 bf16Basis 16 A_wide B_wide = runIIExact bf16Basis 16 A_wide B_wide ∧
    (runIIExact bf16Basis 16 A_wide B_wide).isSome := by decide +kernel
example : runI hopperBF16F32 8 4 A_wide B_wide = runIExact 8 4 A_wide B_wide ∧
    (runIExact 8 4 A_wide B_wide).isSome := by decide +kernel
example : runII hopperBF16F32 bf16Basis 16 A_narrow B_narrow =
    runIIExact bf16Basis 16 A_narrow B_narrow ∧
    (runIIExact bf16Basis 16 A_narrow B_narrow).isSome := by decide +kernel

end OzakiTCTests.AllVariants
