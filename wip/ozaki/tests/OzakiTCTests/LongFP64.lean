import OzakiTCTests.Correct
import OzakiTC.LongDot

/-! # FP64 emulation and long dot products on the Tensor Core model

The binary64 cases of [`data/correct-reference.json`](../../data/correct-reference.json) (random
`4 × 8` by `8 × 4` binary64 products, exponents within `4` and `40` binades), against the words the
exact-fraction oracle computes. With `k = 8` and `11`-bit slices the matrix multiplier needs split-K
(chunks of four), so these checks exercise `tcSplitK` as well:

* `tcOzaki1CRD`: correctly rounded FP64 by Ozaki-I on V100 fp16 blocks, five then six slices, then
  the exact fallback on V100 blocks;
* `tcOzaki2CRD`: the same by Ozaki-II with twelve moduli at most `4096` (`P = 69` for `k = 8`);
* `tcOzaki1D`: FP64 emulation by Ozaki-I with binary64 recombination and six slices, within its
  proven bound of the exact product (checked here by exact rational arithmetic). -/

open TensorCore Ozaki Ozaki.TC OzakiTCTests.Correct

namespace OzakiTCTests.LongFP64

/-- Twelve pairwise coprime moduli at most `4096`. -/
def moduli12 : List ℕ := [4096, 4095, 4093, 4091, 4087, 4079, 4073, 4063, 4061, 4057, 4051, 4049]

def basis12 : CRTBasis := crtBasis moduli12

theorem basis12_valid : basis12.Valid := by decide +kernel

example : ozaki2Bits 8 basis12.modulus 200 = 69 := by decide +kernel

example : (do
    let A ← decode64 A_narrow64; let B ← decode64 B_narrow64
    let C ← A.mapM fun x => (transpose B).mapM fun y => tcOzaki1CRD v100F16F32 11 [5, 6] 175 x y
    encode64 C) = some C_narrow64 := by
  decide +kernel

example : (do
    let A ← decode64 A_wide64; let B ← decode64 B_wide64
    let C ← A.mapM fun x => (transpose B).mapM fun y => tcOzaki1CRD v100F16F32 11 [5, 6] 175 x y
    encode64 C) = some C_wide64 := by
  decide +kernel

example : (do
    let A ← decode64 A_narrow64; let B ← decode64 B_narrow64
    let C ← A.mapM fun x => (transpose B).mapM fun y =>
      tcOzaki2CRD v100F16F32 [(basis12, 69)] 11 175 x y
    encode64 C) = some C_narrow64 := by
  decide +kernel

/-- Plain FP64 emulation (binary64 recombination, six slices) on the wide case: every entry is
within `2^-50` relative to `Σ|xᵢyᵢ|` of the exact product. -/
example : (do
    let A ← decode64 A_wide64; let B ← decode64 B_wide64
    let ok ← A.mapM fun x => (transpose B).mapM fun y => do
      let v ← tcOzaki1D v100F16F32 11 6 x y
      pure (decide (Rat.abs (v - dot x y) ≤ 2 ^ (-50 : ℤ) *
        ((List.zipWith (· * ·) x y).map Rat.abs).sum))
    pure (ok.all fun r => r.all id)) = some true := by
  decide +kernel

/-! ## With a `96`-bit truncated sum

The same results when the rounding test runs on a `96`-bit truncated sum (`tcOzaki1CRDW`): the
accumulator of the rounding test needs about `115` bits here, not the exact sum. -/

example : (do
    let A ← decode64 A_narrow64; let B ← decode64 B_narrow64
    let C ← A.mapM fun x => (transpose B).mapM fun y => tcOzaki1CRDW v100F16F32 11 96 [5, 6] 175 x y
    encode64 C) = some C_narrow64 := by
  decide +kernel

example : (do
    let A ← decode64 A_wide64; let B ← decode64 B_wide64
    let C ← A.mapM fun x => (transpose B).mapM fun y => tcOzaki1CRDW v100F16F32 11 96 [5, 6] 175 x y
    encode64 C) = some C_wide64 := by
  decide +kernel

end OzakiTCTests.LongFP64
