import MatrixCore

/-! # Pinned and anchored accumulation on the AMD models: kernel-checked cases

CDNA 1 and CDNA 2 round to nearest inside a block, so the position of the rounding moves with the
running value, and neither a pin pair nor an anchor makes the result independent of the order of
the blocks. CDNA 3 adds `c` after aligning the products among themselves, so an anchor in `c` does
not fix the alignment either; a pin pair among the products does (`MMAlgebra.MC.runBlocks_pinned`).
Each theorem evaluates the same blocks in different orders. -/

open MatrixCore

namespace MMAlgebra.MC.PinnedCases


/-- The last output word of a chain of blocks from `c`. -/
def run (P : Model) (c : F32) (bs : List (List P.a.Word × List P.b.Word)) : Option F32 :=
  match runBlocks P c bs with
  | .ok ts => some (lastOutput c ts)
  | .error _ => none

def cdna1_anchored_0 : List cdna1F16.a.Word × List cdna1F16.b.Word :=
  ([0x3f0d, 0xbfa2, 0x3c1e, 0x3b2e],
   [0x2fa1, 0xbea0, 0x3de1, 0x280a])
def cdna1_anchored_1 : List cdna1F16.a.Word × List cdna1F16.b.Word :=
  ([0x3126, 0x364d, 0xbcb6, 0x3d9c],
   [0xbe26, 0x4000, 0x3711, 0x38cd])
/-- **Anchoring fails on CDNA 1.** From the anchor `c = 1536` (`1.5 · 2^10`), the two orders of the same
two blocks give `0x44c0b8bf` and the next binary32 value up: CDNA 1 rounds to nearest, so where
the rounding falls moves with the running value. -/
theorem cdna1_anchored_order_dependent :
    run cdna1F16 0x44c00000 [cdna1_anchored_0, cdna1_anchored_1] = some 0x44c0b8bf ∧
    run cdna1F16 0x44c00000 [cdna1_anchored_1, cdna1_anchored_0] = some 0x44c0b8c0 := by
  decide +kernel

def cdna1_pinned_0 : List cdna1F16.a.Word × List cdna1F16.b.Word :=
  ([0x3dad, 0x2a25, 0x5000, 0xd000],
   [0xb402, 0x3951, 0x5000, 0x5000])
def cdna1_pinned_1 : List cdna1F16.a.Word × List cdna1F16.b.Word :=
  ([0xb61d, 0x3f3f, 0x5000, 0xd000],
   [0xbd06, 0x3c07, 0x5000, 0x5000])
/-- **Pinning fails on CDNA 1.** Two blocks, each with the pin pair `±2^10`, in two orders. -/
theorem cdna1_pinned_order_dependent :
    run cdna1F16 0 [cdna1_pinned_0, cdna1_pinned_1] = some 0x3ffd77c6 ∧
    run cdna1F16 0 [cdna1_pinned_1, cdna1_pinned_0] = some 0x3ffd77c7 := by
  decide +kernel

def cdna2_anchored_0 : List cdna2F16.a.Word × List cdna2F16.b.Word :=
  ([0xbdac, 0x3c24, 0x3f09, 0xbd2e],
   [0x27fc, 0x32bf, 0x3938, 0xbf7b])
def cdna2_anchored_1 : List cdna2F16.a.Word × List cdna2F16.b.Word :=
  ([0xbe59, 0xbc86, 0x3c2a, 0x3e31],
   [0x3ff3, 0xbe97, 0xbff4, 0xa882])
/-- **Anchoring fails on CDNA 2**, whose pairwise sums round to nearest. -/
theorem cdna2_anchored_order_dependent :
    run cdna2F16 0x44c00000 [cdna2_anchored_0, cdna2_anchored_1] = some 0x44c00a80 ∧
    run cdna2F16 0x44c00000 [cdna2_anchored_1, cdna2_anchored_0] = some 0x44c00a7f := by
  decide +kernel

def cdna2_pinned_0 : List cdna2F16.a.Word × List cdna2F16.b.Word :=
  ([0xb0bc, 0xbdc9, 0x5000, 0xd000],
   [0xb80e, 0x3ddd, 0x5000, 0x5000])
def cdna2_pinned_1 : List cdna2F16.a.Word × List cdna2F16.b.Word :=
  ([0xbfe6, 0x3e5f, 0x5000, 0xd000],
   [0x21b3, 0xbeb5, 0x5000, 0x5000])
def cdna2_pinned_2 : List cdna2F16.a.Word × List cdna2F16.b.Word :=
  ([0x32f2, 0xbf58, 0x5000, 0xd000],
   [0x3777, 0xb7be, 0x5000, 0x5000])
/-- **Pinning fails on CDNA 2.** Three blocks, each with the pin pair `±2^10`, in two orders. -/
theorem cdna2_pinned_order_dependent :
    run cdna2F16 0 [cdna2_pinned_0, cdna2_pinned_1, cdna2_pinned_2] = some 0xc06fdfec ∧
    run cdna2F16 0 [cdna2_pinned_1, cdna2_pinned_2, cdna2_pinned_0] = some 0xc06fdfed := by
  decide +kernel

def cdna3_anchored_0 : List cdna3F16.a.Word × List cdna3F16.b.Word :=
  ([0xba60, 0x3f27, 0xbe6d, 0x34e8, 0x2067, 0x3dc7, 0xbe9f, 0x3463],
   [0xb176, 0x2b9e, 0xbf7e, 0x3af9, 0x3867, 0xbfe7, 0xbba1, 0xbcbd])
def cdna3_anchored_1 : List cdna3F16.a.Word × List cdna3F16.b.Word :=
  ([0xb9d1, 0xbd2b, 0xbedc, 0xbd91, 0xbf80, 0xbf79, 0x3e5b, 0xb99f],
   [0x3f42, 0x3a3e, 0xb08d, 0xbecd, 0xbc00, 0x3efb, 0x3d35, 0x3b1f])
/-- **Anchoring fails on CDNA 3**: `c` is added late, after the products are aligned among
themselves, so it does not fix the alignment. -/
theorem cdna3_anchored_order_dependent :
    run cdna3F16 0x44c00000 [cdna3_anchored_0, cdna3_anchored_1] = some 0x44c04872 ∧
    run cdna3F16 0x44c00000 [cdna3_anchored_1, cdna3_anchored_0] = some 0x44c04873 := by
  decide +kernel

def c3p_0 : List cdna3F16.a.Word × List cdna3F16.b.Word :=
  ([0xbd5c, 0x3852, 0xbc8b, 0x3ced, 0x2535, 0xbff3, 0x5000, 0xD000],
   [0x3a13, 0xad5a, 0x3caf, 0x2a61, 0xbc39, 0xb820, 0x5000, 0x5000])
def c3p_1 : List cdna3F16.a.Word × List cdna3F16.b.Word :=
  ([0x3577, 0x3cb3, 0xbc47, 0x3ff6, 0x3e00, 0xbf74, 0x5000, 0xD000],
   [0xbee4, 0xbc49, 0xbf53, 0x3ba3, 0x376b, 0xb979, 0x5000, 0x5000])
def c3p_2 : List cdna3F16.a.Word × List cdna3F16.b.Word :=
  ([0xa103, 0x3f3b, 0xbd86, 0xbe01, 0xb200, 0xb907, 0x5000, 0xD000],
   [0xbe26, 0xb836, 0x3d15, 0x3ed9, 0x32a8, 0xabd5, 0x5000, 0x5000])
def c3p_3 : List cdna3F16.a.Word × List cdna3F16.b.Word :=
  ([0xbd02, 0x3ddb, 0x3c7c, 0x3f80, 0x3c14, 0x352b, 0x5000, 0xD000],
   [0xbf68, 0xbc3e, 0xbcaa, 0x3e4e, 0x3c34, 0x3b5a, 0x5000, 0x5000])
/-- **Pinning works on CDNA 3.** Four blocks, each with the pin pair `±2^10`, in three orders, give
the same word `0x3f965000`. -/
theorem cdna3_pinned_orders_agree :
    run cdna3F16 0 [c3p_0, c3p_1, c3p_2, c3p_3] = some 0x3f965000 ∧
    run cdna3F16 0 [c3p_3, c3p_2, c3p_1, c3p_0] = some 0x3f965000 ∧
    run cdna3F16 0 [c3p_2, c3p_0, c3p_3, c3p_1] = some 0x3f965000 := by
  decide +kernel

end MMAlgebra.MC.PinnedCases
