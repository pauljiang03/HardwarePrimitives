import OzakiMC.Ozaki2IntJ
import Ozaki.BoundedChecked2

/-! # Ozaki-II on matrix-core blocks, every integer bounded

`Ozaki.ozaki2CRJC_binary64_eq` and `Ozaki.ozaki2CRJC_binary32_eq` with CDNA 3 fp16 blocks and
split-K as the matrix multiplier: every data integer of correctly rounded Ozaki-II within `264` bits
(FP64) or `161` bits (binary32), every exponent and counter within `24` or `17` bits. -/

open MatrixCore

namespace Ozaki.MC

theorem cdna3F16_fp64CRJ_widths {xs ys : List (ℤ × ℤ)} {cfgs : List (CRTBasis × ℕ)}
    (hlen : xs.length = ys.length) (hk : xs.length ≤ 2 ^ 20)
    (hx : ∀ a ∈ xs, FormatEntry 53 (-1022) 1023 a) (hy : ∀ a ∈ ys, FormatEntry 53 (-1022) 1023 a)
    (hcfgs : ∀ c ∈ cfgs, c.1 = fp64Basis ∧ c.2 ≤ 69)
    (hrange : ∀ c ∈ cfgs, 2 * xs.length * (2 ^ c.2 * 2 ^ c.2) < c.1.modulus) :
    Checked.ozaki2CRJC ⟨264, 24⟩ (mcSplitK cdna3F16 11) 53 (-1022) 1023 cfgs 11 175 xs ys =
      some (rne64 (dot (entryVals xs) (entryVals ys))) :=
  ozaki2CRJC_binary64_eq (mcSplitK_exactOn (cdna3F16_exactMultiplier (by decide)) (by decide) _)
    hlen hk hx hy hcfgs hrange

theorem cdna3F16_binary32CRJ_widths {xs ys : List (ℤ × ℤ)} {cfgs : List (CRTBasis × ℕ)}
    (hlen : xs.length = ys.length) (hk : xs.length ≤ 2 ^ 20)
    (hx : ∀ a ∈ xs, FormatEntry 24 (-126) 127 a) (hy : ∀ a ∈ ys, FormatEntry 24 (-126) 127 a)
    (hcfgs : ∀ c ∈ cfgs, c.1 = fp32Basis6 ∧ c.2 ≤ 34)
    (hrange : ∀ c ∈ cfgs, 2 * xs.length * (2 ^ c.2 * 2 ^ c.2) < c.1.modulus) :
    Checked.ozaki2CRJC ⟨161, 17⟩ (mcSplitK cdna3F16 11) 24 (-126) 127 cfgs 11 24 xs ys =
      some (rne32Q (dot (entryVals xs) (entryVals ys))) :=
  ozaki2CRJC_binary32_eq (mcSplitK_exactOn (cdna3F16_exactMultiplier (by decide)) (by decide) _)
    hlen hk hx hy hcfgs hrange

end Ozaki.MC
