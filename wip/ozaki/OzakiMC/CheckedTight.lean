import OzakiMC.Ozaki2Checked
import Ozaki.CheckedTight

/-! # Tighter widths on the Matrix Core model, with split-K guarded

Ozaki-I and Ozaki-II on CDNA 3 fp16 blocks through the guarded split-K matrix multiplier
(`Ozaki.Checked.chunkedC`): every integer outside the Matrix Core blocks' own arithmetic, split-K's
chunk sums included, within `263` bits and every exponent and counter within `17` bits for FP64
(`cdna3F16_fp64CRI_checked`, `cdna3F16_fp64CRJ_checked`), and `207` and `15` bits for binary32
Ozaki-I (`cdna3F16_binary32CRI_checked`). -/

open MatrixCore

namespace Ozaki.MC

open Ozaki.Checked

/-- The guarded split-K matrix multiplier on CDNA 3 fp16 blocks. -/
def cdna3SplitKC (B : Widths) : MatrixMultiplier := chunkedC B (chunkLen 11) (mcMultiplier cdna3F16)

theorem cdna3SplitKC_exactOn {B : Widths} (hR : 25 ≤ B.R) {D : ℕ} (hD : D < 2 ^ B.R) :
    (cdna3SplitKC B).ExactOn 11 D :=
  chunkedC_exactOn (cdna3F16_exactMultiplier (by decide)).exactOn (chunkLen_pos 11)
    (chunkLen_exactnessBound (by decide))
    (Nat.lt_of_lt_of_le (by decide) (Nat.pow_le_pow_right (by decide) hR)) hD

theorem dotAbsBound_lt_pow {k R : ℕ} (hk : k ≤ 2 ^ 20) (hR : 43 ≤ R) :
    k * (2 ^ 11 * 2 ^ 11) < 2 ^ R :=
  Nat.lt_of_lt_of_le (show k * (2 ^ 11 * 2 ^ 11) < 2 ^ 43 by omega)
    (Nat.pow_le_pow_right (by decide) hR)

/-- **FP64 by Ozaki-I on CDNA 3 fp16, every integer guarded, split-K included**: 263 and 17 bits. -/
theorem cdna3F16_fp64CRI_checked {xs ys : List (ℤ × ℤ)} (hlen : xs.length = ys.length)
    (hk : xs.length ≤ 2 ^ 20) (hx : ∀ a ∈ xs, FormatEntry 53 (-1022) 1023 a)
    (hy : ∀ a ∈ ys, FormatEntry 53 (-1022) 1023 a) {ss : List ℕ} (hss : ∀ s ∈ ss, s ≤ 8) :
    ozaki1CRIC ⟨263, 17⟩ (cdna3SplitKC ⟨263, 17⟩) 53 (-1022) 1023 11 96 ss 175 xs ys =
      some (rne64 (dot (entryVals xs) (entryVals ys))) :=
  ozaki1CRIC_binary64_tight
    (cdna3SplitKC_exactOn (show 25 ≤ 263 by decide) (dotAbsBound_lt_pow hk (show 43 ≤ 263 by decide)))
    hlen hk hx hy hss

/-- **Binary32 by Ozaki-I on CDNA 3 fp16, every integer guarded, split-K included**: 207 and 15
bits. -/
theorem cdna3F16_binary32CRI_checked {xs ys : List (ℤ × ℤ)} (hlen : xs.length = ys.length)
    (hk : xs.length ≤ 2 ^ 20) (hx : ∀ a ∈ xs, FormatEntry 24 (-126) 127 a)
    (hy : ∀ a ∈ ys, FormatEntry 24 (-126) 127 a) {ss : List ℕ} (hss : ∀ s ∈ ss, s ≤ 8) :
    ozaki1CRIC ⟨207, 15⟩ (cdna3SplitKC ⟨207, 15⟩) 24 (-126) 127 11 96 ss 24 xs ys =
      some (rne32Q (dot (entryVals xs) (entryVals ys))) :=
  ozaki1CRIC_binary32_tight
    (cdna3SplitKC_exactOn (show 25 ≤ 207 by decide) (dotAbsBound_lt_pow hk (show 43 ≤ 207 by decide)))
    hlen hk hx hy hss

/-- **FP64 by Ozaki-II on CDNA 3 fp16, every integer guarded, split-K included.** -/
theorem cdna3F16_fp64CRJ_checked {xs ys : List (ℤ × ℤ)} {cfgs : List (CRTBasis × ℕ)}
    (hlen : xs.length = ys.length) (hk : xs.length ≤ 2 ^ 20)
    (hx : ∀ a ∈ xs, FormatEntry 53 (-1022) 1023 a) (hy : ∀ a ∈ ys, FormatEntry 53 (-1022) 1023 a)
    (hcfgs : ∀ c ∈ cfgs, c.1 = fp64Basis ∧ c.2 ≤ 69)
    (hrange : ∀ c ∈ cfgs, 2 * xs.length * (2 ^ c.2 * 2 ^ c.2) < c.1.modulus) :
    ozaki2CRJC ⟨263, 17⟩ (cdna3SplitKC ⟨263, 17⟩) 53 (-1022) 1023 cfgs 11 175 xs ys =
      some (rne64 (dot (entryVals xs) (entryVals ys))) :=
  ozaki2CRJC_binary64_tight
    (cdna3SplitKC_exactOn (show 25 ≤ 263 by decide) (dotAbsBound_lt_pow hk (show 43 ≤ 263 by decide)))
    hlen hk hx hy hcfgs hrange

end Ozaki.MC
