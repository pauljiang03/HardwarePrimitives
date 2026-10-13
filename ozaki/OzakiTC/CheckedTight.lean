import OzakiTC.ADPCheckedSigned
import Ozaki.CheckedTight

/-! # Tighter widths on the Tensor Core model, with split-K guarded

* ADP-style slicing in integers, now on the guarded INT8 engines (`OzakiTC.Int8Checked`): every
  data integer within `259` bits and every exponent and counter within `17` bits, signed and
  unsigned (`adpCRJC_binary64_tight`, `adpCRJSC_binary64_tight`; earlier `264`/`25`).
* Ozaki-I and Ozaki-II on V100 fp16 blocks through the guarded split-K engine
  (`Ozaki.Checked.chunkedC`): every integer outside the Tensor Core blocks' own arithmetic,
  split-K's chunk sums included, within `263` bits and `17` bits for FP64
  (`v100_fp64CRI_checked`, `v100_fp64CRJ_checked`, `v100_fp64CRIS_checked`). -/

open TensorCore

namespace Ozaki.TC

open Ozaki.Checked

/-- **ADP-style slicing, FP64: 259 bits and 17 bits**, on the guarded INT8 engines. -/
theorem adpCRJC_binary64_tight {cfgs : List (ℕ × ℕ)} {xs ys : List (ℤ × ℤ)}
    (hlen : xs.length = ys.length) (hk : xs.length ≤ 2 ^ 20)
    (hx : ∀ a ∈ xs, FormatEntry 53 (-1022) 1023 a) (hy : ∀ a ∈ ys, FormatEntry 53 (-1022) 1023 a)
    (hcfgs : ∀ c ∈ cfgs, 0 < c.1 ∧ c.1 ≤ 11 ∧ c.2 ≤ 81 ∧ ADP.remapFits c.2 c.1 = true) :
    adpCRJC ⟨259, 17⟩ cfgs 300 xs ys = some (rne64 (dot (entryVals xs) (entryVals ys))) := by
  have hE : ((-1022 : ℤ) - ((53 : ℕ) - 1 : ℤ)).natAbs ≤ 1074 ∧
      ((1023 : ℤ) - ((53 : ℕ) - 1 : ℤ)).natAbs ≤ 1074 := by decide
  have hbk := bitlen_length_le hk
  have hbud : bitlen (xs.length * (2 ^ 6 * 2 ^ 6)) ≤ 33 := bitlen_le_iff.mpr (by omega)
  have hW : exactW 53 300 = 74 := by decide
  have hb2 : bitlen (300 * 300 + 2) = 17 := by decide
  have := natAbs_m1022; have := natAbs_1023
  rw [adpCRJC_eq hlen (entriesIn_of_format hE hx) (entriesIn_of_format hE hy) (fun c hc => by
      obtain ⟨h0, h1, h2, h3⟩ := hcfgs c hc
      have := bitlen_le_four h1
      refine ⟨h0, h3, ?_, ?_⟩
      · unfold adpR; simp only; omega
      · unfold adpX; simp only; omega)
    (by unfold exactR; rw [hW, hb2]; simp only; omega) (by decide)
    (by unfold exactX; rw [hW]; simp only; omega),
    adpCRJ_eq (fun c hc => ⟨(hcfgs c hc).1, (hcfgs c hc).2.2.2⟩) (by decide)
      (fun v hv => by obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hv; exact (hx a ha).formatValue)
      (fun v hv => by obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hv; exact (hy a ha).formatValue) hlen]

/-- **Signed ADP-style slicing, FP64: 259 bits and 17 bits.** -/
theorem adpCRJSC_binary64_tight {cfgs : List (ℕ × ℕ)} {xs ys : List SEntry}
    (hlen : xs.length = ys.length) (hk : xs.length ≤ 2 ^ 20)
    (hx : ∀ a ∈ xs, FormatEntry 53 (-1022) 1023 a.1) (hy : ∀ a ∈ ys, FormatEntry 53 (-1022) 1023 a.1)
    (hcfgs : ∀ c ∈ cfgs, 0 < c.1 ∧ c.1 ≤ 11 ∧ c.2 ≤ 81 ∧ ADP.remapFits c.2 c.1 = true) :
    adpCRJSC ⟨259, 17⟩ cfgs 300 xs ys = some (crSigned rne64 (xs.map toSigned) (ys.map toSigned)) := by
  have hE : ((-1022 : ℤ) - ((53 : ℕ) - 1 : ℤ)).natAbs ≤ 1074 ∧
      ((1023 : ℤ) - ((53 : ℕ) - 1 : ℤ)).natAbs ≤ 1074 := by decide
  have hx' : ∀ a ∈ xs.map (·.1), FormatEntry 53 (-1022) 1023 a := by
    intro a ha; obtain ⟨c, hc, rfl⟩ := List.mem_map.mp ha; exact hx c hc
  have hy' : ∀ a ∈ ys.map (·.1), FormatEntry 53 (-1022) 1023 a := by
    intro a ha; obtain ⟨c, hc, rfl⟩ := List.mem_map.mp ha; exact hy c hc
  have hlx : (xs.map (·.1)).length = xs.length := by simp
  have hl' : (xs.map (·.1)).length = (ys.map (·.1)).length := by simp [hlen]
  have hbk := bitlen_length_le hk
  have hbud : bitlen (xs.length * (2 ^ 6 * 2 ^ 6)) ≤ 33 := bitlen_le_iff.mpr (by omega)
  have hW : exactW 53 300 = 74 := by decide
  have hb2 : bitlen (300 * 300 + 2) = 17 := by decide
  have := natAbs_m1022; have := natAbs_1023
  rw [adpCRJSC_eq hlen (entriesIn_of_format hE hx') (entriesIn_of_format hE hy') (fun c hc => by
      obtain ⟨h0, h1, h2, h3⟩ := hcfgs c hc
      have := bitlen_le_four h1
      refine ⟨h0, h3, ?_, ?_⟩
      · unfold adpR; simp only; omega
      · unfold adpX; simp only; omega)
    (by unfold exactR; rw [hW, hb2]; simp only; omega) (by decide) (by decide)
    (by unfold exactX; rw [hW]; simp only; omega) (by decide)
    (fun a ha => (hx a ha).formatValue) (fun a ha => (hy a ha).formatValue),
    adpCRJS_eq (fun c hc => ⟨(hcfgs c hc).1, (hcfgs c hc).2.2.2⟩) (by decide)
      (fun a ha => (hx a ha).formatValue) (fun a ha => (hy a ha).formatValue) hlen]

/-- The guarded split-K engine on V100 fp16 blocks. -/
def v100SplitKC (B : Widths) : MatrixMultiplier := chunkedC B (chunkLen 11) (tcMultiplier v100F16F32)

theorem v100SplitKC_exactOn {B : Widths} (hR : 25 ≤ B.R) {D : ℕ} (hD : D < 2 ^ B.R) :
    (v100SplitKC B).ExactOn 11 D :=
  chunkedC_exactOn v100_exactOn (chunkLen_pos 11) (chunkLen_exactnessBound (by decide))
    (Nat.lt_of_lt_of_le (by decide) (Nat.pow_le_pow_right (by decide) hR)) hD

theorem dotAbsBound_lt_263 {k : ℕ} (hk : k ≤ 2 ^ 20) :
    k * (2 ^ 11 * 2 ^ 11) < 2 ^ (⟨263, 17⟩ : Widths).R :=
  Nat.lt_of_lt_of_le (show k * (2 ^ 11 * 2 ^ 11) < 2 ^ 43 by omega)
    (Nat.pow_le_pow_right (by decide) (show 43 ≤ (⟨263, 17⟩ : Widths).R by show 43 ≤ 263; decide))

theorem r25_263 : 25 ≤ (⟨263, 17⟩ : Widths).R := by show 25 ≤ 263; decide

/-- **FP64 by Ozaki-I on V100 fp16 with every integer guarded, split-K included**: 263 bits for
data, 17 for exponents and counters; only the Tensor Core blocks' own arithmetic is the hardware
model's. -/
theorem v100_fp64CRI_checked {xs ys : List (ℤ × ℤ)} (hlen : xs.length = ys.length)
    (hk : xs.length ≤ 2 ^ 20) (hx : ∀ a ∈ xs, FormatEntry 53 (-1022) 1023 a)
    (hy : ∀ a ∈ ys, FormatEntry 53 (-1022) 1023 a) {ss : List ℕ} (hss : ∀ s ∈ ss, s ≤ 8) :
    ozaki1CRIC ⟨263, 17⟩ (v100SplitKC ⟨263, 17⟩) 53 (-1022) 1023 11 96 ss 175 xs ys =
      some (rne64 (dot (entryVals xs) (entryVals ys))) :=
  ozaki1CRIC_binary64_tight (v100SplitKC_exactOn r25_263 (dotAbsBound_lt_263 hk)) hlen hk hx hy hss

/-- **Signed FP64 by Ozaki-I on V100 fp16, every integer guarded, split-K included.** -/
theorem v100_fp64CRIS_checked {xs ys : List SEntry} (hlen : xs.length = ys.length)
    (hk : xs.length ≤ 2 ^ 20) (hx : ∀ a ∈ xs, FormatEntry 53 (-1022) 1023 a.1)
    (hy : ∀ a ∈ ys, FormatEntry 53 (-1022) 1023 a.1) {ss : List ℕ} (hss : ∀ s ∈ ss, s ≤ 8) :
    ozaki1CRISC ⟨263, 17⟩ (v100SplitKC ⟨263, 17⟩) 53 (-1022) 1023 11 96 ss 175 xs ys =
      some (crSigned rne64 (xs.map toSigned) (ys.map toSigned)) :=
  ozaki1CRISC_binary64_tight (v100SplitKC_exactOn r25_263 (dotAbsBound_lt_263 hk)) hlen hk hx hy hss

/-- **FP64 by Ozaki-II on V100 fp16, every integer guarded, split-K included.** -/
theorem v100_fp64CRJ_checked {xs ys : List (ℤ × ℤ)} {cfgs : List (CRTBasis × ℕ)}
    (hlen : xs.length = ys.length) (hk : xs.length ≤ 2 ^ 20)
    (hx : ∀ a ∈ xs, FormatEntry 53 (-1022) 1023 a) (hy : ∀ a ∈ ys, FormatEntry 53 (-1022) 1023 a)
    (hcfgs : ∀ c ∈ cfgs, c.1 = fp64Basis ∧ c.2 ≤ 69)
    (hrange : ∀ c ∈ cfgs, 2 * xs.length * (2 ^ c.2 * 2 ^ c.2) < c.1.modulus) :
    ozaki2CRJC ⟨263, 17⟩ (v100SplitKC ⟨263, 17⟩) 53 (-1022) 1023 cfgs 11 175 xs ys =
      some (rne64 (dot (entryVals xs) (entryVals ys))) :=
  ozaki2CRJC_binary64_tight (v100SplitKC_exactOn r25_263 (dotAbsBound_lt_263 hk)) hlen hk hx hy hcfgs
    hrange

end Ozaki.TC
