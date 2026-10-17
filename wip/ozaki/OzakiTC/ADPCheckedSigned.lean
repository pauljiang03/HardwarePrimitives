import OzakiTC.ADPChecked
import Ozaki.BoundedCheckedSigned

/-! # ADP-style slicing with signed zeros, every integer bounded

The checked integer ADP-style pipeline (`adpCRJC`) followed by the checked sign step of
`Ozaki.BoundedCheckedSigned` (`signStepC`): `adpCRJSC` returns exactly `adpCRJS`, the signed
integer pipeline, under the requirements of `adpCRJC_eq` and `R ≥ 106` (`adpCRJSC_eq`), the sign
oracle's exact fallback running on the guarded INT8 matrix multiplier (`int8SplitKC`); for binary64
entries, every data integer within `264` bits and every exponent and counter within `25` bits, it is
the IEEE binary64 result with IEEE's sign of zero (`adpCRJSC_binary64_eq`). -/

open TensorCore

namespace Ozaki.TC

open Ozaki.Checked

/-- **ADP-style slicing in integers with signed zeros, every integer guarded.** -/
def adpCRJSC (B : Widths) (cfgs : List (ℕ × ℕ)) (smax : ℕ) (xs ys : List SEntry) :
    Option (Option Signed) := do
  let r ← adpCRJC B cfgs smax (xs.map (·.1)) (ys.map (·.1))
  signStepC B (int8SplitKC B) 6 smax r xs ys

/-- **Signed ADP-style slicing never fails a guard**, and is correctly rounded with IEEE's sign of
zero. -/
theorem adpCRJSC_eq {B : Widths} {EM smax : ℕ} {cfgs : List (ℕ × ℕ)} {xs ys : List SEntry}
    (hlen : xs.length = ys.length) (hx : EntriesIn 53 EM (xs.map (·.1)))
    (hy : EntriesIn 53 EM (ys.map (·.1)))
    (hcfg : ∀ c ∈ cfgs, 0 < c.1 ∧ ADP.remapFits c.2 c.1 = true ∧
      adpR c.1 c.2 53 xs.length ≤ B.R ∧ adpX c.2 53 EM xs.length (-1022) 1023 B.R < 2 ^ B.X)
    (hRe : exactR 53 smax (xs.length * (2 ^ 6 * 2 ^ 6)) ≤ B.R) (hRb : 53 + 6 + 3 ≤ B.R)
    (hR2 : 2 * 53 ≤ B.R)
    (hXe : exactX 53 6 EM smax (xs.length * (2 ^ 6 * 2 ^ 6)) (-1022) 1023 B.R < 2 ^ B.X)
    (hsmax : 2098 < smax * 7) (hx64 : ∀ a ∈ xs, Binary64Value (entryVal a.1))
    (hy64 : ∀ a ∈ ys, Binary64Value (entryVal a.1)) :
    adpCRJSC B cfgs smax xs ys = some (adpCRJS cfgs smax xs ys) := by
  have hl : (xs.map (·.1)).length = (ys.map (·.1)).length := by simp [hlen]
  have hlx : (xs.map (·.1)).length = xs.length := by simp
  unfold adpCRJSC
  rw [adpCRJC_eq hl hx hy (by rw [hlx]; exact hcfg) (by rw [hlx]; exact hRe) hRb
    (by rw [hlx]; exact hXe)]
  simp only [Option.bind_eq_bind, Option.bind_some]
  have hD : xs.length * (2 ^ 6 * 2 ^ 6) < 2 ^ B.R := by
    unfold exactR at hRe
    exact Nat.lt_of_lt_of_le (lt_two_pow_bitlen _) (Nat.pow_le_pow_right (by decide) (by omega))
  rw [signStepC_eq (int8SplitKC_exactOn (by omega) hD) hlen (Nat.le_refl _) hx hy hRe hRb hR2 hXe]
  congr 1
  have hv64 : ∀ {zs : List SEntry}, (∀ a ∈ zs, Binary64Value (entryVal a.1)) →
      ∀ v ∈ entryVals (zs.map (·.1)), Binary64Value v := by
    intro zs hz v hv
    simp only [entryVals, List.map_map, List.mem_map] at hv
    obtain ⟨a, ha, rfl⟩ := hv; exact hz a ha
  rw [adpCRJS_eq (fun c hc => ⟨(hcfg c hc).1, (hcfg c hc).2.1⟩) hsmax hx64 hy64 hlen]
  exact signStep_eq (by decide) (by decide) (int8SplitKC_exactOn (by omega) hD) hlen (Nat.le_refl _)
    (vanishInt64 (by decide) (by simpa using hsmax)
      (fun a ha => by obtain ⟨c, hc, rfl⟩ := List.mem_map.mp ha; exact hx64 c hc)
      (fun a ha => by obtain ⟨c, hc, rfl⟩ := List.mem_map.mp ha; exact hy64 c hc))
    (adpCRJ_eq (fun c hc => ⟨(hcfg c hc).1, (hcfg c hc).2.1⟩) hsmax (hv64 hx64) (hv64 hy64) hl)

/-- **Signed FP64 by ADP-style slicing, every integer within 264 bits and every exponent and
counter within 25 bits**: on binary64 entries with `k ≤ 2^20`, configurations of at most `11`
slices of width at most `81`, and at most `300` slices of `6` bits on the exact fallback. -/
theorem adpCRJSC_binary64_eq {cfgs : List (ℕ × ℕ)} {xs ys : List SEntry}
    (hlen : xs.length = ys.length) (hk : xs.length ≤ 2 ^ 20)
    (hx : ∀ a ∈ xs, FormatEntry 53 (-1022) 1023 a.1) (hy : ∀ a ∈ ys, FormatEntry 53 (-1022) 1023 a.1)
    (hcfgs : ∀ c ∈ cfgs, 0 < c.1 ∧ c.1 ≤ 11 ∧ c.2 ≤ 81 ∧ ADP.remapFits c.2 c.1 = true) :
    adpCRJSC ⟨264, 25⟩ cfgs 300 xs ys = some (crSigned rne64 (xs.map toSigned) (ys.map toSigned)) := by
  have hE : ((-1022 : ℤ) - ((53 : ℕ) - 1 : ℤ)).natAbs ≤ 1074 ∧
      ((1023 : ℤ) - ((53 : ℕ) - 1 : ℤ)).natAbs ≤ 1074 := by decide
  have hx' : ∀ a ∈ xs.map (·.1), FormatEntry 53 (-1022) 1023 a := by
    intro a ha; obtain ⟨c, hc, rfl⟩ := List.mem_map.mp ha; exact hx c hc
  have hy' : ∀ a ∈ ys.map (·.1), FormatEntry 53 (-1022) 1023 a := by
    intro a ha; obtain ⟨c, hc, rfl⟩ := List.mem_map.mp ha; exact hy c hc
  have hlx : (xs.map (·.1)).length = xs.length := by simp
  have hl' : (xs.map (·.1)).length = (ys.map (·.1)).length := by simp [hlen]
  have hu := adpCRJC_binary64 (cfgs := cfgs) hl' (by rw [hlx]; exact hk) hx' hy' hcfgs
  have hval := adpCRJ_eq (cfgs := cfgs) (smax := 300) (xs := xs.map (·.1)) (ys := ys.map (·.1))
    (fun c hc => ⟨(hcfgs c hc).1, (hcfgs c hc).2.2.2⟩) (by decide)
    (fun v hv => by obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hv; exact (hx' a ha).formatValue)
    (fun v hv => by obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hv; exact (hy' a ha).formatValue) hl'
  have hbud : bitlen (xs.length * (2 ^ 6 * 2 ^ 6)) ≤ 33 := bitlen_le_iff.mpr (by omega)
  have hW : exactW 53 300 = 74 := by decide
  have hm1 : (-1022 : ℤ).natAbs = 1022 := by decide
  have hm2 : (1023 : ℤ).natAbs = 1023 := by decide
  unfold adpCRJSC
  rw [hu]
  simp only [Option.bind_eq_bind, Option.bind_some]
  have h31 : 31 ≤ (⟨264, 25⟩ : Widths).R := by show 31 ≤ 264; decide
  have hD : xs.length * (2 ^ 6 * 2 ^ 6) < 2 ^ (⟨264, 25⟩ : Widths).R :=
    Nat.lt_of_lt_of_le (show xs.length * (2 ^ 6 * 2 ^ 6) < 2 ^ 33 by omega)
      (Nat.pow_le_pow_right (by decide) (show 33 ≤ (⟨264, 25⟩ : Widths).R by show 33 ≤ 264; decide))
  rw [signStepC_eq (emin := -1022) (emax := 1023) (int8SplitKC_exactOn h31 hD) hlen
    (Nat.le_refl _)
    (entriesIn_of_format hE hx') (entriesIn_of_format hE hy')
    (by clear hD h31; unfold exactR; rw [hW]; have : bitlen (300 * 300 + 2) = 17 := by decide
        simp only; omega)
    (by decide) (by decide)
    (by clear hD h31; unfold exactX; rw [hW]; simp only; omega)]
  congr 1
  exact signStep_eq (by decide) (by decide) (int8SplitKC_exactOn h31 hD) hlen (Nat.le_refl _)
    (vanishInt64 (by decide) (by decide)
      (fun a ha => by obtain ⟨c, hc, rfl⟩ := List.mem_map.mp ha; exact (hx c hc).formatValue)
      (fun a ha => by obtain ⟨c, hc, rfl⟩ := List.mem_map.mp ha; exact (hy c hc).formatValue))
    hval

end Ozaki.TC
