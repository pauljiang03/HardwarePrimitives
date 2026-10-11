import Ozaki.BoundedCheckedSigned
import Ozaki.CheckedEngines

/-! # Tighter widths

The checked pipelines bound every integer they compute by a data width `R` and every exponent and
counter by `X`. After three changes (the check's integers bounded by `max(W, s(b+1))` bits rather
than `W + s(b+1)`, the descent's fuel guarded as data rather than as an exponent, and the
exponent width set by the exponents alone), the concrete widths are:

| Pipeline | `R` | `X` |
| --- | --- | --- |
| Ozaki-I, FP64 (`11`-bit slices, at most `8` per check, `175` on the exact path, `k ≤ 2^20`) | 263 | 17 |
| Ozaki-I, binary32 (at most `24` slices on the exact path) | 207 | 15 |
| Ozaki-II, FP64 (twelve moduli at most `4096`, `P ≤ 69`) | 263 | 17 |
| Ozaki-II, binary32 (six moduli, `P ≤ 34`) | 161 | 15 |

(earlier `332`/`24`, `303`/`17`, `264`/`24`, `161`/`17`; ADP-style slicing is in `OzakiTC.CheckedTight`:
`259`/`17`, earlier `264`/`25`). The signed variants need `R ≥ 2p`, which these meet. The FP64 data
width is set by the exact path (`exactR`), the binary32 Ozaki-I one by the check. -/

local notation "ℕ" => Nat
local notation "ℤ" => Int
local notation "ℚ" => Rat

namespace Ozaki

open Checked

theorem natAbs_m1022 : (-1022 : ℤ).natAbs = 1022 := by decide
theorem natAbs_1023 : (1023 : ℤ).natAbs = 1023 := by decide
theorem natAbs_m126 : (-126 : ℤ).natAbs = 126 := by decide
theorem natAbs_127 : (127 : ℤ).natAbs = 127 := by decide

/-- **Correctly rounded FP64 Ozaki-I: every data integer within 263 bits, every exponent and
counter within 17 bits.** -/
theorem ozaki1CRIC_binary64_tight {eng : Engine} {xs ys : List (ℤ × ℤ)}
    (heng : eng.ExactOn 11 (xs.length * (2 ^ 11 * 2 ^ 11))) (hlen : xs.length = ys.length)
    (hk : xs.length ≤ 2 ^ 20) (hx : ∀ a ∈ xs, FormatEntry 53 (-1022) 1023 a)
    (hy : ∀ a ∈ ys, FormatEntry 53 (-1022) 1023 a) {ss : List ℕ} (hss : ∀ s ∈ ss, s ≤ 8) :
    ozaki1CRIC ⟨263, 17⟩ eng 53 (-1022) 1023 11 96 ss 175 xs ys =
      some (rne64 (dot (entryVals xs) (entryVals ys))) := by
  have hE : ((-1022 : ℤ) - ((53 : ℕ) - 1 : ℤ)).natAbs ≤ 1074 ∧
      ((1023 : ℤ) - ((53 : ℕ) - 1 : ℤ)).natAbs ≤ 1074 := by decide
  have hbud := bitlen_budget_le hk
  have hW : exactW 53 175 = 72 := by decide
  have hb2 : bitlen (175 * 175 + 2) = 15 := by decide
  have := natAbs_m1022; have := natAbs_1023
  rw [ozaki1CRIC_eq heng hlen (Nat.le_refl _) (entriesIn_of_format hE hx)
    (entriesIn_of_format hE hy) (by unfold exactR; rw [hW, hb2]; simp only; omega) (by decide)
    (by unfold exactX; rw [hW]; simp only; omega) ss
    (fun s hs => by have := checkD_le_8 (p := 53) (hss s hs) hk; simp only; omega)
    (fun s hs => by
      have := checkD_le_8 (p := 53) (hss s hs) hk
      have h8 := hss s hs
      unfold checkX; simp only; omega),
    ozaki1CRI64_eq heng 96 ss (by decide) (by decide) hlen (Nat.le_refl _)
      (fun a ha => (hx a ha).formatValue) (fun a ha => (hy a ha).formatValue)]

/-- **Correctly rounded binary32 Ozaki-I: 207 bits and 15 bits.** -/
theorem ozaki1CRIC_binary32_tight {eng : Engine} {xs ys : List (ℤ × ℤ)}
    (heng : eng.ExactOn 11 (xs.length * (2 ^ 11 * 2 ^ 11))) (hlen : xs.length = ys.length)
    (hk : xs.length ≤ 2 ^ 20) (hx : ∀ a ∈ xs, FormatEntry 24 (-126) 127 a)
    (hy : ∀ a ∈ ys, FormatEntry 24 (-126) 127 a) {ss : List ℕ} (hss : ∀ s ∈ ss, s ≤ 8) :
    ozaki1CRIC ⟨207, 15⟩ eng 24 (-126) 127 11 96 ss 24 xs ys =
      some (rne32Q (dot (entryVals xs) (entryVals ys))) := by
  have hE : ((-126 : ℤ) - ((24 : ℕ) - 1 : ℤ)).natAbs ≤ 149 ∧
      ((127 : ℤ) - ((24 : ℕ) - 1 : ℤ)).natAbs ≤ 149 := by decide
  have hbud := bitlen_budget_le hk
  have hW : exactW 24 24 = 38 := by decide
  have hb2 : bitlen (24 * 24 + 2) = 10 := by decide
  have := natAbs_m126; have := natAbs_127
  rw [ozaki1CRIC_eq heng hlen (Nat.le_refl _) (entriesIn_of_format hE hx)
    (entriesIn_of_format hE hy) (by unfold exactR; rw [hW, hb2]; simp only; omega) (by decide)
    (by unfold exactX; rw [hW]; simp only; omega) ss
    (fun s hs => by have := checkD_le_8 (p := 24) (hss s hs) hk; simp only; omega)
    (fun s hs => by
      have := checkD_le_8 (p := 24) (hss s hs) hk
      have h8 := hss s hs
      unfold checkX; simp only; omega),
    ozaki1CRI32_eq heng 96 ss (by decide) (by decide) hlen (Nat.le_refl _)
      (fun a ha => (hx a ha).formatValue) (fun a ha => (hy a ha).formatValue)]

/-- **Signed FP64 Ozaki-I: 263 bits and 17 bits**, the IEEE result with IEEE's sign of zero. -/
theorem ozaki1CRISC_binary64_tight {eng : Engine} {xs ys : List SEntry}
    (heng : eng.ExactOn 11 (xs.length * (2 ^ 11 * 2 ^ 11))) (hlen : xs.length = ys.length)
    (hk : xs.length ≤ 2 ^ 20) (hx : ∀ a ∈ xs, FormatEntry 53 (-1022) 1023 a.1)
    (hy : ∀ a ∈ ys, FormatEntry 53 (-1022) 1023 a.1) {ss : List ℕ} (hss : ∀ s ∈ ss, s ≤ 8) :
    ozaki1CRISC ⟨263, 17⟩ eng 53 (-1022) 1023 11 96 ss 175 xs ys =
      some (crSigned rne64 (xs.map toSigned) (ys.map toSigned)) := by
  have hE : ((-1022 : ℤ) - ((53 : ℕ) - 1 : ℤ)).natAbs ≤ 1074 ∧
      ((1023 : ℤ) - ((53 : ℕ) - 1 : ℤ)).natAbs ≤ 1074 := by decide
  have hx' : ∀ a ∈ xs.map (·.1), FormatEntry 53 (-1022) 1023 a := by
    intro a ha; obtain ⟨c, hc, rfl⟩ := List.mem_map.mp ha; exact hx c hc
  have hy' : ∀ a ∈ ys.map (·.1), FormatEntry 53 (-1022) 1023 a := by
    intro a ha; obtain ⟨c, hc, rfl⟩ := List.mem_map.mp ha; exact hy c hc
  have hbud := bitlen_budget_le hk
  have hW : exactW 53 175 = 72 := by decide
  have hb2 : bitlen (175 * 175 + 2) = 15 := by decide
  have := natAbs_m1022; have := natAbs_1023
  rw [ozaki1CRISC_eq heng hlen (Nat.le_refl _) (entriesIn_of_format hE hx')
    (entriesIn_of_format hE hy') (by unfold exactR; rw [hW, hb2]; simp only; omega) (by decide)
    (by decide) (by unfold exactX; rw [hW]; simp only; omega)
    (fun s hs => by have := checkD_le_8 (p := 53) (hss s hs) hk; simp only; omega)
    (fun s hs => by
      have := checkD_le_8 (p := 53) (hss s hs) hk
      have h8 := hss s hs
      unfold checkX; simp only; omega)]
  exact congrArg some (ozaki1CRIS64_eq heng 96 ss (by decide) (by decide) hlen (Nat.le_refl _)
    (fun a ha => (hx a ha).formatValue) (fun a ha => (hy a ha).formatValue))

/-- **Correctly rounded FP64 Ozaki-II: 263 bits and 17 bits**, the twelve moduli at most `4096`
with `P ≤ 69`. -/
theorem ozaki2CRJC_binary64_tight {eng : Engine} {xs ys : List (ℤ × ℤ)}
    {cfgs : List (CRTBasis × ℕ)}
    (heng : eng.ExactOn 11 (xs.length * (2 ^ 11 * 2 ^ 11))) (hlen : xs.length = ys.length)
    (hk : xs.length ≤ 2 ^ 20) (hx : ∀ a ∈ xs, FormatEntry 53 (-1022) 1023 a)
    (hy : ∀ a ∈ ys, FormatEntry 53 (-1022) 1023 a)
    (hcfgs : ∀ c ∈ cfgs, c.1 = fp64Basis ∧ c.2 ≤ 69)
    (hrange : ∀ c ∈ cfgs, 2 * xs.length * (2 ^ c.2 * 2 ^ c.2) < c.1.modulus) :
    ozaki2CRJC ⟨263, 17⟩ eng 53 (-1022) 1023 cfgs 11 175 xs ys =
      some (rne64 (dot (entryVals xs) (entryVals ys))) := by
  have hE : ((-1022 : ℤ) - ((53 : ℕ) - 1 : ℤ)).natAbs ≤ 1074 ∧
      ((1023 : ℤ) - ((53 : ℕ) - 1 : ℤ)).natAbs ≤ 1074 := by decide
  have hbud := bitlen_budget_le hk
  have hbk := bitlen_length_le hk
  have hW : exactW 53 175 = 72 := by decide
  have hb2 : bitlen (175 * 175 + 2) = 15 := by decide
  have := natAbs_m1022; have := natAbs_1023
  obtain ⟨hm, hM, hsize, hM2, hbl⟩ := fp64Basis_facts
  rw [ozaki2CRJC_eq heng hlen (Nat.le_refl _) (entriesIn_of_format hE hx)
    (entriesIn_of_format hE hy) (fun c hc => by
      obtain ⟨h1, h2⟩ := hcfgs c hc
      rw [h1]
      refine ⟨hm, hM, Nat.lt_of_lt_of_le hsize (Nat.pow_le_pow_right (by decide) (by decide)),
        Nat.lt_of_lt_of_le hM2 (Nat.pow_le_pow_right (by decide) (by decide)), ?_, ?_⟩
      · unfold ozaki2R; rw [hbl]; simp only; omega
      · unfold ozaki2X ozaki2R; rw [hbl]; simp only; omega)
    (by unfold exactR; rw [hW, hb2]; simp only; omega) (by decide)
    (by unfold exactX; rw [hW]; simp only; omega),
    ozaki2CRJ64_eq heng (by decide) (by decide) (fun c hc => by
      obtain ⟨h1, _⟩ := hcfgs c hc
      refine ⟨?_, ?_, hrange c hc⟩
      · rw [h1]; decide +kernel
      · rw [h1]; exact fun m hm => (fp64Basis_facts.1 m hm).2) hlen (Nat.le_refl _)
    (fun v hv => by obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hv; exact (hx a ha).formatValue)
    (fun v hv => by obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hv; exact (hy a ha).formatValue)]

/-- **Correctly rounded binary32 Ozaki-II: 161 bits and 15 bits**, six moduli at most `4096` with
`P ≤ 34`. -/
theorem ozaki2CRJC_binary32_tight {eng : Engine} {xs ys : List (ℤ × ℤ)}
    {cfgs : List (CRTBasis × ℕ)}
    (heng : eng.ExactOn 11 (xs.length * (2 ^ 11 * 2 ^ 11))) (hlen : xs.length = ys.length)
    (hk : xs.length ≤ 2 ^ 20) (hx : ∀ a ∈ xs, FormatEntry 24 (-126) 127 a)
    (hy : ∀ a ∈ ys, FormatEntry 24 (-126) 127 a)
    (hcfgs : ∀ c ∈ cfgs, c.1 = fp32Basis6 ∧ c.2 ≤ 34) :
    ozaki2CRJC ⟨161, 15⟩ eng 24 (-126) 127 cfgs 11 24 xs ys =
      some (ozaki2CRJ eng 24 (-126) 127 cfgs 11 24 xs ys) := by
  have hE : ((-126 : ℤ) - ((24 : ℕ) - 1 : ℤ)).natAbs ≤ 149 ∧
      ((127 : ℤ) - ((24 : ℕ) - 1 : ℤ)).natAbs ≤ 149 := by decide
  have hbud := bitlen_budget_le hk
  have hbk := bitlen_length_le hk
  have hW : exactW 24 24 = 38 := by decide
  have hb2 : bitlen (24 * 24 + 2) = 10 := by decide
  have := natAbs_m126; have := natAbs_127
  obtain ⟨hm, hM, hsize, hM2, hbl⟩ := fp32Basis6_facts
  exact ozaki2CRJC_eq heng hlen (Nat.le_refl _) (entriesIn_of_format hE hx)
    (entriesIn_of_format hE hy) (fun c hc => by
      obtain ⟨h1, h2⟩ := hcfgs c hc
      rw [h1]
      refine ⟨hm, hM, Nat.lt_of_lt_of_le hsize (Nat.pow_le_pow_right (by decide) (by decide)),
        Nat.lt_of_lt_of_le hM2 (Nat.pow_le_pow_right (by decide) (by decide)), ?_, ?_⟩
      · unfold ozaki2R; rw [hbl]; simp only; omega
      · unfold ozaki2X ozaki2R; rw [hbl]; simp only; omega)
    (by unfold exactR; rw [hW, hb2]; simp only; omega) (by decide)
    (by unfold exactX; rw [hW]; simp only; omega)

/-- **Signed FP64 Ozaki-II: 263 bits and 17 bits.** -/
theorem ozaki2CRJSC_binary64_tight {eng : Engine} {xs ys : List SEntry}
    {cfgs : List (CRTBasis × ℕ)}
    (heng : eng.ExactOn 11 (xs.length * (2 ^ 11 * 2 ^ 11))) (hlen : xs.length = ys.length)
    (hk : xs.length ≤ 2 ^ 20) (hx : ∀ a ∈ xs, FormatEntry 53 (-1022) 1023 a.1)
    (hy : ∀ a ∈ ys, FormatEntry 53 (-1022) 1023 a.1)
    (hcfgs : ∀ c ∈ cfgs, c.1 = fp64Basis ∧ c.2 ≤ 69)
    (hrange : ∀ c ∈ cfgs, 2 * xs.length * (2 ^ c.2 * 2 ^ c.2) < c.1.modulus) :
    ozaki2CRJSC ⟨263, 17⟩ eng 53 (-1022) 1023 cfgs 11 175 xs ys =
      some (crSigned rne64 (xs.map toSigned) (ys.map toSigned)) := by
  have hE : ((-1022 : ℤ) - ((53 : ℕ) - 1 : ℤ)).natAbs ≤ 1074 ∧
      ((1023 : ℤ) - ((53 : ℕ) - 1 : ℤ)).natAbs ≤ 1074 := by decide
  have hx' : ∀ a ∈ xs.map (·.1), FormatEntry 53 (-1022) 1023 a := by
    intro a ha; obtain ⟨c, hc, rfl⟩ := List.mem_map.mp ha; exact hx c hc
  have hy' : ∀ a ∈ ys.map (·.1), FormatEntry 53 (-1022) 1023 a := by
    intro a ha; obtain ⟨c, hc, rfl⟩ := List.mem_map.mp ha; exact hy c hc
  have hlx : (xs.map (·.1)).length = xs.length := by simp
  have hl' : (xs.map (·.1)).length = (ys.map (·.1)).length := by simp [hlen]
  have hbud := bitlen_budget_le hk
  have hW : exactW 53 175 = 72 := by decide
  have := natAbs_m1022; have := natAbs_1023
  unfold ozaki2CRJSC
  rw [ozaki2CRJC_binary64_tight (by rw [hlx]; exact heng) hl' (by rw [hlx]; exact hk) hx' hy'
    hcfgs (by rw [hlx]; exact hrange)]
  simp only [Option.bind_eq_bind, Option.bind_some]
  rw [signStepC_eq (emin := -1022) (emax := 1023) heng hlen (Nat.le_refl _)
    (entriesIn_of_format hE hx') (entriesIn_of_format hE hy')
    (by unfold exactR; rw [hW]; have : bitlen (175 * 175 + 2) = 15 := by decide
        simp only; omega)
    (by decide) (by decide)
    (by unfold exactX; rw [hW]; simp only; omega)]
  congr 1
  exact signStep_eq (by decide) (by decide) heng hlen (Nat.le_refl _)
    (vanishInt64 (by decide) (by decide)
      (fun a ha => by obtain ⟨c, hc, rfl⟩ := List.mem_map.mp ha; exact (hx c hc).formatValue)
      (fun a ha => by obtain ⟨c, hc, rfl⟩ := List.mem_map.mp ha; exact (hy c hc).formatValue))
    rfl

end Ozaki
