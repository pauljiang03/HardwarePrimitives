import Ozaki.CheckedTight

/-! # Binary32 instances of the checked signed pipelines

`Ozaki.CheckedTight` states the signed checked pipelines for FP64 (`ozaki1CRISC_binary64_tight`,
`ozaki2CRJSC_binary64_tight`). Here the binary32 ones, at the binary32 widths of the unsigned
pipelines: correctly rounded binary32 Ozaki-I with IEEE's sign of zero within `207` data bits and
`15` exponent and counter bits (`ozaki1CRISC_binary32_tight`), and Ozaki-II with six moduli at most
`4096` and `P ≤ 34` within `161` and `15` (`ozaki2CRJSC_binary32_tight`). The sign test multiplies
two significands, which needs `R ≥ 2p = 48`; both widths meet it. -/

local notation "ℕ" => Nat
local notation "ℤ" => Int
local notation "ℚ" => Rat

namespace Ozaki

open Checked

/-- **Signed binary32 Ozaki-I: 207 bits and 15 bits**, the IEEE result with IEEE's sign of zero. -/
theorem ozaki1CRISC_binary32_tight {mult : MatrixMultiplier} {xs ys : List SEntry}
    (hmult : mult.ExactOn 11 (xs.length * (2 ^ 11 * 2 ^ 11))) (hlen : xs.length = ys.length)
    (hk : xs.length ≤ 2 ^ 20) (hx : ∀ a ∈ xs, FormatEntry 24 (-126) 127 a.1)
    (hy : ∀ a ∈ ys, FormatEntry 24 (-126) 127 a.1) {ss : List ℕ} (hss : ∀ s ∈ ss, s ≤ 8) :
    ozaki1CRISC ⟨207, 15⟩ mult 24 (-126) 127 11 96 ss 24 xs ys =
      some (crSigned rne32Q (xs.map toSigned) (ys.map toSigned)) := by
  have hE : ((-126 : ℤ) - ((24 : ℕ) - 1 : ℤ)).natAbs ≤ 149 ∧
      ((127 : ℤ) - ((24 : ℕ) - 1 : ℤ)).natAbs ≤ 149 := by decide
  have hx' : ∀ a ∈ xs.map (·.1), FormatEntry 24 (-126) 127 a := by
    intro a ha; obtain ⟨c, hc, rfl⟩ := List.mem_map.mp ha; exact hx c hc
  have hy' : ∀ a ∈ ys.map (·.1), FormatEntry 24 (-126) 127 a := by
    intro a ha; obtain ⟨c, hc, rfl⟩ := List.mem_map.mp ha; exact hy c hc
  have hbud := bitlen_dotAbsBound_le hk
  have hW : exactW 24 24 = 38 := by decide
  have hb2 : bitlen (24 * 24 + 2) = 10 := by decide
  have := natAbs_m126; have := natAbs_127
  rw [ozaki1CRISC_eq hmult hlen (Nat.le_refl _) (entriesIn_of_format hE hx')
    (entriesIn_of_format hE hy') (by unfold exactR; rw [hW, hb2]; simp only; omega) (by decide)
    (by decide) (by unfold exactX; rw [hW]; simp only; omega)
    (fun s hs => by have := testD_le_8 (p := 24) (hss s hs) hk; simp only; omega)
    (fun s hs => by
      have := testD_le_8 (p := 24) (hss s hs) hk
      have h8 := hss s hs
      unfold testX; simp only; omega)]
  exact congrArg some (ozaki1CRIS32_eq hmult 96 ss (by decide) (by decide) hlen (Nat.le_refl _)
    (fun a ha => (hx a ha).formatValue) (fun a ha => (hy a ha).formatValue))

/-- **Signed binary32 Ozaki-II: 161 bits and 15 bits**, six moduli at most `4096` with `P ≤ 34`. -/
theorem ozaki2CRJSC_binary32_tight {mult : MatrixMultiplier} {xs ys : List SEntry}
    {cfgs : List (CRTBasis × ℕ)}
    (hmult : mult.ExactOn 11 (xs.length * (2 ^ 11 * 2 ^ 11))) (hlen : xs.length = ys.length)
    (hk : xs.length ≤ 2 ^ 20) (hx : ∀ a ∈ xs, FormatEntry 24 (-126) 127 a.1)
    (hy : ∀ a ∈ ys, FormatEntry 24 (-126) 127 a.1)
    (hcfgs : ∀ c ∈ cfgs, c.1 = fp32Basis6 ∧ c.2 ≤ 34)
    (hrange : ∀ c ∈ cfgs, 2 * xs.length * (2 ^ c.2 * 2 ^ c.2) < c.1.modulus) :
    ozaki2CRJSC ⟨161, 15⟩ mult 24 (-126) 127 cfgs 11 24 xs ys =
      some (crSigned rne32Q (xs.map toSigned) (ys.map toSigned)) := by
  have hE : ((-126 : ℤ) - ((24 : ℕ) - 1 : ℤ)).natAbs ≤ 149 ∧
      ((127 : ℤ) - ((24 : ℕ) - 1 : ℤ)).natAbs ≤ 149 := by decide
  have hx' : ∀ a ∈ xs.map (·.1), FormatEntry 24 (-126) 127 a := by
    intro a ha; obtain ⟨c, hc, rfl⟩ := List.mem_map.mp ha; exact hx c hc
  have hy' : ∀ a ∈ ys.map (·.1), FormatEntry 24 (-126) 127 a := by
    intro a ha; obtain ⟨c, hc, rfl⟩ := List.mem_map.mp ha; exact hy c hc
  have hlx : (xs.map (·.1)).length = xs.length := by simp
  have hl' : (xs.map (·.1)).length = (ys.map (·.1)).length := by simp [hlen]
  have hbud := bitlen_dotAbsBound_le hk
  have hW : exactW 24 24 = 38 := by decide
  have := natAbs_m126; have := natAbs_127
  have hval : ozaki2CRJ mult 24 (-126) 127 cfgs 11 24 (xs.map (·.1)) (ys.map (·.1)) =
      rne32Q (dot (entryVals (xs.map (·.1))) (entryVals (ys.map (·.1)))) :=
    ozaki2CRJ32_eq (by rw [hlx]; exact hmult) (by decide) (by decide) (fun c hc => by
      obtain ⟨h1, _⟩ := hcfgs c hc
      refine ⟨?_, ?_, by rw [hlx]; exact hrange c hc⟩
      · rw [h1]; decide +kernel
      · rw [h1]; exact fun m hm => (fp32Basis6_facts.1 m hm).2) hl' (Nat.le_refl _)
      (fun v hv => by
        obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hv; exact (hx' a ha).formatValue)
      (fun v hv => by
        obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hv; exact (hy' a ha).formatValue)
  unfold ozaki2CRJSC
  rw [ozaki2CRJC_binary32_tight (by rw [hlx]; exact hmult) hl' (by rw [hlx]; exact hk) hx' hy'
    hcfgs]
  simp only [Option.bind_eq_bind, Option.bind_some]
  rw [signStepC_eq (emin := -126) (emax := 127) hmult hlen (Nat.le_refl _)
    (entriesIn_of_format hE hx') (entriesIn_of_format hE hy')
    (by unfold exactR; rw [hW]; have : bitlen (24 * 24 + 2) = 10 := by decide
        simp only; omega)
    (by decide) (by decide)
    (by unfold exactX; rw [hW]; simp only; omega)]
  congr 1
  exact signStep_eq (by decide) (by decide) hmult hlen (Nat.le_refl _)
    (vanishInt32 (by decide) (by decide)
      (fun a ha => by obtain ⟨c, hc, rfl⟩ := List.mem_map.mp ha; exact (hx c hc).formatValue)
      (fun a ha => by obtain ⟨c, hc, rfl⟩ := List.mem_map.mp ha; exact (hy c hc).formatValue))
    hval

end Ozaki
