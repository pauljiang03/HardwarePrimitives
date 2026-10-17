import Ozaki.BoundedChecked2
import Ozaki.IEEEInt

/-! # Every integer bounded, with signed zeros

`ozaki1CRISC` (in `Ozaki.BoundedChecked`) is the checked twin of correctly rounded Ozaki-I with
IEEE signed zeros. This file gives the same for Ozaki-II, through one sign step shared by the
signed integer pipelines:

* `signStep`: a nonzero rounded value carries its own sign; a zero takes the sign of the exact sum
  from the integer exact fallback (`exactSignI`), and an exact zero is `−0` only when every product
  is `−0` (`allNegZeroI`). Given a correctly rounded value, it is the specification `crSigned`
  (`signStep_eq`).
* `signStepC`: the same with every integer guarded (the checked sign oracle `exactSignIC` and the
  checked products of `allNegZeroIC`); it returns what `signStep` returns (`signStepC_eq`).
* `ozaki2CRJSC`: checked Ozaki-II in integers followed by the checked sign step. Under the
  requirements of `ozaki2CRJC_eq` and `R ≥ 2p`, it returns exactly `ozaki2CRJS`
  (`ozaki2CRJSC_eq`); for binary64 entries, every data integer within `264` bits and every
  exponent and counter within `24` bits, it returns the IEEE binary64 result with IEEE's sign of
  zero (`ozaki2CRJSC_binary64_eq`).

`OzakiTC.ADPCheckedSigned` does the same for ADP-style slicing. -/

local notation "ℕ" => Nat
local notation "ℤ" => Int
local notation "ℚ" => Rat

namespace Ozaki

/-- **The sign step of the signed integer pipelines.** -/
def signStep (mult : MatrixMultiplier) (b smax : ℕ) (r : Option ℚ) (xs ys : List SEntry) : Option Signed :=
  match r with
  | none => none
  | some r =>
    if r ≠ 0 then some ⟨r, decide (r < 0)⟩
    else (exactSignI mult b smax (xs.map (·.1)) (ys.map (·.1))).map fun sg =>
      ⟨0, if sg = 0 then allNegZeroI xs ys else decide (sg < 0)⟩

theorem ozaki1CRIS_eq_signStep (mult : MatrixMultiplier) (p : ℕ) (emin emax : ℤ) (b W : ℕ) (ss : List ℕ)
    (smax : ℕ) (xs ys : List SEntry) :
    ozaki1CRIS mult p emin emax b W ss smax xs ys =
      signStep mult b smax (ozaki1CRI mult p emin emax b W ss smax (xs.map (·.1)) (ys.map (·.1)))
        xs ys := rfl

/-- **The sign step of a correctly rounded value is the specification.** -/
theorem signStep_eq {p : ℕ} {emin emax : ℤ} (hp : 0 < p) (hle : emin ≤ emax) {mult : MatrixMultiplier}
    {b bound smax : ℕ} (hmult : mult.ExactOn b bound) {xs ys : List SEntry}
    (hlen : xs.length = ys.length) (hbound : xs.length * (2 ^ b * 2 ^ b) ≤ bound)
    (hvanish : ∃ s ∈ List.range' 1 smax, vanishInt b s (xs.map (·.1)) (ys.map (·.1)) = true)
    {r : Option ℚ}
    (hr : r = roundRNE p emin emax (dot (entryVals (xs.map (·.1))) (entryVals (ys.map (·.1))))) :
    signStep mult b smax r xs ys =
      crSigned (roundRNE p emin emax) (xs.map toSigned) (ys.map toSigned) := by
  have hl : (xs.map (·.1)).length = (ys.map (·.1)).length := by simp [hlen]
  have hb : (xs.map (·.1)).length * (2 ^ b * 2 ^ b) ≤ bound := by simpa using hbound
  subst hr
  unfold signStep crSigned
  rw [vals_toSigned, vals_toSigned, ← allNegZeroI_eq]
  generalize hv : dot (entryVals (xs.map (·.1))) (entryVals (ys.map (·.1))) = v
  cases hr : roundRNE p emin emax v with
  | none => rfl
  | some r =>
    simp only [Option.map_some]
    by_cases hr0 : r = 0
    · subst hr0
      rw [if_neg (by simp), exactSignI_eq hmult hl hb hvanish, hv, Option.map_some]
      unfold sumNeg
      by_cases hz : v = 0
      · rw [if_pos ((sgnQ_eq_zero_iff v).mpr hz), if_pos hz]
      · rw [if_neg (fun h => hz ((sgnQ_eq_zero_iff v).mp h)), if_neg hz]
        congr 2
        exact decide_eq_decide.mpr (sgnQ_neg_iff v)
    · rw [if_pos hr0]
      obtain ⟨hv0, hsign⟩ := sign_of_round (roundRNE_nearest hp hle) (roundRNE_zero' p emin emax)
        hr hr0
      unfold sumNeg
      rw [if_neg hv0, hsign]

namespace Checked

variable (B : Widths)

/-- **The sign step with every integer guarded.** -/
def signStepC (mult : MatrixMultiplier) (b smax : ℕ) (r : Option ℚ) (xs ys : List SEntry) :
    Option (Option Signed) :=
  match r with
  | none => pure none
  | some r =>
    if r ≠ 0 then pure (some ⟨r, decide (r < 0)⟩)
    else do
      let sg ← exactSignIC B mult b smax (xs.map (·.1)) (ys.map (·.1))
      match sg with
      | none => pure none
      | some sg => do
        let z ← allNegZeroIC B xs ys
        pure (some ⟨0, if sg = 0 then z else decide (sg < 0)⟩)

/-- **Correctly rounded Ozaki-II in integers with signed zeros, every integer guarded.** -/
def ozaki2CRJSC (mult : MatrixMultiplier) (p : ℕ) (emin emax : ℤ) (cfgs : List (CRTBasis × ℕ)) (b smax : ℕ)
    (xs ys : List SEntry) : Option (Option Signed) := do
  let r ← ozaki2CRJC B mult p emin emax cfgs b smax (xs.map (·.1)) (ys.map (·.1))
  signStepC B mult b smax r xs ys

end Checked

open Checked

/-- **The checked sign step never fails a guard.** -/
theorem signStepC_eq {B : Widths} {mult : MatrixMultiplier} {b bound : ℕ} (hmult : mult.ExactOn b bound)
    {p EM smax : ℕ} {emin emax : ℤ} {xs ys : List SEntry} (hlen : xs.length = ys.length)
    (hbound : xs.length * (2 ^ b * 2 ^ b) ≤ bound) (hx : EntriesIn p EM (xs.map (·.1)))
    (hy : EntriesIn p EM (ys.map (·.1))) (hRe : exactR p smax bound ≤ B.R)
    (hRb : p + b + 3 ≤ B.R) (hR2 : 2 * p ≤ B.R)
    (hXe : exactX p b EM smax bound emin emax B.R < 2 ^ B.X) (r : Option ℚ) :
    signStepC B mult b smax r xs ys = some (signStep mult b smax r xs ys) := by
  have hl : (xs.map (·.1)).length = (ys.map (·.1)).length := by simp [hlen]
  have hb : (xs.map (·.1)).length * (2 ^ b * 2 ^ b) ≤ bound := by simpa using hbound
  unfold signStepC signStep
  cases r with
  | none => rfl
  | some r =>
    simp only
    split
    · rfl
    · rw [exactSignIC_eq hmult hl hb hx hy hRe hRb hXe]
      simp only [Option.bind_eq_bind, Option.bind_some]
      cases exactSignI mult b smax (xs.map (·.1)) (ys.map (·.1)) with
      | none => rfl
      | some sg =>
        simp only [Option.map_some]
        rw [allNegZeroIC_eq (p := p) hR2
          (fun a ha => (hx a.1 (List.mem_map_of_mem ha)).1)
          (fun a ha => (hy a.1 (List.mem_map_of_mem ha)).1)]
        rfl

/-- **Signed Ozaki-II, every integer bounded**: under the requirements of `ozaki2CRJC_eq` and
`R ≥ 2p`, the checked function returns exactly what `ozaki2CRJS` returns. -/
theorem ozaki2CRJSC_eq {B : Widths} {p : ℕ} {emin emax : ℤ} (hp : 0 < p) (hle : emin ≤ emax)
    {mult : MatrixMultiplier} {b bound : ℕ} (hmult : mult.ExactOn b bound) {EM smax : ℕ}
    {cfgs : List (CRTBasis × ℕ)} {xs ys : List SEntry} (hlen : xs.length = ys.length)
    (hbound : xs.length * (2 ^ b * 2 ^ b) ≤ bound) (hx : EntriesIn p EM (xs.map (·.1)))
    (hy : EntriesIn p EM (ys.map (·.1)))
    (hcfgC : ∀ c ∈ cfgs, (∀ m ∈ c.1.moduli, 0 < m ∧ m ≤ 2 ^ (b + 1)) ∧ 0 < c.1.modulus ∧
      crtSize c.1 < 2 ^ B.R ∧ 2 * c.1.modulus < 2 ^ B.R ∧ ozaki2R c.1 c.2 p xs.length ≤ B.R ∧
      ozaki2X c.1 c.2 p EM xs.length emin emax B.R < 2 ^ B.X)
    (hcfg : ∀ c ∈ cfgs, c.1.Valid ∧ (∀ m ∈ c.1.moduli, m ≤ 2 ^ (b + 1)) ∧
      2 * xs.length * (2 ^ c.2 * 2 ^ c.2) < c.1.modulus)
    (hRe : exactR p smax bound ≤ B.R) (hRb : p + b + 3 ≤ B.R) (hR2 : 2 * p ≤ B.R)
    (hXe : exactX p b EM smax bound emin emax B.R < 2 ^ B.X)
    (hvanish : ∃ s ∈ List.range' 1 smax, vanishInt b s (xs.map (·.1)) (ys.map (·.1)) = true) :
    ozaki2CRJSC B mult p emin emax cfgs b smax xs ys =
      some (ozaki2CRJS mult p emin emax cfgs b smax xs ys) := by
  have hl : (xs.map (·.1)).length = (ys.map (·.1)).length := by simp [hlen]
  have hb : (xs.map (·.1)).length * (2 ^ b * 2 ^ b) ≤ bound := by simpa using hbound
  have hlx : (xs.map (·.1)).length = xs.length := by simp
  unfold ozaki2CRJSC
  rw [ozaki2CRJC_eq hmult hl hb hx hy (by rw [hlx]; exact hcfgC) hRe hRb hXe]
  simp only [Option.bind_eq_bind, Option.bind_some]
  rw [signStepC_eq hmult hlen hbound hx hy hRe hRb hR2 hXe]
  congr 1
  have hv' : ∃ s ∈ List.range' 1 smax, residualsVanish b s (entryVals (xs.map (·.1)))
      (entryVals (ys.map (·.1))) = true :=
    hvanish.imp fun s h => ⟨h.1, by rw [← vanishInt_eq]; exact h.2⟩
  rw [ozaki2CRJS_eq hp hle hmult hcfg hlen hbound hv']
  exact signStep_eq hp hle hmult hlen hbound hvanish
    (ozaki2CRJ_eq hp hle hmult (by rw [hlx]; exact hcfg) hl hb hv')

/-- **Signed FP64 by Ozaki-II, every integer within 264 bits and every exponent and counter within
24 bits**: on binary64 entries, `k ≤ 2^20`, the twelve moduli at most `4096` with `P ≤ 69`,
`11`-bit slices and at most `175` slices on the exact fallback, the IEEE binary64 result with IEEE's
sign of zero. -/
theorem ozaki2CRJSC_binary64_eq {mult : MatrixMultiplier} {xs ys : List SEntry} {cfgs : List (CRTBasis × ℕ)}
    (hmult : mult.ExactOn 11 (xs.length * (2 ^ 11 * 2 ^ 11))) (hlen : xs.length = ys.length)
    (hk : xs.length ≤ 2 ^ 20) (hx : ∀ a ∈ xs, FormatEntry 53 (-1022) 1023 a.1)
    (hy : ∀ a ∈ ys, FormatEntry 53 (-1022) 1023 a.1)
    (hcfgs : ∀ c ∈ cfgs, c.1 = fp64Basis ∧ c.2 ≤ 69)
    (hrange : ∀ c ∈ cfgs, 2 * xs.length * (2 ^ c.2 * 2 ^ c.2) < c.1.modulus) :
    ozaki2CRJSC ⟨264, 24⟩ mult 53 (-1022) 1023 cfgs 11 175 xs ys =
      some (crSigned rne64 (xs.map toSigned) (ys.map toSigned)) := by
  have hE : ((-1022 : ℤ) - ((53 : ℕ) - 1 : ℤ)).natAbs ≤ 1074 ∧
      ((1023 : ℤ) - ((53 : ℕ) - 1 : ℤ)).natAbs ≤ 1074 := by decide
  have hx' : ∀ a ∈ xs.map (·.1), FormatEntry 53 (-1022) 1023 a := by
    intro a ha; obtain ⟨c, hc, rfl⟩ := List.mem_map.mp ha; exact hx c hc
  have hy' : ∀ a ∈ ys.map (·.1), FormatEntry 53 (-1022) 1023 a := by
    intro a ha; obtain ⟨c, hc, rfl⟩ := List.mem_map.mp ha; exact hy c hc
  have hlx : (xs.map (·.1)).length = xs.length := by simp
  have hl' : (xs.map (·.1)).length = (ys.map (·.1)).length := by simp [hlen]
  -- the checked unsigned value is `ozaki2CRJ`, by the unsigned instance
  have hu := ozaki2CRJC_binary64 (mult := mult) (xs := xs.map (·.1)) (ys := ys.map (·.1))
    (by rw [hlx]; exact hmult) hl' (by rw [hlx]; exact hk) hx' hy' hcfgs
  have hval := ozaki2CRJ64_eq (mult := mult) (cfgs := cfgs) (smax := 175) (xs := xs.map (·.1))
    (ys := ys.map (·.1)) hmult (by decide) (by decide) (fun c hc => by
      obtain ⟨h1, _⟩ := hcfgs c hc
      refine ⟨?_, ?_, by rw [hlx]; exact hrange c hc⟩
      · rw [h1]; decide +kernel
      · rw [h1]; exact fun m hm => (fp64Basis_facts.1 m hm).2) hl' (by rw [hlx]; exact Nat.le_refl _)
    (fun v hv => by obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hv; exact (hx' a ha).formatValue)
    (fun v hv => by obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hv; exact (hy' a ha).formatValue)
  have hbud := bitlen_dotAbsBound_le hk
  have hW : exactW 53 175 = 72 := by decide
  have hm1 : (-1022 : ℤ).natAbs = 1022 := by decide
  have hm2 : (1023 : ℤ).natAbs = 1023 := by decide
  unfold ozaki2CRJSC
  rw [hu]
  simp only [Option.bind_eq_bind, Option.bind_some]
  rw [signStepC_eq (emin := -1022) (emax := 1023) hmult hlen (Nat.le_refl _)
    (entriesIn_of_format hE hx') (entriesIn_of_format hE hy')
    (by unfold exactR; rw [hW]; have : bitlen (175 * 175 + 2) = 15 := by decide
        simp only; omega)
    (by decide) (by decide)
    (by unfold exactX; rw [hW]; simp only; omega)]
  congr 1
  exact signStep_eq (by decide) (by decide) hmult hlen (Nat.le_refl _)
    (vanishInt64 (by decide) (by decide)
      (fun a ha => by obtain ⟨c, hc, rfl⟩ := List.mem_map.mp ha; exact (hx c hc).formatValue)
      (fun a ha => by obtain ⟨c, hc, rfl⟩ := List.mem_map.mp ha; exact (hy c hc).formatValue))
    hval

end Ozaki
