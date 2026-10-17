import Ozaki.Basic

/-! # Chinese remainder reconstruction

Ozaki-II computes an integer product `C' = A'B'` modulo several pairwise coprime moduli and
recovers it with the Chinese remainder theorem. This file defines symmetric residues, a CRT basis
(moduli with weights `wₗ ≡ 1 (mod mₗ)`, `wₗ ≡ 0 (mod mⱼ)` for `j ≠ l`), and proves that
reconstruction returns every integer `c` with `−M < 2c ≤ M`, `M = Π mₗ`, from any residues
congruent to `c` (`crt_eq`). Weights are computed by the extended Euclidean algorithm; whether a
computed basis is valid is decidable, so concrete moduli are checked by the kernel
(`Ozaki.Parameters`). -/

local notation "ℕ" => Nat
local notation "ℤ" => Int
local notation "ℚ" => Rat

namespace Ozaki

/-! ## Symmetric residues -/

/-- `x mod m` in the symmetric range `(−m/2, m/2]`. -/
def symMod (x : ℤ) (m : ℕ) : ℤ :=
  if 2 * (x % (m : ℤ)) > m then x % (m : ℤ) - m else x % (m : ℤ)

theorem symMod_dvd (x : ℤ) (m : ℕ) : (m : ℤ) ∣ x - symMod x m := by
  have h := Int.emod_def x m
  unfold symMod
  split
  · exact ⟨x / m + 1, by rw [h]; grind⟩
  · exact ⟨x / m, by rw [h]; grind⟩

theorem symMod_bounds (x : ℤ) {m : ℕ} (hm : 0 < m) :
    -(m : ℤ) < 2 * symMod x m ∧ 2 * symMod x m ≤ m := by
  have h1 := Int.emod_nonneg x (show (m : ℤ) ≠ 0 by omega)
  have h2 := Int.emod_lt_of_pos x (show (0 : ℤ) < m by omega)
  unfold symMod
  split <;> omega

theorem natAbs_symMod_le (x : ℤ) {m : ℕ} (hm : 0 < m) : 2 * (symMod x m).natAbs ≤ m := by
  have := symMod_bounds x hm
  omega

/-- Congruent integers have the same symmetric residue. -/
theorem symMod_congr {x y : ℤ} {m : ℕ} (h : (m : ℤ) ∣ x - y) : symMod x m = symMod y m := by
  have he : x % (m : ℤ) = y % (m : ℤ) :=
    Int.emod_eq_emod_iff_emod_sub_eq_zero.mpr (Int.dvd_iff_emod_eq_zero.mp h)
  unfold symMod
  rw [he]

/-- An integer in the symmetric range is its own residue. -/
theorem symMod_eq_self {x : ℤ} {m : ℕ} (h1 : -(m : ℤ) < 2 * x) (h2 : 2 * x ≤ m) :
    symMod x m = x := by
  unfold symMod
  by_cases hx : 0 ≤ x
  · have hlt : x < m := by omega
    have : x % (m : ℤ) = x := Int.emod_eq_of_lt hx hlt
    rw [this, if_neg (by omega)]
  · have hm : (0 : ℤ) < m := by omega
    have : x % (m : ℤ) = x + m := by
      have := Int.emod_eq_of_lt (a := x + m) (b := m) (by omega) (by omega)
      rw [← this, Int.add_emod_right]
    rw [this, if_pos (by omega)]
    omega

/-! ## Products of moduli -/

/-- Pairwise coprime moduli that all divide `z` have a product that divides `z`. -/
theorem prod_dvd_of_pairwise_coprime :
    ∀ (ms : List ℕ), ms.Pairwise Nat.Coprime → ∀ z : ℤ, (∀ m ∈ ms, (m : ℤ) ∣ z) →
      ((ms.prod : ℕ) : ℤ) ∣ z
  | [], _, z, _ => by simp
  | m :: ms, hp, z, hd => by
    rw [List.pairwise_cons] at hp
    have hrest := prod_dvd_of_pairwise_coprime ms hp.2 z (fun m' h => hd m' (by simp [h]))
    have hcop : Nat.Coprime m ms.prod := by
      clear hd hrest
      induction ms with
      | nil => exact Nat.coprime_one_right m
      | cons a as ih =>
        rw [List.prod_cons]
        exact Nat.Coprime.mul_right (hp.1 a (by simp))
          (ih ⟨fun a' h => hp.1 a' (by simp [h]), (List.pairwise_cons.mp hp.2).2⟩)
    rw [List.prod_cons, Int.ofNat_dvd_left]
    exact Nat.Coprime.mul_dvd_of_dvd_of_dvd hcop (Int.ofNat_dvd_left.mp (hd m (by simp)))
      (Int.ofNat_dvd_left.mp hrest)

/-! ## CRT bases -/

/-- Moduli with reconstruction weights. -/
structure CRTBasis where
  moduli : List ℕ
  weights : List ℤ
  deriving Repr, DecidableEq

/-- `M = Π mₗ`. -/
def CRTBasis.modulus (B : CRTBasis) : ℕ := B.moduli.prod

/-- Pairwise coprime positive moduli whose weights satisfy `wₗ ≡ [l = j] (mod mⱼ)`. -/
def CRTBasis.Valid (B : CRTBasis) : Prop :=
  B.weights.length = B.moduli.length ∧ (∀ m ∈ B.moduli, 0 < m) ∧ B.moduli.Pairwise Nat.Coprime ∧
    ∀ l j : Fin B.moduli.length,
      (B.moduli[j] : ℤ) ∣ B.weights.getD l 0 - if l = j then 1 else 0

instance (B : CRTBasis) : Decidable B.Valid := by
  unfold CRTBasis.Valid
  exact inferInstance

/-- Reconstruction from residues: `Σ wₗ rₗ` in the symmetric range modulo `M`. -/
def crt (B : CRTBasis) (rs : List ℤ) : ℤ := symMod (dotZ B.weights rs) B.modulus

/-- A weighted sum that is `1` against residue `j` and `0` against the others picks residue `j`
modulo `m`. -/
theorem dvd_dotZ_sub (m : ℤ) :
    ∀ (ws rs : List ℤ) (j : ℕ), ws.length = rs.length → j < ws.length →
      (∀ l < ws.length, m ∣ ws.getD l 0 - if l = j then 1 else 0) →
      m ∣ dotZ ws rs - rs.getD j 0
  | [], _, _, _, hj, _ => by simp at hj
  | _ :: _, [], _, hl, _, _ => by simp at hl
  | w :: ws, r :: rs, j, hl, hj, hw => by
    simp only [dotZ_cons]
    cases j with
    | zero =>
      have h0 := hw 0 (by simp)
      simp only [List.getD_cons_zero, if_pos] at h0
      have hrest : m ∣ dotZ ws rs := by
        have hall : ∀ l < ws.length, m ∣ ws.getD l 0 := by
          intro l hl'
          have := hw (l + 1) (by simp; omega)
          simpa using this
        clear hw h0 hj
        induction ws generalizing rs with
        | nil => simp
        | cons w' ws' ih =>
          cases rs with
          | nil => simp
          | cons r' rs' =>
            simp only [dotZ_cons]
            have h1 : m ∣ w' := by simpa using hall 0 (by simp)
            exact Int.dvd_add (Int.dvd_trans h1 (Int.dvd_mul_right w' r'))
              (ih rs' (by simpa using hl) (fun l hl' => by simpa using hall (l + 1) (by simp; omega)))
      have : w * r + dotZ ws rs - (r :: rs).getD 0 0 = (w - 1) * r + dotZ ws rs := by
        simp only [List.getD_cons_zero]; rw [Int.sub_mul, Int.one_mul]; omega
      rw [this]
      exact Int.dvd_add (Int.dvd_trans h0 (Int.dvd_mul_right _ r)) hrest
    | succ j =>
      have h0 : m ∣ w := by simpa using hw 0 (by simp)
      have ih := dvd_dotZ_sub m ws rs j (by simpa using hl) (by simpa using hj)
        (fun l hl' => by simpa using hw (l + 1) (by simp; omega))
      have : w * r + dotZ ws rs - (r :: rs).getD (j + 1) 0 = w * r + (dotZ ws rs - rs.getD j 0) := by
        simp only [List.getD_cons_succ]; omega
      rw [this]
      exact Int.dvd_add (Int.dvd_trans h0 (Int.dvd_mul_right w r)) ih

/-- **Chinese remainder reconstruction.** With a valid basis, residues `rₗ ≡ c (mod mₗ)` give back
every `c` with `−M < 2c ≤ M`. -/
theorem crt_eq {B : CRTBasis} (hB : B.Valid) {rs : List ℤ} (hlen : rs.length = B.moduli.length)
    {c : ℤ} (hres : ∀ j : Fin B.moduli.length, (B.moduli[j] : ℤ) ∣ rs.getD j 0 - c)
    (h1 : -(B.modulus : ℤ) < 2 * c) (h2 : 2 * c ≤ B.modulus) : crt B rs = c := by
  obtain ⟨hwl, _, hcop, hw⟩ := hB
  unfold crt
  rw [← symMod_eq_self h1 h2]
  apply symMod_congr
  apply prod_dvd_of_pairwise_coprime B.moduli hcop
  intro m hm
  obtain ⟨j, hj, hjm⟩ := List.getElem_of_mem hm
  have hsel := dvd_dotZ_sub (B.moduli[j] : ℤ) B.weights rs j (by rw [hwl, hlen])
    (by rw [hwl]; exact hj)
    (fun l hl => hw ⟨l, by rw [← hwl]; exact hl⟩ ⟨j, hj⟩ |> fun h => by
      simpa [Fin.ext_iff] using h)
  have hr := hres ⟨j, hj⟩
  rw [← hjm]
  have : dotZ B.weights rs - c = (dotZ B.weights rs - rs.getD j 0) + (rs.getD j 0 - c) := by omega
  rw [this]
  exact Int.dvd_add hsel hr

/-! ## Computing a basis -/

/-- Extended Euclid with fuel: `(g, s, t)` with `s a + t b = g = gcd a b` when the fuel suffices. -/
def xgcdFuel : ℕ → ℤ → ℤ → ℤ × ℤ × ℤ
  | 0, a, _ => (a, 1, 0)
  | fuel + 1, a, b =>
    if b = 0 then (a, 1, 0)
    else
      let (g, s, t) := xgcdFuel fuel b (a % b)
      (g, t, s - (a / b) * t)

/-- An inverse of `a` modulo `m` (`0` if `a` is not invertible). -/
def invMod (a m : ℕ) : ℤ := ((xgcdFuel (m + 1) a m).2.1) % m

/-- The standard basis `wₗ = (M / mₗ) · ((M / mₗ)⁻¹ mod mₗ)`. -/
def crtBasis (ms : List ℕ) : CRTBasis :=
  ⟨ms, ms.map fun m => ((ms.prod / m : ℕ) : ℤ) * invMod (ms.prod / m) m⟩

end Ozaki
