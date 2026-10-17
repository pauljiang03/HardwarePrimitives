import Ozaki.CRT

/-! # Every computed CRT basis of pairwise coprime moduli is valid

`crtBasis ms` computes the weights `wₗ = (M / mₗ) · ((M / mₗ)⁻¹ mod mₗ)` with the extended Euclidean
algorithm (`xgcdFuel`, `invMod`). Whether a basis is valid is decidable, and so far concrete bases
were checked by the kernel one by one (`Ozaki.Parameters`, `OzakiTC.Ozaki2Choice`). Here it is
proved once for all moduli:

* `xgcdFuel_spec`: with enough fuel the extended Euclidean algorithm returns `(g, s, t)` with
  `s a + t b = g`, `g ≥ 0`, and `g` dividing `a` and `b`;
* `invMod_spec`: for `a` coprime to `m`, `invMod a m · a ≡ 1 (mod m)`;
* `crtBasis_valid`: for positive pairwise coprime moduli, `crtBasis ms` is valid, so `crt_eq`
  reconstructs with it. In particular every basis of the moduli rule is valid
  (`moduliBasis_valid_all` in `Ozaki.SliceRuleCR`). -/

local notation "ℕ" => Nat
local notation "ℤ" => Int
local notation "ℚ" => Rat

namespace Ozaki

/-! ## The extended Euclidean algorithm -/

/-- **Extended Euclid.** For `a, b ≥ 0` and fuel above `b`, `xgcdFuel fuel a b = (g, s, t)` with
`s a + t b = g`, `0 ≤ g`, `g ∣ a` and `g ∣ b`. -/
theorem xgcdFuel_spec : ∀ (fuel : ℕ) (a b : ℤ), 0 ≤ a → 0 ≤ b → b < fuel →
    (xgcdFuel fuel a b).2.1 * a + (xgcdFuel fuel a b).2.2 * b = (xgcdFuel fuel a b).1 ∧
      0 ≤ (xgcdFuel fuel a b).1 ∧ (xgcdFuel fuel a b).1 ∣ a ∧ (xgcdFuel fuel a b).1 ∣ b
  | 0, _, b, _, hb, hf => by omega
  | fuel + 1, a, b, ha, hb, hf => by
    unfold xgcdFuel
    by_cases hb0 : b = 0
    · subst hb0
      simp only [if_true]
      exact ⟨by simp, ha, Int.dvd_refl a, Int.dvd_zero a⟩
    · rw [if_neg hb0]
      have hbpos : 0 < b := by omega
      have hm0 : 0 ≤ a % b := Int.emod_nonneg a hb0
      have hm1 : a % b < b := Int.emod_lt_of_pos a hbpos
      obtain ⟨h1, h2, h3, h4⟩ := xgcdFuel_spec fuel b (a % b) hb hm0 (by omega)
      generalize xgcdFuel fuel b (a % b) = r at h1 h2 h3 h4
      obtain ⟨g, s, t⟩ := r
      simp only at h1 h2 h3 h4 ⊢
      have hdiv : a = b * (a / b) + a % b := (Int.mul_ediv_add_emod a b).symm
      refine ⟨?_, h2, ?_, h3⟩
      · have : a % b = a - b * (a / b) := by omega
        rw [this] at h1
        rw [← h1, Int.sub_mul, Int.mul_sub]
        simp only [Int.mul_comm, Int.mul_left_comm]
        omega
      · rw [hdiv]
        exact Int.dvd_add (Int.dvd_trans h3 (Int.dvd_mul_right b _)) h4

/-- **The modular inverse.** For `a` coprime to `m ≥ 1`, `m ∣ invMod a m · a − 1`. -/
theorem invMod_spec {a m : ℕ} (hm : 0 < m) (hcop : Nat.Coprime a m) :
    (m : ℤ) ∣ invMod a m * a - 1 := by
  obtain ⟨h1, h2, h3, h4⟩ := xgcdFuel_spec (m + 1) (a : ℤ) (m : ℤ) (by omega) (by omega) (by omega)
  generalize hr : xgcdFuel (m + 1) (a : ℤ) (m : ℤ) = r at h1 h2 h3 h4
  obtain ⟨g, s, t⟩ := r
  simp only at h1 h2 h3 h4
  -- `g` divides `a` and `m`, which are coprime, so `g = 1`
  have hg : g = 1 := by
    have ha := Int.natAbs_dvd_natAbs.mpr h3
    have hmm := Int.natAbs_dvd_natAbs.mpr h4
    simp only [Int.natAbs_natCast] at ha hmm
    have hd := Nat.dvd_gcd ha hmm
    rw [hcop] at hd
    have : g.natAbs = 1 := Nat.eq_one_of_dvd_one hd
    omega
  subst hg
  unfold invMod
  rw [hr]
  simp only
  have hmod : s % (m : ℤ) = s - (m : ℤ) * (s / (m : ℤ)) := by
    have := Int.mul_ediv_add_emod s (m : ℤ); omega
  rw [hmod]
  have : (s - (m : ℤ) * (s / (m : ℤ))) * (a : ℤ) - 1 =
      (m : ℤ) * (-t - (s / (m : ℤ)) * (a : ℤ)) := by
    rw [Int.mul_sub, Int.sub_mul, Int.mul_neg]
    have h1' : s * (a : ℤ) = 1 - t * (m : ℤ) := by omega
    rw [h1']
    simp only [Int.mul_comm, Int.mul_left_comm]
    omega
  rw [this]
  exact Int.dvd_mul_right _ _

/-! ## Products of pairwise coprime moduli -/

theorem mem_dvd_prod : ∀ {l : List ℕ} {a : ℕ}, a ∈ l → a ∣ l.prod
  | [], _, h => by simp at h
  | c :: l, a, h => by
    rw [List.prod_cons]
    rcases List.mem_cons.mp h with rfl | h
    · exact Nat.dvd_mul_right _ _
    · exact Nat.dvd_trans (mem_dvd_prod h) (Nat.dvd_mul_left _ _)

theorem coprime_prod_left : ∀ {l : List ℕ} {a : ℕ}, (∀ c ∈ l, Nat.Coprime c a) →
    Nat.Coprime l.prod a
  | [], _, _ => by simp
  | c :: l, a, h => by
    rw [List.prod_cons]
    exact Nat.Coprime.mul_left (h c (by simp)) (coprime_prod_left fun c' hc => h c' (by simp [hc]))

/-- The product of the moduli other than `mᵢ` is coprime to `mᵢ`. -/
theorem prod_div_coprime : ∀ {ms : List ℕ}, (∀ m ∈ ms, 0 < m) → ms.Pairwise Nat.Coprime →
    ∀ (i : ℕ) (hi : i < ms.length), Nat.Coprime (ms.prod / ms[i]) ms[i]
  | [], _, _, _, hi => by simp at hi
  | a :: rest, hpos, hp, 0, _ => by
    simp only [List.getElem_cons_zero, List.prod_cons]
    rw [Nat.mul_div_cancel_left _ (hpos a (by simp))]
    obtain ⟨ha, _⟩ := List.pairwise_cons.mp hp
    exact coprime_prod_left fun c hc => Nat.Coprime.symm (ha c hc)
  | a :: rest, hpos, hp, i + 1, hi => by
    simp only [List.getElem_cons_succ, List.prod_cons]
    obtain ⟨ha, hrest⟩ := List.pairwise_cons.mp hp
    have hi' : i < rest.length := by simpa using hi
    have hm : rest[i] ∣ rest.prod := mem_dvd_prod (List.getElem_mem hi')
    rw [Nat.mul_div_assoc a hm]
    exact Nat.Coprime.mul_left (ha _ (List.getElem_mem hi'))
      (prod_div_coprime (fun m hm => hpos m (by simp [hm])) hrest i hi')

/-- Every other modulus divides the product of the moduli other than `mᵢ`. -/
theorem dvd_prod_div : ∀ {ms : List ℕ}, (∀ m ∈ ms, 0 < m) →
    ∀ (i j : ℕ) (hi : i < ms.length) (hj : j < ms.length), i ≠ j → ms[j] ∣ ms.prod / ms[i]
  | [], _, _, _, hi, _, _ => by simp at hi
  | a :: rest, hpos, 0, 0, _, _, hij => absurd rfl hij
  | a :: rest, hpos, 0, j + 1, _, hj, _ => by
    simp only [List.getElem_cons_zero, List.getElem_cons_succ, List.prod_cons]
    rw [Nat.mul_div_cancel_left _ (hpos a (by simp))]
    exact mem_dvd_prod (List.getElem_mem _)
  | a :: rest, hpos, i + 1, 0, hi, _, _ => by
    simp only [List.getElem_cons_zero, List.getElem_cons_succ, List.prod_cons]
    have hi' : i < rest.length := by simpa using hi
    rw [Nat.mul_div_assoc a (mem_dvd_prod (List.getElem_mem hi'))]
    exact Nat.dvd_mul_right _ _
  | a :: rest, hpos, i + 1, j + 1, hi, hj, hij => by
    simp only [List.getElem_cons_succ, List.prod_cons]
    have hi' : i < rest.length := by simpa using hi
    have hj' : j < rest.length := by simpa using hj
    rw [Nat.mul_div_assoc a (mem_dvd_prod (List.getElem_mem hi'))]
    exact Nat.dvd_trans (dvd_prod_div (fun m hm => hpos m (by simp [hm])) i j hi' hj' (by omega))
      (Nat.dvd_mul_left _ _)

/-! ## Validity -/

/-- **Every computed basis of positive pairwise coprime moduli is valid.** -/
theorem crtBasis_valid {ms : List ℕ} (hpos : ∀ m ∈ ms, 0 < m) (hcop : ms.Pairwise Nat.Coprime) :
    (crtBasis ms).Valid := by
  refine ⟨by simp [crtBasis], hpos, hcop, ?_⟩
  intro l j
  have hl : (l : ℕ) < ms.length := l.isLt
  have hj : (j : ℕ) < ms.length := j.isLt
  have hw : (crtBasis ms).weights.getD l 0 =
      ((ms.prod / ms[(l : ℕ)] : ℕ) : ℤ) * invMod (ms.prod / ms[(l : ℕ)]) ms[(l : ℕ)] := by
    simp [crtBasis, List.getD_eq_getElem?_getD, hl]
  show ((ms[(j : ℕ)] : ℕ) : ℤ) ∣ (crtBasis ms).weights.getD l 0 - if l = j then 1 else 0
  rw [hw]
  by_cases hlj : l = j
  · subst hlj
    rw [if_pos rfl, Int.mul_comm]
    exact invMod_spec (hpos _ (List.getElem_mem hl)) (prod_div_coprime hpos hcop l hl)
  · rw [if_neg hlj, Int.sub_zero]
    have hne : (l : ℕ) ≠ (j : ℕ) := fun h => hlj (Fin.ext h)
    exact Int.dvd_trans (Int.natCast_dvd_natCast.mpr (dvd_prod_div hpos l j hl hj hne))
      (Int.dvd_mul_right _ _)

end Ozaki
