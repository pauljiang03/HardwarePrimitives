import Ozaki.AbdelfattahCarry

/-! # The spare-carry recursion: one-bit slices, and how it compares with `diagFits`

`Ozaki.AbdelfattahCarry` formalizes Abdelfattah et al.'s spare-carry recursion (4.20)–(4.22) and
proves its count reading sound for slices of `t ≥ 2` bits. This file closes the two remaining
questions.

* **Soundness for every slice width `t ≥ 1`.** For one-bit slices (`c = 2^t = 2`) the bound of the
  `t ≥ 2` proof is too weak, but the level's magnitude has the closed form
  `S(K, Q) + (K + Q + 2) = 2^Q (K + 2)` (`afS_two`), and the spare-carry term `−η` grows fast enough
  once `K ≥ 3` or `Q ≥ 3`; the remaining four levels are checked (`afS_lt_one`). So every level the
  recursion accepts sums exactly, for every `t ≥ 1` (`afAccept_diagFits_pos`,
  `afAccept_levelExact_pos`).
* **How it compares with the sum-of-magnitudes condition `diagFits`.** The recursion never
  accepts more diagonals than `diagFits` (soundness). It accepts strictly fewer
  - at the first level (`K = 0`) for every `t ≥ 2`, whenever anything fits (`T′ < p`): `diagFits`
    accepts one diagonal more than the largest count the recursion accepts
    (`af_diagFits_succ_zero`, `af_strict_zero`);
  - at every level starting at `K ≥ 4 · 2^t − 1`, for every `t ≥ 2`, whenever the recursion accepts
    a diagonal there: again one more (`af_diagFits_succ_late`, `af_strict_late`). There the
    spare-carry term `−η ≥ K + 1 − 2^t` (`afM_ge`) overpays for the level's first diagonal.

  In between, and for `t = 1`, the two can coincide. Kernel-checked witnesses: INT8 slices with
  `T′ = 31` and binary64, where both accept exactly three diagonals at every level start `K = 1 …
  126` (`af_int8_coincide`; at `K = 0` and from `K = 127` the magnitude condition accepts more);
  `11`-bit fp16 slices with `T′ = 32`, where both accept one diagonal for `K = 511 … 599`, while
  `diagFits` accepts two up to `K = 510` (`af_fp16_coincide`); two-bit slices at `K = 1`
  (`af_t2_coincide`, against `af_t2_late` at `K = 15`); and one-bit slices at `K = 0`
  (`af_t1_coincide`), so the condition `t ≥ 2` of the first-level statement is needed. The exact
  set where the two coincide depends on all of `p`, `T′`, `t` and `K`; no closed form is claimed
  for it. -/

local notation "ℕ" => Nat
local notation "ℤ" => Int
local notation "ℚ" => Rat

namespace Ozaki

/-! ## Soundness for one-bit slices -/

/-- With `c = 2`: `S(K, Q) + (K + Q + 2) = 2^Q (K + 2)`. -/
theorem afS_two (K Q : ℕ) : afS 2 K Q + (K + Q + 2) = 2 ^ Q * (K + 2) := by
  have h := afS_identity 1 K Q
  simp only [Nat.mul_one, Nat.one_mul] at h
  rw [show (1 + 1 : ℕ) = 2 from rfl, show K + 1 + 1 = K + 2 by omega] at h
  omega

/-- **The one-bit level against the recursion's budget**: `S(K, Q) < 2 · 2^Q · max{1, −η}`. -/
theorem afS_lt_one (K Q : ℕ) (hQ : 1 ≤ Q) :
    afS 2 K Q < 2 * 2 ^ Q * (max 1 (-afEta 1 K (K + Q))).toNat := by
  have hid := afS_two K Q
  by_cases hsmall : 1 ≤ K ∧ K ≤ 2 ∧ Q ≤ 2
  · obtain ⟨h1, h2, h3⟩ := hsmall
    rcases (show K = 1 ∨ K = 2 by omega) with rfl | rfl <;>
      rcases (show Q = 1 ∨ Q = 2 by omega) with rfl | rfl <;> decide +kernel
  have hm1 := one_le_afM 1 K (K + Q)
  have hc := afEta_closed (t := 1) (show K ≤ K + Q by omega)
  rw [show K + Q + 1 - K = Q + 1 by omega, show ((2 ^ (1 + 1) : ℕ) : ℤ) = 4 by decide] at hc
  generalize hE : afEta 1 K (K + Q) = E at hc hm1 ⊢
  push_cast at hc
  by_cases hK0 : K = 0
  · subst hK0
    simp only [Nat.zero_add] at hid
    have : 2 * 2 ^ Q * 1 ≤ 2 * 2 ^ Q * (max 1 (-E)).toNat := Nat.mul_le_mul_left _ hm1
    omega
  -- `−2η = (Q + 1)(2K + Q − 4)`
  have hc2 : -2 * E = ((Q : ℤ) + 1) * (2 * K + Q - 4) := by
    rw [show -2 * E = -(2 * E) by omega, hc]
    grind
  -- so `K + 2 ≤ 2 max{1, −η}`
  have key : (K : ℤ) + 2 ≤ 2 * max 1 (-E) := by
    have hmx : -E ≤ max 1 (-E) := Int.le_max_right _ _
    by_cases hK3 : 3 ≤ K
    · have hY : (2 : ℤ) ≤ (Q : ℤ) + 1 := by omega
      have hX : (0 : ℤ) ≤ 2 * K + Q - 4 := by omega
      have hprod := Int.mul_le_mul_of_nonneg_right hY hX
      generalize ((Q : ℤ) + 1) * (2 * K + Q - 4) = P at hprod hc2
      omega
    · have hQ3 : 3 ≤ Q := by omega
      have hY : (4 : ℤ) ≤ (Q : ℤ) + 1 := by omega
      have hX : (0 : ℤ) ≤ 2 * K + Q - 4 := by omega
      have hprod := Int.mul_le_mul_of_nonneg_right hY hX
      generalize ((Q : ℤ) + 1) * (2 * K + Q - 4) = P at hprod hc2
      omega
  generalize hm : (max 1 (-E)) = M at key hm1 ⊢
  have key' : K + 2 ≤ 2 * M.toNat := by omega
  have hmul : 2 ^ Q * (K + 2) ≤ 2 ^ Q * (2 * M.toNat) := Nat.mul_le_mul_left _ key'
  have e : 2 ^ Q * (2 * M.toNat) = 2 * 2 ^ Q * M.toNat := by grind
  omega

/-- **The recursion is sound for one-bit slices**: an accepted level of `Q ≥ 1` diagonals satisfies
the sum-of-magnitudes condition. -/
theorem afAccept_diagFits_one {p Tp K Q : ℕ} (hQ : 1 ≤ Q) (h : afAccept p Tp 1 K Q = true) :
    diagFits p (2 ^ Tp) 1 K Q = true := by
  unfold afAccept at h
  rw [decide_eq_true_iff] at h
  unfold diagFits
  rw [decide_eq_true_iff, diagSum_eq_afS]
  have hS := afS_lt_one K Q hQ
  have hme := le_two_pow_afExtra 1 K (K + Q)
  generalize (max 1 (-afEta 1 K (K + Q))).toNat = m at hS hme
  have hpow : 2 ^ Tp * (2 * 2 ^ Q * m) ≤ 2 ^ p := by
    calc 2 ^ Tp * (2 * 2 ^ Q * m) ≤ 2 ^ Tp * (2 * 2 ^ Q * 2 ^ afExtra 1 K (K + Q)) :=
          Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ hme)
      _ = 2 ^ (Tp + Q * 1 + 1 + afExtra 1 K (K + Q)) := by
          rw [Nat.mul_one, Nat.pow_add, Nat.pow_add, Nat.pow_add, Nat.pow_one]
          grind
      _ ≤ 2 ^ p := Nat.pow_le_pow_right (by decide) h
  have hpos : 0 < 2 ^ Tp := Nat.two_pow_pos Tp
  calc 2 ^ Tp * afS (2 ^ 1) K Q = 2 ^ Tp * afS 2 K Q := rfl
    _ < 2 ^ Tp * (2 * 2 ^ Q * m) := Nat.mul_lt_mul_of_pos_left hS hpos
    _ ≤ 2 ^ p := hpow

/-- **The recursion's count reading is sound for every slice width `t ≥ 1`.** -/
theorem afAccept_diagFits_pos {p Tp t K Q : ℕ} (ht : 1 ≤ t) (hQ : 1 ≤ Q)
    (h : afAccept p Tp t K Q = true) : diagFits p (2 ^ Tp) t K Q = true := by
  rcases Nat.lt_or_ge t 2 with h1 | h2
  · obtain rfl : t = 1 := by omega
    exact afAccept_diagFits_one hQ h
  · exact afAccept_diagFits h2 hQ h

/-- **A level the recursion accepts adds up exactly**, for every slice width `t ≥ 1`. -/
theorem afAccept_levelExact_pos {p Tp t K Q : ℕ} {emin emax G0 : ℤ} (ht : 1 ≤ t) (hQ : 1 ≤ Q)
    (h : afAccept p Tp t K Q = true) (diags : ℕ → List ℚ)
    (hg : ∀ d ∈ List.range' K Q, ∀ x ∈ diags d, GridMultiple (G0 - (d : ℤ) * t) x)
    (hb : ∀ d ∈ List.range' K Q,
      ((diags d).map Rat.abs).sum ≤ ((d + 1 : ℕ) : ℚ) * (2 ^ Tp : ℕ) * 2 ^ (G0 - (d : ℤ) * t))
    (h1 : emin ≤ G0 - ((K + Q - 1 : ℕ) : ℤ) * t + ((p : ℤ) - 1))
    (h2 : G0 - ((K + Q - 1 : ℕ) : ℤ) * t + ((p : ℤ) - 1) ≤ emax) :
    LevelExact p emin emax (G0 - ((K + Q - 1 : ℕ) : ℤ) * t) ((List.range' K Q).flatMap diags) :=
  level_exact_of_diagonals diags hg hb (diagFits_spec (afAccept_diagFits_pos ht hQ h)) h1 h2

/-! ## The largest accepted count is largest -/

theorem afQAux_ge {p Tp t K : ℕ} :
    ∀ n Q : ℕ, 1 ≤ Q → Q ≤ n → afAccept p Tp t K Q = true → Q ≤ afQAux p Tp t K n
  | 0, Q, h1, h2, _ => by omega
  | n + 1, Q, h1, h2, hQ => by
    unfold afQAux
    split
    · omega
    · rename_i hn
      by_cases hQn : Q = n + 1
      · subst hQn; exact absurd hQ hn
      · exact afQAux_ge n Q h1 (by omega) hQ

/-- `afQ` is the largest count the recursion accepts. -/
theorem afQ_max {p Tp t K Q : ℕ} (ht : 1 ≤ t) (hQ1 : 1 ≤ Q) (h : afAccept p Tp t K Q = true) :
    Q ≤ afQ p Tp t K :=
  afQAux_ge p Q hQ1 (afAccept_le ht h) h

/-- One diagonal more than `afQ` is rejected. -/
theorem afAccept_afQ_succ {p Tp t K : ℕ} (ht : 1 ≤ t) :
    afAccept p Tp t K (afQ p Tp t K + 1) = false := by
  cases h : afAccept p Tp t K (afQ p Tp t K + 1) with
  | false => rfl
  | true =>
    have := afQ_max ht (by omega) h
    omega

/-! ## Where the sum-of-magnitudes condition accepts strictly more -/

/-- **At the first level, one diagonal more**: for `t ≥ 2`, whenever the recursion accepts `Q`
diagonals at `K = 0` (any `Q`, `0` included), `diagFits` accepts `Q + 1`. -/
theorem af_diagFits_succ_zero {p Tp t Q : ℕ} (ht : 2 ≤ t) (h : afAccept p Tp t 0 Q = true) :
    diagFits p (2 ^ Tp) t 0 (Q + 1) = true := by
  unfold afAccept at h
  rw [decide_eq_true_iff] at h
  unfold diagFits
  rw [decide_eq_true_iff, diagSum_eq_afS]
  obtain ⟨d, hd⟩ : ∃ d, 2 ^ t = d + 1 := ⟨2 ^ t - 1, by have := Nat.one_le_two_pow (n := t); omega⟩
  have h4 : 4 ≤ 2 ^ t := by
    calc 4 = 2 ^ 2 := rfl
      _ ≤ 2 ^ t := Nat.pow_le_pow_right (by decide) ht
  have hd3 : 3 ≤ d := by omega
  have hpos : 0 < 2 ^ Tp := Nat.two_pow_pos Tp
  have hS : afS (d + 1) 0 (Q + 1) < 2 * (d + 1) ^ Q := by
    have h1 := afS_mul_lt d 0 (Q + 1)
    rw [Nat.pow_succ, show (0 + 1) * d + 1 = d + 1 by omega] at h1
    have hsq : (d + 1) * (d + 1) ≤ 2 * (d * d) := by
      have h3 : 3 * d ≤ d * d := Nat.mul_le_mul_right d hd3
      have e : (d + 1) * (d + 1) = d * d + 2 * d + 1 := by grind
      omega
    have h2 : (d + 1) ^ Q * (d + 1) * (d + 1) ≤ 2 * (d + 1) ^ Q * (d * d) := by
      calc (d + 1) ^ Q * (d + 1) * (d + 1) = (d + 1) ^ Q * ((d + 1) * (d + 1)) :=
            Nat.mul_assoc _ _ _
        _ ≤ (d + 1) ^ Q * (2 * (d * d)) := Nat.mul_le_mul_left _ hsq
        _ = 2 * (d + 1) ^ Q * (d * d) := by grind
    exact Nat.lt_of_mul_lt_mul_right (Nat.lt_of_lt_of_le h1 h2)
  rw [hd]
  calc 2 ^ Tp * afS (d + 1) 0 (Q + 1) < 2 ^ Tp * (2 * (d + 1) ^ Q) :=
        Nat.mul_lt_mul_of_pos_left hS hpos
    _ = 2 ^ (Tp + Q * t + 1) := by
        rw [← hd, ← Nat.pow_mul, Nat.mul_comm t Q, Nat.pow_add, Nat.pow_add, Nat.pow_one]
        grind
    _ ≤ 2 ^ p := Nat.pow_le_pow_right (by decide) (by omega)

/-- **At the first level the magnitude condition accepts strictly more** (`t ≥ 2`, `T′ < p`): one
diagonal more than the largest count the recursion accepts, which the recursion rejects. -/
theorem af_strict_zero {p Tp t : ℕ} (ht : 2 ≤ t) (hp : Tp < p) :
    diagFits p (2 ^ Tp) t 0 (afQ p Tp t 0 + 1) = true ∧
      afAccept p Tp t 0 (afQ p Tp t 0 + 1) = false := by
  refine ⟨?_, afAccept_afQ_succ (by omega)⟩
  by_cases h0 : afQ p Tp t 0 = 0
  · rw [h0]
    unfold diagFits
    rw [decide_eq_true_iff]
    simp only [Nat.zero_add, List.range'_one, List.map_cons, List.map_nil, List.sum_cons,
      List.sum_nil, Nat.sub_self, Nat.zero_mul, Nat.pow_zero, Nat.mul_one, Nat.one_mul,
      Nat.add_zero]
    exact Nat.pow_lt_pow_right (by decide) hp
  · exact af_diagFits_succ_zero ht (afQ_accept (Nat.pos_of_ne_zero h0))

/-- **At late levels, one diagonal more**: for `t ≥ 2` and a level starting at `K ≥ 4 · 2^t − 1`,
whenever the recursion accepts `Q ≥ 1` diagonals, `diagFits` accepts `Q + 1`. -/
theorem af_diagFits_succ_late {p Tp t K Q : ℕ} (ht : 2 ≤ t) (hK : 4 * 2 ^ t ≤ K + 1)
    (hQ : 1 ≤ Q) (h : afAccept p Tp t K Q = true) :
    diagFits p (2 ^ Tp) t K (Q + 1) = true := by
  unfold afAccept at h
  rw [decide_eq_true_iff] at h
  unfold diagFits
  rw [decide_eq_true_iff, diagSum_eq_afS]
  obtain ⟨d, hd⟩ : ∃ d, 2 ^ t = d + 1 := ⟨2 ^ t - 1, by have := Nat.one_le_two_pow (n := t); omega⟩
  have h4 : 4 ≤ 2 ^ t := by
    calc 4 = 2 ^ 2 := rfl
      _ ≤ 2 ^ t := Nat.pow_le_pow_right (by decide) ht
  have hd3 : 3 ≤ d := by omega
  have hKc : 2 ^ t ≤ K := by omega
  have hmK := afM_ge hKc hQ
  have hme := le_two_pow_afExtra t K (K + Q)
  generalize (max 1 (-afEta t K (K + Q))).toNat = m at hmK hme
  rw [hd] at hmK hK
  -- the level's first diagonal is overpaid: `c ((K + 1) d + 1) ≤ 2 m d²`
  have key : (d + 1) * ((K + 1) * d + 1) ≤ 2 * m * (d * d) := by
    obtain ⟨e, rfl⟩ : ∃ e, d = e + 3 := ⟨d - 3, by omega⟩
    obtain ⟨f, hf⟩ : ∃ f, K + 1 = 4 * (e + 4) + f := ⟨K + 1 - 4 * (e + 4), by omega⟩
    have hm' : 3 * e + 12 + f ≤ m := by omega
    rw [hf]
    have hpoly : 2 * (3 * e + 12 + f) * ((e + 3) * (e + 3)) =
        (e + 3 + 1) * ((4 * (e + 4) + f) * (e + 3) + 1) +
          (20 + 6 * f + 37 * e + 5 * e * f + 16 * e * e + e * e * f + 2 * e * e * e) := by
      grind
    have hmul : 2 * (3 * e + 12 + f) * ((e + 3) * (e + 3)) ≤ 2 * m * ((e + 3) * (e + 3)) :=
      Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ hm')
    omega
  have hpos : 0 < 2 ^ Tp := Nat.two_pow_pos Tp
  have hS : afS (d + 1) K (Q + 1) < 2 * (d + 1) ^ Q * m := by
    have h1 := afS_mul_lt d K (Q + 1)
    rw [Nat.pow_succ] at h1
    have h2 : (d + 1) ^ Q * (d + 1) * ((K + 1) * d + 1) ≤ 2 * (d + 1) ^ Q * m * (d * d) := by
      calc (d + 1) ^ Q * (d + 1) * ((K + 1) * d + 1)
          = (d + 1) ^ Q * ((d + 1) * ((K + 1) * d + 1)) := Nat.mul_assoc _ _ _
        _ ≤ (d + 1) ^ Q * (2 * m * (d * d)) := Nat.mul_le_mul_left _ key
        _ = 2 * (d + 1) ^ Q * m * (d * d) := by grind
    exact Nat.lt_of_mul_lt_mul_right (Nat.lt_of_lt_of_le h1 h2)
  rw [hd]
  calc 2 ^ Tp * afS (d + 1) K (Q + 1) < 2 ^ Tp * (2 * (d + 1) ^ Q * m) :=
        Nat.mul_lt_mul_of_pos_left hS hpos
    _ ≤ 2 ^ Tp * (2 * (d + 1) ^ Q * 2 ^ afExtra t K (K + Q)) :=
        Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ hme)
    _ = 2 ^ (Tp + Q * t + 1 + afExtra t K (K + Q)) := by
        rw [← hd, ← Nat.pow_mul, Nat.mul_comm t Q, Nat.pow_add, Nat.pow_add, Nat.pow_add,
          Nat.pow_one]
        grind
    _ ≤ 2 ^ p := Nat.pow_le_pow_right (by decide) h

/-- **At late levels the magnitude condition accepts strictly more** (`t ≥ 2`,
`K ≥ 4 · 2^t − 1`), wherever the recursion accepts a diagonal. -/
theorem af_strict_late {p Tp t K : ℕ} (ht : 2 ≤ t) (hK : 4 * 2 ^ t ≤ K + 1)
    (h1 : 1 ≤ afQ p Tp t K) :
    diagFits p (2 ^ Tp) t K (afQ p Tp t K + 1) = true ∧
      afAccept p Tp t K (afQ p Tp t K + 1) = false :=
  ⟨af_diagFits_succ_late ht hK h1 (afQ_accept h1), afAccept_afQ_succ (by omega)⟩

/-! ## Where the two coincide -/

/-- **INT8 slices, `T′ = 31`, binary64**: for every level start `K = 1 … 126` both accept exactly
three diagonals (at `K = 0` the magnitude condition accepts four, `af_int8_vs_diagFits`). -/
theorem af_int8_coincide :
    ∀ K ∈ List.range' 1 126, afQ 53 31 7 K = 3 ∧ diagFits 53 (2 ^ 31) 7 K 3 = true ∧
      diagFits 53 (2 ^ 31) 7 K 4 = false := by
  decide +kernel

/-- **`11`-bit fp16 slices, `T′ = 32`, binary64**: the magnitude condition accepts two diagonals up
to `K = 510`, where the recursion accepts one; from `K = 511` (checked to `599`) both accept one. -/
theorem af_fp16_coincide :
    afQ 53 32 12 510 = 1 ∧ diagFits 53 (2 ^ 32) 12 510 2 = true ∧
      ∀ K ∈ List.range' 511 89, afQ 53 32 12 K = 1 ∧ diagFits 53 (2 ^ 32) 12 K 1 = true ∧
        diagFits 53 (2 ^ 32) 12 K 2 = false := by
  decide +kernel

/-- **Two-bit slices** (`p = 53`, `T′ = 40`): both accept six diagonals at `K = 1` ... -/
theorem af_t2_coincide :
    afQ 53 40 2 1 = 6 ∧ diagFits 53 (2 ^ 40) 2 1 6 = true ∧ diagFits 53 (2 ^ 40) 2 1 7 = false := by
  decide +kernel

/-- ... while from `K = 15 = 4 · 2^2 − 1` the magnitude condition accepts more (`af_strict_late`):
five diagonals against three. -/
theorem af_t2_late :
    afQ 53 40 2 15 = 3 ∧ diagFits 53 (2 ^ 40) 2 15 5 = true := by
  decide +kernel

/-- **One-bit slices** (`p = 11`, `T′ = 6`): both accept four diagonals at `K = 0`, so the first-level
statement needs `t ≥ 2`. -/
theorem af_t1_coincide :
    afQ 11 6 1 0 = 4 ∧ diagFits 11 (2 ^ 6) 1 0 4 = true ∧ diagFits 11 (2 ^ 6) 1 0 5 = false := by
  decide +kernel

end Ozaki
