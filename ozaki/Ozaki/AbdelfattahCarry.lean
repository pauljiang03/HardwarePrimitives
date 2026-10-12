import Ozaki.AbdelfattahAcc
import Ozaki.SliceRuleCR

/-! # The spare-carry recursion of Abdelfattah et al., §4.4

Abdelfattah, Dongarra, Fasi, Mikaitis and Tisseur, *Analysis of floating-point matrix
multiplication computed via integer arithmetic* (arXiv:2506.11277, v3, §4.4), decide how many
diagonals of exact slice products fit in one exactly summed level by bookkeeping of "spare carry
locations":

* (4.20) `T′ := 2t + ⌈log₂ k⌉`, the bits of the integer accumulator actually used (`afTp`);
* (4.21) `η(K, M) := Σ_{l=K}^{M} (2^t − l) = (M − K + 1)(2^{t+1} − M − K)/2`, the spare carry
  positions of a level from diagonal `K` to diagonal `M` (`afEta`, `afEta_closed`);
* (4.22) `Q_j := ⌊(p − T′ − 1 − ⌈log₂ max{1, −η(K_j, K_j + Q_j)}⌉) / t⌋`, the diagonals of level `j`
  (`afRHS`, `afFix`).

This file formalizes the recursion as printed and settles what it means.

* **Two readings.** The derivation before (4.22) ("`C₀ + C₁` requires `p ≥ T′ + t + 1`",
  "`C₀ + C₁ + C₂` requires `p ≥ T′ + 2t + 1`", "until `p < T′ + Kt + 1`") counts *shifts*, so a level
  from `K_j` with `Q_j` would hold the `Q_j + 1` diagonals `K_j … K_j + Q_j`; the sentence after
  (4.22) says `Q_j` is "the exact number of diagonals at level `j`", the `Q_j` diagonals
  `K_j … K_j + Q_j − 1`. (A third sentence, "`p ≥ T′ + Kt − 1`", is a typo for `T′ + Kt + 1`.)
* **The count reading is sound** for every slice width `t ≥ 2` (`afAccept_diagFits`): whatever
  number of diagonals the recursion accepts, the level's worst-case magnitude satisfies the
  sum-of-magnitudes condition `diagFits` of `Ozaki.AbdelfattahAcc`, so the level adds up exactly in
  any order (`afAccept_levelExact`, with `sumTree_exact`). The proof bounds the level's magnitude
  `S = Σ_{i<Q} (K + 1 + i) 2^{(Q−1−i)t}` through the identity
  `S (c − 1)² + (c − 1)(K + Q + 1) + 1 = c^Q ((K + 1)(c − 1) + 1)`, `c = 2^t` (`afS_identity`), and the
  spare-carry term `η` through its closed form.
* **The shift reading is unsound** for every level that does not start at diagonal `0`: it charges
  the level's first diagonal `2^t − K` spare carry positions, but only a diagonal shifted against a
  preceding one in the same level has them. For INT8 slices (`t = 7`), `T′ = 31` and binary64,
  (4.22) holds with `Q = 3` at `K = 1` (`af_shift_fix`), but the four diagonals `1 … 4` with every
  product at its largest value add up to a value that is not a binary64 number, so no order of
  binary64 additions computes it (`af_shift_unsound`, `af_shift_noTree`).
* **(4.22) as an equation need not have a solution**: at `K = 127` in the same configuration no `Q`
  satisfies it (`af_noFix_127`); the right-hand side alternates `3, 2` for `Q = 2, 3`. The
  well-defined version used here is the largest accepted `Q` (`afQ`), `Q ≤ ⌊…⌋`, which every
  solution satisfies (`afFix_accept`).
* **The paper's simplification of `η`** to `η(1, max{s_A, s_B})` is not a bound on
  `η(K_j, K_j + Q_j)`: `η(1, 255) = 0` while `η(200, 203) = −294` (`af_eta_simplification`). The
  conclusion it is used for (three diagonals per level for INT8 slices and binary64 up to diagonal
  `255`) holds by the sum-of-magnitudes condition up to diagonal `252` (`fits_int8_binary64`), but
  not by the recursion, which accepts three diagonals only for levels starting at `126` or below
  (`af_int8_Q3`, `af_int8_Q2`).
* **Against the sum-of-magnitudes condition** (`diagFits`): the recursion never accepts more
  diagonals, and accepts fewer at the first level and at late levels (`Ozaki.AbdelfattahCarry2`);
  the two can coincide in between. It reserves `t + 1` bits for the first diagonal's carries where the magnitude
  condition charges only what the diagonals' products can reach. For the paper's configuration it
  accepts three diagonals per level from `K ≤ 126` where the magnitude condition accepts four at
  `K = 0` and three up to `K = 252` (`af_int8_vs_diagFits`); with `11`-bit fp16 slices on a Tensor
  Core (`t = 12`, products up to `2^32`) it accepts one diagonal per level, the magnitude condition
  two (`af_fp16_Q1`, `af_fp16_vs_diagFits`). So six slices take six levels by the recursion and
  three by the magnitude condition (`af_fp16_levels`).

Here diagonal `l` holds at most `l + 1` products, each an integer of magnitude at most `2^{T′}` on the
grid of its diagonal, the grids `t` bits apart, as in the paper's Figure 3.2 and in
`level_exact_of_diagonals`. -/

local notation "ℕ" => Nat
local notation "ℤ" => Int
local notation "ℚ" => Rat

namespace Ozaki

/-! ## The definitions (4.20)–(4.22) -/

/-- (4.20) `T′ := 2t + ⌈log₂ k⌉`. -/
def afTp (t k : ℕ) : ℕ := 2 * t + clog2 k

/-- `k` products of integers of magnitude at most `2^t` total at most `2^{T′}`. -/
theorem afTp_bound (t k : ℕ) : k * (2 ^ t * 2 ^ t) ≤ 2 ^ afTp t k := by
  unfold afTp
  rw [Nat.pow_add, show 2 * t = t + t by omega, Nat.pow_add, Nat.mul_comm k]
  exact Nat.mul_le_mul_left _ (le_two_pow_clog2 k)

/-- The first `n` terms of (4.21): `Σ_{i<n} (2^t − (K + i))`, as an integer. -/
def afEtaN (t K : ℕ) : ℕ → ℤ
  | 0 => 0
  | n + 1 => afEtaN t K n + (((2 ^ t : ℕ) : ℤ) - ((K + n : ℕ) : ℤ))

/-- (4.21) `η(K, M) := Σ_{l=K}^{M} (2^t − l)`, the spare carry positions of a level from diagonal
`K` to diagonal `M`. -/
def afEta (t K M : ℕ) : ℤ := afEtaN t K (M + 1 - K)

theorem afEtaN_closed (t K : ℕ) :
    ∀ n : ℕ, 2 * afEtaN t K n = (n : ℤ) * (2 * ((2 ^ t : ℕ) : ℤ) - 2 * K - n + 1)
  | 0 => by simp [afEtaN]
  | n + 1 => by
    simp only [afEtaN]
    rw [Int.mul_add, afEtaN_closed t K n]
    push_cast
    grind

/-- **(4.21) in closed form**: `2 η(K, M) = (M − K + 1)(2^{t+1} − M − K)`. -/
theorem afEta_closed {t K M : ℕ} (h : K ≤ M) :
    2 * afEta t K M = ((M + 1 - K : ℕ) : ℤ) * (((2 ^ (t + 1) : ℕ) : ℤ) - M - K) := by
  unfold afEta
  rw [afEtaN_closed]
  congr 1
  rw [Nat.pow_succ]
  push_cast
  omega

/-- The extra carry bits of (4.22): `⌈log₂ max{1, −η(K, M)}⌉`. -/
def afExtra (t K M : ℕ) : ℕ := clog2 (max 1 (-afEta t K M)).toNat

/-- (4.22)'s right-hand side, `⌊(p − T′ − 1 − ⌈log₂ max{1, −η(K, K + Q)}⌉) / t⌋`. -/
def afRHS (p Tp t K Q : ℕ) : ℤ := ((p : ℤ) - Tp - 1 - afExtra t K (K + Q)) / t

/-- (4.22) as printed: `Q` solves the recursion at a level starting at diagonal `K`. -/
def AfFix (p Tp t K Q : ℕ) : Prop := (Q : ℤ) = afRHS p Tp t K Q

instance (p Tp t K Q : ℕ) : Decidable (AfFix p Tp t K Q) := by unfold AfFix; infer_instance

/-- `Q` is accepted at `K`: `Q ≤ ⌊(p − T′ − 1 − extra)/t⌋`, that is `T′ + Qt + 1 + extra ≤ p`. -/
def afAccept (p Tp t K Q : ℕ) : Bool := decide (Tp + Q * t + 1 + afExtra t K (K + Q) ≤ p)

theorem afAccept_iff_le_rhs {p Tp t K Q : ℕ} (ht : 0 < t) :
    afAccept p Tp t K Q = true ↔ (Q : ℤ) ≤ afRHS p Tp t K Q := by
  unfold afAccept afRHS
  rw [decide_eq_true_iff, Int.le_ediv_iff_mul_le (by exact_mod_cast ht)]
  omega

/-- Every solution of (4.22) is accepted. -/
theorem afFix_accept {p Tp t K Q : ℕ} (ht : 0 < t) (h : AfFix p Tp t K Q) :
    afAccept p Tp t K Q = true :=
  (afAccept_iff_le_rhs ht).mpr (Int.le_of_eq h)

/-- The largest accepted `Q` up to `n`, `0` if none. -/
def afQAux (p Tp t K : ℕ) : ℕ → ℕ
  | 0 => 0
  | n + 1 => if afAccept p Tp t K (n + 1) then n + 1 else afQAux p Tp t K n

/-- **The well-defined (4.22)**: the largest number of diagonals the recursion accepts for a level
starting at diagonal `K` (no `Q > p` is accepted when `t ≥ 1`). -/
def afQ (p Tp t K : ℕ) : ℕ := afQAux p Tp t K p

theorem afQAux_accept {p Tp t K : ℕ} :
    ∀ n : ℕ, 0 < afQAux p Tp t K n → afAccept p Tp t K (afQAux p Tp t K n) = true
  | 0, h => by simp [afQAux] at h
  | n + 1, h => by
    unfold afQAux at h ⊢
    split
    · assumption
    · rename_i hn
      rw [if_neg hn] at h
      exact afQAux_accept n h

theorem afQ_accept {p Tp t K : ℕ} (h : 0 < afQ p Tp t K) : afAccept p Tp t K (afQ p Tp t K) = true :=
  afQAux_accept p h

/-- The levels of the recursion from diagonal `K` until diagonal `D` is covered, as
`(first diagonal, number of diagonals)`; it stops early if no diagonal fits. -/
def afLevels (p Tp t : ℕ) : ℕ → ℕ → ℕ → List (ℕ × ℕ)
  | 0, _, _ => []
  | fuel + 1, K, D =>
    if D ≤ K then [] else
      if afQ p Tp t K = 0 then [] else (K, afQ p Tp t K) :: afLevels p Tp t fuel (K + afQ p Tp t K) D

theorem afLevels_accept {p Tp t : ℕ} :
    ∀ (fuel K D : ℕ), ∀ L ∈ afLevels p Tp t fuel K D, afAccept p Tp t L.1 L.2 = true ∧ 0 < L.2
  | 0, _, _, L, hL => by simp [afLevels] at hL
  | fuel + 1, K, D, L, hL => by
    unfold afLevels at hL
    split at hL
    · simp at hL
    · split at hL
      · simp at hL
      · rename_i hQ
        rcases List.mem_cons.mp hL with rfl | hL
        · exact ⟨afQ_accept (Nat.pos_of_ne_zero hQ), Nat.pos_of_ne_zero hQ⟩
        · exact afLevels_accept fuel _ D L hL

/-! ## A level's worst-case magnitude -/

/-- The level's magnitude in units of the product bound and of its finest grid:
`S(K, Q) = Σ_{l=K}^{K+Q−1} (l + 1) c^{K+Q−1−l}`, with `S(K, Q + 1) = (K + Q + 1) + c S(K, Q)`. -/
def afS (c K : ℕ) : ℕ → ℕ
  | 0 => 0
  | Q + 1 => (K + Q + 1) + c * afS c K Q

theorem sum_map_mul_left_nat (c : ℕ) (f : ℕ → ℕ) :
    ∀ l : List ℕ, (l.map fun d => c * f d).sum = c * (l.map f).sum
  | [] => by simp
  | x :: l => by simp only [List.map_cons, List.sum_cons, sum_map_mul_left_nat c f l, Nat.mul_add]

/-- The sum of `diagFits` is `Kb · S(K, Q)`. -/
theorem diagSum_eq_afS (Kb t K : ℕ) :
    ∀ Q : ℕ, ((List.range' K Q).map fun d => (d + 1) * Kb * 2 ^ ((K + Q - 1 - d) * t)).sum =
      Kb * afS (2 ^ t) K Q
  | 0 => by simp [afS]
  | Q + 1 => by
    rw [List.range'_concat, List.map_append, List.sum_append]
    have hmap : ((List.range' K Q).map fun d => (d + 1) * Kb * 2 ^ ((K + (Q + 1) - 1 - d) * t)) =
        ((List.range' K Q).map fun d => 2 ^ t * ((d + 1) * Kb * 2 ^ ((K + Q - 1 - d) * t))) := by
      apply List.map_congr_left
      intro d hd
      have hdl : d < K + Q := by have := List.mem_range'_1.mp hd; omega
      have e : (K + (Q + 1) - 1 - d) * t = (K + Q - 1 - d) * t + t := by
        rw [show K + (Q + 1) - 1 - d = (K + Q - 1 - d) + 1 by omega, Nat.succ_mul]
      rw [e, Nat.pow_add]
      generalize 2 ^ ((K + Q - 1 - d) * t) = X
      generalize 2 ^ t = Y
      rw [Nat.mul_comm Y]
      simp only [Nat.mul_assoc]
    rw [hmap, sum_map_mul_left_nat, diagSum_eq_afS Kb t K Q]
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, afS]
    rw [show K + (Q + 1) - 1 - (K + 1 * Q) = 0 by omega, Nat.zero_mul, Nat.pow_zero, Nat.mul_one,
      show K + 1 * Q + 1 = K + Q + 1 by omega]
    grind

/-- **The identity behind the bound**, with `c = d + 1`:
`S d² + d (K + Q + 1) + 1 = (d + 1)^Q ((K + 1) d + 1)`. -/
theorem afS_identity (d K : ℕ) :
    ∀ Q : ℕ, afS (d + 1) K Q * (d * d) + (d * (K + Q + 1) + 1) = (d + 1) ^ Q * ((K + 1) * d + 1)
  | 0 => by simp [afS]; grind
  | Q + 1 => by
    have ih := afS_identity d K Q
    simp only [afS, Nat.pow_succ]
    generalize afS (d + 1) K Q = A at ih ⊢
    generalize hP : (d + 1) ^ Q = P at ih ⊢
    -- [(K + Q + 1) + (d + 1) A] d² + d (K + Q + 2) + 1 = P (d + 1) X, with A d² + B = P X
    have e : ((K + Q + 1) + (d + 1) * A) * (d * d) + (d * (K + (Q + 1) + 1) + 1) =
        (d + 1) * (A * (d * d) + (d * (K + Q + 1) + 1)) := by grind
    rw [e, ih]
    grind

/-- The level's magnitude is below `c^Q ((K + 1)(c − 1) + 1)/(c − 1)²`. -/
theorem afS_mul_lt (d K Q : ℕ) :
    afS (d + 1) K Q * (d * d) < (d + 1) ^ Q * ((K + 1) * d + 1) := by
  have := afS_identity d K Q
  omega

/-! ## The spare-carry term -/

/-- `m = max{1, −η(K, K + Q)}` as a natural number; `2^{extra} ≥ m`. -/
theorem le_two_pow_afExtra (t K M : ℕ) :
    (max 1 (-afEta t K M)).toNat ≤ 2 ^ afExtra t K M :=
  le_two_pow_clog2 _

theorem one_le_afM (t K M : ℕ) : 1 ≤ (max 1 (-afEta t K M)).toNat := by omega

/-- **Late levels pay for their first diagonal**: when the level starts at or beyond diagonal
`2^t`, `−η(K, K + Q) ≥ K − 2^t + 1`. -/
theorem afM_ge {t K Q : ℕ} (hK : 2 ^ t ≤ K) (hQ : 1 ≤ Q) :
    K + 1 - 2 ^ t ≤ (max 1 (-afEta t K (K + Q))).toNat := by
  have hc := afEta_closed (t := t) (show K ≤ K + Q by omega)
  rw [show K + Q + 1 - K = Q + 1 by omega, Nat.pow_succ] at hc
  -- 2η = (Q + 1)(2c − 2K − Q), and 2K + Q − 2c ≥ 1
  generalize hc' : (2 ^ t : ℕ) = c at hc hK
  generalize hE : afEta t K (K + Q) = E at hc ⊢
  push_cast at hc
  have hY : (2 : ℤ) ≤ (Q : ℤ) + 1 := by omega
  have hX : (0 : ℤ) ≤ 2 * (K : ℤ) + Q - 2 * c := by omega
  have hprod : 2 * (2 * (K : ℤ) + Q - 2 * c) ≤ ((Q : ℤ) + 1) * (2 * (K : ℤ) + Q - 2 * c) :=
    Int.mul_le_mul_of_nonneg_right hY hX
  have hE2 : -2 * E = ((Q : ℤ) + 1) * (2 * (K : ℤ) + Q - 2 * c) := by
    have : -2 * E = -(2 * E) := by omega
    rw [this, hc]
    grind
  generalize ((Q : ℤ) + 1) * (2 * (K : ℤ) + Q - 2 * c) = P at hprod hE2
  have hm : -E ≤ max 1 (-E) := Int.le_max_right _ _
  generalize max 1 (-E) = m at hm ⊢
  omega

/-! ## Soundness of the count reading -/

/-- The level's magnitude against the recursion's budget, with `c = d + 1 ≥ 4`:
`S(K, Q) < 2 c^Q m`. -/
theorem afS_lt (d K Q m : ℕ) (hd : 3 ≤ d) (hm : 1 ≤ m)
    (hK : K + 1 ≤ d + 1 ∨ K + 1 - (d + 1) ≤ m) :
    afS (d + 1) K Q < 2 * (d + 1) ^ Q * m := by
  have h1 := afS_mul_lt d K Q
  -- it suffices that (K + 1) d + 1 ≤ 2 m d²
  have key : (K + 1) * d + 1 ≤ 2 * m * (d * d) := by
    rcases hK with hK | hK
    · -- K + 1 ≤ c: (K + 1) d + 1 ≤ (d + 1) d + 1 ≤ 2 d² ≤ 2 m d²
      have : (K + 1) * d ≤ (d + 1) * d := Nat.mul_le_mul_right d hK
      have hdd : 3 * d ≤ d * d := Nat.mul_le_mul_right d hd
      have hmd : 1 * (d * d) ≤ m * (d * d) := Nat.mul_le_mul_right _ hm
      grind
    · -- K ≥ c, m ≥ K + 1 − c = a: (K + 1) d + 1 = (a + d + 1) d + 1 ≤ 2 a d² ≤ 2 m d²
      by_cases hKc : K + 1 ≤ d + 1
      · have : (K + 1) * d ≤ (d + 1) * d := Nat.mul_le_mul_right d hKc
        have hdd : 3 * d ≤ d * d := Nat.mul_le_mul_right d hd
        have hmd : 1 * (d * d) ≤ m * (d * d) := Nat.mul_le_mul_right _ hm
        grind
      · obtain ⟨a, ha⟩ : ∃ a, K = d + a + 1 := ⟨K - d - 1, by omega⟩
        subst ha
        have ham : a + 1 ≤ m := by omega
        have h2 : (a + 1) * (d * d) ≤ m * (d * d) := Nat.mul_le_mul_right _ ham
        have h3 : (a + 1) * d * 3 ≤ (a + 1) * d * d := Nat.mul_le_mul_left _ hd
        have h4 : 3 * d ≤ d * d := Nat.mul_le_mul_right d hd
        have h5 : 1 * d ≤ (a + 1) * d := Nat.mul_le_mul_right d (by omega)
        have h6 : 1 * (d * d) ≤ (a + 1) * (d * d) := Nat.mul_le_mul_right _ (by omega)
        have e1 : (d + a + 1 + 1) * d = (a + 1) * d + d * d + d := by
          rw [show d + a + 1 + 1 = (a + 1) + d + 1 by omega, Nat.add_mul, Nat.add_mul, Nat.one_mul]
        have e2 : (a + 1) * d * d = (a + 1) * (d * d) := Nat.mul_assoc _ _ _
        have e3 : 2 * m * (d * d) = 2 * (m * (d * d)) := Nat.mul_assoc _ _ _
        rw [e1, e3]
        rw [e2] at h3
        generalize (a + 1) * d = x at *
        generalize d * d = y at *
        generalize (a + 1) * y = z at *
        generalize m * y = w at *
        omega
  have h5 : (d + 1) ^ Q * ((K + 1) * d + 1) ≤ (d + 1) ^ Q * (2 * m * (d * d)) :=
    Nat.mul_le_mul_left _ key
  have h6 : afS (d + 1) K Q * (d * d) < 2 * (d + 1) ^ Q * m * (d * d) := by
    have : (d + 1) ^ Q * (2 * m * (d * d)) = 2 * (d + 1) ^ Q * m * (d * d) := by grind
    omega
  exact Nat.lt_of_mul_lt_mul_right h6

/-- **The recursion's count reading is sound**: for slices of `t ≥ 2` bits, if the recursion accepts
`Q ≥ 1` diagonals at a level starting at `K`, the level's worst-case magnitude, with products of
at most `2^{T′}`, satisfies the sum-of-magnitudes condition. -/
theorem afAccept_diagFits {p Tp t K Q : ℕ} (ht : 2 ≤ t) (hQ : 1 ≤ Q)
    (h : afAccept p Tp t K Q = true) : diagFits p (2 ^ Tp) t K Q = true := by
  unfold afAccept at h
  rw [decide_eq_true_iff] at h
  unfold diagFits
  rw [decide_eq_true_iff, diagSum_eq_afS]
  obtain ⟨d, hd⟩ : ∃ d, 2 ^ t = d + 1 := ⟨2 ^ t - 1, by have := Nat.one_le_two_pow (n := t); omega⟩
  have h4 : 4 ≤ 2 ^ t := by
    calc 4 = 2 ^ 2 := rfl
      _ ≤ 2 ^ t := Nat.pow_le_pow_right (by decide) ht
  have hd3 : 3 ≤ d := by omega
  have hm := one_le_afM t K (K + Q)
  have hme := le_two_pow_afExtra t K (K + Q)
  have hK : K + 1 ≤ d + 1 ∨ K + 1 - (d + 1) ≤ (max 1 (-afEta t K (K + Q))).toNat := by
    by_cases hKc : 2 ^ t ≤ K
    · right; rw [← hd]; exact afM_ge hKc hQ
    · left; omega
  generalize (max 1 (-afEta t K (K + Q))).toNat = m at hm hme hK
  have hS := afS_lt d K Q m hd3 hm hK
  rw [← hd] at hS
  have hpow : 2 ^ Tp * (2 * (2 ^ t) ^ Q * m) ≤ 2 ^ p := by
    calc 2 ^ Tp * (2 * (2 ^ t) ^ Q * m) ≤ 2 ^ Tp * (2 * (2 ^ t) ^ Q * 2 ^ afExtra t K (K + Q)) :=
          Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ hme)
      _ = 2 ^ (Tp + Q * t + 1 + afExtra t K (K + Q)) := by
          rw [← Nat.pow_mul, Nat.mul_comm t Q, Nat.pow_add, Nat.pow_add, Nat.pow_add, Nat.pow_one]
          grind
      _ ≤ 2 ^ p := Nat.pow_le_pow_right (by decide) h
  have hpos : 0 < 2 ^ Tp := Nat.two_pow_pos Tp
  calc 2 ^ Tp * afS (2 ^ t) K Q < 2 ^ Tp * (2 * (2 ^ t) ^ Q * m) := Nat.mul_lt_mul_of_pos_left hS hpos
    _ ≤ 2 ^ p := hpow

/-- **A level the recursion accepts adds up exactly**: for a regular slicing (diagonal `d` holds at
most `d + 1` products, each an integer multiple of `2^{G₀ − dt}` of magnitude at most
`2^{T′} 2^{G₀ − dt}`), the level of the `Q` diagonals the recursion accepts at `K` is exact, so
it adds up exactly along any tree (`sumTree_exact`). -/
theorem afAccept_levelExact {p Tp t K Q : ℕ} {emin emax G0 : ℤ} (ht : 2 ≤ t) (hQ : 1 ≤ Q)
    (h : afAccept p Tp t K Q = true) (diags : ℕ → List ℚ)
    (hg : ∀ d ∈ List.range' K Q, ∀ x ∈ diags d, GridMultiple (G0 - (d : ℤ) * t) x)
    (hb : ∀ d ∈ List.range' K Q,
      ((diags d).map Rat.abs).sum ≤ ((d + 1 : ℕ) : ℚ) * (2 ^ Tp : ℕ) * 2 ^ (G0 - (d : ℤ) * t))
    (h1 : emin ≤ G0 - ((K + Q - 1 : ℕ) : ℤ) * t + ((p : ℤ) - 1))
    (h2 : G0 - ((K + Q - 1 : ℕ) : ℤ) * t + ((p : ℤ) - 1) ≤ emax) :
    LevelExact p emin emax (G0 - ((K + Q - 1 : ℕ) : ℤ) * t) ((List.range' K Q).flatMap diags) :=
  level_exact_of_diagonals diags hg hb (diagFits_spec (afAccept_diagFits ht hQ h)) h1 h2

/-! ## The shift reading is unsound -/

/-- The largest products of the four diagonals `1 … 4` of INT8 slices (`t = 7`) with `T′ = 31`:
diagonal `d` holds `d + 1` products `(2^31 − 1) 2^{−7d}`. -/
def afShiftDiags (d : ℕ) : List ℚ :=
  List.replicate (d + 1) (((2 ^ 31 - 1 : ℕ) : ℚ) * 2 ^ (-((d : ℤ) * 7)))

/-- The level of diagonals `1 … 4`. -/
def afShiftLevel : List ℚ := (List.range' 1 4).flatMap afShiftDiags

/-- (4.22) holds with `Q = 3` at `K = 1` for INT8 slices, `T′ = 31`, binary64: under the shift
reading the level is the four diagonals `1 … 4`. -/
theorem af_shift_fix : AfFix 53 31 7 1 3 := by decide +kernel

/-- The products of each diagonal meet the paper's bounds: integer multiples of the diagonal's
grid ... -/
theorem afShiftDiags_grid (d : ℕ) : ∀ x ∈ afShiftDiags d, GridMultiple (-((d : ℤ) * 7)) x := by
  intro x hx
  rw [afShiftDiags, List.mem_replicate] at hx
  exact ⟨2 ^ 31 - 1, by rw [hx.2]; push_cast; rfl⟩

/-- ... and at most `2^{T′}` each, `T′ = 31`, as `level_exact_of_diagonals` requires. -/
theorem afShiftDiags_bound :
    ∀ d ∈ List.range' 1 4,
      ((afShiftDiags d).map Rat.abs).sum ≤ ((d + 1 : ℕ) : ℚ) * (2 ^ 31 : ℕ) * 2 ^ (-((d : ℤ) * 7)) := by
  decide +kernel

/-- **The shift reading is unsound**: the level's sum is not a binary64 value. -/
theorem af_shift_unsound : ¬ FormatValue 53 (-1022) 1023 afShiftLevel.sum := by
  intro h
  have h1 := roundRNE_of_formatValue (by decide) h
  have h2 : roundRNE 53 (-1022) 1023 afShiftLevel.sum ≠ some afShiftLevel.sum := by decide +kernel
  exact h2 h1

/-- The result of a rounded addition is a format value. -/
theorem evalWith_node_formatValue {p : ℕ} {emin emax : ℤ} (hp : 0 < p) (hle : emin ≤ emax)
    (l r : SumTree) {v : ℚ}
    (h : (SumTree.node l r).evalWith some (roundRNE p emin emax) = some v) :
    FormatValue p emin emax v := by
  simp only [SumTree.evalWith] at h
  cases hl : l.evalWith some (roundRNE p emin emax) with
  | none => simp [hl] at h
  | some a =>
    cases hr : r.evalWith some (roundRNE p emin emax) with
    | none => simp [hl, hr] at h
    | some b =>
      simp only [hl, hr, Option.bind_some] at h
      obtain ⟨rfl, hM⟩ := roundRNE_eq_some.mp h
      exact rneU_formatValue hp hle hM

/-- **No order of binary64 additions adds the level up exactly**: every tree over its terms
returns a rounded value, which is not the level's sum. -/
theorem af_shift_noTree (T : SumTree) (hT : T.leaves.Perm afShiftLevel) :
    T.evalWith some (roundRNE 53 (-1022) 1023) ≠ some afShiftLevel.sum := by
  intro h
  cases T with
  | leaf x =>
    have hlen := hT.length_eq
    simp only [SumTree.leaves, List.length_cons, List.length_nil] at hlen
    have : afShiftLevel.length = 14 := by decide +kernel
    omega
  | node l r =>
    exact af_shift_unsound (evalWith_node_formatValue (by decide) (by decide) l r h)

/-- The count reading rejects four diagonals at `K = 1`, and accepts the three diagonals `1 … 3`. -/
theorem af_count_K1 : afAccept 53 31 7 1 4 = false ∧ afQ 53 31 7 1 = 3 := by decide +kernel

/-! ## (4.22) as an equation, and the simplification of `η` -/

/-- **(4.22) as printed can have no solution**: at `K = 127` (INT8 slices, `T′ = 31`, binary64) no
`Q` satisfies it; its right-hand side is `3` at `Q = 2` and `2` at `Q = 3`. -/
theorem af_noFix_127 :
    (∀ Q ∈ List.range 54, ¬ AfFix 53 31 7 127 Q) ∧ afRHS 53 31 7 127 2 = 3 ∧
      afRHS 53 31 7 127 3 = 2 := by
  decide +kernel

/-- `Q > p` is never accepted for `t ≥ 1`, so `afQ` searches every candidate. -/
theorem afAccept_le {p Tp t K Q : ℕ} (ht : 1 ≤ t) (h : afAccept p Tp t K Q = true) : Q ≤ p := by
  unfold afAccept at h
  rw [decide_eq_true_iff] at h
  have : Q * 1 ≤ Q * t := Nat.mul_le_mul_left Q ht
  omega

/-- **The simplification after (4.22) is not a bound**: `η(1, 255) = 0`, but `η(200, 203) = −294`,
so `η(1, max{s_A, s_B}) ≥ 0` does not make the extra bits of a later level vanish. -/
theorem af_eta_simplification : afEta 7 1 255 = 0 ∧ afEta 7 200 203 = -294 := by decide +kernel

/-! ## The configurations -/

/-- (4.20) for INT8 slices and `k = 2^17`: `T′ = 31`, the paper's example. -/
theorem afTp_int8_k17 : afTp 7 (2 ^ 17) = 31 := by decide +kernel

/-- **INT8 slices, `T′ = 31`, binary64, by the recursion**: three diagonals for levels starting at
`K ≤ 126`, two from `127` to `169`, one from `170` (checked to `299`). -/
theorem af_int8_Q3 : ∀ K ∈ List.range 127, afQ 53 31 7 K = 3 := by decide +kernel

theorem af_int8_Q2 : ∀ K ∈ List.range' 127 43, afQ 53 31 7 K = 2 := by decide +kernel

theorem af_int8_Q1 : ∀ K ∈ List.range' 170 130, afQ 53 31 7 K = 1 := by decide +kernel

/-- The solutions of (4.22) where they exist: `Q = 3` for `K ≤ 126`. -/
theorem af_int8_fix : ∀ K ∈ List.range 127, AfFix 53 31 7 K 3 := by decide +kernel

/-- **Against the sum-of-magnitudes condition**: it accepts four diagonals at `K = 0` and three up
to `K = 252`, where the recursion accepts three only up to `K = 126`. -/
theorem af_int8_vs_diagFits :
    diagFits 53 (2 ^ 31) 7 0 4 = true ∧ afAccept 53 31 7 0 4 = false ∧
      (∀ K ∈ List.range' 127 126, diagFits 53 (2 ^ 31) 7 K 3 = true) ∧
      afAccept 53 31 7 127 3 = false ∧ diagFits 53 (2 ^ 31) 7 253 3 = false := by
  decide +kernel

/-- INT8 slices with `k = 1024` (`T′ = 24`): the recursion accepts four diagonals for `K ≤ 126`;
the sum-of-magnitudes condition five at `K = 0` and four up to `K = 252`. -/
theorem af_int8_k1024 :
    afTp 7 1024 = 24 ∧ (∀ K ∈ List.range 127, afQ 53 24 7 K = 4) ∧
      diagFits 53 (2 ^ 24) 7 0 5 = true ∧ afAccept 53 24 7 0 5 = false ∧
      diagFits 53 (2 ^ 24) 7 252 4 = true ∧ afAccept 53 24 7 252 4 = false := by
  decide +kernel

/-- The recursion's levels for `7` INT8 slices (diagonals `0 … 6`), `T′ = 31`: three levels. -/
theorem af_int8_levels : afLevels 53 31 7 10 0 7 = [(0, 3), (3, 3), (6, 3)] := by decide +kernel

/-- **`11`-bit fp16 slices on a Tensor Core** (grids `12` bits apart, products up to `2^32`,
binary64): the recursion accepts one diagonal per level (checked to `K = 299`)... -/
theorem af_fp16_Q1 : ∀ K ∈ List.range 300, afQ 53 32 12 K = 1 := by decide +kernel

/-- ... where the sum-of-magnitudes condition accepts two (`fits_fp16_binary64`). -/
theorem af_fp16_vs_diagFits :
    diagFits 53 (2 ^ 32) 12 0 2 = true ∧ afAccept 53 32 12 0 2 = false := by decide +kernel

/-- Six slices take six levels by the recursion, three by the sum-of-magnitudes condition. -/
theorem af_fp16_levels :
    afLevels 53 32 12 10 0 6 = [(0, 1), (1, 1), (2, 1), (3, 1), (4, 1), (5, 1)] ∧
      diagFits 53 (2 ^ 32) 12 0 2 = true ∧ diagFits 53 (2 ^ 32) 12 2 2 = true ∧
      diagFits 53 (2 ^ 32) 12 4 2 = true := by
  decide +kernel

end Ozaki
