import Ozaki.UchinoConst

/-! # Uchino, Ozaki and Imamura's scaling (Algorithm 2) and their Lemma 1

Uchino, Ozaki and Imamura (arXiv:2602.02549, §3.2, Algorithm 2) choose the scaling exponents of
Ozaki-II with a single-precision `log2f`:

* `μ'ᵢ = 5 − ⌊log₂ maxₕ |aᵢₕ|⌋`, `Ā = ⌈diag(2^μ') |A|⌉`, likewise `ν'` and `B̄`, so that
  `|A||B| ≤ diag(2^-μ') C̄ diag(2^-ν')` for `C̄ = Ā B̄` (their (16));
* `D̄ = single△(C̄)` (rounded up), `eᵢ = log2f(maxⱼ d̄ᵢⱼ)`, `fⱼ = log2f(maxᵢ d̄ᵢⱼ)`;
* `P' = single▽(log₂(P − 1)/2 − 0.5)`, `c0 = single▽(−0.5/(1 − 4u₃₂))`;
* `μᵢ = μ'ᵢ + ⌊fl▽(fma(c0, eᵢ, P'))⌋`, likewise `νⱼ`; then `A' = trunc(diag(2^μ) A)` and
  `B' = trunc(B diag(2^ν))`.

Their **Lemma 1** states `|A'||B'| < P/2`, the range condition of the CRT reconstruction. Real
logarithms are not available here, so the statements use rational powers of two: `Le2 a x` is
`a ≤ 2^x` and `Ge2 a x` is `2^x ≤ a`, for rational `x`, through `a^d ≤ 2^n` for some `x d = n`.

* **Assumption (1)**, `|log2f(x) − log₂ x| ≤ 4u₃₂ log₂ x`, is `Log2fSpec`: for `x ≥ 1`,
  `x ≤ 2^(log2f x / (1 − 4u))` and `2^(log2f x / (1 + 4u)) ≤ x`. As written, (1) cannot hold for
  `0 < x < 1` (its right side is negative); it is only used for `x ≥ 1`, and only its first half.
* `uchino_shift_le`: the computed shift `g = ⌊F⌋`, `F ≤ c0 e + P'`, of a row whose maximum of `D̄`
  is `d ≥ 1` satisfies `2^(2g) c̄ ≤ 2^(2P')` for every entry `c̄ ≤ d` of `C̄` in the row.
* **Lemma 1** (`uchino_lemma1`, `uchino_lemma1_lt`): `Σₕ |A'ₕ| |B'ₕ| ≤ (P − 1)/2 < P/2` for every
  entry, from its row's and its column's shifts (the geometric mean of their (31)). The `_of`
  versions take (1) only at the values used.

**Three imprecisions.** Line 11 of Algorithm 2 reads `fl▽(⌊fma(c0, eᵢ, P')⌋)`, the proof
`⌊fl▽(fma(c0, eᵢ, P'))⌋`; only the second (a round-down `fma`, then the floor) is covered, a
round-to-nearest `fma` rounding up to an integer would add one to the shift. `log2f` needs the
row and column maxima of `D̄` to be at least `1`: a zero row of `C̄` (possible for a nonzero row
of `A` that is nonzero only where the rows of `B` are zero) gives `log2f(0)`. And the exhaustive
check of their proof, `⌊P' − (1 + u)e'/2⌋ ≤ P' − e'/2 − 2^-21` "for all `0 ≤ e' ≤ 29`", can only
range over the values `e' = log₂ m` of integers `m`: on the interval it fails for every `P'`
(`uchino_slack_needs_integers`).

**A simplification.** That check gives `|A'||B'| ≤ (P − 1) 2^(−1−2^-20)`. Lemma 1 itself needs no
such constant: the floor is at most its argument, which gives `(P − 1)/2`.

**Where the constant is needed: Lemma 4.** The quotient `Q` is right only if
`|A'B'| + δ < P/2`, with `δ` the error of `fl(P_inv C1)` scaled by `P`, about `(K + 2) u ρ P`, which
`(P − 1)/2` does not leave room for, and not only in the proof: on their first twelve moduli the
product `(P − 1)/2 − 5` is reconstructed as itself minus `P`
(`tests/OzakiTCTests/UchinoScaling.lean`).
Their slack does leave room: `uchino_lemma1_slack` takes the consequence of their check as a
hypothesis, `2^(2g) m ≤ 2^(2P' − 1/k)` for the row's maximum `m` of `C̄` (theirs: `k = 2^20`), and
gives `|A'||B'| (1 + t) ≤ (P − 1)/2` for `k t ≤ 1/2`. This slack is the one numeric fact of their
analysis that is not derived here.

**End to end.** `ozaki2Uchino_R64` discharges the reconstruction hypothesis of `ozaki2Uchino_error`
for every residue vector the matrix multiplier can produce, with the closed form `R64` of
`uchino_R64`, under a margin `2(Λ + δ̄) < P` for a bound `Λ` on `|A'||B'|` (`δ̄ = uchinoDeltaBar`,
about `(K + 2) u ρ P`); `ozaki2Uchino_scaled_error` takes `Λ` from their scaling with the slack.
Both are instantiated, every hypothesis checked by the kernel, in
`tests/OzakiTCTests/UchinoScaling.lean`. -/

local notation "ℕ" => Nat
local notation "ℤ" => Int
local notation "ℚ" => Rat

namespace Ozaki

/-! ## Natural powers of rationals -/

theorem qpow_add (a : ℚ) (i : ℕ) : ∀ j : ℕ, a ^ (i + j) = a ^ i * a ^ j
  | 0 => by rw [Nat.add_zero, Rat.pow_zero]; grind
  | j + 1 => by rw [← Nat.add_assoc, Rat.pow_succ, Rat.pow_succ, qpow_add a i j]; grind

theorem qpow_mul (a : ℚ) (m : ℕ) : ∀ n : ℕ, (a ^ m) ^ n = a ^ (m * n)
  | 0 => by rw [Rat.pow_zero, Nat.mul_zero, Rat.pow_zero]
  | n + 1 => by rw [Rat.pow_succ, qpow_mul a m n, Nat.mul_succ, qpow_add]

theorem mul_qpow (a b : ℚ) : ∀ n : ℕ, (a * b) ^ n = a ^ n * b ^ n
  | 0 => by simp [Rat.pow_zero]
  | n + 1 => by rw [Rat.pow_succ, Rat.pow_succ, Rat.pow_succ, mul_qpow a b n]; grind

theorem two_zpow_qpow (z : ℤ) : ∀ n : ℕ, ((2 : ℚ) ^ z) ^ n = (2 : ℚ) ^ (z * n)
  | 0 => by rw [Rat.pow_zero, Int.natCast_zero, Int.mul_zero, two_pow_zero]
  | n + 1 => by
    rw [Rat.pow_succ, two_zpow_qpow z n, ← two_pow_add]
    congr 1; push_cast; grind

theorem qpow_le_qpow {s t : ℚ} (hs : 0 ≤ s) (hst : s ≤ t) : ∀ n : ℕ, s ^ n ≤ t ^ n
  | 0 => by rw [Rat.pow_zero, Rat.pow_zero]; exact Rat.le_refl
  | n + 1 => by
    rw [Rat.pow_succ, Rat.pow_succ]
    exact Rat.le_trans (Rat.mul_le_mul_of_nonneg_right (qpow_le_qpow hs hst n) hs)
      (Rat.mul_le_mul_of_nonneg_left hst (Rat.pow_nonneg (Rat.le_trans hs hst)))

theorem qpow_lt_qpow {s t : ℚ} (hs : 0 ≤ s) (hst : s < t) : ∀ n : ℕ, 0 < n → s ^ n < t ^ n
  | 0, h => absurd h (by decide)
  | n + 1, _ => by
    rw [Rat.pow_succ, Rat.pow_succ]
    have ht : 0 < t := by grind
    have h1 := Rat.mul_le_mul_of_nonneg_left (Rat.le_of_lt hst) (Rat.pow_nonneg hs (n := n))
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · rw [Rat.pow_zero, Rat.pow_zero]; grind
    · have h2 := Rat.mul_lt_mul_of_pos_right (qpow_lt_qpow hs hst n hn) ht
      grind

theorem le_of_qpow_le {s t : ℚ} (ht : 0 ≤ t) {n : ℕ} (hn : 0 < n)
    (h : s ^ n ≤ t ^ n) : s ≤ t := by
  apply Rat.not_lt.mp
  intro hts
  exact absurd h (Rat.not_le.mpr (qpow_lt_qpow ht hts n hn))

theorem mul_le_mul_nonneg {a b c d : ℚ} (h1 : a ≤ b) (h2 : c ≤ d) (ha : 0 ≤ a) (hc : 0 ≤ c) :
    a * c ≤ b * d :=
  Rat.le_trans (Rat.mul_le_mul_of_nonneg_left h2 ha)
    (Rat.mul_le_mul_of_nonneg_right h1 (Rat.le_trans hc h2))

theorem mul_den_eq_num (x : ℚ) : x * (x.den : ℚ) = (x.num : ℚ) := by
  have h := Rat.mkRat_self x
  rw [Rat.mkRat_eq_div] at h
  have hd : (x.den : ℚ) ≠ 0 := by
    have := x.den_pos; exact_mod_cast (show x.den ≠ 0 by omega)
  calc x * (x.den : ℚ) = (x.num : ℚ) / (x.den : ℚ) * (x.den : ℚ) := by rw [h]
    _ = (x.num : ℚ) := Rat.div_mul_cancel hd

/-! ## Rational powers of two -/

/-- `a ≤ 2^x` for a rational exponent: `a^d ≤ 2^n` for some `x d = n`, `d > 0`. -/
def Le2 (a x : ℚ) : Prop := ∃ (n : ℤ) (d : ℕ), 0 < d ∧ x * d = n ∧ a ^ d ≤ (2 : ℚ) ^ n

/-- `2^x ≤ a` for a rational exponent: `2^n ≤ a^d` for some `x d = n`, `d > 0`. -/
def Ge2 (a x : ℚ) : Prop := ∃ (n : ℤ) (d : ℕ), 0 < d ∧ x * d = n ∧ (2 : ℚ) ^ n ≤ a ^ d

theorem le2_of_le_two_pow {a : ℚ} {k : ℤ} (h : a ≤ 2 ^ k) : Le2 a k :=
  ⟨k, 1, by decide, by simp, by rw [Rat.pow_succ, Rat.pow_zero]; grind⟩

theorem ge2_of_two_pow_le {a : ℚ} {k : ℤ} (h : (2 : ℚ) ^ k ≤ a) : Ge2 a k :=
  ⟨k, 1, by decide, by simp, by rw [Rat.pow_succ, Rat.pow_zero]; grind⟩

/-- `a ≤ 2^x`, `b ≤ 2^y` give `a b ≤ 2^(x + y)`. -/
theorem le2_mul {a b x y : ℚ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hx : Le2 a x) (hy : Le2 b y) :
    Le2 (a * b) (x + y) := by
  obtain ⟨n, d, hd, hxd, hax⟩ := hx
  obtain ⟨m, e, he, hye, hby⟩ := hy
  refine ⟨n * e + m * d, d * e, Nat.mul_pos hd he, ?_, ?_⟩
  · push_cast
    grind
  · rw [mul_qpow, ← qpow_mul, Nat.mul_comm d e, ← qpow_mul, two_pow_add, ← two_zpow_qpow,
      ← two_zpow_qpow]
    exact mul_le_mul_nonneg (qpow_le_qpow (Rat.pow_nonneg ha) hax e)
      (qpow_le_qpow (Rat.pow_nonneg hb) hby d) (Rat.pow_nonneg (Rat.pow_nonneg ha))
      (Rat.pow_nonneg (Rat.pow_nonneg hb))

/-- `2^x ≤ a`, `2^y ≤ b` give `2^(x + y) ≤ a b`. -/
theorem ge2_mul {a b x y : ℚ} (hx : Ge2 a x) (hy : Ge2 b y) : Ge2 (a * b) (x + y) := by
  obtain ⟨n, d, hd, hxd, hax⟩ := hx
  obtain ⟨m, e, he, hye, hby⟩ := hy
  refine ⟨n * e + m * d, d * e, Nat.mul_pos hd he, ?_, ?_⟩
  · push_cast
    grind
  · rw [mul_qpow, ← qpow_mul, Nat.mul_comm d e, ← qpow_mul, two_pow_add, ← two_zpow_qpow,
      ← two_zpow_qpow]
    exact mul_le_mul_nonneg (qpow_le_qpow (Rat.le_of_lt (two_pow_pos n)) hax e)
      (qpow_le_qpow (Rat.le_of_lt (two_pow_pos m)) hby d)
      (Rat.pow_nonneg (Rat.le_of_lt (two_pow_pos n))) (Rat.pow_nonneg (Rat.le_of_lt (two_pow_pos m)))

/-- A larger exponent: `a ≤ 2^x` and `x ≤ y` give `a ≤ 2^y`. -/
theorem le2_mono {a x y : ℚ} (ha : 0 ≤ a) (hx : Le2 a x) (hxy : x ≤ y) : Le2 a y := by
  obtain ⟨n, d, hd, hxd, hax⟩ := hx
  have hy := mul_den_eq_num y
  refine ⟨y.num * d, d * y.den, Nat.mul_pos hd y.den_pos, ?_, ?_⟩
  · push_cast; grind
  · rw [← qpow_mul]
    refine Rat.le_trans (qpow_le_qpow (Rat.pow_nonneg ha) hax y.den) ?_
    rw [two_zpow_qpow]
    apply two_pow_le
    have hden : (0 : ℚ) ≤ (y.den : ℚ) := by exact_mod_cast Nat.zero_le _
    have hd0 : (0 : ℚ) ≤ (d : ℚ) := by exact_mod_cast Nat.zero_le _
    have := Rat.mul_le_mul_of_nonneg_right hxy (Rat.mul_nonneg hd0 hden)
    have e1 : x * ((d : ℚ) * y.den) = (n : ℚ) * y.den := by rw [← hxd]; grind
    have e2 : y * ((d : ℚ) * y.den) = (y.num : ℚ) * d := by rw [← hy]; grind
    rw [e1, e2] at this
    exact_mod_cast this

/-- A smaller base: `a ≤ b ≤ 2^x` gives `a ≤ 2^x`. -/
theorem le2_of_le {a b x : ℚ} (ha : 0 ≤ a) (hab : a ≤ b) (hb : Le2 b x) : Le2 a x := by
  obtain ⟨n, d, hd, hxd, hbx⟩ := hb
  exact ⟨n, d, hd, hxd, Rat.le_trans (qpow_le_qpow ha hab d) hbx⟩

/-- A smaller exponent: `2^y ≤ a` and `x ≤ y` give `2^x ≤ a`. -/
theorem ge2_mono {a x y : ℚ} (hy : Ge2 a y) (hxy : x ≤ y) : Ge2 a x := by
  obtain ⟨n, d, hd, hyd, hay⟩ := hy
  have hx := mul_den_eq_num x
  refine ⟨x.num * d, d * x.den, Nat.mul_pos hd x.den_pos, ?_, ?_⟩
  · push_cast; grind
  · rw [← qpow_mul]
    refine Rat.le_trans ?_ (qpow_le_qpow (Rat.le_of_lt (two_pow_pos n)) hay x.den)
    rw [two_zpow_qpow]
    apply two_pow_le
    have hden : (0 : ℚ) ≤ (x.den : ℚ) := by exact_mod_cast Nat.zero_le _
    have hd0 : (0 : ℚ) ≤ (d : ℚ) := by exact_mod_cast Nat.zero_le _
    have := Rat.mul_le_mul_of_nonneg_right hxy (Rat.mul_nonneg hd0 hden)
    have e1 : y * ((d : ℚ) * x.den) = (n : ℚ) * x.den := by rw [← hyd]; grind
    have e2 : x * ((d : ℚ) * x.den) = (x.num : ℚ) * d := by rw [← hx]; grind
    rw [e1, e2] at this
    exact_mod_cast this

/-- `a ≤ 2^x ≤ b` gives `a ≤ b`. -/
theorem le_of_le2_ge2 {a b x : ℚ} (ha : 0 ≤ a) (hb : 0 ≤ b) (h1 : Le2 a x) (h2 : Ge2 b x) :
    a ≤ b := by
  obtain ⟨n, d, hd, hxd, hax⟩ := h1
  obtain ⟨m, e, he, hxe, hbx⟩ := h2
  have hne : n * (e : ℤ) = m * (d : ℤ) := by
    have : (n : ℚ) * e = (m : ℚ) * d := by rw [← hxd, ← hxe]; grind
    exact_mod_cast this
  apply le_of_qpow_le hb (Nat.mul_pos hd he)
  calc a ^ (d * e) = (a ^ d) ^ e := (qpow_mul a d e).symm
    _ ≤ ((2 : ℚ) ^ n) ^ e := qpow_le_qpow (Rat.pow_nonneg ha) hax e
    _ = (2 : ℚ) ^ (m * d) := by rw [two_zpow_qpow, hne]
    _ = ((2 : ℚ) ^ m) ^ d := (two_zpow_qpow m d).symm
    _ ≤ (b ^ e) ^ d := qpow_le_qpow (Rat.le_of_lt (two_pow_pos m)) hbx d
    _ = b ^ (d * e) := by rw [qpow_mul, Nat.mul_comm]

/-- `a ≤ 2^x` with `a ≥ 1` forces `x ≥ 0`. -/
theorem one_qpow : ∀ n : ℕ, (1 : ℚ) ^ n = 1
  | 0 => Rat.pow_zero 1
  | n + 1 => by rw [Rat.pow_succ, one_qpow n, Rat.mul_one]

theorem nonneg_of_le2 {a x : ℚ} (h1 : 1 ≤ a) (h : Le2 a x) : 0 ≤ x := by
  obtain ⟨n, d, hd, hxd, hax⟩ := h
  apply Rat.not_lt.mp
  intro hx
  have hn : n < 0 := by
    have : (n : ℚ) < 0 := by
      have := Rat.mul_lt_mul_of_pos_right hx (show (0 : ℚ) < d by exact_mod_cast hd)
      grind
    exact_mod_cast this
  have h2 : (2 : ℚ) ^ n < 1 := by
    have := two_pow_lt (show n < 0 by omega); rwa [two_pow_zero] at this
  have h3 : (1 : ℚ) ≤ a ^ d := by
    have := qpow_le_qpow (by decide) h1 d
    rwa [one_qpow] at this
  grind

/-- **A rational lower bound for a power of two**: `1 + t ≤ 2^(1/k)` when `k t ≤ 1/2`. -/
theorem le2_one_add {t : ℚ} {k : ℕ} (hk : 0 < k) (ht : 0 ≤ t) (hkt : (k : ℚ) * t ≤ 1 / 2) :
    Le2 (1 + t) (1 / k) := by
  refine ⟨1, k, hk, ?_, ?_⟩
  · have : (k : ℚ) ≠ 0 := by exact_mod_cast (show k ≠ 0 by omega)
    rw [Rat.div_def, Rat.one_mul, Rat.inv_mul_cancel _ this]; rfl
  · have h := pow_mul_one_sub_le ht k
    rw [two_pow_one]
    have hpos : 0 ≤ (1 + t) ^ k := Rat.pow_nonneg (by grind)
    have : (1 + t) ^ k * (1 / 2) ≤ (1 + t) ^ k * (1 - k * t) :=
      Rat.mul_le_mul_of_nonneg_left (by grind) hpos
    grind

/-! ## The computed shifts -/

/-- **Their assumption (1)**, `|log2f(x) − log₂ x| ≤ 4u log₂ x`, for `x ≥ 1`: equivalently
`log₂ x ≤ log2f(x)/(1 − 4u)` and `log2f(x)/(1 + 4u) ≤ log₂ x`. -/
def Log2fSpec (u : ℚ) (log2f : ℚ → ℚ) : Prop :=
  ∀ x : ℚ, 1 ≤ x → Le2 x (log2f x / (1 - 4 * u)) ∧ Ge2 x (log2f x / (1 + 4 * u))

/-- **The floor of lines 11–12**: with `c0 ≤ −1/(2(1 − 4u))` (`single▽(−0.5/(1 − 4u))`), a
round-down `fma`, `F ≤ c0 e + P'`, and `g = ⌊F⌋`, `2g ≤ 2P' − e/(1 − 4u)` for `e ≥ 0`. -/
theorem uchino_shift_floor {u c0 P' e F : ℚ} {g : ℤ} (hu4 : 4 * u < 1) (he : 0 ≤ e)
    (hc0 : c0 ≤ -1 / (2 * (1 - 4 * u))) (hF : F ≤ c0 * e + P') (hg : g = F.floor) :
    2 * (g : ℚ) ≤ 2 * P' - e / (1 - 4 * u) := by
  have hgF : (g : ℚ) ≤ F := hg ▸ Rat.floor_le F
  have h1 := Rat.mul_le_mul_of_nonneg_right hc0 he
  have hpos : (0 : ℚ) < 1 - 4 * u := by grind
  have e1 : -1 / (2 * (1 - 4 * u)) * e = -(e / (1 - 4 * u)) / 2 := by grind
  grind

/-- **The shift bound**: for a row (or column) whose maximum of `D̄` is `d ≥ 1`, with
`e = log2f(d)`, every entry `c̄ ≤ d` of `C̄` satisfies `2^(2g) c̄ ≤ 2^(2P')`. -/
theorem uchino_shift_le_of {u c0 P' d e F : ℚ} {g : ℤ} (hu4 : 4 * u < 1)
    (hle : Le2 d (e / (1 - 4 * u))) (hd : 1 ≤ d) (hc0 : c0 ≤ -1 / (2 * (1 - 4 * u)))
    (hF : F ≤ c0 * e + P') (hg : g = F.floor) {cbar : ℚ} (hc : 0 ≤ cbar) (hcd : cbar ≤ d) :
    Le2 (2 ^ (2 * g) * cbar) (2 * P') := by
  have hE0 := nonneg_of_le2 hd hle
  have hpos : (0 : ℚ) < 1 - 4 * u := by grind
  have he0 : 0 ≤ e := by
    have e1 : e = e / (1 - 4 * u) * (1 - 4 * u) := by grind
    rw [e1]; exact Rat.mul_nonneg hE0 (Rat.le_of_lt hpos)
  have h2g := uchino_shift_floor hu4 he0 hc0 hF hg
  have h2 : (0 : ℚ) ≤ 2 ^ (2 * g) := Rat.le_of_lt (two_pow_pos _)
  have hm := le2_mul h2 (by grind) (le2_of_le_two_pow (k := 2 * g) Rat.le_refl) hle
  have hm2 := le2_mono (Rat.mul_nonneg h2 (by grind)) hm
    (show (((2 * g : ℤ) : ℚ)) + e / (1 - 4 * u) ≤ 2 * P' by push_cast; grind)
  exact le2_of_le (Rat.mul_nonneg h2 hc) (Rat.mul_le_mul_of_nonneg_left hcd h2) hm2

theorem uchino_shift_le {u c0 P' d F : ℚ} {log2f : ℚ → ℚ} {g : ℤ} (hu4 : 4 * u < 1)
    (hL : Log2fSpec u log2f) (hd : 1 ≤ d) (hc0 : c0 ≤ -1 / (2 * (1 - 4 * u)))
    (hF : F ≤ c0 * log2f d + P') (hg : g = F.floor) {cbar : ℚ} (hc : 0 ≤ cbar) (hcd : cbar ≤ d) :
    Le2 (2 ^ (2 * g) * cbar) (2 * P') :=
  uchino_shift_le_of hu4 (hL d hd).1 hd hc0 hF hg hc hcd

/-- **One entry from its row and its column** (the geometric mean in their (31)): if
`2^(2g) X ≤ 2^(2P')` and `2^(2h) X ≤ 2^(2P') ≤ M`, then `2^(g + h) X ≤ M`. -/
theorem le_of_row_col {P' M X : ℚ} {g h : ℤ} (hX : 0 ≤ X) (hM : 0 ≤ M)
    (hrow : Le2 (2 ^ (2 * g) * X) (2 * P')) (hcol : Le2 (2 ^ (2 * h) * X) (2 * P'))
    (hP' : Ge2 M (2 * P')) : 2 ^ (g + h) * X ≤ M := by
  have hg := Rat.le_of_lt (two_pow_pos (2 * g))
  have hh := Rat.le_of_lt (two_pow_pos (2 * h))
  have h1 := le2_mul (Rat.mul_nonneg hg hX) (Rat.mul_nonneg hh hX) hrow hcol
  have h2 := ge2_mul hP' hP'
  have e : 2 ^ (2 * g) * X * (2 ^ (2 * h) * X) = (2 ^ (g + h) * X) ^ 2 := by
    rw [Rat.pow_succ, Rat.pow_succ, Rat.pow_zero]
    have h' : (2 : ℚ) ^ (g + h) * 2 ^ (g + h) = 2 ^ (2 * g) * 2 ^ (2 * h) := by
      rw [← two_pow_add, ← two_pow_add]; congr 1; omega
    grind
  rw [e] at h1
  have hY : 0 ≤ 2 ^ (g + h) * X := Rat.mul_nonneg (Rat.le_of_lt (two_pow_pos _)) hX
  have h3 := le_of_le2_ge2 (Rat.pow_nonneg hY) (Rat.mul_nonneg hM hM) h1 h2
  apply le_of_qpow_le hM (n := 2) (by decide)
  rw [show M ^ 2 = M * M by rw [Rat.pow_succ, Rat.pow_succ, Rat.pow_zero]; grind]
  exact h3

/-! ## Their Lemma 1 -/

/-- `Ā = ⌈diag(2^μ') |A|⌉` for one row (their line 4), and `B̄` for one column (line 6). -/
def barScale (s : ℤ) (x : List ℚ) : List ℤ := x.map fun a => (Rat.abs a * 2 ^ s).ceil

theorem barScale_nonneg (s : ℤ) (x : List ℚ) : ∀ z ∈ barScale s x, 0 ≤ z := by
  intro z hz
  obtain ⟨a, _, rfl⟩ := List.mem_map.mp hz
  have h0 : (0 : ℚ) ≤ Rat.abs a * 2 ^ s := Rat.mul_nonneg (abs_nonneg a) (Rat.le_of_lt (two_pow_pos s))
  have : (0 : ℚ) ≤ ((Rat.abs a * 2 ^ s).ceil : ℚ) := Rat.le_trans h0 Rat.le_ceil
  exact_mod_cast this

theorem dotZ_nonneg : ∀ {x y : List ℤ}, (∀ a ∈ x, 0 ≤ a) → (∀ b ∈ y, 0 ≤ b) → 0 ≤ dotZ x y
  | [], _, _, _ => by simp
  | _ :: _, [], _, _ => by simp
  | a :: x, b :: y, hx, hy => by
    rw [dotZ_cons]
    have := dotZ_nonneg (fun c hc => hx c (List.mem_cons_of_mem _ hc))
      (fun c hc => hy c (List.mem_cons_of_mem _ hc))
    have := Int.mul_nonneg (hx a List.mem_cons_self) (hy b List.mem_cons_self)
    omega

/-- `|A'||B'| ≤ diag(2^g) C̄ diag(2^h)` entrywise, for `A' = trunc(diag(2^(μ' + g)) A)` and
`B' = trunc(B diag(2^(ν' + h)))` (their (16) and (28)). -/
theorem dotAbs_scaleTrunc_le (μ' ν' g h : ℤ) : ∀ x y : List ℚ,
    (dotAbs (scaleTrunc (μ' + g) x) (scaleTrunc (ν' + h) y) : ℚ) ≤
      2 ^ (g + h) * (dotZ (barScale μ' x) (barScale ν' y) : ℚ)
  | [], y => by
    simp only [scaleTrunc, barScale, List.map_nil, dotAbs_nil_left, dotZ_nil_left]
    simp
  | _ :: _, [] => by
    simp only [scaleTrunc, barScale, List.map_nil, List.map_cons, dotAbs_nil_right,
      dotZ_nil_right]
    simp
  | a :: x, b :: y => by
    have ih := dotAbs_scaleTrunc_le μ' ν' g h x y
    simp only [scaleTrunc, barScale, List.map_cons, dotAbs_cons, dotZ_cons] at ih ⊢
    push_cast
    have ha := abs_truncInt_le a (μ' + g)
    have hb := abs_truncInt_le b (ν' + h)
    have hca : Rat.abs a * 2 ^ μ' ≤ (((Rat.abs a * 2 ^ μ').ceil : ℤ) : ℚ) := Rat.le_ceil
    have hcb : Rat.abs b * 2 ^ ν' ≤ (((Rat.abs b * 2 ^ ν').ceil : ℤ) : ℚ) := Rat.le_ceil
    have hg := Rat.le_of_lt (two_pow_pos g)
    have hh := Rat.le_of_lt (two_pow_pos h)
    have ea : (2 : ℚ) ^ (μ' + g) * Rat.abs a = 2 ^ g * (Rat.abs a * 2 ^ μ') := by
      rw [two_pow_add]; grind
    have eb : (2 : ℚ) ^ (ν' + h) * Rat.abs b = 2 ^ h * (Rat.abs b * 2 ^ ν') := by
      rw [two_pow_add]; grind
    have ha2 := Rat.le_trans ha (ea ▸ Rat.mul_le_mul_of_nonneg_left hca hg)
    have hb2 := Rat.le_trans hb (eb ▸ Rat.mul_le_mul_of_nonneg_left hcb hh)
    have hab := mul_le_mul_nonneg ha2 hb2 (abs_nonneg _) (abs_nonneg _)
    have e1 : ((((truncInt (a * 2 ^ (μ' + g)) * truncInt (b * 2 ^ (ν' + h))).natAbs : ℕ) : ℚ)) =
        Rat.abs (truncInt (a * 2 ^ (μ' + g)) : ℚ) * Rat.abs (truncInt (b * 2 ^ (ν' + h)) : ℚ) := by
      rw [← abs_mul, ← Rat.intCast_mul, abs_intCast]
    rw [e1]
    have e2 : (2 : ℚ) ^ (g + h) = 2 ^ g * 2 ^ h := two_pow_add g h
    rw [e2] at ih ⊢
    grind

/-- **Their Lemma 1** for one entry: with the computed shifts `g = ⌊F_row⌋`, `h = ⌊F_col⌋` of
lines 9–12 (`d_row`, `d_col ≥ 1` the maxima of `D̄` in the entry's row and column, both at least
the entry `c̄` of `C̄`), and `2^(2P') ≤ (P − 1)/2` (`P' = single▽(log₂(P − 1)/2 − 0.5)`),
`Σₕ |A'ₕ| |B'ₕ| ≤ (P − 1)/2`. No empirical constant is needed. -/
theorem uchino_lemma1_of {u c0 P' : ℚ} {P : ℕ} (hu4 : 4 * u < 1)
    (hc0 : c0 ≤ -1 / (2 * (1 - 4 * u))) (hP : 1 ≤ P) (hP' : Ge2 (((P : ℚ) - 1) / 2) (2 * P'))
    {μ' ν' g h : ℤ} {x y : List ℚ} {dr dc er ec Fr Fc : ℚ}
    (hdr : (dotZ (barScale μ' x) (barScale ν' y) : ℚ) ≤ dr) (hdr1 : 1 ≤ dr)
    (her : Le2 dr (er / (1 - 4 * u))) (hFr : Fr ≤ c0 * er + P') (hg : g = Fr.floor)
    (hdc : (dotZ (barScale μ' x) (barScale ν' y) : ℚ) ≤ dc) (hdc1 : 1 ≤ dc)
    (hec : Le2 dc (ec / (1 - 4 * u))) (hFc : Fc ≤ c0 * ec + P') (hh : h = Fc.floor) :
    (dotAbs (scaleTrunc (μ' + g) x) (scaleTrunc (ν' + h) y) : ℚ) ≤ ((P : ℚ) - 1) / 2 := by
  have hc0' : (0 : ℚ) ≤ (dotZ (barScale μ' x) (barScale ν' y) : ℚ) := by
    exact_mod_cast dotZ_nonneg (barScale_nonneg μ' x) (barScale_nonneg ν' y)
  have hrow := uchino_shift_le_of hu4 her hdr1 hc0 hFr hg hc0' hdr
  have hcol := uchino_shift_le_of hu4 hec hdc1 hc0 hFc hh hc0' hdc
  have hM : (0 : ℚ) ≤ ((P : ℚ) - 1) / 2 := by
    have : (1 : ℚ) ≤ P := by exact_mod_cast hP
    rw [show ((P : ℚ) - 1) / 2 = ((P : ℚ) - 1) * (1 / 2) by grind]
    exact Rat.mul_nonneg (by grind) (by decide +kernel)
  exact Rat.le_trans (dotAbs_scaleTrunc_le μ' ν' g h x y) (le_of_row_col hc0' hM hrow hcol hP')

theorem uchino_lemma1 {u c0 P' : ℚ} {log2f : ℚ → ℚ} {P : ℕ} (hu4 : 4 * u < 1)
    (hL : Log2fSpec u log2f) (hc0 : c0 ≤ -1 / (2 * (1 - 4 * u))) (hP : 1 ≤ P)
    (hP' : Ge2 (((P : ℚ) - 1) / 2) (2 * P'))
    {μ' ν' g h : ℤ} {x y : List ℚ} {dr dc Fr Fc : ℚ}
    (hdr : (dotZ (barScale μ' x) (barScale ν' y) : ℚ) ≤ dr) (hdr1 : 1 ≤ dr)
    (hFr : Fr ≤ c0 * log2f dr + P') (hg : g = Fr.floor)
    (hdc : (dotZ (barScale μ' x) (barScale ν' y) : ℚ) ≤ dc) (hdc1 : 1 ≤ dc)
    (hFc : Fc ≤ c0 * log2f dc + P') (hh : h = Fc.floor) :
    (dotAbs (scaleTrunc (μ' + g) x) (scaleTrunc (ν' + h) y) : ℚ) ≤ ((P : ℚ) - 1) / 2 :=
  uchino_lemma1_of hu4 hc0 hP hP' hdr hdr1 (hL dr hdr1).1 hFr hg hdc hdc1 (hL dc hdc1).1 hFc hh

/-- Lemma 1 as they state it: `|A'||B'| < P/2`. -/
theorem uchino_lemma1_lt {u c0 P' : ℚ} {log2f : ℚ → ℚ} {P : ℕ} (hu4 : 4 * u < 1)
    (hL : Log2fSpec u log2f) (hc0 : c0 ≤ -1 / (2 * (1 - 4 * u))) (hP : 1 ≤ P)
    (hP' : Ge2 (((P : ℚ) - 1) / 2) (2 * P'))
    {μ' ν' g h : ℤ} {x y : List ℚ} {dr dc Fr Fc : ℚ}
    (hdr : (dotZ (barScale μ' x) (barScale ν' y) : ℚ) ≤ dr) (hdr1 : 1 ≤ dr)
    (hFr : Fr ≤ c0 * log2f dr + P') (hg : g = Fr.floor)
    (hdc : (dotZ (barScale μ' x) (barScale ν' y) : ℚ) ≤ dc) (hdc1 : 1 ≤ dc)
    (hFc : Fc ≤ c0 * log2f dc + P') (hh : h = Fc.floor) :
    2 * dotAbs (scaleTrunc (μ' + g) x) (scaleTrunc (ν' + h) y) < P := by
  have := uchino_lemma1 hu4 hL hc0 hP hP' hdr hdr1 hFr hg hdc hdc1 hFc hh
  have h2 : (2 * dotAbs (scaleTrunc (μ' + g) x) (scaleTrunc (ν' + h) y) : ℚ) < P := by grind
  exact_mod_cast h2

/-- **Lemma 1 with their slack**: if the shifts satisfy their exhaustively checked
`⌊fl▽(fma(c0, e, P'))⌋ ≤ P' − e'/2 − 2^-21` (`e' = log₂` of the row's maximum `m` of `C̄`),
written `2^(2g) m ≤ 2^(2P' − 1/k)` with `k = 2^20`, then `|A'||B'| (1 + t) ≤ (P − 1)/2` for every
`t ≥ 0` with `k t ≤ 1/2` (theirs: `(P − 1) 2^(−1 − 2^-20)`). -/
theorem uchino_lemma1_slack {P' : ℚ} {P : ℕ} (hP : 1 ≤ P) (hP' : Ge2 (((P : ℚ) - 1) / 2) (2 * P'))
    {k : ℕ} (hk : 0 < k) {t : ℚ} (ht : 0 ≤ t) (hkt : (k : ℚ) * t ≤ 1 / 2)
    {μ' ν' g h : ℤ} {x y : List ℚ} {mr mc : ℚ}
    (hmr : (dotZ (barScale μ' x) (barScale ν' y) : ℚ) ≤ mr)
    (hrow : Le2 (2 ^ (2 * g) * mr) (2 * P' - 1 / k))
    (hmc : (dotZ (barScale μ' x) (barScale ν' y) : ℚ) ≤ mc)
    (hcol : Le2 (2 ^ (2 * h) * mc) (2 * P' - 1 / k)) :
    (dotAbs (scaleTrunc (μ' + g) x) (scaleTrunc (ν' + h) y) : ℚ) * (1 + t) ≤
      ((P : ℚ) - 1) / 2 := by
  have hc0 : (0 : ℚ) ≤ (dotZ (barScale μ' x) (barScale ν' y) : ℚ) := by
    exact_mod_cast dotZ_nonneg (barScale_nonneg μ' x) (barScale_nonneg ν' y)
  have hv := Rat.mul_le_mul_of_nonneg_right (dotAbs_scaleTrunc_le μ' ν' g h x y)
    (show (0 : ℚ) ≤ 1 + t by grind)
  generalize (dotZ (barScale μ' x) (barScale ν' y) : ℚ) = cb at hc0 hmr hmc hv
  have ht1 := le2_one_add hk ht hkt
  have hX : 0 ≤ cb * (1 + t) := Rat.mul_nonneg hc0 (by grind)
  have side : ∀ {s : ℤ} {m : ℚ}, cb ≤ m → Le2 (2 ^ (2 * s) * m) (2 * P' - 1 / k) →
      Le2 (2 ^ (2 * s) * (cb * (1 + t))) (2 * P') := by
    intro s m hm hs
    have h2 := Rat.le_of_lt (two_pow_pos (2 * s))
    have h1 := le2_of_le (Rat.mul_nonneg h2 hc0) (Rat.mul_le_mul_of_nonneg_left hm h2) hs
    have h3 := le2_mul (Rat.mul_nonneg h2 hc0) (by grind) h1 ht1
    rw [show 2 * P' - 1 / (k : ℚ) + 1 / k = 2 * P' by grind] at h3
    rwa [← Rat.mul_assoc]
  have hM : (0 : ℚ) ≤ ((P : ℚ) - 1) / 2 := by
    have : (1 : ℚ) ≤ P := by exact_mod_cast hP
    rw [show ((P : ℚ) - 1) / 2 = ((P : ℚ) - 1) * (1 / 2) by grind]
    exact Rat.mul_nonneg (by grind) (by decide +kernel)
  have hent := le_of_row_col hX hM (side hmr hrow) (side hmc hcol) hP'
  grind

/-- Their exhaustive check `⌊P' − (1 + u)e'/2⌋ ≤ P' − e'/2 − 2^-21` (proof of Lemma 1) holds for
the values `e' = log₂ m` of the integer maxima `m` they enumerate, not on the interval
`0 ≤ e' ≤ 29`: for every `P'` a rational `e' ≤ 4` violates it. -/
theorem uchino_slack_needs_integers (P' : ℚ) :
    ∃ e : ℚ, 0 ≤ e ∧ e ≤ 29 ∧
      P' - e / 2 - 2 ^ (-21 : ℤ) < (((P' - (1 + 2 ^ (-24 : ℤ)) * e / 2).floor : ℤ) : ℚ) := by
  have hu : (2 : ℚ) ^ (-24 : ℤ) = 1 / 16777216 := by decide +kernel
  have h21 : (2 : ℚ) ^ (-21 : ℤ) = 1 / 2097152 := by decide +kernel
  rw [hu, h21]
  have hf1 := Rat.floor_le P'
  have hf2 := Rat.lt_floor_add_one P'
  push_cast at hf2
  refine ⟨2 * (P' - ((P'.floor - 1 : ℤ) : ℚ)) / (1 + 1 / 16777216), ?_, ?_, ?_⟩
  · push_cast
    have h0 : (0 : ℚ) ≤ 2 * (P' - (P'.floor - 1)) := by grind
    have e : 2 * (P' - ((P'.floor : ℚ) - 1)) / (1 + 1 / 16777216) =
        2 * (P' - (P'.floor - 1)) * (16777216 / 16777217) := by grind
    rw [e]; exact Rat.mul_nonneg h0 (by decide +kernel)
  · push_cast
    have e : 2 * (P' - ((P'.floor : ℚ) - 1)) / (1 + 1 / 16777216) =
        2 * (P' - (P'.floor - 1)) * (16777216 / 16777217) := by grind
    rw [e]
    have : 2 * (P' - ((P'.floor : ℚ) - 1)) ≤ 4 := by grind
    have := Rat.mul_le_mul_of_nonneg_right this (show (0 : ℚ) ≤ 16777216 / 16777217 by decide +kernel)
    grind
  · have e : P' - (1 + 1 / 16777216) * (2 * (P' - ((P'.floor - 1 : ℤ) : ℚ)) /
        (1 + 1 / 16777216)) / 2 = ((P'.floor - 1 : ℤ) : ℚ) := by grind
    rw [e, Rat.floor_intCast]
    push_cast
    have e2 : 2 * (P' - ((P'.floor : ℚ) - 1)) / (1 + 1 / 16777216) =
        2 * (P' - (P'.floor - 1)) * (16777216 / 16777217) := by grind
    rw [e2]
    grind

/-! ## The reconstruction for every residue vector -/

/-- `ρ = Σ ⌊p_ℓ/2⌋`, the bound on `Σ |W_ℓ|` for symmetric residues. -/
def uchinoRho (B : CRTBasis) : ℚ := ((B.moduli.map (· / 2)).sum : ℕ)

theorem absSum_ofInts_le_rho : ∀ (W : List ℤ) (ms : List ℕ), W.length = ms.length →
    (∀ pr ∈ W.zip ms, 2 * pr.1.natAbs ≤ pr.2) →
    absSum (ofInts W) ≤ ((ms.map (· / 2)).sum : ℕ)
  | [], _, _, _ => by simp only [absSum, ofInts, List.map_nil, List.sum_nil]; exact Rat.natCast_nonneg
  | _ :: _, [], h, _ => by simp at h
  | r :: W, m :: ms, h, hb => by
    have ih := absSum_ofInts_le_rho W ms (by simpa using h)
      fun pr hpr => hb pr (by simp [hpr])
    have hr : 2 * r.natAbs ≤ m := hb (r, m) (by simp)
    have hr2 : r.natAbs ≤ m / 2 := by omega
    have e : absSum (ofInts (r :: W)) = Rat.abs (r : ℚ) + absSum (ofInts W) := by
      simp [absSum, ofInts]
    rw [e, abs_intCast, List.map_cons, List.sum_cons]
    push_cast
    have : ((r.natAbs : ℕ) : ℚ) ≤ ((m / 2 : ℕ) : ℚ) := by exact_mod_cast hr2
    grind

theorem abs_dotZ_sub_hi_le (G : ℤ) : ∀ w W : List ℤ,
    Rat.abs ((dotZ w W : ℚ) - dot (w.map (weightHi G)) (ofInts W)) ≤
      (List.zipWith (fun a r : ℤ => Rat.abs ((a : ℚ) - weightHi G a) * Rat.abs (r : ℚ)) w W).sum
  | [], W => by simp <;> decide +kernel
  | _ :: _, [] => by simp [ofInts] <;> decide +kernel
  | a :: w, r :: W => by
    have ih := abs_dotZ_sub_hi_le G w W
    simp only [ofInts, List.map_cons, dotZ_cons, dot_cons, Rat.intCast_add, Rat.intCast_mul,
      List.zipWith_cons_cons, List.sum_cons] at ih ⊢
    generalize dot (w.map (weightHi G)) (List.map (fun z : ℤ => (z : ℚ)) W) = d1 at ih ⊢
    generalize (dotZ w W : ℚ) = d0 at ih ⊢
    have e : (a : ℚ) * r + d0 - (weightHi G a * r + d1) = ((a : ℚ) - weightHi G a) * r + (d0 - d1) := by
      grind
    rw [e]
    have := abs_add_le (((a : ℚ) - weightHi G a) * r) (d0 - d1)
    rw [abs_mul] at this
    grind

theorem natAbs_products_le {M : ℚ} (hM : 0 ≤ M) : ∀ w W : List ℤ, (∀ a ∈ w, 0 ≤ a ∧ (a : ℚ) ≤ M) →
    (List.zipWith (fun a r : ℤ => (((a * r).natAbs : ℕ) : ℚ)) w W).sum ≤ M * absSum (ofInts W)
  | [], W, _ => by simpa using Rat.mul_nonneg hM (absSum_nonneg (ofInts W))
  | _ :: _, [], _ => by simp [absSum]
  | a :: w, r :: W, hw => by
    have ih := natAbs_products_le hM w W fun b hb => hw b (List.mem_cons_of_mem _ hb)
    obtain ⟨ha0, haM⟩ := hw a List.mem_cons_self
    simp only [List.zipWith_cons_cons, List.sum_cons, ofInts_cons]
    have e : absSum ((r : ℚ) :: ofInts W) = Rat.abs (r : ℚ) + absSum (ofInts W) := by
      simp [absSum]
    rw [e, ← abs_intCast, Rat.intCast_mul, abs_mul, abs_of_nonneg (by exact_mod_cast ha0)]
    have := Rat.mul_le_mul_of_nonneg_right haM (abs_nonneg (r : ℚ))
    grind

/-- The quotient is small: `|q| ≤ ρ + 1/2` when `Σ w_ℓ W_ℓ = q P + c` with `0 ≤ w_ℓ ≤ P`,
`Σ |W_ℓ| ≤ ρ` and `2|c| < P`. -/
theorem abs_quot_le {P : ℕ} (hP : 0 < P) {w W : List ℤ} (hw : ∀ a ∈ w, 0 ≤ a ∧ (a : ℚ) ≤ P)
    {ρ : ℚ} (hWρ : absSum (ofInts W) ≤ ρ) {q c : ℤ} (hqc : dotZ w W = q * P + c)
    (hc : 2 * Rat.abs (c : ℚ) < P) : Rat.abs (q : ℚ) ≤ ρ + 1 / 2 := by
  have hPq : (0 : ℚ) < P := by exact_mod_cast hP
  have hP0 : (0 : ℚ) ≤ P := Rat.le_of_lt hPq
  have hdot : Rat.abs ((dotZ w W : ℤ) : ℚ) ≤ P * absSum (ofInts W) := by
    rw [← dot_ofInts]
    refine abs_dot_le_mul_absSum hP0 (ofInts w) (ofInts W) fun a ha => ?_
    obtain ⟨z, hz, rfl⟩ := List.mem_map.mp ha
    rw [abs_of_nonneg (by exact_mod_cast (hw z hz).1)]
    exact (hw z hz).2
  have hd : ((dotZ w W : ℤ) : ℚ) = (q : ℚ) * P + c := by rw [hqc]; push_cast; rfl
  have hqP : Rat.abs (q : ℚ) * P ≤ (ρ + 1 / 2) * P := by
    have e : (q : ℚ) * P = ((dotZ w W : ℤ) : ℚ) - c := by grind
    have := abs_sub_le ((dotZ w W : ℤ) : ℚ) (c : ℚ)
    rw [← e, abs_mul, abs_of_nonneg hP0] at this
    have := Rat.mul_le_mul_of_nonneg_left hWρ hP0
    grind
  exact Rat.le_of_mul_le_mul_right hqP hPq

/-- **The first fused multiply-add is exact** for every residue vector when `P1` and the high
parts lie on a grid `2^g0` with `P/2 + K u P ρ + (ρ + 1/2) u P ≤ 2^(p + g0)` (in their
configuration `P1 = fl(P)` has `g0 = ⌊log₂ P⌋ − 52 ≤ G1`, and `P/2 < 2^(52 + g0)`). -/
theorem uchino_fma_exact {p : ℕ} {emin emax : ℤ} (hp : 0 < p) {u : ℚ} (hu0 : 0 ≤ u)
    {P : ℕ} (hP : 0 < P) {w W : List ℤ} (hw : ∀ a ∈ w, 0 ≤ a ∧ (a : ℚ) ≤ P) {G1 g0 : ℤ}
    (hg0 : g0 ≤ G1) {K ρ : ℚ} (hK0 : 0 ≤ K) (hs1 : ∀ a ∈ w, (a : ℚ) - weightHi G1 a ≤ K * u * P)
    (hWρ : absSum (ofInts W) ≤ ρ) {P1 : ℚ} (hP1 : Rat.abs ((P : ℚ) - P1) ≤ u * P)
    (hP1g : GridMultiple g0 P1) {q c : ℤ} (hqc : dotZ w W = q * P + c)
    (hc : 2 * Rat.abs (c : ℚ) < P)
    (hbound : (P : ℚ) / 2 + K * u * P * ρ + (ρ + 1 / 2) * (u * P) ≤ 2 ^ ((p : ℤ) + g0))
    (h1 : emin ≤ g0 + ((p : ℤ) - 1)) (h2 : g0 + ((p : ℤ) - 1) ≤ emax) :
    roundRNE p emin emax (-(q : ℚ) * P1 + dot (w.map (weightHi G1)) (ofInts W)) =
      some (-(q : ℚ) * P1 + dot (w.map (weightHi G1)) (ofInts W)) := by
  have hPq : (0 : ℚ) < P := by exact_mod_cast hP
  have hP0 : (0 : ℚ) ≤ P := Rat.le_of_lt hPq
  have hC1 : GridMultiple g0 (dot (w.map (weightHi G1)) (ofInts W)) :=
    gridMultiple_mono hg0 (gridMultiple_sum (weightHi_products_grid G1 w W))
  apply fma_exact_of_grid hp hC1 hP1g q _ h1 h2
  have hq := abs_quot_le hP hw hWρ hqc hc
  have hs := abs_dotZ_sub_hi_le G1 w W
  have hKuP : ∀ a ∈ w, Rat.abs ((a : ℚ) - weightHi G1 a) ≤ K * u * P := fun a ha => by
    rw [abs_of_nonneg (sub_weightHi_nonneg G1 a)]; exact hs1 a ha
  have h0 : 0 ≤ K * u * P := Rat.mul_nonneg (Rat.mul_nonneg hK0 hu0) hP0
  have hsum : (List.zipWith (fun a r : ℤ => Rat.abs ((a : ℚ) - weightHi G1 a) * Rat.abs (r : ℚ))
      w W).sum ≤ K * u * P * ρ :=
    Rat.le_trans (sum_zipWith_weight_le h0 w W hKuP) (Rat.mul_le_mul_of_nonneg_left hWρ h0)
  have hd : ((dotZ w W : ℤ) : ℚ) = (q : ℚ) * P + c := by rw [hqc]; push_cast; rfl
  generalize dot (w.map (weightHi G1)) (ofInts W) = D1 at hs ⊢
  generalize ((dotZ w W : ℤ) : ℚ) = d at hs hd
  have e : -(q : ℚ) * P1 + D1 = (D1 - d) + c + (q : ℚ) * ((P : ℚ) - P1) := by grind
  rw [e]
  have := abs_add_le ((D1 - d) + c) ((q : ℚ) * ((P : ℚ) - P1))
  have := abs_add_le (D1 - d) (c : ℚ)
  have := abs_sub_comm D1 d
  have hqe : Rat.abs ((q : ℚ) * ((P : ℚ) - P1)) ≤ (ρ + 1 / 2) * (u * P) := by
    rw [abs_mul]
    exact mul_le_mul_nonneg hq hP1 (abs_nonneg _) (abs_nonneg _)
  have hc2 : Rat.abs (c : ℚ) < (P : ℚ) / 2 := by
    have : (P : ℚ) / 2 = (P : ℚ) * (1 / 2) := by grind
    rw [this]; grind
  grind

/-- The bound on `uchinoDelta` for every residue vector: `(K + 2 + u) u P ρ` (their `δ`, from
`fl(P_inv C1)`, `P_inv` and the high parts) plus underflow terms. -/
def uchinoDeltaBar (u η : ℚ) (P : ℕ) (K ρ : ℚ) : ℚ :=
  (K + 2 + u) * u * P * ρ + P * η + (1 + u) * η * P * P * ρ

theorem prod_pos_of_pos : ∀ {ms : List ℕ}, (∀ m ∈ ms, 0 < m) → 0 < ms.prod
  | [], _ => by decide
  | m :: ms, h => by
    rw [List.prod_cons]
    exact Nat.mul_pos (h m List.mem_cons_self)
      (prod_pos_of_pos fun a ha => h a (List.mem_cons_of_mem _ ha))

theorem uchinoDelta_le {u η : ℚ} (hu0 : 0 ≤ u) (hη0 : 0 ≤ η) {P : ℕ} {Pinv : ℚ}
    (hPinv : Rat.abs ((P : ℚ) * Pinv - 1) ≤ u + P * η) {G1 : ℤ} {w W : List ℤ}
    (hw : ∀ a ∈ w, 0 ≤ a ∧ (a : ℚ) ≤ P) {K ρ : ℚ} (hK0 : 0 ≤ K)
    (hs1 : ∀ a ∈ w, (a : ℚ) - weightHi G1 a ≤ K * u * P) (hWρ : absSum (ofInts W) ≤ ρ) :
    uchinoDelta u η P Pinv G1 w W ≤ uchinoDeltaBar u η P K ρ := by
  have hP0 : (0 : ℚ) ≤ P := Rat.natCast_nonneg
  have hρ0 : 0 ≤ ρ := Rat.le_trans (absSum_nonneg _) hWρ
  -- `|C1| ≤ P ρ`
  have hD : Rat.abs (dot (w.map (weightHi G1)) (ofInts W)) ≤ P * ρ := by
    refine Rat.le_trans (abs_dot_le_mul_absSum hP0 _ _ fun a ha => ?_)
      (Rat.mul_le_mul_of_nonneg_left hWρ hP0)
    obtain ⟨z, hz, rfl⟩ := List.mem_map.mp ha
    rw [abs_of_nonneg (weightHi_nonneg (hw z hz).1)]
    exact Rat.le_trans (weightHi_le G1 z) (hw z hz).2
  -- the high parts
  have hKuP : ∀ a ∈ w, Rat.abs ((a : ℚ) - weightHi G1 a) ≤ K * u * P := fun a ha => by
    rw [abs_of_nonneg (sub_weightHi_nonneg G1 a)]; exact hs1 a ha
  have h0 : 0 ≤ K * u * P := Rat.mul_nonneg (Rat.mul_nonneg hK0 hu0) hP0
  have hS := Rat.le_trans (abs_dotZ_sub_hi_le G1 w W)
    (Rat.le_trans (sum_zipWith_weight_le h0 w W hKuP) (Rat.mul_le_mul_of_nonneg_left hWρ h0))
  unfold uchinoDelta uchinoDeltaBar
  generalize dot (w.map (weightHi G1)) (ofInts W) = D1 at hD hS ⊢
  -- `P |P_inv C1| = |P P_inv| |C1|`
  have e1 : (P : ℚ) * (u * Rat.abs (Pinv * D1) + η) =
      u * (Rat.abs ((P : ℚ) * Pinv) * Rat.abs D1) + P * η := by
    rw [abs_mul, abs_mul, abs_of_nonneg hP0]; grind
  rw [e1]
  have hr : Rat.abs ((P : ℚ) * Pinv) ≤ 1 + (u + P * η) := by
    have := abs_add_le ((P : ℚ) * Pinv - 1) 1
    rw [show (P : ℚ) * Pinv - 1 + 1 = P * Pinv by grind] at this
    have : Rat.abs (1 : ℚ) = 1 := by decide +kernel
    grind
  have hPη : 0 ≤ (P : ℚ) * η := Rat.mul_nonneg hP0 hη0
  have m1 := mul_le_mul_nonneg hr hD (abs_nonneg _) (abs_nonneg _)
  have m1' := Rat.mul_le_mul_of_nonneg_left m1 hu0
  have m2 := mul_le_mul_nonneg hPinv hD (abs_nonneg _) (abs_nonneg _)
  -- the target, expanded
  have hPρ : 0 ≤ (P : ℚ) * ρ := Rat.mul_nonneg hP0 hρ0
  have t1 : u * ((1 + (u + P * η)) * (P * ρ)) = (1 + u) * u * P * ρ + u * η * P * P * ρ := by grind
  have t2 : (u + P * η) * (P * ρ) = u * P * ρ + η * P * P * ρ := by grind
  have t3 : K * u * P * ρ = K * u * P * ρ := rfl
  grind

/-- The constant of `uchino_R64`: `(1 + 3u) K (N + 2) u² ρ P + 3u |c|` and the underflow term. -/
def uchinoR64 (u η K ρ N : ℚ) (P : ℕ) (c : ℚ) : ℚ :=
  (1 + 3 * u) * (K * (N + 2) * (u * u) * ρ * P) + 3 * u * Rat.abs c + uchinoEta u η N ρ

/-- **Ozaki-II with their reconstruction and the closed-form `R64`**, for any shifts whose
scaled integers satisfy `|a||c| ≤ Λ` with `2(Λ + δ̄) < P` (`δ̄ = uchinoDeltaBar`), in IEEE
round to nearest even. The other hypotheses are their setting: nonnegative CRT weights at most
`M ≤ P` with `M ρ < 2^(p + G1)` (their choice of `G1`), high parts within `K u P` of the weights,
`ρ ≥ 2`, `K ≥ 2ρ`, `|P − P1| ≤ u P`, `P1` on a grid `2^g0` (`g0 ≤ G1`) with room for the first
`fma`, `P2 = fl(P − P1)`, `P_inv = fl(1/P)`, the rounded low parts `s2`, and `N u ≤ 1/8`. -/
theorem ozaki2Uchino_R64 {mult : MatrixMultiplier} {b bound : ℕ} (hmult : mult.ExactOn b bound)
    {p : ℕ} {emin emax : ℤ} (hp : 0 < p) (hle : emin ≤ emax) {u η : ℚ}
    (hu : u = 2 ^ (-(p : ℤ))) (hη : η = 2 ^ (emin - p))
    {B : CRTBasis} (hB : B.Valid) (hmb : ∀ m ∈ B.moduli, m ≤ 2 ^ (b + 1))
    (hN1 : 1 ≤ B.weights.length) (hNu : (B.weights.length : ℚ) * u ≤ 1 / 8)
    {M : ℚ} (hw : ∀ a ∈ B.weights, 0 ≤ a ∧ (a : ℚ) ≤ M) (hMP : M ≤ B.modulus)
    {G1 g0 : ℤ} (hMρ : M * uchinoRho B < 2 ^ ((p : ℤ) + G1))
    (h1 : emin ≤ G1 + ((p : ℤ) - 1)) (h2 : G1 + ((p : ℤ) - 1) ≤ emax)
    {K : ℚ} (hρ : 2 ≤ uchinoRho B) (hK : 2 * uchinoRho B ≤ K)
    (hs1 : ∀ a ∈ B.weights, (a : ℚ) - weightHi G1 a ≤ K * u * B.modulus)
    {P1 P2 Pinv : ℚ} (hP1 : Rat.abs ((B.modulus : ℚ) - P1) ≤ u * B.modulus)
    (hg0 : g0 ≤ G1) (hP1g : GridMultiple g0 P1)
    (hfma : (B.modulus : ℚ) / 2 + K * u * B.modulus * uchinoRho B +
      (uchinoRho B + 1 / 2) * (u * B.modulus) ≤ 2 ^ ((p : ℤ) + g0))
    (hg01 : emin ≤ g0 + ((p : ℤ) - 1)) (hg02 : g0 + ((p : ℤ) - 1) ≤ emax)
    (hP2 : roundRNE p emin emax ((B.modulus : ℚ) - P1) = some P2)
    (hPinv : roundRNE p emin emax (1 / (B.modulus : ℚ)) = some Pinv)
    {s2 : List ℚ}
    (hs2 : B.weights.mapM (fun a : ℤ => roundRNE p emin emax ((a : ℚ) - weightHi G1 a)) = some s2)
    (sx sy : ℤ) {x y : List ℚ} (hlen : x.length = y.length)
    (hbound : x.length * (2 ^ b * 2 ^ b) ≤ bound)
    {Λ : ℚ} (hΛ : (dotAbs (scaleTrunc sx x) (scaleTrunc sy y) : ℚ) ≤ Λ)
    (hmargin : 2 * (Λ + uchinoDeltaBar u η B.modulus K (uchinoRho B)) < B.modulus)
    {v : ℚ} (hv : ozaki2Uchino mult (roundRNE p emin emax) B G1 P1 P2 Pinv s2 sx sy x y = some v) :
    Rat.abs (v - dot x y) ≤
      u * (Rat.abs ((dotZ (scaleTrunc sx x) (scaleTrunc sy y) : ℚ) * 2 ^ (-(sx + sy))) +
          uchinoR64 u η K (uchinoRho B) B.weights.length B.modulus
            (dotZ (scaleTrunc sx x) (scaleTrunc sy y)) * 2 ^ (-(sx + sy))) + η +
        uchinoR64 u η K (uchinoRho B) B.weights.length B.modulus
          (dotZ (scaleTrunc sx x) (scaleTrunc sy y)) * 2 ^ (-(sx + sy)) +
        (2 ^ (-sx) * absSum y + 2 ^ (-sy) * absSum x) := by
  have hround : RoundWithin (roundRNE p emin emax) u η := by rw [hu, hη]; exact roundRNE_within
  have hu0 : 0 ≤ u := by rw [hu]; exact Rat.le_of_lt (two_pow_pos _)
  have hη0 : 0 ≤ η := by rw [hη]; exact Rat.le_of_lt (two_pow_pos _)
  have hPpos : 0 < B.modulus := by
    unfold CRTBasis.modulus
    exact prod_pos_of_pos hB.2.1
  have hPq : (0 : ℚ) < B.modulus := by exact_mod_cast hPpos
  have hP0 : (0 : ℚ) ≤ B.modulus := Rat.le_of_lt hPq
  have hK0 : 0 ≤ K := by grind
  have hwP : ∀ a ∈ B.weights, 0 ≤ a ∧ (a : ℚ) ≤ B.modulus := fun a ha =>
    ⟨(hw a ha).1, Rat.le_trans (hw a ha).2 hMP⟩
  -- `|P P_inv − 1| ≤ u + P η`
  have hPinv' : Rat.abs ((B.modulus : ℚ) * Pinv - 1) ≤ u + B.modulus * η := by
    have hr := hround _ _ hPinv
    have hne : (B.modulus : ℚ) ≠ 0 := by grind
    have hi : 0 ≤ 1 / (B.modulus : ℚ) := by
      have : (1 : ℚ) / B.modulus * B.modulus = 1 := by grind
      apply Rat.not_lt.mp
      intro hlt
      have := Rat.mul_lt_mul_of_pos_right hlt hPq
      grind
    rw [abs_of_nonneg hi] at hr
    have e : (B.modulus : ℚ) * Pinv - 1 = B.modulus * (Pinv - 1 / B.modulus) := by grind
    rw [e, abs_mul, abs_of_nonneg hP0]
    have := Rat.mul_le_mul_of_nonneg_left hr hP0
    have e2 : (B.modulus : ℚ) * (u * (1 / B.modulus) + η) = u + B.modulus * η := by grind
    grind
  apply ozaki2Uchino_error hmult hu0 hround hB hmb sx sy hlen hbound _ hv
  intro W hWlen hWb hdvd C hC
  generalize hcd : dotZ (scaleTrunc sx x) (scaleTrunc sy y) = c at hdvd hΛ ⊢
  obtain ⟨q, hq⟩ := hdvd
  have hqc : dotZ B.weights W = q * B.modulus + c := by grind
  have hWρ : absSum (ofInts W) ≤ uchinoRho B := absSum_ofInts_le_rho W B.moduli hWlen hWb
  have hcΛ : Rat.abs (c : ℚ) ≤ Λ := by
    have h := natAbs_dotZ_le (scaleTrunc sx x) (scaleTrunc sy y)
    rw [hcd] at h
    rw [abs_intCast]
    exact Rat.le_trans (by exact_mod_cast h) hΛ
  have hδ := uchinoDelta_le hu0 hη0 hPinv' hwP hK0 hs1 hWρ (G1 := G1)
  have hmarg : 2 * (Rat.abs (c : ℚ) + uchinoDelta u η B.modulus Pinv G1 B.weights W) <
      B.modulus := by grind
  have hc2 : 2 * Rat.abs (c : ℚ) < B.modulus := by
    have := Rat.le_trans (absSum_nonneg _) hWρ
    have : 0 ≤ uchinoDelta u η B.modulus Pinv G1 B.weights W := by
      unfold uchinoDelta
      have := Rat.mul_nonneg hu0
        (abs_nonneg (Pinv * dot (B.weights.map (weightHi G1)) (ofInts W)))
      have := Rat.mul_nonneg hP0 (show 0 ≤ u * Rat.abs (Pinv * dot (B.weights.map (weightHi G1))
        (ofInts W)) + η by grind)
      have := Rat.mul_nonneg (abs_nonneg ((B.modulus : ℚ) * Pinv - 1))
        (abs_nonneg (dot (B.weights.map (weightHi G1)) (ofInts W)))
      have := abs_nonneg ((dotZ B.weights W : ℚ) - dot (B.weights.map (weightHi G1)) (ofInts W))
      grind
    grind
  have hfit : (List.zipWith (fun a r : ℤ => (((a * r).natAbs : ℕ) : ℚ)) B.weights W).sum <
      2 ^ ((p : ℤ) + G1) := by
    have hM0 : 0 ≤ M := by
      obtain ⟨a, ha⟩ := List.exists_mem_of_length_pos (show 0 < B.weights.length by omega)
      exact Rat.le_trans (by exact_mod_cast (hw a ha).1) (hw a ha).2
    have := Rat.le_trans (natAbs_products_le hM0 B.weights W hw)
      (Rat.mul_le_mul_of_nonneg_left hWρ hM0)
    grind
  have hr1 := uchino_fma_exact hp hu0 hPpos hwP hg0 hK0 hs1 hWρ hP1 hP1g hqc hc2 hfma hg01 hg02
  have hlenW : B.weights.length = W.length := by rw [hB.1, hWlen]
  have := uchino_R64 hp hle hu hη hPpos (fun a ha => (hw a ha).1) hlenW hfit h1 h2 hs2 hP2 hqc
    hmarg hr1 hρ hK hWρ (fun a ha => (hwP a ha).2) hs1 hP1 hN1 hNu hC
  unfold uchinoR64
  exact this

/-- **Ozaki-II with Uchino, Ozaki and Imamura's scaling (Algorithm 2) and reconstruction
(Algorithm 3)**, end to end: the shifts `μ' + g`, `ν' + h` of one entry, with their slack
(`uchino_lemma1_slack`: `2^(2g) m ≤ 2^(2P' − 1/k)` for the row's and the column's maxima `m ≥ c̄`),
give `|A'||B'| ≤ ((P − 1)/2)/(1 + t)`, and if that leaves room for `δ̄` (`hmargin`; their Lemma 4)
the result is within the closed-form `R64` scaled by `2^(−μ−ν)`, through one rounding, plus the
truncation error, of `x · y`. -/
theorem ozaki2Uchino_scaled_error {mult : MatrixMultiplier} {b bound : ℕ} (hmult : mult.ExactOn b bound)
    {p : ℕ} {emin emax : ℤ} (hp : 0 < p) (hle : emin ≤ emax) {u η : ℚ}
    (hu : u = 2 ^ (-(p : ℤ))) (hη : η = 2 ^ (emin - p))
    {B : CRTBasis} (hB : B.Valid) (hmb : ∀ m ∈ B.moduli, m ≤ 2 ^ (b + 1))
    (hN1 : 1 ≤ B.weights.length) (hNu : (B.weights.length : ℚ) * u ≤ 1 / 8)
    {M : ℚ} (hw : ∀ a ∈ B.weights, 0 ≤ a ∧ (a : ℚ) ≤ M) (hMP : M ≤ B.modulus)
    {G1 g0 : ℤ} (hMρ : M * uchinoRho B < 2 ^ ((p : ℤ) + G1))
    (h1 : emin ≤ G1 + ((p : ℤ) - 1)) (h2 : G1 + ((p : ℤ) - 1) ≤ emax)
    {K : ℚ} (hρ : 2 ≤ uchinoRho B) (hK : 2 * uchinoRho B ≤ K)
    (hs1 : ∀ a ∈ B.weights, (a : ℚ) - weightHi G1 a ≤ K * u * B.modulus)
    {P1 P2 Pinv : ℚ} (hP1 : Rat.abs ((B.modulus : ℚ) - P1) ≤ u * B.modulus)
    (hg0 : g0 ≤ G1) (hP1g : GridMultiple g0 P1)
    (hfma : (B.modulus : ℚ) / 2 + K * u * B.modulus * uchinoRho B +
      (uchinoRho B + 1 / 2) * (u * B.modulus) ≤ 2 ^ ((p : ℤ) + g0))
    (hg01 : emin ≤ g0 + ((p : ℤ) - 1)) (hg02 : g0 + ((p : ℤ) - 1) ≤ emax)
    (hP2 : roundRNE p emin emax ((B.modulus : ℚ) - P1) = some P2)
    (hPinv : roundRNE p emin emax (1 / (B.modulus : ℚ)) = some Pinv)
    {s2 : List ℚ}
    (hs2 : B.weights.mapM (fun a : ℤ => roundRNE p emin emax ((a : ℚ) - weightHi G1 a)) = some s2)
    {x y : List ℚ} (hlen : x.length = y.length) (hbound : x.length * (2 ^ b * 2 ^ b) ≤ bound)
    {P' : ℚ} (hP' : Ge2 (((B.modulus : ℚ) - 1) / 2) (2 * P'))
    {k : ℕ} (hk : 0 < k) {t : ℚ} (ht : 0 ≤ t) (hkt : (k : ℚ) * t ≤ 1 / 2)
    {μ' ν' g h : ℤ} {mr mc : ℚ}
    (hmr : (dotZ (barScale μ' x) (barScale ν' y) : ℚ) ≤ mr)
    (hrow : Le2 (2 ^ (2 * g) * mr) (2 * P' - 1 / k))
    (hmc : (dotZ (barScale μ' x) (barScale ν' y) : ℚ) ≤ mc)
    (hcol : Le2 (2 ^ (2 * h) * mc) (2 * P' - 1 / k))
    (hmargin : 2 * (((B.modulus : ℚ) - 1) / 2 / (1 + t) +
      uchinoDeltaBar u η B.modulus K (uchinoRho B)) < B.modulus)
    {v : ℚ} (hv : ozaki2Uchino mult (roundRNE p emin emax) B G1 P1 P2 Pinv s2 (μ' + g) (ν' + h) x y =
      some v) :
    Rat.abs (v - dot x y) ≤
      u * (Rat.abs ((dotZ (scaleTrunc (μ' + g) x) (scaleTrunc (ν' + h) y) : ℚ) *
            2 ^ (-((μ' + g) + (ν' + h)))) +
          uchinoR64 u η K (uchinoRho B) B.weights.length B.modulus
            (dotZ (scaleTrunc (μ' + g) x) (scaleTrunc (ν' + h) y)) *
            2 ^ (-((μ' + g) + (ν' + h)))) + η +
        uchinoR64 u η K (uchinoRho B) B.weights.length B.modulus
          (dotZ (scaleTrunc (μ' + g) x) (scaleTrunc (ν' + h) y)) * 2 ^ (-((μ' + g) + (ν' + h))) +
        (2 ^ (-(μ' + g)) * absSum y + 2 ^ (-(ν' + h)) * absSum x) := by
  have hPpos : 0 < B.modulus := by
    unfold CRTBasis.modulus
    exact prod_pos_of_pos hB.2.1
  have hsl := uchino_lemma1_slack (show 1 ≤ B.modulus by omega) hP' hk ht hkt hmr hrow hmc hcol
  have hΛ : (dotAbs (scaleTrunc (μ' + g) x) (scaleTrunc (ν' + h) y) : ℚ) ≤
      ((B.modulus : ℚ) - 1) / 2 / (1 + t) := by
    have ht1 : (0 : ℚ) < 1 + t := by grind
    apply Rat.le_of_mul_le_mul_right _ ht1
    rw [Rat.div_mul_cancel (by grind)]
    exact hsl
  exact ozaki2Uchino_R64 hmult hp hle hu hη hB hmb hN1 hNu hw hMP hMρ h1 h2 hρ hK hs1 hP1 hg0 hP1g
    hfma hg01 hg02 hP2 hPinv hs2 (μ' + g) (ν' + h) hlen hbound hΛ hmargin hv

end Ozaki
