import Ozaki.Binary

/-! # Slicing binary-format values with bounded integer operations

The scheme's split (`Ozaki.split`) is defined in exact rational arithmetic, and the binary32 σ-trick
that computes it in hardware (`OzakiTC.Split32`) is proved only for grids in `[2^-149, 2^104]`. This
file gives an implementation that works for every grid: every entry is an integer pair `(m, e)`
worth `m · 2^e`, as a binary format stores it, and a slice is computed with integer operations on
the significands.

* `rneShift m k`: the nearest integer to `m / 2^k`, ties to even, by an integer division, its
  remainder and a round-half-even comparison. The shift saturates at `⌊log₂ |m|⌋ + 2`, beyond which
  the result is `0`, so the divisor never exceeds `4 |m|` (`rneShift_eq`, `shiftPow_le`).
* `gridInt`: the slice grid `⌈log₂ max|xᵢ|⌉ − b` from the significands' bit lengths and the
  exponents, with the zero-vector rule of `sliceGrid` (`gridInt_eq`).
* `coeffInt`, `restInt`: a coefficient is `m · 2^(e−g)` when the entry lies on the grid (a shift by
  at most `b` bits, `coeffPow_le`), otherwise `rneShift m (g − e)`; the rest keeps the exponent and
  replaces `m` by `m − q · 2^(g−e)`, whose magnitude never exceeds `|m|` (`restInt_natAbs_le`).
* `splitInt`: the whole split. It computes exactly `split` (`splitInt_eq`), for every grid, and on
  significands below `2^p` every coefficient is at most `2^b`, every remaining significand stays
  below `2^p` and every exponent is one of the inputs' (`splitInt_width`): the widths depend on `p`
  and `b`, never on the exponents.
* Every binary32 and binary64 vector has such a representation, so the integer implementation
  computes `split b s x` exactly for every `s` (`split_binary32_int`, `split_binary64_int`), with no
  condition on the grids. -/

local notation "ℕ" => Nat
local notation "ℤ" => Int
local notation "ℚ" => Rat

namespace Ozaki

/-! ## Entries -/

/-- The value `m · 2^e` of an entry `(m, e)`. -/
def entryVal (a : ℤ × ℤ) : ℚ := (a.1 : ℚ) * 2 ^ a.2

/-- The values of a vector of entries. -/
def entryVals (xs : List (ℤ × ℤ)) : List ℚ := xs.map entryVal

/-- A binary-format value is an entry with a significand below `2^p`. -/
theorem formatValue_entry {p : ℕ} {emin emax : ℤ} {v : ℚ} (h : FormatValue p emin emax v) :
    ∃ a : ℤ × ℤ, entryVal a = v ∧ a.1.natAbs < 2 ^ p := by
  obtain ⟨k, e, _, _, hk, rfl⟩ := h
  exact ⟨(k, e - ((p : ℤ) - 1)), rfl, hk⟩

/-- A vector of binary-format values has a vector of entries with significands below `2^p`. -/
theorem formatValues_entries {p : ℕ} {emin emax : ℤ} :
    ∀ {x : List ℚ}, (∀ v ∈ x, FormatValue p emin emax v) →
      ∃ xs : List (ℤ × ℤ), entryVals xs = x ∧ ∀ a ∈ xs, a.1.natAbs < 2 ^ p
  | [], _ => ⟨[], rfl, by simp⟩
  | v :: x, h => by
    obtain ⟨a, ha, hab⟩ := formatValue_entry (h v List.mem_cons_self)
    obtain ⟨xs, hxs, hb⟩ :=
      formatValues_entries (x := x) fun w hw => h w (List.mem_cons_of_mem _ hw)
    refine ⟨a :: xs, by simp [entryVals, ha, ← hxs], ?_⟩
    intro c hc
    rcases List.mem_cons.mp hc with rfl | hc
    · exact hab
    · exact hb c hc

/-- `m 2^e / 2^g = m 2^(e − g)`. -/
theorem entryVal_div (a : ℤ × ℤ) (g : ℤ) : entryVal a / 2 ^ g = (a.1 : ℚ) * 2 ^ (a.2 - g) := by
  unfold entryVal
  rw [div_two_pow, Rat.mul_assoc, ← two_pow_add]
  congr 2

/-! ## Round half to even by an integer shift -/

/-- The nearest integer to `m / 2^j`, ties to even: integer division, remainder, comparison. -/
def rneDiv (m : ℤ) (j : ℕ) : ℤ :=
  if ((2 ^ j : ℕ) : ℤ) < 2 * (m % ((2 ^ j : ℕ) : ℤ)) ∨
      (2 * (m % ((2 ^ j : ℕ) : ℤ)) = ((2 ^ j : ℕ) : ℤ) ∧ (m / ((2 ^ j : ℕ) : ℤ)) % 2 = 1) then
    m / ((2 ^ j : ℕ) : ℤ) + 1
  else m / ((2 ^ j : ℕ) : ℤ)

/-- Beyond this shift the rounded quotient is `0`: `⌊log₂ |m|⌋ + 2`. -/
def shiftCap (m : ℤ) : ℕ := m.natAbs.log2 + 2

/-- **The nearest integer to `m / 2^k`, ties to even**, with the shift capped at `shiftCap m`. -/
def rneShift (m : ℤ) (k : ℕ) : ℤ := if m = 0 then 0 else rneDiv m (min k (shiftCap m))

/-- `m = d q + r` with `0 ≤ r < d`, as rationals. -/
theorem divMod_rat (m : ℤ) {d : ℕ} (hd : 0 < d) :
    (m : ℚ) = (d : ℚ) * ((m / (d : ℤ) : ℤ) : ℚ) + ((m % (d : ℤ) : ℤ) : ℚ) ∧
      (0 : ℚ) ≤ ((m % (d : ℤ) : ℤ) : ℚ) ∧ ((m % (d : ℤ) : ℤ) : ℚ) < (d : ℚ) := by
  have hdz : (0 : ℤ) < (d : ℤ) := by omega
  have hr0 := Int.emod_nonneg m (Int.ne_of_gt hdz)
  have hr1 := Int.emod_lt_of_pos m hdz
  refine ⟨?_, Rat.intCast_nonneg.mpr hr0, ?_⟩
  · have h := Int.emod_def m (d : ℤ)
    have : m = (d : ℤ) * (m / (d : ℤ)) + m % (d : ℤ) := by omega
    conv => lhs; rw [this]
    rw [Rat.intCast_add, Rat.intCast_mul, Rat.intCast_natCast]
  · have := Rat.intCast_lt_intCast.mpr hr1; rwa [Rat.intCast_natCast] at this

/-- Integer division by a positive natural number is the floor of the quotient. -/
theorem floor_div_nat (m : ℤ) {d : ℕ} (hd : 0 < d) :
    ((m : ℚ) / (d : ℚ)).floor = m / (d : ℤ) := by
  have hD : (0 : ℚ) < (d : ℚ) := Rat.natCast_pos.mpr hd
  obtain ⟨hm, hr0, hr1⟩ := divMod_rat m hd
  have ht : (m : ℚ) / (d : ℚ) * (d : ℚ) = m := Rat.div_mul_cancel (Rat.ne_of_gt hD)
  have hlo : ((m / (d : ℤ) : ℤ) : ℚ) ≤ (m : ℚ) / (d : ℚ) := by
    apply Rat.not_lt.mp; intro hlt
    have := Rat.mul_lt_mul_of_pos_right hlt hD
    grind
  have hhi : (m : ℚ) / (d : ℚ) < ((m / (d : ℤ) : ℤ) : ℚ) + 1 := by
    apply Rat.not_le.mp; intro hle
    have := Rat.mul_le_mul_of_nonneg_right hle (Rat.le_of_lt hD)
    grind
  apply Int.le_antisymm
  · have h1 := Rat.floor_le ((m : ℚ) / (d : ℚ))
    have h2 : (((m : ℚ) / (d : ℚ)).floor : ℚ) < ((m / (d : ℤ) + 1 : ℤ) : ℚ) := by
      rw [Rat.intCast_add, Rat.intCast_one]; exact lt_of_le_of_lt' h1 hhi
    have := Rat.intCast_lt_intCast.mp h2
    omega
  · exact Rat.le_floor_iff.mpr hlo

/-- **The integer shift rounds to nearest, ties to even.** -/
theorem rneDiv_eq_nat (m : ℤ) (j : ℕ) :
    rneDiv m j = roundNearestEven ((m : ℚ) / ((2 ^ j : ℕ) : ℚ)) := by
  have hd : 0 < 2 ^ j := Nat.two_pow_pos j
  unfold rneDiv roundNearestEven
  generalize 2 ^ j = d at hd ⊢
  have hD : (0 : ℚ) < (d : ℚ) := Rat.natCast_pos.mpr hd
  rw [floor_div_nat m hd]
  obtain ⟨hm, hr0, hr1⟩ := divMod_rat m hd
  have ht : (m : ℚ) / (d : ℚ) * (d : ℚ) = m := Rat.div_mul_cancel (Rat.ne_of_gt hD)
  generalize hF : (m : ℚ) / (d : ℚ) - ((m / (d : ℤ) : ℤ) : ℚ) = F
  have hFD : F * (d : ℚ) = ((m % (d : ℤ) : ℤ) : ℚ) := by rw [← hF]; grind
  generalize hR : ((m % (d : ℤ) : ℤ) : ℚ) = R at hFD hr0 hr1
  have hcast1 : ((d : ℤ) < 2 * (m % (d : ℤ))) ↔ (d : ℚ) < 2 * R := by
    rw [← hR, ← Rat.intCast_natCast, show (2 : ℚ) = ((2 : ℤ) : ℚ) from rfl, ← Rat.intCast_mul]
    exact Rat.intCast_lt_intCast.symm
  have hcast2 : (2 * (m % (d : ℤ)) = (d : ℤ)) ↔ 2 * R = (d : ℚ) := by
    rw [← hR, ← Rat.intCast_natCast, show (2 : ℚ) = ((2 : ℤ) : ℚ) from rfl, ← Rat.intCast_mul]
    exact Rat.intCast_inj.symm
  have c1 : (d : ℚ) < 2 * R ↔ 1 < 2 * F := by
    constructor
    · intro h
      apply Rat.not_le.mp; intro hle
      have := Rat.mul_le_mul_of_nonneg_right hle (Rat.le_of_lt hD)
      grind
    · intro h
      have := Rat.mul_lt_mul_of_pos_right h hD
      grind
  have c2 : 2 * R = (d : ℚ) ↔ 2 * F = 1 := by
    constructor
    · intro h
      have h0 : (2 * F - 1) * (d : ℚ) = 0 := by grind
      rcases Rat.mul_eq_zero.mp h0 with h0 | h0
      · grind
      · exact absurd h0 (Rat.ne_of_gt hD)
    · intro h; grind
  by_cases hc : (d : ℤ) < 2 * (m % (d : ℤ)) ∨
      (2 * (m % (d : ℤ)) = (d : ℤ) ∧ (m / (d : ℤ)) % 2 = 1)
  · rw [if_pos hc, if_pos]
    rw [hcast1, hcast2, c1, c2] at hc; exact hc
  · rw [if_neg hc, if_neg]
    rw [hcast1, hcast2, c1, c2] at hc; exact hc

theorem rneDiv_eq (m : ℤ) (j : ℕ) : rneDiv m j = roundNearestEven ((m : ℚ) / 2 ^ (j : ℤ)) := by
  rw [two_pow_natCast]; exact rneDiv_eq_nat m j

/-- A value within `1/2` of `0` rounds to `0`. -/
theorem roundNearestEven_eq_zero_of_small {t : ℚ} (h : 2 * Rat.abs t < 1) :
    roundNearestEven t = 0 := by
  have he := roundNearestEven_error t
  have hn : 2 * Rat.abs ((roundNearestEven t : ℤ) : ℚ) < 2 := by
    have := abs_sub_le t (t - roundNearestEven t)
    have e : t - (t - (roundNearestEven t : ℚ)) = (roundNearestEven t : ℚ) := by grind
    rw [e] at this
    grind
  rw [abs_intCast] at hn
  have : (((roundNearestEven t).natAbs : ℕ) : ℚ) < 1 := by grind
  have h1 : (roundNearestEven t).natAbs < 1 := by exact_mod_cast this
  omega

/-- Shifting by at least `⌊log₂ |m|⌋ + 2` rounds to `0`. -/
theorem rne_div_eq_zero (m : ℤ) {j : ℕ} (hj : m.natAbs.log2 + 2 ≤ j) :
    roundNearestEven ((m : ℚ) / 2 ^ (j : ℤ)) = 0 := by
  apply roundNearestEven_eq_zero_of_small
  have hL : Rat.abs (m : ℚ) < (2 : ℚ) ^ (((m.natAbs.log2 + 1 : ℕ)) : ℤ) := by
    rw [abs_intCast, two_pow_natCast]
    exact Rat.natCast_lt_natCast.mpr Nat.lt_log2_self
  have h2 : 2 * Rat.abs (m : ℚ) < 2 ^ (j : ℤ) := by
    have : (2 : ℚ) ^ (((m.natAbs.log2 + 1 : ℕ)) : ℤ) * 2 ≤ 2 ^ (j : ℤ) := by
      rw [← two_pow_succ]; exact two_pow_le (by omega)
    grind
  rw [div_two_pow, abs_mul_two_pow]
  have hpos := two_pow_pos (-(j : ℤ))
  have := Rat.mul_lt_mul_of_pos_right h2 hpos
  have hone : (2 : ℚ) ^ (j : ℤ) * 2 ^ (-(j : ℤ)) = 1 := by
    rw [Rat.mul_comm]; exact two_pow_neg_mul _
  grind

theorem rneShift_eq_rneDiv {m : ℤ} (hm : m ≠ 0) (k : ℕ) :
    rneShift m k = rneDiv m (min k (shiftCap m)) := by
  unfold rneShift; rw [if_neg hm]

/-- **`rneShift m k` is `m / 2^k` rounded to nearest, ties to even**, for every shift `k`. -/
theorem rneShift_eq (m : ℤ) (k : ℕ) : rneShift m k = roundNearestEven ((m : ℚ) / 2 ^ (k : ℤ)) := by
  by_cases hm : m = 0
  · subst hm
    unfold rneShift
    rw [if_pos rfl, show ((0 : ℤ) : ℚ) / 2 ^ (k : ℤ) = ((0 : ℤ) : ℚ) by
      rw [Rat.div_def, Rat.intCast_zero, Rat.zero_mul], roundNearestEven_intCast]
  · rw [rneShift_eq_rneDiv hm]
    by_cases hk : k ≤ shiftCap m
    · rw [Nat.min_eq_left hk, rneDiv_eq]
    · rw [Nat.min_eq_right (by omega), rneDiv_eq,
        rne_div_eq_zero m (j := shiftCap m) (by unfold shiftCap; omega),
        rne_div_eq_zero m (by unfold shiftCap at hk; omega)]

/-- A saturated shift gives `0`. -/
theorem rneShift_eq_zero {m : ℤ} {k : ℕ} (hk : shiftCap m ≤ k) : rneShift m k = 0 := by
  rw [rneShift_eq]; exact rne_div_eq_zero m (by unfold shiftCap at hk; omega)

/-- **The divisor stays small**: the shift actually used is at most `⌊log₂ |m|⌋ + 2`, so
`2^shift ≤ 4 |m|`. -/
theorem shiftPow_le {m : ℤ} (hm : m ≠ 0) (k : ℕ) : 2 ^ min k (shiftCap m) ≤ 4 * m.natAbs := by
  have h1 : 2 ^ min k (shiftCap m) ≤ 2 ^ shiftCap m :=
    Nat.pow_le_pow_right (by decide) (Nat.min_le_right _ _)
  have h2 := Nat.log2_self_le (n := m.natAbs) (by omega)
  have h3 : 2 ^ shiftCap m = 4 * 2 ^ m.natAbs.log2 := by
    unfold shiftCap; rw [Nat.pow_add]; omega
  omega

/-! ## The grid from bit lengths -/

/-- `⌈log₂ n⌉` of a positive natural number, from its bit length. -/
def clog2Nat (n : ℕ) : ℕ := if n = 2 ^ n.log2 then n.log2 else n.log2 + 1

/-- `⌈log₂ |m 2^e|⌉` of a nonzero entry; `none` for a zero one. -/
def entryExp (a : ℤ × ℤ) : Option ℤ :=
  if a.1 = 0 then none else some ((clog2Nat a.1.natAbs : ℤ) + a.2)

/-- The larger of two optional exponents. -/
def optMax : Option ℤ → Option ℤ → Option ℤ
  | none, o => o
  | some a, none => some a
  | some a, some c => some (max a c)

/-- `⌈log₂ max|xᵢ|⌉` of a vector of entries; `none` for a zero vector. -/
def maxEntryExp : List (ℤ × ℤ) → Option ℤ
  | [] => none
  | a :: xs => optMax (entryExp a) (maxEntryExp xs)

/-- **The slice grid with integer operations**: `⌈log₂ max|xᵢ|⌉ − b`, or `prev − (b + 1)` for a zero
vector. -/
def gridInt (b : ℕ) (prev : ℤ) (xs : List (ℤ × ℤ)) : ℤ :=
  match maxEntryExp xs with
  | none => prev - (b + 1)
  | some c => c - b

theorem entryExp_ne_zero {a : ℤ × ℤ} {c : ℤ} (h : entryExp a = some c) : a.1 ≠ 0 := by
  unfold entryExp at h; split at h
  · cases h
  · assumption

/-- A nonzero entry lies in `(2^(c−1), 2^c]` for its exponent `c`. -/
theorem entryExp_spec {a : ℤ × ℤ} {c : ℤ} (h : entryExp a = some c) :
    2 ^ (c - 1) < Rat.abs (entryVal a) ∧ Rat.abs (entryVal a) ≤ 2 ^ c := by
  have ha := entryExp_ne_zero h
  unfold entryExp at h
  rw [if_neg ha] at h
  cases h
  generalize hn : a.1.natAbs = n
  have hn0 : n ≠ 0 := by omega
  have hL1 := Nat.log2_self_le hn0
  have hL2 := Nat.lt_log2_self (n := n)
  have hval : Rat.abs (entryVal a) = (n : ℚ) * 2 ^ a.2 := by
    unfold entryVal; rw [abs_mul_two_pow, abs_intCast, hn]
  rw [hval]
  have hp := two_pow_pos a.2
  unfold clog2Nat
  split
  · rename_i hpow
    have hnq : (n : ℚ) = 2 ^ ((n.log2 : ℕ) : ℤ) := by
      rw [two_pow_natCast]; exact congrArg _ hpow
    rw [hnq, ← two_pow_add]
    exact ⟨two_pow_lt (by omega), Rat.le_refl⟩
  · rename_i hpow
    have hlt : 2 ^ n.log2 < n := by omega
    have hq1 : (2 : ℚ) ^ ((n.log2 : ℕ) : ℤ) < (n : ℚ) := by
      rw [two_pow_natCast]; exact Rat.natCast_lt_natCast.mpr hlt
    have hq2 : (n : ℚ) < (2 : ℚ) ^ (((n.log2 + 1 : ℕ)) : ℤ) := by
      rw [two_pow_natCast]; exact Rat.natCast_lt_natCast.mpr hL2
    have e1 : (2 : ℚ) ^ (((n.log2 + 1 : ℕ) : ℤ) + a.2 - 1) =
        2 ^ ((n.log2 : ℕ) : ℤ) * 2 ^ a.2 := by
      rw [← two_pow_add]; congr 1; omega
    have e2 : (2 : ℚ) ^ (((n.log2 + 1 : ℕ) : ℤ) + a.2) =
        2 ^ (((n.log2 + 1 : ℕ)) : ℤ) * 2 ^ a.2 := two_pow_add _ _
    rw [e1, e2]
    exact ⟨Rat.mul_lt_mul_of_pos_right hq1 hp,
      Rat.le_of_lt (Rat.mul_lt_mul_of_pos_right hq2 hp)⟩

theorem entryExp_eq_none {a : ℤ × ℤ} (h : entryExp a = none) : a.1 = 0 := by
  unfold entryExp at h; split at h
  · assumption
  · cases h

theorem maxExp_eq_none : ∀ {xs : List (ℤ × ℤ)}, maxEntryExp xs = none → ∀ a ∈ xs, a.1 = 0
  | [], _ => by simp
  | a :: xs, h => by
    simp only [maxEntryExp] at h
    cases ha : entryExp a with
    | some c => rw [ha] at h; cases hm : maxEntryExp xs <;> rw [hm] at h <;> cases h
    | none =>
      rw [ha] at h
      simp only [optMax] at h
      intro c hc
      rcases List.mem_cons.mp hc with rfl | hc
      · exact entryExp_eq_none ha
      · exact maxExp_eq_none h c hc

theorem maxExp_eq_some : ∀ {xs : List (ℤ × ℤ)} {c : ℤ}, maxEntryExp xs = some c →
    (∀ a ∈ xs, ∀ c', entryExp a = some c' → c' ≤ c) ∧ ∃ a ∈ xs, entryExp a = some c
  | [], _, h => by simp [maxEntryExp] at h
  | a :: xs, c, h => by
    simp only [maxEntryExp] at h
    cases ha : entryExp a with
    | none =>
      rw [ha] at h
      simp only [optMax] at h
      obtain ⟨h1, b, hb, hbc⟩ := maxExp_eq_some h
      refine ⟨?_, b, List.mem_cons_of_mem _ hb, hbc⟩
      intro d hd c' hc'
      rcases List.mem_cons.mp hd with rfl | hd
      · rw [ha] at hc'; cases hc'
      · exact h1 d hd c' hc'
    | some ca =>
      rw [ha] at h
      cases hm : maxEntryExp xs with
      | none =>
        rw [hm] at h
        simp only [optMax, Option.some.injEq] at h
        subst h
        refine ⟨?_, a, List.mem_cons_self, ha⟩
        intro d hd c' hc'
        rcases List.mem_cons.mp hd with rfl | hd
        · rw [ha] at hc'; cases hc'; exact Int.le_refl _
        · have := entryExp_ne_zero hc'
          exact absurd (maxExp_eq_none hm d hd) this
      | some cm =>
        rw [hm] at h
        simp only [optMax, Option.some.injEq] at h
        subst h
        obtain ⟨h1, b, hb, hbc⟩ := maxExp_eq_some hm
        refine ⟨?_, ?_⟩
        · intro d hd c' hc'
          rcases List.mem_cons.mp hd with rfl | hd
          · rw [ha] at hc'; cases hc'; omega
          · have := h1 d hd c' hc'; omega
        · by_cases hmax : cm ≤ ca
          · exact ⟨a, List.mem_cons_self, by rw [ha]; congr 1; omega⟩
          · exact ⟨b, List.mem_cons_of_mem _ hb, by rw [hbc]; congr 1; omega⟩

/-- **The integer grid is the scheme's grid.** -/
theorem gridInt_eq (b : ℕ) (prev : ℤ) (xs : List (ℤ × ℤ)) :
    gridInt b prev xs = sliceGrid b prev (entryVals xs) := by
  unfold gridInt sliceGrid
  cases h : maxEntryExp xs with
  | none =>
    have h0 := maxExp_eq_none h
    have hM : maxAbs (entryVals xs) = 0 := by
      have hle : maxAbs (entryVals xs) ≤ 0 := maxAbs_le (Rat.le_refl) fun v hv => by
        obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hv
        unfold entryVal; rw [h0 a ha, Rat.intCast_zero, Rat.zero_mul, abs_zero]
        exact Rat.le_refl
      have := maxAbs_nonneg (entryVals xs)
      grind
    rw [if_pos hM]
  | some c =>
    dsimp only
    obtain ⟨hle, a, ha, hac⟩ := maxExp_eq_some h
    obtain ⟨hlo, _⟩ := entryExp_spec hac
    have hupper : maxAbs (entryVals xs) ≤ 2 ^ c :=
      maxAbs_le (Rat.le_of_lt (two_pow_pos c)) fun v hv => by
        obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hv
        cases hde : entryExp d with
        | none =>
          unfold entryVal; rw [entryExp_eq_none hde, Rat.intCast_zero, Rat.zero_mul, abs_zero]
          exact Rat.le_of_lt (two_pow_pos c)
        | some c' =>
          exact Rat.le_trans (entryExp_spec hde).2 (two_pow_le (hle d hd c' hde))
    have hlower : 2 ^ (c - 1) < maxAbs (entryVals xs) := by
      have h := abs_le_maxAbs (x := entryVals xs) (List.mem_map_of_mem (f := entryVal) ha)
      grind
    have hpos : 0 < maxAbs (entryVals xs) := lt_of_le_of_lt' (Rat.le_of_lt (two_pow_pos _)) hlower
    rw [if_neg (Rat.ne_of_gt hpos)]
    have h1 := (ceilLog2_le_iff hpos c).mpr hupper
    have h2 : ¬ ceilLog2 (maxAbs (entryVals xs)) ≤ c - 1 := fun hc => by
      have := (ceilLog2_le_iff hpos (c - 1)).mp hc
      exact absurd hlower (Rat.not_lt.mpr this)
    omega

/-! ## One slice -/

/-- **The coefficient of an entry with integer operations**: `m · 2^(e−g)` when the entry lies on the
grid (a shift by at most `b` bits), otherwise `m / 2^(g−e)` rounded by `rneShift`. -/
def coeffInt (b : ℕ) (g : ℤ) (a : ℤ × ℤ) : ℤ :=
  if a.1 = 0 then 0
  else if g ≤ a.2 then a.1 * ((2 ^ min (a.2 - g).toNat b : ℕ) : ℤ)
  else rneShift a.1 (g - a.2).toNat

/-- **What a slice leaves of an entry**, with the same exponent:
`m − q · 2^(g−e)` (with the shift capped as in `rneShift`, which changes nothing). -/
def restInt (g : ℤ) (a : ℤ × ℤ) : ℤ × ℤ :=
  if a.1 = 0 ∨ g ≤ a.2 then (0, a.2)
  else (a.1 - rneShift a.1 (g - a.2).toNat * ((2 ^ min (g - a.2).toNat (shiftCap a.1) : ℕ) : ℤ),
    a.2)

/-- The coefficient shift is at most `b` bits. -/
theorem coeffPow_le (b : ℕ) (g : ℤ) (a : ℤ × ℤ) : 2 ^ min (a.2 - g).toNat b ≤ 2 ^ b :=
  Nat.pow_le_pow_right (by decide) (Nat.min_le_right _ _)

/-- An entry below `2^(g+b)` lies at most `b` bits above the grid `2^g`. -/
theorem shift_le_of_abs {b : ℕ} {g : ℤ} {a : ℤ × ℤ} (ha : a.1 ≠ 0)
    (hinv : Rat.abs (entryVal a) ≤ 2 ^ (g + b)) : a.2 - g ≤ b := by
  have hval : Rat.abs (entryVal a) = ((a.1.natAbs : ℕ) : ℚ) * 2 ^ a.2 := by
    unfold entryVal; rw [abs_mul_two_pow, abs_intCast]
  rw [hval] at hinv
  have h1 : (1 : ℚ) ≤ ((a.1.natAbs : ℕ) : ℚ) := by
    have : 1 ≤ a.1.natAbs := by omega
    exact_mod_cast this
  have hp := two_pow_pos a.2
  have h2 : (2 : ℚ) ^ a.2 ≤ 2 ^ (g + b) := by
    have := Rat.mul_le_mul_of_nonneg_right h1 (Rat.le_of_lt hp)
    rw [Rat.one_mul] at this
    exact Rat.le_trans this hinv
  have := two_pow_le_iff.mp h2
  omega

/-- **The integer coefficient is the scheme's**, for an entry below `2^(g+b)`. -/
theorem coeffInt_eq {b : ℕ} {g : ℤ} {a : ℤ × ℤ} (hinv : Rat.abs (entryVal a) ≤ 2 ^ (g + b)) :
    coeffInt b g a = roundNearestEven (entryVal a / 2 ^ g) := by
  unfold coeffInt
  split
  · rename_i h0
    rw [entryVal_div, h0, Rat.intCast_zero, Rat.zero_mul, ← Rat.intCast_zero,
      roundNearestEven_intCast]
  · rename_i h0
    split
    · rename_i hg
      have hk := shift_le_of_abs h0 hinv
      rw [Nat.min_eq_left (by omega), entryVal_div]
      have e : (2 : ℚ) ^ (a.2 - g) = (((2 ^ (a.2 - g).toNat : ℕ) : ℤ) : ℚ) := by
        rw [Rat.intCast_natCast, ← two_pow_natCast]; congr 1; omega
      rw [e, ← Rat.intCast_mul, roundNearestEven_intCast]
    · rename_i hg
      rw [rneShift_eq, entryVal_div, div_two_pow]
      congr 3; omega

/-- **The integer rest is the scheme's**: `m' 2^e = x − rne(x / 2^g) 2^g`. -/
theorem restInt_val (g : ℤ) (a : ℤ × ℤ) :
    entryVal (restInt g a) = entryVal a - (roundNearestEven (entryVal a / 2 ^ g) : ℚ) * 2 ^ g := by
  unfold restInt
  split
  · rename_i h
    rcases h with h0 | hg
    · have hz : entryVal a = 0 := by unfold entryVal; rw [h0, Rat.intCast_zero, Rat.zero_mul]
      rw [hz, show (0 : ℚ) / 2 ^ g = ((0 : ℤ) : ℚ) by
        rw [Rat.div_def, Rat.zero_mul, Rat.intCast_zero], roundNearestEven_intCast]
      unfold entryVal
      simp only [Rat.intCast_zero, Rat.zero_mul]
      grind
    · rw [entryVal_div]
      have e : (2 : ℚ) ^ (a.2 - g) = (((2 ^ (a.2 - g).toNat : ℕ) : ℤ) : ℚ) := by
        rw [Rat.intCast_natCast, ← two_pow_natCast]; congr 1; omega
      rw [e, ← Rat.intCast_mul, roundNearestEven_intCast]
      unfold entryVal
      simp only [Rat.intCast_zero, Rat.zero_mul, Rat.intCast_mul, Rat.intCast_natCast]
      rw [← two_pow_natCast, Rat.mul_assoc, ← two_pow_add]
      have : (((a.2 - g).toNat : ℕ) : ℤ) + g = a.2 := by omega
      rw [this]; grind
  · rename_i h
    have h0 : a.1 ≠ 0 := fun h' => h (Or.inl h')
    have hg : a.2 < g := by
      apply Int.lt_of_not_ge; intro h'; exact h (Or.inr h')
    have hq : roundNearestEven (entryVal a / 2 ^ g) = rneShift a.1 (g - a.2).toNat := by
      rw [rneShift_eq, entryVal_div, div_two_pow]; congr 3; omega
    rw [hq]
    -- the capped shift changes nothing
    have hcap : rneShift a.1 (g - a.2).toNat * ((2 ^ min (g - a.2).toNat (shiftCap a.1) : ℕ) : ℤ) =
        rneShift a.1 (g - a.2).toNat * ((2 ^ (g - a.2).toNat : ℕ) : ℤ) := by
      by_cases hk : (g - a.2).toNat ≤ shiftCap a.1
      · rw [Nat.min_eq_left hk]
      · rw [rneShift_eq_zero (by omega)]; simp
    unfold entryVal
    simp only
    rw [hcap, Rat.intCast_sub, Rat.intCast_mul, Rat.intCast_natCast, ← two_pow_natCast]
    have e : (2 : ℚ) ^ (((g - a.2).toNat : ℕ) : ℤ) * 2 ^ a.2 = 2 ^ g := by
      rw [← two_pow_add]; congr 1; omega
    grind

/-- **Rests never grow**: the significand of what a slice leaves is at most the entry's, and the
exponent is unchanged. -/
theorem restInt_natAbs_le (g : ℤ) (a : ℤ × ℤ) :
    (restInt g a).1.natAbs ≤ a.1.natAbs ∧ (restInt g a).2 = a.2 := by
  unfold restInt
  split
  · exact ⟨by simp, rfl⟩
  · rename_i h
    refine ⟨?_, rfl⟩
    have h0 : a.1 ≠ 0 := fun h' => h (Or.inl h')
    have hg : a.2 < g := by
      apply Int.lt_of_not_ge; intro h'; exact h (Or.inr h')
    simp only
    generalize hk : (g - a.2).toNat = k
    by_cases hq : rneShift a.1 k = 0
    · rw [hq]; simp
    · -- `q ≠ 0`, so the shift is not capped and `|m − q 2^k| ≤ 2^k / 2 ≤ |m|`
      have hk' : k ≤ shiftCap a.1 := by
        apply Nat.le_of_not_gt; intro hlt; exact hq (rneShift_eq_zero (Nat.le_of_lt hlt))
      rw [Nat.min_eq_left hk']
      have hD : (0 : ℚ) < 2 ^ (k : ℤ) := two_pow_pos _
      have hrne := rneShift_eq a.1 k
      have herr := roundNearestEven_error ((a.1 : ℚ) / 2 ^ (k : ℤ))
      have hbig : ¬ 2 * Rat.abs ((a.1 : ℚ) / 2 ^ (k : ℤ)) < 1 := fun hs => by
        apply hq; rw [hrne]; exact roundNearestEven_eq_zero_of_small hs
      rw [← hrne] at herr
      generalize hq' : rneShift a.1 k = q at herr hq
      have ht : (a.1 : ℚ) / 2 ^ (k : ℤ) * 2 ^ (k : ℤ) = a.1 :=
        Rat.div_mul_cancel (Rat.ne_of_gt hD)
      generalize (a.1 : ℚ) / 2 ^ (k : ℤ) = t at herr hbig ht
      have hrat : Rat.abs (((a.1 - q * ((2 ^ k : ℕ) : ℤ) : ℤ) : ℚ)) ≤ Rat.abs (a.1 : ℚ) := by
        rw [Rat.intCast_sub, Rat.intCast_mul, Rat.intCast_natCast, ← two_pow_natCast, ← ht]
        have e1 : t * 2 ^ (k : ℤ) - (q : ℚ) * 2 ^ (k : ℤ) = (t - q) * 2 ^ (k : ℤ) := by grind
        rw [e1, abs_mul_two_pow, abs_mul_two_pow]
        have : Rat.abs (t - q) ≤ Rat.abs t := by grind
        exact Rat.mul_le_mul_of_nonneg_right this (Rat.le_of_lt hD)
      rw [abs_intCast, abs_intCast] at hrat
      exact_mod_cast hrat

/-! ## The whole split -/

/-- **The split with integer operations**: `s` slices of `b` bits of a vector of entries, and the
rest as entries. -/
def splitIntFrom (b : ℕ) : ℕ → ℤ → List (ℤ × ℤ) → List Slice × List (ℤ × ℤ)
  | 0, _, xs => ([], xs)
  | s + 1, prev, xs =>
    let g := gridInt b prev xs
    let r := splitIntFrom b s g (xs.map (restInt g))
    (⟨g, xs.map (coeffInt b g)⟩ :: r.1, r.2)

/-- `s` slices of `b` bits with integer operations, starting as `split` does. -/
def splitInt (b s : ℕ) (xs : List (ℤ × ℤ)) : List Slice × List (ℤ × ℤ) := splitIntFrom b s b xs

theorem splitIntFrom_eq (b : ℕ) : ∀ (s : ℕ) (prev : ℤ) (xs : List (ℤ × ℤ)),
    (splitIntFrom b s prev xs).1 = (splitFrom b s prev (entryVals xs)).1 ∧
      entryVals (splitIntFrom b s prev xs).2 = (splitFrom b s prev (entryVals xs)).2
  | 0, _, _ => ⟨rfl, rfl⟩
  | s + 1, prev, xs => by
    have hg := gridInt_eq b prev xs
    have hcoeff : xs.map (coeffInt b (gridInt b prev xs)) =
        sliceCoeffs (sliceGrid b prev (entryVals xs)) (entryVals xs) := by
      rw [← hg]
      unfold sliceCoeffs entryVals
      rw [List.map_map]
      apply List.map_congr_left
      intro a ha
      apply coeffInt_eq
      rw [hg]
      exact abs_le_two_pow_sliceGrid b prev (entryVals xs) _ (List.mem_map_of_mem ha)
    have hrest : entryVals (xs.map (restInt (gridInt b prev xs))) =
        sliceRest (sliceGrid b prev (entryVals xs)) (entryVals xs) := by
      rw [← hg]
      unfold sliceRest entryVals
      rw [List.map_map, List.map_map]
      apply List.map_congr_left
      intro a _
      exact restInt_val _ a
    obtain ⟨ih1, ih2⟩ :=
      splitIntFrom_eq b s (gridInt b prev xs) (xs.map (restInt (gridInt b prev xs)))
    simp only [splitIntFrom, splitFrom]
    rw [ih1, ih2, hrest, hcoeff, hg]
    exact ⟨rfl, rfl⟩

/-- **The integer split is the scheme's split**, for every vector of entries and every grid: the
same grids and coefficients, and rests of the same values. -/
theorem splitInt_eq (b s : ℕ) (xs : List (ℤ × ℤ)) :
    (splitInt b s xs).1 = (split b s (entryVals xs)).1 ∧
      entryVals (splitInt b s xs).2 = (split b s (entryVals xs)).2 :=
  splitIntFrom_eq b s b xs

theorem splitIntFrom_rest (b : ℕ) {p : ℕ} : ∀ (s : ℕ) (prev : ℤ) (xs : List (ℤ × ℤ)),
    (∀ a ∈ xs, a.1.natAbs < 2 ^ p) →
      ∀ r ∈ (splitIntFrom b s prev xs).2, r.1.natAbs < 2 ^ p ∧ ∃ a ∈ xs, r.2 = a.2
  | 0, _, xs, hx => fun r hr => ⟨hx r hr, r, hr, rfl⟩
  | s + 1, prev, xs, hx => by
    intro r hr
    simp only [splitIntFrom] at hr
    have hx' : ∀ a ∈ xs.map (restInt (gridInt b prev xs)), a.1.natAbs < 2 ^ p := by
      intro c hc
      obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hc
      exact Nat.lt_of_le_of_lt (restInt_natAbs_le _ a).1 (hx a ha)
    obtain ⟨hr1, c, hc, hrc⟩ := splitIntFrom_rest b s _ _ hx' r hr
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hc
    exact ⟨hr1, a, ha, by rw [hrc, (restInt_natAbs_le _ a).2]⟩

/-- **The widths depend on the format, not on the exponents.** On significands below `2^p`, every
coefficient is at most `2^b`, every remaining significand stays below `2^p`, and every exponent is
one of the inputs'. -/
theorem splitInt_width (b s : ℕ) {p : ℕ} {xs : List (ℤ × ℤ)} (hx : ∀ a ∈ xs, a.1.natAbs < 2 ^ p) :
    (∀ sl ∈ (splitInt b s xs).1, ∀ q ∈ sl.coeffs, q.natAbs ≤ 2 ^ b) ∧
      ∀ r ∈ (splitInt b s xs).2, r.1.natAbs < 2 ^ p ∧ ∃ a ∈ xs, r.2 = a.2 := by
  refine ⟨?_, splitIntFrom_rest b s b xs hx⟩
  rw [(splitInt_eq b s xs).1]
  exact split_coeff_bound b s (entryVals xs)

/-! ## Binary formats -/

/-- **Every vector of a binary format is split exactly with integer operations**, for every number
of slices and every grid: the coefficients are at most `2^b`, the significands stay below `2^p`. -/
theorem split_formatValue_int (b s : ℕ) {p : ℕ} {emin emax : ℤ} {x : List ℚ}
    (hx : ∀ v ∈ x, FormatValue p emin emax v) :
    ∃ xs : List (ℤ × ℤ), entryVals xs = x ∧ (∀ a ∈ xs, a.1.natAbs < 2 ^ p) ∧
      (splitInt b s xs).1 = (split b s x).1 ∧ entryVals (splitInt b s xs).2 = (split b s x).2 ∧
      (∀ sl ∈ (splitInt b s xs).1, ∀ q ∈ sl.coeffs, q.natAbs ≤ 2 ^ b) ∧
      ∀ r ∈ (splitInt b s xs).2, r.1.natAbs < 2 ^ p := by
  obtain ⟨xs, hxs, hb⟩ := formatValues_entries hx
  obtain ⟨h1, h2⟩ := splitInt_eq b s xs
  obtain ⟨w1, w2⟩ := splitInt_width b s hb
  subst hxs
  exact ⟨xs, rfl, hb, h1, h2, w1, fun r hr => (w2 r hr).1⟩

/-- **Binary32**: every vector is split exactly with integer operations on 24-bit significands, with
no condition on the grids (the σ-trick needs `−149 ≤ g ≤ 104`). -/
theorem split_binary32_int (b s : ℕ) {x : List ℚ} (hx : ∀ v ∈ x, Binary32Value v) :
    ∃ xs : List (ℤ × ℤ), entryVals xs = x ∧ (∀ a ∈ xs, a.1.natAbs < 2 ^ 24) ∧
      (splitInt b s xs).1 = (split b s x).1 ∧ entryVals (splitInt b s xs).2 = (split b s x).2 ∧
      (∀ sl ∈ (splitInt b s xs).1, ∀ q ∈ sl.coeffs, q.natAbs ≤ 2 ^ b) ∧
      ∀ r ∈ (splitInt b s xs).2, r.1.natAbs < 2 ^ 24 :=
  split_formatValue_int b s hx

/-- **Binary64**: the same with 53-bit significands. -/
theorem split_binary64_int (b s : ℕ) {x : List ℚ} (hx : ∀ v ∈ x, Binary64Value v) :
    ∃ xs : List (ℤ × ℤ), entryVals xs = x ∧ (∀ a ∈ xs, a.1.natAbs < 2 ^ 53) ∧
      (splitInt b s xs).1 = (split b s x).1 ∧ entryVals (splitInt b s xs).2 = (split b s x).2 ∧
      (∀ sl ∈ (splitInt b s xs).1, ∀ q ∈ sl.coeffs, q.natAbs ≤ 2 ^ b) ∧
      ∀ r ∈ (splitInt b s xs).2, r.1.natAbs < 2 ^ 53 :=
  split_formatValue_int b s hx

/-! ## Examples

Kernel-checked, each against the rational split of the scheme as well. -/

/-- `[2^127, 1]`: the σ-trick's `fl(a + σ)` overflows binary32 here (`σ = 3 · 2^138`); the integer
split does not. -/
example : splitInt 11 2 [(1, 127), (1, 0)] =
    ([⟨116, [2048, 0]⟩, ⟨-11, [0, 2048]⟩], [(0, 127), (0, 0)]) := by decide +kernel

example : (splitInt 11 2 [(1, 127), (1, 0)]).1 = (split 11 2 (entryVals [(1, 127), (1, 0)])).1 := by
  decide +kernel

/-- Subnormal binary32 values `3 · 2^-149` and `−5 · 2^-149` beside `7 · 2^-140`: the second grid,
`2^-160`, is below the binary32 range the σ-trick needs. -/
example : splitInt 11 2 [(3, -149), (-5, -149), (7, -140)] =
    ([⟨-148, [2, -2, 1792]⟩, ⟨-160, [-2048, -2048, 0]⟩], [(0, -149), (0, -149), (0, -140)]) := by
  decide +kernel

example : (splitInt 11 2 [(3, -149), (-5, -149), (7, -140)]).1 =
    (split 11 2 (entryVals [(3, -149), (-5, -149), (7, -140)])).1 := by
  decide +kernel

/-- `[1, 2^-149]` in three slices: grids `2^-11`, `2^-160` and `2^-172`, nothing left over. -/
example : splitInt 11 3 [(1, 0), (1, -149)] =
    ([⟨-11, [2048, 0]⟩, ⟨-160, [0, 2048]⟩, ⟨-172, [0, 0]⟩], [(0, 0), (0, -149)]) := by
  decide +kernel

example : (splitInt 11 3 [(1, 0), (1, -149)]).1 = (split 11 3 (entryVals [(1, 0), (1, -149)])).1 := by
  decide +kernel

/-- The largest binary32 value beside the smallest negative one: the first coefficient rounds
`16777215 / 2^13` up to `2048`, and the rest `−1 · 2^104` keeps its exponent. -/
example : splitInt 11 2 [(16777215, 104), (-1, -149)] =
    ([⟨117, [2048, 0]⟩, ⟨93, [-2048, 0]⟩], [(0, 104), (-1, -149)]) := by
  decide +kernel

end Ozaki
