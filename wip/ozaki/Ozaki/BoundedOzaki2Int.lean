import Ozaki.BoundedOzaki2
import Ozaki.SliceInt

/-! # Ozaki-II as an integer pipeline

`ozaki2CRB` takes rational inputs: its scaling and truncation (`scaleShift`, `scaleTrunc`) and the
slicing of its exact fallback are rational definitions. Here the inputs are integer pairs `(m, e)`
worth `m 2^e` (`Ozaki.entryVal`), and every step is integer arithmetic:

* **scaling exponents from bit lengths**: `scaleShiftZ` from `maxEntryExp` (`⌈log₂ max|xᵢ|⌉` from
  the significands' bit lengths), equal to `scaleShift` (`scaleShiftZ_eq`); `maxFloorExp`,
  `⌊log₂ max|xᵢ|⌋` the same way (`maxFloorExp_floorLog2`), for ADP's fixed point;
* **shifts of the significands**: `truncShiftZ m j` is `m 2^j` truncated toward zero and
  `floorShiftZ m j` the floor, by a left shift, or a right shift of `|m|` by a natural division
  (`truncShiftZ_eq`, `floorShiftZ_eq`). A right shift past the significand's top bit returns `0`
  (or `−1` for the floor of a negative value) without forming the power of two, so no divisor
  exceeds `|m|`. `dropsBits` tells whether a shift drops nonzero bits, by a remainder
  (`dropsBits_eq`);
* **Ozaki-II's integer enclosure** from these integers (`ozaki2EnclosureZ`), equal to
  `ozaki2EnclosureB` on the values (`ozaki2EnclosureZ_eq`);
* **the exact fallback with integer slicing** (`ozaki1ExactFallbackZ`): `splitInt` for the slices
  and the test that nothing is left over, equal to `ozaki1ExactFallbackB` on the values
  (`ozaki1ExactFallbackZ_eq`);
* `ozaki2CRZ`: correctly rounded Ozaki-II from integer pairs to the IEEE round to nearest, every step
  integer (`ozaki2CRZ_eq`; binary64 and binary32 instances `ozaki2CRZ64_eq`, `ozaki2CRZ32_eq`).

**Widths**, register by register, none depending on the inputs' exponents:

* inputs: `|m| < 2^p`;
* a shifted significand: at most `2^P` (`scaleTruncZ_natAbs_le`); a left shift's result is that
  value; a right shift divides `|m|` by `2^k ≤ |m| < 2^p` (`truncShiftZ_divisor_le`), and a
  remainder test likewise (`dropsBits_divisor_le`);
* the symmetric residues: at most `m/2`; the residue products on the matrix multiplier: within
  its exactness bound; the reduced residues: below `m`;
* the CRT sum `Σ wⱼ rⱼ`: at most `Σ |wⱼ| mⱼ` (`crtSum_natAbs_le`), and its symmetric reduction
  `N`: `2|N| ≤ M`;
* the bound `K ≤ k (2^(P+1) + 1)` and `N ± K` (`ozaki2EnclosureB_width`);
* the exact fallback: coefficients at most `2^b`, significands below `2^p` (`splitInt_width`), slice
  products within the exactness bound of the matrix multiplier, and the ranges of `roundSum`
  (`Ozaki.BoundedOzaki`).

What depends on the exponents is only exponent arithmetic: the scaling exponents, the shift
amounts `e + s`, and the slice grids. -/

local notation "ℕ" => Nat
local notation "ℤ" => Int
local notation "ℚ" => Rat

namespace Ozaki

/-! ## Shifts of significands -/

/-- `m 2^j` truncated toward zero: a left shift, or a right shift of `|m|` with the sign restored;
`0` when the shift passes the top bit. -/
def truncShiftZ (m j : ℤ) : ℤ :=
  if m = 0 then 0
  else if 0 ≤ j then m * 2 ^ j.toNat
  else if m.natAbs.log2 < (-j).toNat then 0
  else if m < 0 then -((m.natAbs / 2 ^ (-j).toNat : ℕ) : ℤ)
  else ((m.natAbs / 2 ^ (-j).toNat : ℕ) : ℤ)

/-- `⌊m 2^j⌋`: a left shift, or a floor division by `2^k`; `0` or `−1` when the shift passes the
top bit. -/
def floorShiftZ (m j : ℤ) : ℤ :=
  if m = 0 then 0
  else if 0 ≤ j then m * 2 ^ j.toNat
  else if m.natAbs.log2 < (-j).toNat then (if m < 0 then -1 else 0)
  else m / ((2 ^ (-j).toNat : ℕ) : ℤ)

/-- Whether `m 2^j` is not an integer: a right shift that drops nonzero bits. -/
def dropsBits (m j : ℤ) : Bool :=
  if m = 0 then false
  else if 0 ≤ j then false
  else if m.natAbs.log2 < (-j).toNat then true
  else m.natAbs % 2 ^ (-j).toNat ≠ 0

theorem truncInt_intCast (z : ℤ) : truncInt (z : ℚ) = z := by
  unfold truncInt
  split
  · rw [← Rat.intCast_neg, Rat.floor_intCast]; omega
  · rw [Rat.floor_intCast]

theorem mul_two_pow_nonneg (m j : ℤ) (hj : 0 ≤ j) :
    (m : ℚ) * 2 ^ j = ((m * 2 ^ j.toNat : ℤ) : ℚ) := by
  rw [Rat.intCast_mul, intCast_two_pow]
  congr 2; omega

theorem mul_two_pow_neg (m j : ℤ) (hj : j < 0) :
    (m : ℚ) * 2 ^ j = (m : ℚ) / ((2 ^ (-j).toNat : ℕ) : ℚ) := by
  rw [← two_pow_natCast, div_two_pow]
  congr 2; omega

theorem natAbs_lt_of_log2_lt {m : ℤ} {k : ℕ} (h : m.natAbs.log2 < k) : m.natAbs < 2 ^ k :=
  Nat.lt_of_lt_of_le Nat.lt_log2_self (Nat.pow_le_pow_right (by decide) h)

theorem divisor_le_of_log2 {m : ℤ} (hm : m ≠ 0) {k : ℕ} (h : ¬ m.natAbs.log2 < k) :
    2 ^ k ≤ m.natAbs :=
  Nat.le_trans (Nat.pow_le_pow_right (by decide) (by omega)) (Nat.log2_self_le (by omega))

/-- The truncation of `m / d` toward zero, `d > 0`, by natural division of `|m|`. -/
theorem truncInt_div (m : ℤ) {d : ℕ} (hd : 0 < d) :
    truncInt ((m : ℚ) / (d : ℚ)) =
      if m < 0 then -((m.natAbs / d : ℕ) : ℤ) else ((m.natAbs / d : ℕ) : ℤ) := by
  have hD : (0 : ℚ) < (d : ℚ) := Rat.natCast_pos.mpr hd
  unfold truncInt
  by_cases hm : m < 0
  · have ht : (m : ℚ) / (d : ℚ) < 0 := by
      rw [Rat.div_def]
      have := Rat.mul_lt_mul_of_pos_right (show (m : ℚ) < 0 by exact_mod_cast hm)
        (Rat.inv_pos.mpr hD)
      rwa [Rat.zero_mul] at this
    rw [if_pos ht, if_pos hm]
    have e : -((m : ℚ) / (d : ℚ)) = (((m.natAbs : ℤ)) : ℚ) / (d : ℚ) := by
      have : ((m.natAbs : ℤ) : ℚ) = -(m : ℚ) := by
        rw [show (m.natAbs : ℤ) = -m by omega, Rat.intCast_neg]
      rw [this, Rat.div_def, Rat.div_def, Rat.neg_mul]
    rw [e, floor_div_nat _ hd]
    congr 1
  · have ht : ¬ (m : ℚ) / (d : ℚ) < 0 := by
      rw [Rat.not_lt, Rat.div_def]
      exact Rat.mul_nonneg (by exact_mod_cast Int.not_lt.mp hm) (Rat.le_of_lt (Rat.inv_pos.mpr hD))
    rw [if_neg ht, if_neg hm, floor_div_nat _ hd]
    rw [show m = (m.natAbs : ℤ) by omega, Int.natAbs_natCast, Int.ofNat_ediv_ofNat]

/-- **The truncating shift is `truncInt (m 2^j)`.** -/
theorem truncShiftZ_eq (m j : ℤ) : truncShiftZ m j = truncInt ((m : ℚ) * 2 ^ j) := by
  unfold truncShiftZ
  by_cases hm : m = 0
  · subst hm; rw [if_pos rfl, Rat.intCast_zero, Rat.zero_mul]
    exact (truncInt_intCast 0).symm
  rw [if_neg hm]
  by_cases hj : 0 ≤ j
  · rw [if_pos hj, mul_two_pow_nonneg m j hj, truncInt_intCast]
  rw [if_neg hj, mul_two_pow_neg m j (by omega), truncInt_div m (Nat.two_pow_pos _)]
  split
  · rename_i hlt
    have := natAbs_lt_of_log2_lt hlt
    rw [Nat.div_eq_of_lt this]; split <;> rfl
  · rfl

/-- **The floor shift is `⌊m 2^j⌋`.** -/
theorem floorShiftZ_eq (m j : ℤ) : floorShiftZ m j = ((m : ℚ) * 2 ^ j).floor := by
  unfold floorShiftZ
  by_cases hm : m = 0
  · subst hm; rw [if_pos rfl, Rat.intCast_zero, Rat.zero_mul]; rfl
  rw [if_neg hm]
  by_cases hj : 0 ≤ j
  · rw [if_pos hj, mul_two_pow_nonneg m j hj, Rat.floor_intCast]
  rw [if_neg hj, mul_two_pow_neg m j (by omega), floor_div_nat _ (Nat.two_pow_pos _)]
  split
  · rename_i hlt
    have hlt' := natAbs_lt_of_log2_lt hlt
    have hd : (0 : ℤ) < ((2 ^ (-j).toNat : ℕ) : ℤ) := by exact_mod_cast Nat.two_pow_pos _
    have hlt2 : (m.natAbs : ℤ) < ((2 ^ (-j).toNat : ℕ) : ℤ) := by exact_mod_cast hlt'
    split
    · rename_i hneg
      have hq := (Int.ediv_emod_unique (a := m) (b := ((2 ^ (-j).toNat : ℕ) : ℤ))
        (r := m + ((2 ^ (-j).toNat : ℕ) : ℤ)) (q := -1) hd).mpr ⟨by omega, by omega, by omega⟩
      exact hq.1.symm
    · exact (Int.ediv_eq_zero_of_lt (by omega) (by omega)).symm
  · rfl

/-- `g` returns every integer unchanged, so `g u = u` exactly when `u` is an integer. -/
theorem eq_self_iff_int {g : ℚ → ℤ} (hg : ∀ z : ℤ, g z = z) (u : ℚ) :
    ((g u : ℤ) : ℚ) = u ↔ ∃ z : ℤ, u = z :=
  ⟨fun h => ⟨g u, h.symm⟩, fun ⟨z, hz⟩ => by rw [hz, hg]⟩

theorem int_iff_dvd (m : ℤ) {d : ℕ} (hd : 0 < d) :
    (∃ z : ℤ, (m : ℚ) / (d : ℚ) = z) ↔ m.natAbs % d = 0 := by
  have hD : (d : ℚ) ≠ 0 := Rat.ne_of_gt (Rat.natCast_pos.mpr hd)
  constructor
  · rintro ⟨z, hz⟩
    have h1 : (m : ℚ) = ((z * d : ℤ) : ℚ) := by
      rw [Rat.intCast_mul, Rat.intCast_natCast, ← hz, Rat.div_mul_cancel hD]
    have h2 : m = z * d := Rat.intCast_inj.mp h1
    rw [h2, Int.natAbs_mul, Int.natAbs_natCast, Nat.mul_mod_left]
  · intro h
    have hdv : (d : ℤ) ∣ m := by
      have : d ∣ m.natAbs := Nat.dvd_of_mod_eq_zero h
      exact Int.natAbs_dvd_natAbs.mp (by simpa using this)
    obtain ⟨q, rfl⟩ := hdv
    refine ⟨q, ?_⟩
    rw [Rat.intCast_mul, Rat.intCast_natCast, Rat.mul_comm, Rat.mul_div_cancel hD]

theorem int_mul_two_pow_iff (m j : ℤ) :
    (∃ z : ℤ, (m : ℚ) * 2 ^ j = z) ↔ dropsBits m j = false := by
  by_cases hm : m = 0
  · subst hm
    have hd : dropsBits 0 j = false := by unfold dropsBits; simp
    exact ⟨fun _ => hd, fun _ => ⟨0, by simp⟩⟩
  by_cases hj : 0 ≤ j
  · have hd : dropsBits m j = false := by unfold dropsBits; rw [if_neg hm, if_pos hj]
    exact ⟨fun _ => hd, fun _ => ⟨_, mul_two_pow_nonneg m j hj⟩⟩
  rw [mul_two_pow_neg m j (by omega), int_iff_dvd m (Nat.two_pow_pos _)]
  unfold dropsBits
  rw [if_neg hm, if_neg hj]
  split
  · rename_i hlt
    have h1 := natAbs_lt_of_log2_lt hlt
    have h2 : m.natAbs % 2 ^ (-j).toNat = m.natAbs := Nat.mod_eq_of_lt h1
    simp only [Bool.true_eq_false, iff_false]
    omega
  · simp

/-- **`dropsBits` tells whether rounding `m 2^j` to an integer changes it**, for truncation and
floor alike. -/
theorem dropsBits_eq {g : ℚ → ℤ} (hg : ∀ z : ℤ, g z = z) (m j : ℤ) :
    dropsBits m j = decide (((g ((m : ℚ) * 2 ^ j) : ℤ) : ℚ) ≠ (m : ℚ) * 2 ^ j) := by
  have h1 := eq_self_iff_int hg ((m : ℚ) * 2 ^ j)
  have h2 := int_mul_two_pow_iff m j
  cases hd : dropsBits m j
  · simp only [Bool.false_eq, decide_eq_false_iff_not, Classical.not_not]
    exact h1.mpr (h2.mpr hd)
  · simp only [Bool.true_eq, decide_eq_true_eq]
    intro h
    have := h2.mp (h1.mp h)
    rw [hd] at this; cases this

theorem floor_intCast' (z : ℤ) : ((z : ℚ)).floor = z := Rat.floor_intCast z

/-- **Widths of the shifts**: a right shift (truncating or floor) divides by at most `|m|`. -/
theorem truncShiftZ_divisor_le {m j : ℤ} (hm : m ≠ 0) (_hj : j < 0)
    (hk : ¬ m.natAbs.log2 < (-j).toNat) : 2 ^ (-j).toNat ≤ m.natAbs :=
  divisor_le_of_log2 hm hk

theorem dropsBits_divisor_le {m j : ℤ} (hm : m ≠ 0) (_hj : j < 0)
    (hk : ¬ m.natAbs.log2 < (-j).toNat) : m.natAbs % 2 ^ (-j).toNat < 2 ^ (-j).toNat ∧
      2 ^ (-j).toNat ≤ m.natAbs :=
  ⟨Nat.mod_lt _ (Nat.two_pow_pos _), divisor_le_of_log2 hm hk⟩

/-! ## Scaling exponents from bit lengths -/

theorem entryVal_mul_two_pow (a : ℤ × ℤ) (s : ℤ) :
    entryVal a * 2 ^ s = (a.1 : ℚ) * 2 ^ (a.2 + s) := by
  unfold entryVal; rw [Rat.mul_assoc, ← two_pow_add]

/-- The ceiling exponent of `max|xᵢ|` from bit lengths: `maxEntryExp` is `⌈log₂ max|xᵢ|⌉`, `none`
for a zero vector. -/
theorem maxEntryExp_spec (xs : List (ℤ × ℤ)) :
    (maxEntryExp xs = none → maxAbs (entryVals xs) = 0) ∧
      ∀ c, maxEntryExp xs = some c →
        maxAbs (entryVals xs) ≠ 0 ∧ ceilLog2 (maxAbs (entryVals xs)) = c := by
  have h := fun prev => gridInt_eq 0 prev xs
  unfold gridInt sliceGrid at h
  constructor
  · intro hn
    simp only [hn] at h
    by_cases hne : maxAbs (entryVals xs) = 0
    · exact hne
    · have := h (ceilLog2 (maxAbs (entryVals xs)) + 2)
      rw [if_neg hne] at this
      omega
  · intro c hc
    simp only [hc] at h
    have hne : maxAbs (entryVals xs) ≠ 0 := by
      intro h0
      have := h (c + 5)
      rw [if_pos h0] at this
      omega
    refine ⟨hne, ?_⟩
    have := h 0
    rw [if_neg hne] at this
    omega

/-- **Ozaki-II's scaling exponent from bit lengths.** -/
def scaleShiftZ (P : ℕ) (xs : List (ℤ × ℤ)) : ℤ :=
  match maxEntryExp xs with
  | none => 0
  | some c => P - c

theorem scaleShiftZ_eq (P : ℕ) (xs : List (ℤ × ℤ)) :
    scaleShiftZ P xs = scaleShift P (entryVals xs) := by
  obtain ⟨hn, hs⟩ := maxEntryExp_spec xs
  unfold scaleShiftZ scaleShift
  cases h : maxEntryExp xs with
  | none => rw [if_pos (hn h)]
  | some c =>
    obtain ⟨hne, hc⟩ := hs c h
    rw [if_neg hne, hc]

/-- `⌊log₂ |m 2^e|⌋` of a nonzero entry; `none` for a zero one. -/
def floorEntryExp (a : ℤ × ℤ) : Option ℤ :=
  if a.1 = 0 then none else some ((a.1.natAbs.log2 : ℤ) + a.2)

/-- `⌊log₂ max|xᵢ|⌋` of a vector of entries from bit lengths; `none` for a zero vector. -/
def maxFloorExp : List (ℤ × ℤ) → Option ℤ
  | [] => none
  | a :: xs => optMax (floorEntryExp a) (maxFloorExp xs)

theorem floorEntryExp_spec {a : ℤ × ℤ} {c : ℤ} (h : floorEntryExp a = some c) :
    2 ^ c ≤ Rat.abs (entryVal a) ∧ Rat.abs (entryVal a) < 2 ^ (c + 1) := by
  unfold floorEntryExp at h
  split at h
  · cases h
  rename_i ha
  cases h
  generalize hn : a.1.natAbs = n
  have hn0 : n ≠ 0 := by omega
  have hval : Rat.abs (entryVal a) = (n : ℚ) * 2 ^ a.2 := by
    unfold entryVal; rw [abs_mul_two_pow, abs_intCast, hn]
  rw [hval]
  have hp := two_pow_pos a.2
  have hq1 : (2 : ℚ) ^ ((n.log2 : ℕ) : ℤ) ≤ (n : ℚ) := by
    rw [two_pow_natCast]; exact Rat.natCast_le_natCast.mpr (Nat.log2_self_le hn0)
  have hq2 : (n : ℚ) < (2 : ℚ) ^ (((n.log2 + 1 : ℕ)) : ℤ) := by
    rw [two_pow_natCast]; exact Rat.natCast_lt_natCast.mpr Nat.lt_log2_self
  have e1 : (2 : ℚ) ^ ((n.log2 : ℤ) + a.2) = 2 ^ ((n.log2 : ℕ) : ℤ) * 2 ^ a.2 := two_pow_add _ _
  have e2 : (2 : ℚ) ^ ((n.log2 : ℤ) + a.2 + 1) = 2 ^ (((n.log2 + 1 : ℕ)) : ℤ) * 2 ^ a.2 := by
    rw [← two_pow_add]; congr 1; omega
  rw [e1, e2]
  exact ⟨Rat.mul_le_mul_of_nonneg_right hq1 (Rat.le_of_lt hp), Rat.mul_lt_mul_of_pos_right hq2 hp⟩

theorem floorEntryExp_eq_none {a : ℤ × ℤ} (h : floorEntryExp a = none) : a.1 = 0 := by
  unfold floorEntryExp at h; split at h
  · assumption
  · cases h

theorem maxFloorExp_eq_none : ∀ {xs : List (ℤ × ℤ)}, maxFloorExp xs = none → ∀ a ∈ xs, a.1 = 0
  | [], _ => by simp
  | a :: xs, h => by
    simp only [maxFloorExp] at h
    cases ha : floorEntryExp a with
    | some c => rw [ha] at h; cases hm : maxFloorExp xs <;> rw [hm] at h <;> cases h
    | none =>
      rw [ha] at h
      simp only [optMax] at h
      intro c hc
      rcases List.mem_cons.mp hc with rfl | hc
      · exact floorEntryExp_eq_none ha
      · exact maxFloorExp_eq_none h c hc

theorem maxFloorExp_eq_some : ∀ {xs : List (ℤ × ℤ)} {c : ℤ}, maxFloorExp xs = some c →
    (∀ a ∈ xs, ∀ c', floorEntryExp a = some c' → c' ≤ c) ∧ ∃ a ∈ xs, floorEntryExp a = some c
  | [], _, h => by simp [maxFloorExp] at h
  | a :: xs, c, h => by
    simp only [maxFloorExp] at h
    cases ha : floorEntryExp a with
    | none =>
      rw [ha] at h
      simp only [optMax] at h
      obtain ⟨h1, b, hb, hbc⟩ := maxFloorExp_eq_some h
      refine ⟨?_, b, List.mem_cons_of_mem _ hb, hbc⟩
      intro d hd c' hc'
      rcases List.mem_cons.mp hd with rfl | hd
      · rw [ha] at hc'; cases hc'
      · exact h1 d hd c' hc'
    | some ca =>
      rw [ha] at h
      cases hm : maxFloorExp xs with
      | none =>
        rw [hm] at h
        simp only [optMax, Option.some.injEq] at h
        subst h
        refine ⟨?_, a, List.mem_cons_self, ha⟩
        intro d hd c' hc'
        rcases List.mem_cons.mp hd with rfl | hd
        · rw [ha] at hc'; cases hc'; exact Int.le_refl _
        · have h0 := maxFloorExp_eq_none hm d hd
          unfold floorEntryExp at hc'; rw [if_pos h0] at hc'; cases hc'
      | some cm =>
        rw [hm] at h
        simp only [optMax, Option.some.injEq] at h
        subst h
        obtain ⟨h1, b, hb, hbc⟩ := maxFloorExp_eq_some hm
        refine ⟨?_, ?_⟩
        · intro d hd c' hc'
          rcases List.mem_cons.mp hd with rfl | hd
          · rw [ha] at hc'; cases hc'; omega
          · have := h1 d hd c' hc'; omega
        · by_cases hmax : cm ≤ ca
          · exact ⟨a, List.mem_cons_self, by rw [ha]; congr 1; omega⟩
          · exact ⟨b, List.mem_cons_of_mem _ hb, by rw [hbc]; congr 1; omega⟩

theorem maxAbs_lt {x : List ℚ} {B : ℚ} (hB : 0 < B) (h : ∀ a ∈ x, Rat.abs a < B) :
    maxAbs x < B := by
  induction x with
  | nil => simpa [maxAbs] using hB
  | cons b x ih =>
    simp only [maxAbs, List.foldr_cons] at *
    have h1 := h b (by simp)
    have h2 := ih (fun a ha => h a (by simp [ha]))
    grind

theorem floorLog2_zero : floorLog2 0 = -1 := by decide +kernel

/-- **`⌊log₂ max|xᵢ|⌋` from bit lengths**; `−1` (`floorLog2 0`) for a zero vector. -/
theorem maxFloorExp_floorLog2 (xs : List (ℤ × ℤ)) :
    floorLog2 (maxAbs (entryVals xs)) = (maxFloorExp xs).getD (-1) := by
  cases h : maxFloorExp xs with
  | none =>
    have h0 := maxFloorExp_eq_none h
    have hM : maxAbs (entryVals xs) = 0 := by
      have hle : maxAbs (entryVals xs) ≤ 0 := maxAbs_le (Rat.le_refl) fun v hv => by
        obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hv
        unfold entryVal; rw [h0 a ha, Rat.intCast_zero, Rat.zero_mul, abs_zero]
        exact Rat.le_refl
      have := maxAbs_nonneg (entryVals xs)
      grind
    rw [hM, floorLog2_zero]; rfl
  | some c =>
    obtain ⟨hle, a, ha, hac⟩ := maxFloorExp_eq_some h
    obtain ⟨hlo, _⟩ := floorEntryExp_spec hac
    simp only [Option.getD_some]
    apply floorLog2_eq
    · exact Rat.le_trans hlo (abs_le_maxAbs (List.mem_map_of_mem (f := entryVal) ha))
    · apply maxAbs_lt (two_pow_pos _)
      intro v hv
      obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hv
      cases hde : floorEntryExp d with
      | none =>
        unfold entryVal; rw [floorEntryExp_eq_none hde, Rat.intCast_zero, Rat.zero_mul, abs_zero]
        exact two_pow_pos _
      | some c' =>
        have h1 := (floorEntryExp_spec hde).2
        have h2 : (2 : ℚ) ^ (c' + 1) ≤ 2 ^ (c + 1) :=
          two_pow_le (by have := hle d hd c' hde; omega)
        exact lt_of_le_of_lt' (Rat.le_refl) (by grind)

/-! ## Ozaki-II's integer enclosure from integer inputs -/

/-- The truncated integers `trunc(xᵢ 2^s)` from the significands. -/
def scaleTruncZ (s : ℤ) (xs : List (ℤ × ℤ)) : List ℤ := xs.map fun a => truncShiftZ a.1 (a.2 + s)

/-- Whether truncating `xᵢ 2^s` drops bits, from the significands. -/
def dropsZ (s : ℤ) (xs : List (ℤ × ℤ)) : Bool := xs.any fun a => dropsBits a.1 (a.2 + s)

theorem scaleTruncZ_eq (s : ℤ) (xs : List (ℤ × ℤ)) :
    scaleTruncZ s xs = scaleTrunc s (entryVals xs) := by
  unfold scaleTruncZ scaleTrunc entryVals
  rw [List.map_map]
  apply List.map_congr_left
  intro a _
  simp only [Function.comp]
  rw [truncShiftZ_eq, entryVal_mul_two_pow]

theorem dropsZ_trunc_eq (s : ℤ) (xs : List (ℤ × ℤ)) :
    dropsZ s xs = drops truncInt s (entryVals xs) := by
  unfold dropsZ drops entryVals
  rw [List.any_map]
  congr 1
  funext a
  simp only [Function.comp]
  rw [dropsBits_eq truncInt_intCast, entryVal_mul_two_pow]

/-- **Ozaki-II's reconstructed product from integer inputs**: scaling exponents from bit lengths,
truncation by shifts, the residue products on the matrix multiplier, and the CRT. -/
def ozaki2IntZ (mult : MatrixMultiplier) (B : CRTBasis) (P : ℕ) (xs ys : List (ℤ × ℤ)) : Option ℤ :=
  (B.moduli.mapM fun m =>
    residueProduct mult m (scaleTruncZ (scaleShiftZ P xs) xs) (scaleTruncZ (scaleShiftZ P ys) ys)).map
    (crt B)

/-- **Ozaki-II's integer enclosure from integer inputs.** -/
def ozaki2EnclosureZ (mult : MatrixMultiplier) (B : CRTBasis) (P : ℕ) (xs ys : List (ℤ × ℤ)) :
    Option (ℤ × ℤ × ℤ × ℤ) :=
  (ozaki2IntZ mult B P xs ys).map fun N =>
    (N, -(scaleShiftZ P xs + scaleShiftZ P ys),
      boundK (scaleTruncZ (scaleShiftZ P xs) xs) (scaleTruncZ (scaleShiftZ P ys) ys)
        (dropsZ (scaleShiftZ P xs) xs) (dropsZ (scaleShiftZ P ys) ys) xs.length,
      -(scaleShiftZ P xs + scaleShiftZ P ys))

theorem entryVals_length (xs : List (ℤ × ℤ)) : (entryVals xs).length = xs.length := by
  simp [entryVals]

/-- **The integer pipeline's enclosure is Ozaki-II's integer enclosure of the values.** -/
theorem ozaki2EnclosureZ_eq (mult : MatrixMultiplier) (B : CRTBasis) (P : ℕ) (xs ys : List (ℤ × ℤ)) :
    ozaki2EnclosureZ mult B P xs ys = ozaki2EnclosureB mult B P (entryVals xs) (entryVals ys) := by
  unfold ozaki2EnclosureZ ozaki2EnclosureB ozaki2IntZ ozaki2Int ozaki2K
  rw [scaleShiftZ_eq, scaleShiftZ_eq, scaleTruncZ_eq, scaleTruncZ_eq, dropsZ_trunc_eq,
    dropsZ_trunc_eq, entryVals_length]

/-! ## The exact fallback with integer slicing -/

/-- Nothing is left over after `s` integer slices of both vectors. -/
def residualsVanishZ (b s : ℕ) (xs ys : List (ℤ × ℤ)) : Bool :=
  (splitInt b s xs).2.all (fun r => r.1 == 0) && (splitInt b s ys).2.all (fun r => r.1 == 0)

theorem residualsVanishZ_eq (b s : ℕ) (xs ys : List (ℤ × ℤ)) :
    residualsVanishZ b s xs ys = residualsVanish b s (entryVals xs) (entryVals ys) := by
  have h : ∀ zs : List (ℤ × ℤ), (splitInt b s zs).2.all (fun r => r.1 == 0) =
      (split b s (entryVals zs)).2.all (· == 0) := by
    intro zs
    rw [← (splitInt_eq b s zs).2]
    unfold entryVals
    rw [List.all_map]
    congr 1
    funext r
    simp only [Function.comp]
    unfold entryVal
    have hp := two_pow_pos r.2
    by_cases hr : r.1 = 0
    · simp [hr]
    · have : (r.1 : ℚ) * 2 ^ r.2 ≠ 0 := fun h => hr (by
        have h0 := (sgnQ_eq_zero_iff _).mpr h
        rw [sgnQ_mul_two_pow, sgnQ_eq_zero_iff] at h0
        exact_mod_cast h0)
      have e1 : (r.1 == 0) = false := by simpa using hr
      have e2 : ((r.1 : ℚ) * 2 ^ r.2 == 0) = false := by simpa using this
      rw [e1, e2]
  unfold residualsVanishZ residualsVanish
  rw [h xs, h ys]

/-- **The bounded exact fallback with integer slicing**: `splitInt` for the test that nothing is
left over and for the slices, the slice products from the matrix multiplier as integer terms,
`roundSum`. -/
def ozaki1ExactFallbackZ (mult : MatrixMultiplier) (p : ℕ) (emin emax : ℤ) (b smax : ℕ)
    (xs ys : List (ℤ × ℤ)) : Option ℚ :=
  match (List.range' 1 smax).find? fun s => residualsVanishZ b s xs ys with
  | some s =>
    match (slicePairs (splitInt b s xs).1 (splitInt b s ys).1).mapM
        (fun pr => sliceProductInt mult pr.1 pr.2) with
    | some ts => roundSum p emin emax (bitlen (ts.length + 1) + p + 4) ts
    | none => none
  | none => none

theorem ozaki1ExactFallbackZ_eq (mult : MatrixMultiplier) (p : ℕ) (emin emax : ℤ) (b smax : ℕ)
    (xs ys : List (ℤ × ℤ)) :
    ozaki1ExactFallbackZ mult p emin emax b smax xs ys =
      ozaki1ExactFallbackB mult p emin emax b smax (entryVals xs) (entryVals ys) := by
  have hf : (fun s => residualsVanishZ b s xs ys) =
      fun s => residualsVanish b s (entryVals xs) (entryVals ys) := by
    funext s; exact residualsVanishZ_eq b s xs ys
  unfold ozaki1ExactFallbackZ ozaki1ExactFallbackB
  rw [hf]
  cases (List.range' 1 smax).find? fun s => residualsVanish b s (entryVals xs) (entryVals ys) with
  | none => rfl
  | some s =>
    simp only
    rw [(splitInt_eq b s xs).1, (splitInt_eq b s ys).1]
    cases (slicePairs (split b s (entryVals xs)).1 (split b s (entryVals ys)).1).mapM
      (fun pr => sliceProductInt mult pr.1 pr.2) <;> rfl

/-! ## Correctly rounded Ozaki-II from integer inputs -/

/-- **Correctly rounded Ozaki-II as an integer pipeline**: integer pairs in, the integer enclosures
of the configurations in turn, then the exact fallback with integer slicing; every step integer
arithmetic, and the result the IEEE round to nearest. -/
def ozaki2CRZ (mult : MatrixMultiplier) (p : ℕ) (emin emax : ℤ) (cfgs : List (CRTBasis × ℕ)) (b smax : ℕ)
    (xs ys : List (ℤ × ℤ)) : Option ℚ :=
  roundingTestB p emin emax (cfgs.map fun c => ozaki2EnclosureZ mult c.1 c.2 xs ys)
    (ozaki1ExactFallbackZ mult p emin emax b smax xs ys)

theorem ozaki2CRZ_eq_CRB (mult : MatrixMultiplier) (p : ℕ) (emin emax : ℤ) (cfgs : List (CRTBasis × ℕ))
    (b smax : ℕ) (xs ys : List (ℤ × ℤ)) :
    ozaki2CRZ mult p emin emax cfgs b smax xs ys =
      ozaki2CRB mult p emin emax cfgs b smax (entryVals xs) (entryVals ys) := by
  unfold ozaki2CRZ ozaki2CRB
  rw [ozaki1ExactFallbackZ_eq]
  congr 1
  apply List.map_congr_left
  intro c _
  exact ozaki2EnclosureZ_eq mult c.1 c.2 xs ys

/-- **The integer pipeline is correctly rounded.** -/
theorem ozaki2CRZ_eq {p : ℕ} {emin emax : ℤ} (hp : 0 < p) (hle : emin ≤ emax) {mult : MatrixMultiplier}
    {b bound : ℕ} (hmult : mult.ExactOn b bound) {cfgs : List (CRTBasis × ℕ)} {smax : ℕ}
    {xs ys : List (ℤ × ℤ)}
    (hcfg : ∀ c ∈ cfgs, c.1.Valid ∧ (∀ m ∈ c.1.moduli, m ≤ 2 ^ (b + 1)) ∧
      2 * xs.length * (2 ^ c.2 * 2 ^ c.2) < c.1.modulus)
    (hlen : xs.length = ys.length) (hbound : xs.length * (2 ^ b * 2 ^ b) ≤ bound)
    (hvanish : ∃ s ∈ List.range' 1 smax,
      residualsVanish b s (entryVals xs) (entryVals ys) = true) :
    ozaki2CRZ mult p emin emax cfgs b smax xs ys =
      roundRNE p emin emax (dot (entryVals xs) (entryVals ys)) := by
  rw [ozaki2CRZ_eq_CRB]
  exact ozaki2CRB_eq hp hle hmult (by rw [entryVals_length]; exact hcfg)
    (by rw [entryVals_length, entryVals_length, hlen]) (by rw [entryVals_length]; exact hbound)
    hvanish

/-- **Binary64 inputs as integer pairs**: correctly rounded to binary64. -/
theorem ozaki2CRZ64_eq {mult : MatrixMultiplier} {b bound : ℕ} (hmult : mult.ExactOn b bound)
    {cfgs : List (CRTBasis × ℕ)} {smax : ℕ} (hb : b ≤ 1025) (hsmax : 2098 < smax * (b + 1))
    {xs ys : List (ℤ × ℤ)}
    (hcfg : ∀ c ∈ cfgs, c.1.Valid ∧ (∀ m ∈ c.1.moduli, m ≤ 2 ^ (b + 1)) ∧
      2 * xs.length * (2 ^ c.2 * 2 ^ c.2) < c.1.modulus)
    (hlen : xs.length = ys.length) (hbound : xs.length * (2 ^ b * 2 ^ b) ≤ bound)
    (hx : ∀ v ∈ entryVals xs, Binary64Value v) (hy : ∀ v ∈ entryVals ys, Binary64Value v) :
    ozaki2CRZ mult 53 (-1022) 1023 cfgs b smax xs ys = rne64 (dot (entryVals xs) (entryVals ys)) :=
  ozaki2CRZ_eq (by decide) (by decide) hmult hcfg hlen hbound (vanish64 hb hsmax hx hy)

/-- **Binary32 inputs as integer pairs**: correctly rounded to binary32. -/
theorem ozaki2CRZ32_eq {mult : MatrixMultiplier} {b bound : ℕ} (hmult : mult.ExactOn b bound)
    {cfgs : List (CRTBasis × ℕ)} {smax : ℕ} (hb : b ≤ 129) (hsmax : 277 < smax * (b + 1))
    {xs ys : List (ℤ × ℤ)}
    (hcfg : ∀ c ∈ cfgs, c.1.Valid ∧ (∀ m ∈ c.1.moduli, m ≤ 2 ^ (b + 1)) ∧
      2 * xs.length * (2 ^ c.2 * 2 ^ c.2) < c.1.modulus)
    (hlen : xs.length = ys.length) (hbound : xs.length * (2 ^ b * 2 ^ b) ≤ bound)
    (hx : ∀ v ∈ entryVals xs, Binary32Value v) (hy : ∀ v ∈ entryVals ys, Binary32Value v) :
    ozaki2CRZ mult 24 (-126) 127 cfgs b smax xs ys = rne32Q (dot (entryVals xs) (entryVals ys)) :=
  ozaki2CRZ_eq (by decide) (by decide) hmult hcfg hlen hbound (vanish32Q hb hsmax hx hy)

/-! ## Widths of the integer pipeline -/

/-- **The shifted significands are at most `2^P`**, whatever the exponents. -/
theorem scaleTruncZ_natAbs_le (P : ℕ) (xs : List (ℤ × ℤ)) :
    ∀ z ∈ scaleTruncZ (scaleShiftZ P xs) xs, z.natAbs ≤ 2 ^ P := by
  rw [scaleShiftZ_eq, scaleTruncZ_eq]
  exact scaleTrunc_bound P (entryVals xs)

/-- **A left shift's amount is at most `P`** for a nonzero significand, since its result is at most
`2^P`. -/
theorem truncShift_left_le {P : ℕ} {m j : ℤ} (hm : m ≠ 0) (hj : 0 ≤ j)
    (h : (truncShiftZ m j).natAbs ≤ 2 ^ P) : j.toNat ≤ P := by
  unfold truncShiftZ at h
  rw [if_neg hm, if_pos hj, Int.natAbs_mul, Int.natAbs_pow] at h
  have h1 : 1 ≤ m.natAbs := by omega
  have h2 : 2 ^ j.toNat ≤ 2 ^ P := by
    have := Nat.mul_le_mul_right ((2 : ℤ).natAbs ^ j.toNat) h1
    simp only [Nat.one_mul] at this
    exact Nat.le_trans this h
  exact (Nat.pow_le_pow_iff_right (by decide)).mp h2

/-- **The CRT sum** `Σ wⱼ rⱼ` with reduced residues `|rⱼ| ≤ R` is at most `(Σ |wⱼ|) R`. -/
theorem crtSum_natAbs_le {R : ℕ} : ∀ (ws rs : List ℤ), (∀ r ∈ rs, r.natAbs ≤ R) →
    (dotZ ws rs).natAbs ≤ (ws.map Int.natAbs).sum * R
  | [], _, _ => by simp
  | _ :: _, [], _ => by simp
  | w :: ws, r :: rs, h => by
    have ih := crtSum_natAbs_le ws rs fun r' hr' => h r' (List.mem_cons_of_mem _ hr')
    have hr := h r List.mem_cons_self
    simp only [dotZ_cons, List.map_cons, List.sum_cons]
    have h1 := Int.natAbs_add_le (w * r) (dotZ ws rs)
    have h2 : (w * r).natAbs ≤ w.natAbs * R := by
      rw [Int.natAbs_mul]; exact Nat.mul_le_mul_left _ hr
    rw [Nat.add_mul]
    omega

/-- **A reduced residue** `z mod m` is below `m`. -/
theorem residue_natAbs_lt (z : ℤ) {m : ℕ} (hm : 0 < m) : (z % (m : ℤ)).natAbs < m := by
  have h0 := Int.emod_nonneg z (show (m : ℤ) ≠ 0 by omega)
  have h1 := Int.emod_lt_of_pos z (show (0 : ℤ) < m by omega)
  omega

end Ozaki
