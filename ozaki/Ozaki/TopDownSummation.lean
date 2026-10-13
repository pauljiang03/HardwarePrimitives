import Ozaki.SignOracle

/-! # A descent whose number of windows does not depend on the exponents

`topDownSum` (in `Ozaki.SignOracle`) moves its window down from the accumulator's top. When a
cancellation leaves the accumulator exactly zero, the next window starts at the old grid, however
far below it the remaining terms lie, so the number of windows grows with the exponent span
(`topDownSumAll_fuel_le`). `topDownSumJ` jumps instead: with a zero accumulator the next window starts at
the top of the largest remaining term (`rangeTop`). Everything else is unchanged.

* `topDownSumJ_sound`: what it returns is exact, as for `topDownSum`.
* `topDownSumJ_spec`: it ends with fuel `potential rs`, the total bit length of the terms'
  coefficients: every window that does not stop removes at least one bit from some remaining term
  (`potential_rangeRest_lt`). So it evaluates at most `potential + 1` windows (`topDownSumJRanges_le`),
  at most `n · bitlen M + 1` for `n` terms of magnitude at most `M` (`rangesJ_le`), whatever the
  exponents.
* `signSumJ`, `roundSumJ`: the sign and the round to nearest even of a sum of terms, as
  `signSum` and `roundSum`, with this descent (`signSumJ_eq`, `roundSumJ_eq`). -/

local notation "ℕ" => Nat
local notation "ℤ" => Int
local notation "ℚ" => Rat

namespace Ozaki

/-! ## The potential -/

/-- The total bit length of the coefficients of a list of terms. -/
def potential (ts : List (ℤ × ℤ)) : ℕ := (ts.map fun t => bitlen t.1.natAbs).sum

theorem potential_cons (t : ℤ × ℤ) (ts : List (ℤ × ℤ)) :
    potential (t :: ts) = bitlen t.1.natAbs + potential ts := by
  simp [potential]

theorem potential_nonzero (ts : List (ℤ × ℤ)) : potential (nonzero ts) = potential ts := by
  induction ts with
  | nil => rfl
  | cons t ts ih =>
    unfold nonzero at ih ⊢
    rw [List.filter_cons]
    by_cases h : t.1 = 0
    · have : (t.1 != 0) = false := by simp [h]
      rw [if_neg (by simp [this]), ih, potential_cons, h]; simp [bitlen]
    · have : (t.1 != 0) = true := by simp [h]
      rw [if_pos this, potential_cons, potential_cons, ih]

/-- **The potential bounds the window count**: at most `n · bitlen M` for `n` terms of magnitude at
most `M`. -/
theorem potential_le {M : ℕ} : ∀ {ts : List (ℤ × ℤ)}, (∀ t ∈ ts, t.1.natAbs ≤ M) →
    potential ts ≤ ts.length * bitlen M
  | [], _ => by simp [potential]
  | t :: ts, h => by
    rw [potential_cons, List.length_cons, Nat.succ_mul]
    have h1 := bitlen_mono (h t List.mem_cons_self)
    have h2 := potential_le (ts := ts) fun u hu => h u (List.mem_cons_of_mem _ hu)
    omega

theorem sum_map_le {α : Type} {f g : α → ℕ} : ∀ {l : List α}, (∀ a ∈ l, f a ≤ g a) →
    (l.map f).sum ≤ (l.map g).sum
  | [], _ => by simp
  | a :: l, hle => by
    simp only [List.map_cons, List.sum_cons]
    have h1 := hle a List.mem_cons_self
    have h2 := sum_map_le (l := l) fun e he => hle e (List.mem_cons_of_mem _ he)
    omega

theorem sum_map_lt {α : Type} {f g : α → ℕ} : ∀ {l : List α}, (∀ a ∈ l, f a ≤ g a) →
    (∃ a ∈ l, f a < g a) → (l.map f).sum < (l.map g).sum
  | [], _, ⟨_, h, _⟩ => by simp at h
  | a :: l, hle, ⟨c, hc, hlt⟩ => by
    simp only [List.map_cons, List.sum_cons]
    rcases List.mem_cons.mp hc with rfl | hc
    · have h2 := sum_map_le (l := l) fun e he => hle e (List.mem_cons_of_mem _ he)
      omega
    · have h1 := hle a List.mem_cons_self
      have h2 := sum_map_lt (fun e he => hle e (List.mem_cons_of_mem _ he)) ⟨c, hc, hlt⟩
      omega

/-- A term reaching above the grid `q` loses at least one bit when cut there. -/
theorem bitlen_loPart_lt {q : ℤ} {t : ℤ × ℤ} (ht : t.1 ≠ 0) (hq : q < topOf t) :
    bitlen (loPart q t).1.natAbs < bitlen t.1.natAbs := by
  obtain ⟨z, g⟩ := t
  unfold topOf at hq; simp only at ht hq
  have hb := bitlen_pos (n := z.natAbs) (by omega)
  unfold loPart; simp only
  split
  · have : bitlen (0 : ℤ).natAbs = 0 := by simp [bitlen]
    rw [this]; omega
  · rename_i hlt
    rw [natAbs_tmodPow]
    have hm := Nat.mod_lt z.natAbs (Nat.two_pow_pos (q - g).toNat)
    have := bitlen_le_iff.mpr hm
    omega

theorem potential_map_loPart_le (q : ℤ) (ts : List (ℤ × ℤ)) :
    potential (ts.map (loPart q)) ≤ potential ts := by
  unfold potential
  rw [List.map_map]
  exact sum_map_le fun t _ => bitlen_mono (natAbs_loPart_le q t)

/-- **Cutting at a grid below the top of some term lowers the potential.** -/
theorem potential_rangeRest_lt {q : ℤ} {ts : List (ℤ × ℤ)} (hne : ∀ t ∈ ts, t.1 ≠ 0)
    (h : ∃ t ∈ ts, q < topOf t) : potential (rangeRest q ts) < potential ts := by
  unfold rangeRest
  rw [potential_nonzero]
  unfold potential
  rw [List.map_map]
  obtain ⟨t, ht, hq⟩ := h
  exact sum_map_lt (fun u _ => bitlen_mono (natAbs_loPart_le q u))
    ⟨t, ht, bitlen_loPart_lt (hne t ht) hq⟩

theorem potential_pos {ts : List (ℤ × ℤ)} (hne : ∀ t ∈ ts, t.1 ≠ 0) (h : ts ≠ []) :
    0 < potential ts := by
  obtain ⟨t, ts', rfl⟩ := List.exists_cons_of_ne_nil h
  rw [potential_cons]
  have := bitlen_pos (n := t.1.natAbs) (by have := hne t List.mem_cons_self; omega)
  omega

/-! ## Parts and tops -/

theorem sum_map_eq_zero {α : Type} {f : α → ℤ} : ∀ {l : List α}, (∀ a ∈ l, f a = 0) →
    (l.map f).sum = 0
  | [], _ => rfl
  | a :: l, h => by
    rw [List.map_cons, List.sum_cons, h a List.mem_cons_self,
      sum_map_eq_zero fun c hc => h c (List.mem_cons_of_mem _ hc)]
    rfl

theorem hiPart_zero (q g : ℤ) : hiPart q (0, g) = 0 := by
  unfold hiPart tdivPow; simp

theorem loPart_zero (q g : ℤ) : (loPart q (0, g)).1 = 0 := by
  unfold loPart tmodPow; simp

/-- A term below `2^q` has no part above `q`. -/
theorem hiPart_eq_zero {q : ℤ} {t : ℤ × ℤ} (h : topOf t ≤ q) : hiPart q t = 0 := by
  obtain ⟨z, g⟩ := t
  unfold topOf at h; simp only at h
  unfold hiPart; simp only
  split
  · rename_i hle
    have h0 : bitlen z.natAbs = 0 := by omega
    have hz := lt_two_pow_bitlen z.natAbs
    rw [h0, Nat.pow_zero] at hz
    have : z = 0 := by omega
    subst this; simp
  · rename_i hlt
    have hz := lt_two_pow_bitlen z.natAbs
    have hzz : z.natAbs < 2 ^ (q - g).toNat :=
      Nat.lt_of_lt_of_le hz (Nat.pow_le_pow_right (by decide) (by omega))
    unfold tdivPow
    rw [Nat.shiftRight_eq_div_pow, Nat.div_eq_of_lt hzz]
    simp

theorem bitlen_mul_two_pow {n : ℕ} (hn : n ≠ 0) (d : ℕ) : bitlen (n * 2 ^ d) = bitlen n + d := by
  have h1 := lt_two_pow_bitlen n
  have h2 := two_pow_bitlen_le hn
  have hb := bitlen_pos hn
  have hu : n * 2 ^ d < 2 ^ (bitlen n + d) := by
    rw [Nat.pow_add]; exact Nat.mul_lt_mul_of_pos_right h1 (Nat.two_pow_pos d)
  have hl : 2 ^ (bitlen n - 1 + d) ≤ n * 2 ^ d := by
    rw [Nat.pow_add]; exact Nat.mul_le_mul_right _ h2
  have a := bitlen_le_iff.mpr hu
  have hne : n * 2 ^ d ≠ 0 := Nat.mul_ne_zero hn (Nat.ne_of_gt (Nat.two_pow_pos d))
  have b := lt_two_pow_bitlen (n * 2 ^ d)
  have c : bitlen n - 1 + d < bitlen (n * 2 ^ d) := by
    apply Classical.byContradiction; intro hc
    have : 2 ^ bitlen (n * 2 ^ d) ≤ 2 ^ (bitlen n - 1 + d) :=
      Nat.pow_le_pow_right (by decide) (by omega)
    omega
  omega

theorem maxTopFrom_mem : ∀ (ts : List (ℤ × ℤ)) (e : ℤ),
    maxTopFrom e ts = e ∨ ∃ t ∈ ts, topOf t = maxTopFrom e ts
  | [], e => Or.inl rfl
  | t :: ts, e => by
    rcases maxTopFrom_mem ts (max e (topOf t)) with h | ⟨u, hu, h⟩
    · unfold maxTopFrom
      rw [h]
      by_cases hle : e ≤ topOf t
      · right; exact ⟨t, List.mem_cons_self, by omega⟩
      · left; omega
    · right; exact ⟨u, List.mem_cons_of_mem _ hu, by unfold maxTopFrom; exact h⟩

/-- A nonempty list has a term at its largest top. -/
theorem exists_maxTop {ts : List (ℤ × ℤ)} (h : ts ≠ []) : ∃ t ∈ ts, topOf t = maxTop ts := by
  obtain ⟨u, us, rfl⟩ := List.exists_cons_of_ne_nil h
  unfold maxTop
  rcases maxTopFrom_mem us (topOf u) with h | ⟨t, ht, h⟩
  · exact ⟨u, List.mem_cons_self, h.symm⟩
  · exact ⟨t, List.mem_cons_of_mem _ ht, h⟩

/-! ## The descent -/

/-- The top of the next window: the accumulator's, or the largest remaining term's when the
accumulator is zero. -/
def rangeTop (A qa : ℤ) (rs : List (ℤ × ℤ)) : ℤ := if A = 0 then maxTop rs else topOf (A, qa)

/-- **Windows from the top down, jumping over empty gaps.** As `topDownSum`, except that a zero
accumulator does not hold the window up: the next window starts at the top of the largest
remaining term. -/
def topDownSumJ (W T : ℕ) : ℕ → ℤ → ℤ → List (ℤ × ℤ) → Option (ℤ × ℤ × List (ℤ × ℤ))
  | fuel, A, qa, rs =>
    let ts := (A, qa) :: rs
    let q := rangeTop A qa rs - W
    let parts := ts.map (hiPart q)
    let N := fixedSum (W + bitlen parts.length + 1) parts
    let rs' := rangeRest q ts
    if parts.all (fun z => decide (z.natAbs < 2 ^ W)) then
      if rs' = [] ∨ T < bitlen N.natAbs then some (N, q, rs')
      else match fuel with
        | 0 => none
        | k + 1 => topDownSumJ W T k N q rs'
    else none

/-- The number of windows `topDownSumJ` evaluates. -/
def topDownSumJRanges (W T : ℕ) : ℕ → ℤ → ℤ → List (ℤ × ℤ) → ℕ
  | fuel, A, qa, rs =>
    let ts := (A, qa) :: rs
    let q := rangeTop A qa rs - W
    let parts := ts.map (hiPart q)
    let N := fixedSum (W + bitlen parts.length + 1) parts
    let rs' := rangeRest q ts
    if parts.all (fun z => decide (z.natAbs < 2 ^ W)) then
      if rs' = [] ∨ T < bitlen N.natAbs then 1
      else match fuel with
        | 0 => 1
        | k + 1 => topDownSumJRanges W T k N q rs' + 1
    else 1

/-- A run with fuel `f` evaluates at most `f + 1` windows. -/
theorem topDownSumJRanges_le (W T : ℕ) : ∀ (fuel : ℕ) (A qa : ℤ) (rs : List (ℤ × ℤ)),
    topDownSumJRanges W T fuel A qa rs ≤ fuel + 1
  | 0, A, qa, rs => by
    unfold topDownSumJRanges; simp only; split <;> (try split) <;> omega
  | k + 1, A, qa, rs => by
    unfold topDownSumJRanges; simp only
    split
    · split
      · omega
      · exact Nat.add_le_add_right (topDownSumJRanges_le W T k _ _ _) 1
    · omega

/-- The accumulator leaves nothing when it is zero or lies on or above the grid. -/
theorem rangeRest_acc {q A qa : ℤ} {rs : List (ℤ × ℤ)} (h : A = 0 ∨ q ≤ qa) :
    rangeRest q ((A, qa) :: rs) = rangeRest q rs := by
  rcases h with h | h
  · subst h
    unfold rangeRest nonzero
    rw [List.map_cons, List.filter_cons]
    rw [if_neg (by simp [loPart_zero])]
  · exact rangeRest_cons_of_le h

theorem rangeRest_nil (q : ℤ) : rangeRest q [] = [] := rfl

/-- **What `topDownSumJ` returns is exact**, as for `topDownSum`. -/
theorem topDownSumJ_sound {W T : ℕ} : ∀ (fuel : ℕ) (A qa : ℤ) (rs : List (ℤ × ℤ)) {N q : ℤ}
    {rs' : List (ℤ × ℤ)}, topDownSumJ W T fuel A qa rs = some (N, q, rs') →
    tval (A, qa) + tsum rs = (N : ℚ) * 2 ^ q + tsum rs' ∧
      (∀ t ∈ rs', t.1 ≠ 0 ∧ topOf t ≤ q) ∧ (rs' = [] ∨ T < bitlen N.natAbs) := by
  intro fuel
  induction fuel with
  | zero =>
    intro A qa rs N q rs' h
    unfold topDownSumJ at h
    simp only at h
    split at h
    · rename_i hall
      have hsum := register_fixedSum (W := W)
        (ps := ((A, qa) :: rs).map (hiPart (rangeTop A qa rs - W)))
        (fun z hz => by simpa using List.all_eq_true.mp hall z hz)
      split at h
      · rename_i hstop
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl, rfl⟩ := h
        rw [hsum, ← tsum_cons]
        exact ⟨tsum_range _ _, fun t ht => (mem_rangeRest ht).imp_right fun h => h.1,
          by rw [← hsum]; exact hstop⟩
      · simp at h
    · simp at h
  | succ k ih =>
    intro A qa rs N q rs' h
    unfold topDownSumJ at h
    simp only at h
    split at h
    · rename_i hall
      have hsum := register_fixedSum (W := W)
        (ps := ((A, qa) :: rs).map (hiPart (rangeTop A qa rs - W)))
        (fun z hz => by simpa using List.all_eq_true.mp hall z hz)
      split at h
      · rename_i hstop
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl, rfl⟩ := h
        rw [hsum, ← tsum_cons]
        exact ⟨tsum_range _ _, fun t ht => (mem_rangeRest ht).imp_right fun h => h.1,
          by rw [← hsum]; exact hstop⟩
      · obtain ⟨h1, h2, h3⟩ := ih _ _ _ h
        refine ⟨?_, h2, h3⟩
        rw [← h1, ← tsum_cons, tsum_range (rangeTop A qa rs - W), hsum]
        unfold tval; rfl
    · simp at h

/-- The window parts are `W`-bit integers on every state the descent reaches. -/
theorem topDownSumJ_parts_lt {W : ℕ} {A qa : ℤ} {rs : List (ℤ × ℤ)} (hA : bitlen A.natAbs ≤ W)
    (hrs : ∀ t ∈ rs, topOf t ≤ qa) :
    ∀ z ∈ ((A, qa) :: rs).map (hiPart (rangeTop A qa rs - W)), z.natAbs < 2 ^ W := by
  intro z hz
  obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hz
  by_cases hA0 : A = 0
  · subst hA0
    rcases List.mem_cons.mp ht with rfl | ht
    · rw [hiPart_zero]; exact Nat.two_pow_pos W
    · apply natAbs_hiPart_lt
      unfold rangeTop; rw [if_pos rfl]
      have := le_maxTop ht; omega
  · have hq : rangeTop A qa rs = topOf (A, qa) := by unfold rangeTop; rw [if_neg hA0]
    rw [hq]
    apply natAbs_hiPart_lt
    rcases List.mem_cons.mp ht with rfl | ht
    · omega
    · have := hrs t ht; unfold topOf at this ⊢; simp only at this ⊢; omega

/-- **`topDownSumJ` ends with fuel the potential of the remaining terms**, with no more residuals
than it started with, each on the grid of an original term and no larger. -/
theorem topDownSumJ_spec {W T : ℕ} (hTW : T < W) : ∀ (fuel : ℕ) (A qa : ℤ)
    (rs : List (ℤ × ℤ)), bitlen A.natAbs ≤ T → (∀ t ∈ rs, t.1 ≠ 0 ∧ topOf t ≤ qa) →
    potential rs ≤ fuel → ∃ N q rs', topDownSumJ W T fuel A qa rs = some (N, q, rs') ∧
      rs'.length ≤ rs.length ∧
      (∀ t' ∈ rs', ∃ t ∈ rs, t'.2 = t.2 ∧ t'.1.natAbs ≤ t.1.natAbs) ∧
      N.natAbs ≤ 2 ^ (W + bitlen (rs.length + 1)) := by
  intro fuel
  induction fuel with
  | zero =>
    intro A qa rs hA hrs hpot
    have hrs0 : rs = [] := by
      apply Classical.byContradiction; intro hne
      have := potential_pos (fun t ht => (hrs t ht).1) hne; omega
    subst hrs0
    have hall : (((A, qa) :: []).map (hiPart (rangeTop A qa [] - W))).all
        (fun z => decide (z.natAbs < 2 ^ W)) = true :=
      List.all_eq_true.mpr fun z hz => decide_eq_true
        (topDownSumJ_parts_lt (by omega) (by simp) z hz)
    have hacc : A = 0 ∨ rangeTop A qa [] - W ≤ qa := by
      by_cases hA0 : A = 0
      · exact Or.inl hA0
      · right; unfold rangeTop topOf; rw [if_neg hA0]; simp only; omega
    unfold topDownSumJ
    simp only
    rw [if_pos hall, rangeRest_acc hacc, rangeRest_nil, if_pos (Or.inl rfl)]
    refine ⟨_, _, _, rfl, by simp, by simp, ?_⟩
    refine Nat.le_trans (fixedSum_natAbs_le (by omega) _) (Nat.le_of_eq ?_)
    simp
  | succ k ih =>
    intro A qa rs hA hrs hpot
    have hall : (((A, qa) :: rs).map (hiPart (rangeTop A qa rs - W))).all
        (fun z => decide (z.natAbs < 2 ^ W)) = true :=
      List.all_eq_true.mpr fun z hz => decide_eq_true
        (topDownSumJ_parts_lt (by omega) (fun t ht => (hrs t ht).2) z hz)
    have hacc : A = 0 ∨ rangeTop A qa rs - W ≤ qa := by
      by_cases hA0 : A = 0
      · exact Or.inl hA0
      · right; unfold rangeTop topOf; rw [if_neg hA0]; simp only; omega
    have hsum := register_fixedSum (W := W)
      (ps := ((A, qa) :: rs).map (hiPart (rangeTop A qa rs - W)))
      (fun z hz => by simpa using List.all_eq_true.mp hall z hz)
    unfold topDownSumJ
    simp only
    rw [if_pos hall, rangeRest_acc hacc]
    split
    · refine ⟨_, _, _, rfl, length_rangeRest _ _, fun t' ht' => ?_, ?_⟩
      · obtain ⟨_, _, t, ht, h1, h2, _⟩ := mem_rangeRest ht'
        exact ⟨t, ht, h1, h2⟩
      · refine Nat.le_trans (fixedSum_natAbs_le (by omega) _) (Nat.le_of_eq ?_)
        simp only [List.length_map, List.length_cons]
        congr 1
    · rename_i hstop
      have hN := Nat.le_of_not_lt (fun h => hstop (Or.inr h))
      have hrsne : rangeRest (rangeTop A qa rs - W) rs ≠ [] := fun h => hstop (Or.inl h)
      -- some remaining term reaches above the window's grid
      have hwit : ∃ t ∈ rs, rangeTop A qa rs - W < topOf t := by
        by_cases hA0 : A = 0
        · have hne : rs ≠ [] := by
            intro h; subst h; exact hrsne (rangeRest_nil _)
          obtain ⟨t, ht, htop⟩ := exists_maxTop hne
          refine ⟨t, ht, ?_⟩
          unfold rangeTop; rw [if_pos hA0, ← htop]; omega
        · apply Classical.byContradiction; intro hno
          have hall0 : ∀ t ∈ rs, hiPart (rangeTop A qa rs - W) t = 0 := fun t ht =>
            hiPart_eq_zero (Int.not_lt.mp fun h => hno ⟨t, ht, h⟩)
          have hq : rangeTop A qa rs - W = qa + bitlen A.natAbs - W := by
            unfold rangeTop topOf; rw [if_neg hA0]
          have hsum0 : (rs.map (hiPart (rangeTop A qa rs - W))).sum = 0 :=
            sum_map_eq_zero hall0
          have hNe : fixedSum (W + bitlen (((A, qa) :: rs).map
              (hiPart (rangeTop A qa rs - W))).length + 1)
              (((A, qa) :: rs).map (hiPart (rangeTop A qa rs - W))) =
              A * 2 ^ (qa - (rangeTop A qa rs - W)).toNat := by
            rw [hsum, List.map_cons, List.sum_cons, hsum0, Int.add_zero]
            unfold hiPart; rw [if_pos (by omega)]
          apply hstop; right
          rw [hNe, Int.natAbs_mul, Int.natAbs_pow]
          show T < bitlen (A.natAbs * 2 ^ (qa - (rangeTop A qa rs - W)).toNat)
          rw [bitlen_mul_two_pow (by omega)]
          omega
      have hpot' : potential (rangeRest (rangeTop A qa rs - W) rs) ≤ k := by
        have := potential_rangeRest_lt (fun t ht => (hrs t ht).1) hwit
        omega
      have hrs' : ∀ t' ∈ rangeRest (rangeTop A qa rs - W) rs,
          t'.1 ≠ 0 ∧ topOf t' ≤ rangeTop A qa rs - W := fun t' ht' => by
        obtain ⟨hne, htop, _⟩ := mem_rangeRest ht'
        exact ⟨hne, htop⟩
      obtain ⟨N', q', rs'', h, hlen, hsub, hN'⟩ := ih _ _ _ hN hrs' hpot'
      refine ⟨N', q', rs'', h, Nat.le_trans hlen (length_rangeRest _ _), fun t'' ht'' => ?_, ?_⟩
      · obtain ⟨t', ht', h1, h2⟩ := hsub t'' ht''
        obtain ⟨_, _, t, ht, h3, h4, _⟩ := mem_rangeRest ht'
        exact ⟨t, ht, h1.trans h3, Nat.le_trans h2 h4⟩
      · refine Nat.le_trans hN' (Nat.pow_le_pow_right (by decide) ?_)
        have := bitlen_mono
          (Nat.add_le_add_right (length_rangeRest (rangeTop A qa rs - W) rs) 1)
        omega

/-! ## From the top of the nonzero terms -/

/-- `topDownSumJ` from the top of the nonzero terms, with fuel their potential. -/
def topDownSumAllJ (W T : ℕ) (ts : List (ℤ × ℤ)) : Option (ℤ × ℤ × List (ℤ × ℤ)) :=
  let rs := nonzero ts
  topDownSumJ W T (potential rs) 0 (maxTop rs) rs

/-- The number of windows of `topDownSumAllJ`. -/
def rangesJ (W T : ℕ) (ts : List (ℤ × ℤ)) : ℕ :=
  let rs := nonzero ts
  topDownSumJRanges W T (potential rs) 0 (maxTop rs) rs

/-- **The number of windows does not depend on the exponents**: at most `n · bitlen M + 1` for
`n` terms of magnitude at most `M`. -/
theorem rangesJ_le (W T : ℕ) {ts : List (ℤ × ℤ)} {M : ℕ} (h : ∀ t ∈ ts, t.1.natAbs ≤ M) :
    rangesJ W T ts ≤ ts.length * bitlen M + 1 := by
  unfold rangesJ
  simp only
  have h1 := topDownSumJRanges_le W T (potential (nonzero ts)) 0 (maxTop (nonzero ts)) (nonzero ts)
  have h2 := potential_le (M := M) (ts := nonzero ts) fun t ht => h t (mem_nonzero.mp ht).1
  have h3 := Nat.mul_le_mul_right (bitlen M) (length_nonzero ts)
  omega

theorem topDownSumAllJ_spec {W T : ℕ} (hTW : T < W) (ts : List (ℤ × ℤ)) :
    ∃ N q rs', topDownSumAllJ W T ts = some (N, q, rs') ∧
      tsum ts = (N : ℚ) * 2 ^ q + tsum rs' ∧ (∀ t ∈ rs', t.1 ≠ 0 ∧ topOf t ≤ q) ∧
      (rs' = [] ∨ T < bitlen N.natAbs) ∧ rs'.length ≤ (nonzero ts).length ∧
      (∀ t' ∈ rs', ∃ t ∈ ts, t'.2 = t.2 ∧ t'.1.natAbs ≤ t.1.natAbs) ∧
      N.natAbs ≤ 2 ^ (W + bitlen ((nonzero ts).length + 1)) := by
  obtain ⟨N, q, rs', h, hlen, hsub, hN⟩ := topDownSumJ_spec hTW
    (potential (nonzero ts)) 0 (maxTop (nonzero ts)) (nonzero ts)
    (by simp [bitlen]) (fun t ht => ⟨(mem_nonzero.mp ht).2, le_maxTop ht⟩) (Nat.le_refl _)
  obtain ⟨h1, h2, h3⟩ := topDownSumJ_sound _ _ _ _ h
  refine ⟨N, q, rs', h, ?_, h2, h3, hlen, fun t' ht' => ?_, hN⟩
  · rw [← tsum_nonzero ts, ← h1, tval_zero, Rat.zero_add]
  · obtain ⟨t, ht, h4, h5⟩ := hsub t' ht'
    exact ⟨t, (mem_nonzero.mp ht).1, h4, h5⟩

/-! ## The sign and the round to nearest even of a sum -/

/-- **The sign of a sum of terms**, from windows of `W` bits, with the jumping descent. -/
def signSumJ (W : ℕ) (ts : List (ℤ × ℤ)) : ℤ :=
  match topDownSumAllJ W (bitlen (nonzero ts).length) ts with
  | some (N, _, _) => N.sign
  | none => 0

/-- **The sign oracle is exact** for windows wider than `bitlen n`. -/
theorem signSumJ_eq {W : ℕ} {ts : List (ℤ × ℤ)} (hW : bitlen ts.length < W) :
    signSumJ W ts = sgnQ (tsum ts) := by
  have hbl : bitlen (nonzero ts).length ≤ bitlen ts.length :=
    bitlen_le_iff.mpr (Nat.lt_of_le_of_lt (length_nonzero ts) (lt_two_pow_bitlen _))
  obtain ⟨N, q, rs', h, hval, htop, hstop, hlen, _⟩ :=
    topDownSumAllJ_spec (W := W) (T := bitlen (nonzero ts).length) (by omega) ts
  unfold signSumJ
  rw [h]
  simp only
  rw [hval]
  rcases hstop with h0 | hT
  · subst h0
    rw [tsum_nil, Rat.add_zero, sgnQ_mul_two_pow, sgnQ_intCast]
  · obtain ⟨h1, h2⟩ := abs_tsum_lt_of_bitlen (fun t ht => (htop t ht).2) hlen (Nat.le_refl _) hT
    rw [sgnQ_add_of_abs_lt (lt_le_trans' h1 h2), sgnQ_mul_two_pow, sgnQ_intCast]

/-- **Round to nearest even of a sum of terms** with bounded registers and the jumping descent. One descent with
threshold `2^(bitlen n + p + 3)`; if nothing is left over, round `N 2^q` exactly; if the sum is below
half the smallest subnormal, return `0`; otherwise answer the comparisons of `roundByCmp` with the
sign oracle on the residuals and one query term, refusing any query outside the ranges proved to
suffice (so every query term is below `2^(bitlen |N| + p + 6)`). -/
def roundSumJ (p : ℕ) (emin emax : ℤ) (W : ℕ) (ts : List (ℤ × ℤ)) : Option ℚ :=
  match topDownSumAllJ W (bitlen (nonzero ts).length + p + 3) ts with
  | none => none
  | some (N, q, rs') =>
    if rs' = [] then roundExact p emin emax N q
    else
      let B := bitlen N.natAbs
      let eH := q + B - 1
      if eH + 2 ≤ emin - p then some 0
      else
        let s := N.sign
        finishRNE p emax s (roundByCmp p emin
          (fun K h => if 0 ≤ K ∧ K < 2 ^ (p + 4) ∧ q ≤ h ∧ h ≤ q + B + 1 then
              s * signSumJ W (queryTerm N q s K h :: rs') else 0)
          eH (shiftFloor N.natAbs q))

/-- **The bounded rounding of a sum is round to nearest even**, for windows of
`W > bitlen (n + 1) + p + 3` bits, whatever the exponents. -/
theorem roundSumJ_eq {p : ℕ} (emin emax : ℤ) {W : ℕ} {ts : List (ℤ × ℤ)}
    (hW : bitlen (ts.length + 1) + p + 3 < W) :
    roundSumJ p emin emax W ts = roundRNE p emin emax (tsum ts) := by
  have hmono : ∀ {a b : ℕ}, a ≤ b → bitlen a ≤ bitlen b := bitlen_mono
  have hbl : bitlen (nonzero ts).length ≤ bitlen (ts.length + 1) :=
    hmono (Nat.le_trans (length_nonzero ts) (Nat.le_succ _))
  obtain ⟨N, q, rs', h, hval, htop, hstop, hlen, _⟩ :=
    topDownSumAllJ_spec (W := W) (T := bitlen (nonzero ts).length + p + 3) (by omega) ts
  unfold roundSumJ
  rw [h]
  simp only
  by_cases h0 : rs' = []
  · subst h0
    rw [if_pos rfl, roundExact_eq, hval, tsum_nil, Rat.add_zero]
  rw [if_neg h0]
  have hT := hstop.resolve_left h0
  generalize hBdef : bitlen N.natAbs = B at hT
  have hNA : N.natAbs ≠ 0 := by intro h; rw [h] at hBdef; simp [bitlen] at hBdef; omega
  have hN0 : N ≠ 0 := by omega
  generalize hx : tsum rs' = x at hval
  generalize hS : tsum ts = S at hval
  -- the residuals are far below `N 2^q`
  obtain ⟨hx1, hx2⟩ := abs_tsum_lt_of_bitlen (N := N) (q := q) (T := bitlen (nonzero ts).length)
    (fun t ht => (htop t ht).2) hlen (Nat.le_refl _) (by omega)
  rw [hx] at hx1
  have hpq := two_pow_pos q
  have hY : Rat.abs ((N : ℚ) * 2 ^ q) = ((N.natAbs : ℕ) : ℚ) * 2 ^ q := by
    rw [abs_mul_two_pow, abs_intCast]
  generalize hYdef : ((N.natAbs : ℕ) : ℚ) * 2 ^ q = Y at hY
  have hYlo : (2 : ℚ) ^ (q + B - 1) ≤ Y := by
    rw [← hYdef]
    have := Rat.mul_le_mul_of_nonneg_right (two_pow_bitlen_le_natCast hNA) (Rat.le_of_lt hpq)
    refine Rat.le_trans ?_ this
    rw [← two_pow_add, hBdef]; exact two_pow_le (by omega)
  have hYhi : Y < 2 ^ (q + B) := by
    rw [← hYdef, ← hBdef, Int.add_comm q]
    have := natCast_mul_two_pow_lt N.natAbs q
    rw [Int.add_comm q] at this; exact this
  generalize heH : q + B - 1 = eH
  have hxs : Rat.abs x < 2 ^ (eH - p - 3) :=
    lt_le_trans' hx1 (two_pow_le (by omega))
  -- the sign and the magnitude of the sum
  have hsgnS : sgnQ S = N.sign := by
    rw [hval, sgnQ_add_of_abs_lt (lt_le_trans' hx1 hx2), sgnQ_mul_two_pow, sgnQ_intCast]
  have hSabs1 : Rat.abs S ≤ Y + Rat.abs x := by
    rw [hval, ← hY]; exact abs_add_le _ _
  have hSabs2 : Y ≤ Rat.abs S + Rat.abs x := by
    rw [← hY, show (N : ℚ) * 2 ^ q = S + -x by rw [hval]; grind, ← abs_neg x]
    exact abs_add_le _ _
  have hp1 : (2 : ℚ) ^ (eH - p - 3) ≤ 2 ^ (eH - 1) := two_pow_le (by omega)
  have hE2' : (2 : ℚ) ^ (eH + 2) = 2 ^ (eH + 1) * 2 := by
    rw [show eH + 2 = (eH + 1) + 1 by omega]; exact two_pow_succ _
  have hE1' : (2 : ℚ) ^ eH = 2 ^ (eH - 1) * 2 := by
    rw [← two_pow_succ]; congr 1; omega
  have hYlo' : (2 : ℚ) ^ eH ≤ Y := by rw [← heH]; exact hYlo
  have hYhi' : Y < 2 ^ (eH + 1) := by rw [← heH]; rw [show q + B - 1 + 1 = q + B by omega]; exact hYhi
  have ha : 0 < Rat.abs S := by have := two_pow_pos (eH - 1); grind
  have hE1 : (2 : ℚ) ^ (eH - 1) ≤ Rat.abs S := by grind
  have hE2 : Rat.abs S < 2 ^ (eH + 2) := by
    have : (2 : ℚ) ^ (eH - p - 3) ≤ 2 ^ (eH + 1) := two_pow_le (by omega)
    grind
  have hsS : (N.sign : ℚ) * S = Rat.abs S := by
    rcases Int.lt_or_gt_of_ne hN0 with hn | hn
    · rw [Int.sign_eq_neg_one_of_neg hn] at hsgnS ⊢
      rw [abs_of_neg (neg_of_sgnQ hsgnS)]; grind
    · rw [Int.sign_eq_one_of_pos hn] at hsgnS ⊢
      rw [abs_of_nonneg (Rat.le_of_lt (pos_of_sgnQ hsgnS))]; grind
  have hsgn : ((N.sign : ℤ) : ℚ) = if S < 0 then -1 else 1 := by
    rcases Int.lt_or_gt_of_ne hN0 with hn | hn
    · rw [Int.sign_eq_neg_one_of_neg hn] at hsgnS ⊢
      rw [if_pos (neg_of_sgnQ hsgnS)]; rfl
    · rw [Int.sign_eq_one_of_pos hn] at hsgnS ⊢
      have := pos_of_sgnQ hsgnS
      rw [if_neg (by grind)]; rfl
  have hBq : (bitlen (nonzero ts).length : ℤ) + p + 4 ≤ B := by omega
  by_cases htiny : eH + 2 ≤ emin - p
  · rw [if_pos htiny]
    have hmag : rneMag p emin (Rat.abs S) = ((0 : ℤ) : ℚ) * 2 ^ (0 : ℤ) := by
      rw [rneMag_tiny ha (lt_le_trans' hE2 (two_pow_le htiny))]; simp
    rw [roundRNE_eq_finish hsgn hmag (Int.le_refl 0), finishRNE_zero]
  rw [if_neg htiny]
  obtain ⟨hmag, hM0⟩ := roundByCmp_spec (p := p) (emin := emin) ha
    (cmp := fun K h => if 0 ≤ K ∧ K < 2 ^ (p + 4) ∧ q ≤ h ∧ h ≤ q + B + 1 then
              N.sign * signSumJ W (queryTerm N q N.sign K h :: rs') else 0)
    (eH := eH)
    (fun K h ⟨hK0, hK, hL, hU⟩ => by
      have hqh : q ≤ h := by omega
      have hhU : h ≤ q + B + 1 := by
        have : gridOf p emin (eH + 1) ≤ eH + 2 := by unfold gridOf; omega
        omega
      rw [if_pos ⟨hK0, hK, hqh, hhU⟩]
      have hlen' : bitlen (rs'.length + 1) < W :=
        Nat.lt_of_le_of_lt (hmono (b := ts.length + 1) (by have := length_nonzero ts; omega)) (by omega)
      rw [signSumJ_eq (by simpa using hlen'), tsum_queryTerm _ _ _ _ _ _ hqh, hx, ← hval]
      rw [← hsS]
      rcases Int.lt_or_gt_of_ne hN0 with hn | hn
      · rw [Int.sign_eq_neg_one_of_neg hn]
        rw [show ((-1 : ℤ) : ℚ) * S - (K : ℚ) * 2 ^ h = -(S - ((-1 : ℤ) : ℚ) * K * 2 ^ h) by
          simp; grind, sgnQ_neg]
        omega
      · rw [Int.sign_eq_one_of_pos hn]
        rw [show ((1 : ℤ) : ℚ) * S - (K : ℚ) * 2 ^ h = S - ((1 : ℤ) : ℚ) * K * 2 ^ h by
          simp]
        omega)
    hE1 hE2 (FH := shiftFloor N.natAbs q)
    (fun g hg => by
      obtain ⟨h1, h2⟩ := shiftFloor_spec N.natAbs q g
      rw [hYdef] at h1 h2
      have hpg := two_pow_pos g
      have hxg : Rat.abs x < 2 ^ g := lt_le_trans' hxs (two_pow_le (by omega))
      constructor
      · have : ((shiftFloor N.natAbs q g : ℚ) - 1) * 2 ^ g =
            (shiftFloor N.natAbs q g : ℚ) * 2 ^ g - 2 ^ g := by grind
        rw [this]; grind
      · have : ((shiftFloor N.natAbs q g : ℚ) + 2) * 2 ^ g =
            ((shiftFloor N.natAbs q g : ℚ) + 1) * 2 ^ g + 2 ^ g := by grind
        rw [this]; grind)
  rw [roundRNE_eq_finish hsgn hmag hM0]

/-! ## Examples, checked by the kernel -/

example : signSumJ 8 cancelTerms = 1 := by decide +kernel

example : roundSumJ 24 (-126) 127 34 cancelTerms = roundRNE 24 (-126) 127 (tsum cancelTerms) := by
  decide +kernel

example : roundSumJ 24 (-126) 127 34 tieTerms = some 1 := by decide +kernel

/-- An exact cancellation `2^1000 − 2^1000` far above `3 · 2^-1000`: the window after the cancellation
jumps straight to the last term: `topDownSumJ` needs two windows, where `topDownSum` walks down the 2000 bits
in between `W` bits at a time. -/
def gapTerms : List (ℤ × ℤ) := [(1, 1000), (-1, 1000), (3, -1000)]

example : rangesJ 34 31 gapTerms = 2 := by decide +kernel

example : roundSumJ 24 (-126) 127 34 gapTerms = roundRNE 24 (-126) 127 (tsum gapTerms) ∧
    signSumJ 8 gapTerms = 1 := by decide +kernel

end Ozaki
