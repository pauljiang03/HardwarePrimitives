import Ozaki.Bounded

/-! # Correct rounding of a sum with bounded registers

A sum of terms `zᵢ 2^gᵢ` spread over a wide exponent range is exact in a register only as wide as
the range. This file rounds it correctly with registers whose width depends on the precision, the
number of terms and the range width `W`, never on the exponents; only the number of steps grows with
the exponent span.

* `topDownSum`: ranges from the top down. Each takes the `W` bits below the top of an accumulator
  `A 2^qa`, cuts every term at the grid `q` (exactly above, truncated toward zero below, `hiPart`,
  `loPart`), adds the parts above `q` in a register of `W + log₂ n + 1` bits, and keeps the parts
  below as residual terms on their own grids, never larger than the original. It stops when nothing
  is left over or the register sum `N` reaches `2^T`; otherwise `N 2^q` becomes the accumulator (a
  heavy cancellation) and the next range starts below it. Every term it returns satisfies
  `x = N 2^q + Σ residuals` with each residual below `2^q` (`topDownSum_sound`), and it ends within
  `qa − m` steps for terms on the grid `2^m` (`topDownSum_spec`): at most `E − m` steps for terms on
  the grid `2^m` below `2^E` (`topDownSumAll_fuel_le`);
* `signSum`: the sign of the sum (`signSum_eq`);
* `roundSum`: the round to nearest even (`roundSum_eq`). If nothing is left over it rounds `N 2^q`
  with integer operations (`roundExact`); otherwise `N` has `p + 4` bits more than the residuals
  can move, and the five comparisons of `roundByCmp` are asked of the sign oracle, each on the
  residuals and one more term `N − K 2^(h−q)` at the grid `q`, whose width is checked by the code
  itself.

Register widths (`topDownSum_parts_lt`, `fixedSum_natAbs_le`, `topDownSumAll_spec`,
`query_natAbs_lt`): parts in the current range below `2^W` (checked by `topDownSum`, which refuses
otherwise and provably never does), register sums at most `2^(W + bitlen (n + 1))`, residuals no
larger than an input coefficient or a query term, comparison multipliers below `2^(p+4)` and query
terms below `2^(bitlen |N| + p + 6)` (guarded in `roundSum`). Exponents and the step count are the
only quantities that grow with the exponent range. -/

local notation "ℕ" => Nat
local notation "ℤ" => Int
local notation "ℚ" => Rat

namespace Ozaki

/-! ## Terms -/

/-- The value `z · 2^g` of a term `(z, g)`. -/
def tval (t : ℤ × ℤ) : ℚ := (t.1 : ℚ) * 2 ^ t.2

/-- The value of a list of terms. -/
def tsum (ts : List (ℤ × ℤ)) : ℚ := (ts.map tval).sum

/-- The top bit position of a term: `|z 2^g| < 2^(g + bitlen |z|)`. -/
def topOf (t : ℤ × ℤ) : ℤ := t.2 + bitlen t.1.natAbs

theorem tsum_nil : tsum [] = 0 := rfl

theorem tsum_cons (t : ℤ × ℤ) (ts : List (ℤ × ℤ)) : tsum (t :: ts) = tval t + tsum ts := by
  simp only [tsum, List.map_cons, List.sum_cons]

theorem abs_tval (t : ℤ × ℤ) : Rat.abs (tval t) = ((t.1.natAbs : ℕ) : ℚ) * 2 ^ t.2 := by
  unfold tval; rw [abs_mul_two_pow, abs_intCast]

theorem abs_tval_lt (t : ℤ × ℤ) : Rat.abs (tval t) < 2 ^ topOf t := by
  rw [abs_tval]; exact natCast_mul_two_pow_lt _ _

theorem tval_zero (g : ℤ) : tval (0, g) = 0 := by unfold tval; simp

theorem tval_of_fst_eq_zero {t : ℤ × ℤ} (h : t.1 = 0) : tval t = 0 := by
  obtain ⟨z, g⟩ := t; simp only at h; subst h; exact tval_zero g

/-- Drop the terms with coefficient zero. -/
def nonzero (ts : List (ℤ × ℤ)) : List (ℤ × ℤ) := ts.filter fun t => t.1 != 0

theorem mem_nonzero {t : ℤ × ℤ} {ts : List (ℤ × ℤ)} : t ∈ nonzero ts ↔ t ∈ ts ∧ t.1 ≠ 0 := by
  simp [nonzero, List.mem_filter]

theorem length_nonzero (ts : List (ℤ × ℤ)) : (nonzero ts).length ≤ ts.length :=
  List.length_filter_le _ _

theorem tsum_nonzero (ts : List (ℤ × ℤ)) : tsum (nonzero ts) = tsum ts := by
  induction ts with
  | nil => rfl
  | cons t ts ih =>
    unfold nonzero at ih ⊢
    rw [List.filter_cons]
    by_cases h : t.1 = 0
    · have : (t.1 != 0) = false := by simp [h]
      rw [if_neg (by simp [this]), ih, tsum_cons, tval_of_fst_eq_zero h, Rat.zero_add]
    · have : (t.1 != 0) = true := by simp [h]
      rw [if_pos this, tsum_cons, tsum_cons, ih]

theorem abs_tsum_le {q : ℤ} {ts : List (ℤ × ℤ)} (h : ∀ t ∈ ts, topOf t ≤ q) :
    Rat.abs (tsum ts) ≤ ts.length * 2 ^ q := by
  unfold tsum
  refine Rat.le_trans (abs_sum_le _ _) (sum_le_length_mul fun t ht => ?_)
  exact Rat.le_of_lt (lt_le_trans' (abs_tval_lt t) (two_pow_le (h t ht)))

/-! ## Cutting a term at a grid -/

/-- `⌊|z| / 2^d⌋` with the sign of `z`: the magnitude shifted right by `d`. -/
def tdivPow (z : ℤ) (d : ℕ) : ℤ :=
  if z < 0 then -((z.natAbs >>> d : ℕ) : ℤ) else ((z.natAbs >>> d : ℕ) : ℤ)

/-- `|z| mod 2^d` with the sign of `z`: the low `d` bits of the magnitude. -/
def tmodPow (z : ℤ) (d : ℕ) : ℤ :=
  if z < 0 then -((z.natAbs % 2 ^ d : ℕ) : ℤ) else ((z.natAbs % 2 ^ d : ℕ) : ℤ)

theorem tdivPow_add_tmodPow (z : ℤ) (d : ℕ) : tdivPow z d * 2 ^ d + tmodPow z d = z := by
  have h := Nat.div_add_mod z.natAbs (2 ^ d)
  rw [← Nat.shiftRight_eq_div_pow] at h
  have h' : ((2 ^ d : ℕ) : ℤ) * ((z.natAbs >>> d : ℕ) : ℤ) + ((z.natAbs % 2 ^ d : ℕ) : ℤ) =
      (z.natAbs : ℤ) := by exact_mod_cast h
  have hc : ((2 ^ d : ℕ) : ℤ) = (2 : ℤ) ^ d := by rw [Int.natCast_pow]; rfl
  rw [hc, Int.mul_comm] at h'
  unfold tdivPow tmodPow
  generalize ((z.natAbs >>> d : ℕ) : ℤ) = X at h' ⊢
  generalize ((z.natAbs % 2 ^ d : ℕ) : ℤ) = Y at h' ⊢
  split
  · rw [Int.neg_mul]
    generalize X * 2 ^ d = P at h' ⊢
    omega
  · generalize X * 2 ^ d = P at h' ⊢
    omega

theorem natAbs_tmodPow (z : ℤ) (d : ℕ) : (tmodPow z d).natAbs = z.natAbs % 2 ^ d := by
  unfold tmodPow; split <;> simp only [Int.natAbs_neg, Int.natAbs_natCast]

theorem natAbs_tdivPow (z : ℤ) (d : ℕ) : (tdivPow z d).natAbs = z.natAbs / 2 ^ d := by
  unfold tdivPow; rw [Nat.shiftRight_eq_div_pow]; split <;> simp only [Int.natAbs_neg, Int.natAbs_natCast]

/-- The part of a term on the grid `2^q`, in units of `2^q`: exact when `q ≤ g` (a left shift),
truncated toward zero otherwise (a right shift of the magnitude). -/
def hiPart (q : ℤ) (t : ℤ × ℤ) : ℤ :=
  if q ≤ t.2 then t.1 * 2 ^ (t.2 - q).toNat else tdivPow t.1 (q - t.2).toNat

/-- What `hiPart` leaves: a term on the same grid, below `2^q`, no larger than the original. -/
def loPart (q : ℤ) (t : ℤ × ℤ) : ℤ × ℤ :=
  (if q ≤ t.2 then 0 else tmodPow t.1 (q - t.2).toNat, t.2)

theorem intCast_two_pow (n : ℕ) : (((2 : ℤ) ^ n : ℤ) : ℚ) = (2 : ℚ) ^ (n : ℤ) := by
  rw [Rat.intCast_pow, Rat.zpow_natCast]; rfl

theorem tval_split (q : ℤ) (t : ℤ × ℤ) :
    tval t = (hiPart q t : ℚ) * 2 ^ q + tval (loPart q t) := by
  obtain ⟨z, g⟩ := t
  unfold hiPart loPart
  simp only
  split
  · rename_i h
    rw [tval_zero, Rat.add_zero, Rat.intCast_mul, intCast_two_pow, Rat.mul_assoc, ← two_pow_add]
    unfold tval; simp only
    congr 2; omega
  · rename_i h
    generalize hd : (q - g).toNat = d
    have hq : q = g + d := by omega
    have hz := tdivPow_add_tmodPow z d
    unfold tval; simp only
    have hz' : (z : ℚ) = (tdivPow z d : ℚ) * 2 ^ (d : ℤ) + (tmodPow z d : ℚ) := by
      rw [← intCast_two_pow, ← Rat.intCast_mul, ← Rat.intCast_add, hz]
    rw [hz', hq, two_pow_add]
    grind

theorem natAbs_hiPart_lt {q : ℤ} {W : ℕ} {t : ℤ × ℤ} (h : topOf t ≤ q + W) :
    (hiPart q t).natAbs < 2 ^ W := by
  obtain ⟨z, g⟩ := t
  unfold topOf at h; simp only at h
  have hz := lt_two_pow_bitlen z.natAbs
  unfold hiPart; simp only
  split
  · rename_i hle
    rw [Int.natAbs_mul, Int.natAbs_pow]
    show z.natAbs * 2 ^ (g - q).toNat < 2 ^ W
    calc z.natAbs * 2 ^ (g - q).toNat < 2 ^ bitlen z.natAbs * 2 ^ (g - q).toNat :=
          Nat.mul_lt_mul_of_pos_right hz (Nat.two_pow_pos _)
      _ = 2 ^ (bitlen z.natAbs + (g - q).toNat) := (Nat.pow_add _ _ _).symm
      _ ≤ 2 ^ W := Nat.pow_le_pow_right (by decide) (by omega)
  · rename_i hlt
    rw [natAbs_tdivPow, Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _), ← Nat.pow_add]
    exact Nat.lt_of_lt_of_le hz (Nat.pow_le_pow_right (by decide) (by omega))

theorem loPart_snd (q : ℤ) (t : ℤ × ℤ) : (loPart q t).2 = t.2 := rfl

theorem loPart_fst_of_le {q : ℤ} {t : ℤ × ℤ} (h : q ≤ t.2) : (loPart q t).1 = 0 := by
  unfold loPart; simp only; rw [if_pos h]

theorem natAbs_loPart_le (q : ℤ) (t : ℤ × ℤ) : (loPart q t).1.natAbs ≤ t.1.natAbs := by
  unfold loPart; simp only
  split
  · simp
  · rw [natAbs_tmodPow]; exact Nat.mod_le _ _

theorem loPart_top {q : ℤ} {t : ℤ × ℤ} (h : (loPart q t).1 ≠ 0) :
    topOf (loPart q t) ≤ q ∧ t.2 < q := by
  obtain ⟨z, g⟩ := t
  unfold loPart at h ⊢; simp only at h ⊢
  split at h
  · exact absurd rfl h
  · rename_i hlt
    rw [if_neg hlt]
    unfold topOf; simp only
    have := Nat.mod_lt z.natAbs (Nat.two_pow_pos (q - g).toNat)
    rw [← natAbs_tmodPow] at this
    have hb := bitlen_le_iff.mpr this
    omega

/-! ## One range -/

/-- The residual terms after the range at grid `q`. -/
def rangeRest (q : ℤ) (ts : List (ℤ × ℤ)) : List (ℤ × ℤ) := nonzero (ts.map (loPart q))

theorem tsum_range (q : ℤ) (ts : List (ℤ × ℤ)) :
    tsum ts = (((ts.map (hiPart q)).sum : ℤ) : ℚ) * 2 ^ q + tsum (rangeRest q ts) := by
  unfold rangeRest
  rw [tsum_nonzero]
  induction ts with
  | nil => simp [tsum]; exact (Rat.add_zero 0).symm
  | cons t ts ih =>
    rw [List.map_cons, List.map_cons, List.sum_cons, tsum_cons, tsum_cons, ih, tval_split q t,
      Rat.intCast_add]
    grind

theorem mem_rangeRest {q : ℤ} {ts : List (ℤ × ℤ)} {t' : ℤ × ℤ} (h : t' ∈ rangeRest q ts) :
    t'.1 ≠ 0 ∧ topOf t' ≤ q ∧
      ∃ t ∈ ts, t'.2 = t.2 ∧ t'.1.natAbs ≤ t.1.natAbs ∧ t.2 < q := by
  obtain ⟨hm, hne⟩ := mem_nonzero.mp h
  obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hm
  obtain ⟨htop, hlt⟩ := loPart_top hne
  exact ⟨hne, htop, t, ht, rfl, natAbs_loPart_le q t, hlt⟩

theorem rangeRest_cons_of_le {q A qa : ℤ} {rs : List (ℤ × ℤ)} (h : q ≤ qa) :
    rangeRest q ((A, qa) :: rs) = rangeRest q rs := by
  unfold rangeRest nonzero
  rw [List.map_cons, List.filter_cons]
  have h0 : (loPart q (A, qa)).1 = 0 := loPart_fst_of_le h
  rw [if_neg (by simp [h0])]

theorem length_rangeRest (q : ℤ) (ts : List (ℤ × ℤ)) : (rangeRest q ts).length ≤ ts.length := by
  unfold rangeRest
  exact Nat.le_trans (length_nonzero _) (by simp)

/-- Magnitudes below `B` add up to at most `length · B`. -/
theorem sum_natAbs_le {B : ℕ} : ∀ {ps : List ℤ}, (∀ z ∈ ps, z.natAbs < B) →
    (ps.map Int.natAbs).sum ≤ ps.length * B
  | [], _ => by simp
  | z :: ps, h => by
    have h1 := h z List.mem_cons_self
    have h2 := sum_natAbs_le (ps := ps) (fun w hw => h w (List.mem_cons_of_mem _ hw))
    simp only [List.map_cons, List.sum_cons, List.length_cons, Nat.succ_mul]
    omega

/-- **The register.** Parts below `2^W` add up exactly in `W + bitlen n + 1` bits. -/
theorem register_fixedSum {W : ℕ} {ps : List ℤ} (h : ∀ z ∈ ps, z.natAbs < 2 ^ W) :
    fixedSum (W + bitlen ps.length + 1) ps = ps.sum := by
  apply fixedSum_eq (by omega)
  rw [show W + bitlen ps.length + 1 - 1 = bitlen ps.length + W by omega, Nat.pow_add]
  exact Nat.lt_of_le_of_lt (sum_natAbs_le h)
    (Nat.mul_lt_mul_of_pos_right (lt_two_pow_bitlen _) (Nat.two_pow_pos _))

/-- A wrapped register holds at most `2^(w−1)` in magnitude. -/
theorem wrap_natAbs_le {w : ℕ} (hw : 0 < w) (x : ℤ) : (wrap w x).natAbs ≤ 2 ^ (w - 1) := by
  unfold wrap
  obtain ⟨v, rfl⟩ : ∃ v, w = v + 1 := ⟨w - 1, by omega⟩
  simp only [Nat.add_sub_cancel]
  have hP : (2 : ℤ) ^ (v + 1) = 2 ^ v * 2 := Int.pow_succ 2 v
  have hc : ((2 ^ v : ℕ) : ℤ) = (2 : ℤ) ^ v := by rw [Int.natCast_pow]; rfl
  have hpos : (0 : ℤ) < 2 ^ v := by have := Nat.two_pow_pos v; omega
  rw [hP]
  have h1 := Int.emod_nonneg (x + 2 ^ v) (b := 2 ^ v * 2) (by omega)
  have h2 := Int.emod_lt_of_pos (x + 2 ^ v) (b := 2 ^ v * 2) (by omega)
  generalize (x + 2 ^ v) % (2 ^ v * 2) = r at h1 h2 ⊢
  generalize (2 : ℤ) ^ v = P at hc hpos h1 h2 ⊢
  generalize 2 ^ v = Q at hc ⊢
  omega

theorem fixedSum_natAbs_le {w : ℕ} (hw : 0 < w) (zs : List ℤ) :
    (fixedSum w zs).natAbs ≤ 2 ^ (w - 1) := by
  unfold fixedSum
  suffices ∀ acc, acc.natAbs ≤ 2 ^ (w - 1) → (fixedSumFrom w acc zs).natAbs ≤ 2 ^ (w - 1) from
    this 0 (by simp)
  induction zs with
  | nil => intro acc h; exact h
  | cons z zs ih => intro acc _; exact ih _ (wrap_natAbs_le hw _)

/-! ## Ranges from the top down -/

/-- **Ranges from the top down.** The state is an accumulator `A 2^qa` and residual terms below
`2^qa`. The range takes the `W` bits below the accumulator's top: grid `q = qa + bitlen |A| − W`.
Every part above `q` must be a `W`-bit integer (checked); they are added in a register of
`W + bitlen n + 1` bits. Stops with `(N, q, residuals)` when nothing is left over or `|N| ≥ 2^T`;
otherwise continues with `N 2^q` as the accumulator, at most `fuel` more times. -/
def topDownSum (W T : ℕ) : ℕ → ℤ → ℤ → List (ℤ × ℤ) → Option (ℤ × ℤ × List (ℤ × ℤ))
  | fuel, A, qa, rs =>
    let ts := (A, qa) :: rs
    let q := topOf (A, qa) - W
    let parts := ts.map (hiPart q)
    let N := fixedSum (W + bitlen parts.length + 1) parts
    let rs' := rangeRest q ts
    if parts.all (fun z => decide (z.natAbs < 2 ^ W)) then
      if rs' = [] ∨ T < bitlen N.natAbs then some (N, q, rs')
      else match fuel with
        | 0 => none
        | k + 1 => topDownSum W T k N q rs'
    else none

/-- **What `topDownSum` returns is exact**: `A 2^qa + Σ residuals = N 2^q + Σ new residuals`, every new
residual is nonzero and below `2^q`, and it stopped because nothing was left over or `|N| ≥ 2^T`. -/
theorem topDownSum_sound {W T : ℕ} : ∀ (fuel : ℕ) (A qa : ℤ) (rs : List (ℤ × ℤ)) {N q : ℤ}
    {rs' : List (ℤ × ℤ)}, topDownSum W T fuel A qa rs = some (N, q, rs') →
    tval (A, qa) + tsum rs = (N : ℚ) * 2 ^ q + tsum rs' ∧
      (∀ t ∈ rs', t.1 ≠ 0 ∧ topOf t ≤ q) ∧ (rs' = [] ∨ T < bitlen N.natAbs) := by
  intro fuel
  induction fuel with
  | zero =>
    intro A qa rs N q rs' h
    unfold topDownSum at h
    simp only at h
    split at h
    · rename_i hall
      have hsum := register_fixedSum (W := W)
        (ps := ((A, qa) :: rs).map (hiPart (topOf (A, qa) - W)))
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
    unfold topDownSum at h
    simp only at h
    split at h
    · rename_i hall
      have hsum := register_fixedSum (W := W)
        (ps := ((A, qa) :: rs).map (hiPart (topOf (A, qa) - W)))
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
        rw [← h1, ← tsum_cons, tsum_range (topOf (A, qa) - W), hsum]
        unfold tval; rfl
    · simp at h

/-- **`topDownSum` ends**, on terms on the grid `2^m` below `2^qa`, within `qa − m` steps, with no more
residuals than it started with, each on the grid of an original term and no larger. -/
theorem topDownSum_spec {W T : ℕ} (hTW : T < W) {m : ℤ} : ∀ (fuel : ℕ) (A qa : ℤ)
    (rs : List (ℤ × ℤ)), bitlen A.natAbs ≤ T → (∀ t ∈ rs, t.1 ≠ 0 ∧ topOf t ≤ qa ∧ m ≤ t.2) →
    qa - m ≤ fuel → ∃ N q rs', topDownSum W T fuel A qa rs = some (N, q, rs') ∧
      rs'.length ≤ rs.length ∧
      (∀ t' ∈ rs', ∃ t ∈ rs, t'.2 = t.2 ∧ t'.1.natAbs ≤ t.1.natAbs) ∧
      N.natAbs ≤ 2 ^ (W + bitlen (rs.length + 1)) := by
  intro fuel
  induction fuel with
  | zero =>
    intro A qa rs hA hrs hfuel
    have hq : topOf (A, qa) - W ≤ qa - 1 := by
      show qa + (bitlen A.natAbs : ℤ) - W ≤ qa - 1; omega
    have hall : (((A, qa) :: rs).map (hiPart (topOf (A, qa) - W))).all
        (fun z => decide (z.natAbs < 2 ^ W)) = true := by
      apply List.all_eq_true.mpr
      intro z hz
      obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hz
      apply decide_eq_true
      apply natAbs_hiPart_lt
      have hqa : qa ≤ topOf (A, qa) := by show qa ≤ qa + (bitlen A.natAbs : ℤ); omega
      rcases List.mem_cons.mp ht with rfl | ht
      · omega
      · have := (hrs t ht).2.1; omega
    unfold topDownSum
    simp only
    rw [if_pos hall, rangeRest_cons_of_le (by omega)]
    split
    · refine ⟨_, _, _, rfl, length_rangeRest _ _, fun t' ht' => ?_, ?_⟩
      · obtain ⟨_, _, t, ht, h1, h2, _⟩ := mem_rangeRest ht'
        exact ⟨t, ht, h1, h2⟩
      · refine Nat.le_trans (fixedSum_natAbs_le (by omega) _) (Nat.le_of_eq ?_)
        simp only [List.length_map, List.length_cons]
        congr 1
    · rename_i hstop
      exfalso
      obtain ⟨t', ht'⟩ := List.exists_mem_of_ne_nil _ (fun h => hstop (Or.inl h))
      obtain ⟨hne, htop, t, ht, h1, _, _⟩ := mem_rangeRest ht'
      have := (hrs t ht).2.2
      have hb := bitlen_pos (n := t'.1.natAbs) (by omega)
      generalize topOf (A, qa) - W = q at htop hq
      unfold topOf at htop
      omega
  | succ k ih =>
    intro A qa rs hA hrs hfuel
    have hq : topOf (A, qa) - W ≤ qa - 1 := by
      show qa + (bitlen A.natAbs : ℤ) - W ≤ qa - 1; omega
    have hall : (((A, qa) :: rs).map (hiPart (topOf (A, qa) - W))).all
        (fun z => decide (z.natAbs < 2 ^ W)) = true := by
      apply List.all_eq_true.mpr
      intro z hz
      obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hz
      apply decide_eq_true
      apply natAbs_hiPart_lt
      have hqa : qa ≤ topOf (A, qa) := by show qa ≤ qa + (bitlen A.natAbs : ℤ); omega
      rcases List.mem_cons.mp ht with rfl | ht
      · omega
      · have := (hrs t ht).2.1; omega
    unfold topDownSum
    simp only
    rw [if_pos hall, rangeRest_cons_of_le (by omega)]
    split
    · refine ⟨_, _, _, rfl, length_rangeRest _ _, fun t' ht' => ?_, ?_⟩
      · obtain ⟨_, _, t, ht, h1, h2, _⟩ := mem_rangeRest ht'
        exact ⟨t, ht, h1, h2⟩
      · refine Nat.le_trans (fixedSum_natAbs_le (by omega) _) (Nat.le_of_eq ?_)
        simp only [List.length_map, List.length_cons]
        congr 1
    · rename_i hstop
      have hN := Nat.le_of_not_lt (fun h => hstop (Or.inr h))
      have hrs' : ∀ t' ∈ rangeRest (topOf (A, qa) - W) rs,
          t'.1 ≠ 0 ∧ topOf t' ≤ topOf (A, qa) - W ∧ m ≤ t'.2 := fun t' ht' => by
        obtain ⟨hne, htop, t, ht, h1, _, _⟩ := mem_rangeRest ht'
        exact ⟨hne, htop, by rw [h1]; exact (hrs t ht).2.2⟩
      have hstep : topOf (A, qa) - W - m ≤ k := by
        obtain ⟨t', ht'⟩ := List.exists_mem_of_ne_nil _ (fun h => hstop (Or.inl h))
        obtain ⟨hne, htop, t, ht, h1, _, _⟩ := mem_rangeRest ht'
        have := (hrs t ht).2.2
        have hb := bitlen_pos (n := t'.1.natAbs) (by omega)
        generalize topOf (A, qa) - W = q at htop hq ⊢
        unfold topOf at htop
        omega
      obtain ⟨N', q', rs'', h, hlen, hsub, hN'⟩ := ih _ _ _ hN hrs' hstep
      refine ⟨N', q', rs'', h, Nat.le_trans hlen (length_rangeRest _ _), fun t'' ht'' => ?_, ?_⟩
      · obtain ⟨t', ht', h1, h2⟩ := hsub t'' ht''
        obtain ⟨_, _, t, ht, h3, h4, _⟩ := mem_rangeRest ht'
        exact ⟨t, ht, h1.trans h3, Nat.le_trans h2 h4⟩
      · refine Nat.le_trans hN' (Nat.pow_le_pow_right (by decide) ?_)
        have := bitlen_mono (Nat.add_le_add_right (length_rangeRest (topOf (A, qa) - W) rs) 1)
        omega

/-- **The parts in the current range are `W`-bit integers**: on every state `topDownSum` reaches
from terms below
`2^qa`, the parts are below `2^W` (so `topDownSum` never refuses). -/
theorem topDownSum_parts_lt {W : ℕ} {A qa : ℤ} {rs : List (ℤ × ℤ)}
    (hrs : ∀ t ∈ rs, topOf t ≤ qa) :
    ∀ z ∈ ((A, qa) :: rs).map (hiPart (topOf (A, qa) - W)), z.natAbs < 2 ^ W := by
  intro z hz
  obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hz
  apply natAbs_hiPart_lt
  rcases List.mem_cons.mp ht with rfl | ht
  · omega
  · have := hrs t ht; unfold topOf at this ⊢; simp only at this ⊢; omega

/-! ## The largest top and the smallest grid -/

def maxTopFrom (e : ℤ) : List (ℤ × ℤ) → ℤ
  | [] => e
  | t :: ts => maxTopFrom (max e (topOf t)) ts

/-- The largest top bit position of the terms. -/
def maxTop : List (ℤ × ℤ) → ℤ
  | [] => 0
  | t :: ts => maxTopFrom (topOf t) ts

def minGridFrom (e : ℤ) : List (ℤ × ℤ) → ℤ
  | [] => e
  | t :: ts => minGridFrom (min e t.2) ts

/-- The smallest grid of the terms. -/
def minGrid : List (ℤ × ℤ) → ℤ
  | [] => 0
  | t :: ts => minGridFrom t.2 ts

theorem maxTopFrom_spec : ∀ (ts : List (ℤ × ℤ)) (e : ℤ),
    e ≤ maxTopFrom e ts ∧ ∀ t ∈ ts, topOf t ≤ maxTopFrom e ts
  | [], e => ⟨Int.le_refl e, by simp⟩
  | t :: ts, e => by
    obtain ⟨h1, h2⟩ := maxTopFrom_spec ts (max e (topOf t))
    refine ⟨by unfold maxTopFrom; omega, fun u hu => ?_⟩
    unfold maxTopFrom
    rcases List.mem_cons.mp hu with rfl | hu
    · omega
    · exact h2 u hu

theorem le_maxTop {ts : List (ℤ × ℤ)} {t : ℤ × ℤ} (h : t ∈ ts) : topOf t ≤ maxTop ts := by
  cases ts with
  | nil => simp at h
  | cons u ts =>
    obtain ⟨h1, h2⟩ := maxTopFrom_spec ts (topOf u)
    unfold maxTop
    rcases List.mem_cons.mp h with rfl | h
    · exact h1
    · exact h2 t h

theorem minGridFrom_spec : ∀ (ts : List (ℤ × ℤ)) (e : ℤ),
    minGridFrom e ts ≤ e ∧ ∀ t ∈ ts, minGridFrom e ts ≤ t.2
  | [], e => ⟨Int.le_refl e, by simp⟩
  | t :: ts, e => by
    obtain ⟨h1, h2⟩ := minGridFrom_spec ts (min e t.2)
    refine ⟨by unfold minGridFrom; omega, fun u hu => ?_⟩
    unfold minGridFrom
    rcases List.mem_cons.mp hu with rfl | hu
    · omega
    · exact h2 u hu

theorem minGrid_le {ts : List (ℤ × ℤ)} {t : ℤ × ℤ} (h : t ∈ ts) : minGrid ts ≤ t.2 := by
  cases ts with
  | nil => simp at h
  | cons u ts =>
    obtain ⟨h1, h2⟩ := minGridFrom_spec ts u.2
    unfold minGrid
    rcases List.mem_cons.mp h with rfl | h
    · exact h1
    · exact h2 t h

theorem topOf_le_of_abs_lt {t : ℤ × ℤ} {E : ℤ} (ht : t.1 ≠ 0) (h : Rat.abs (tval t) < 2 ^ E) :
    topOf t ≤ E := by
  have h1 := two_pow_le_natCast_mul (A := t.1.natAbs) (by omega) t.2
  rw [← abs_tval] at h1
  have := two_pow_lt_iff.mp (le_lt_trans' h1 h)
  unfold topOf; omega

theorem maxTopFrom_le : ∀ (ts : List (ℤ × ℤ)) {e E : ℤ}, e ≤ E → (∀ t ∈ ts, topOf t ≤ E) →
    maxTopFrom e ts ≤ E
  | [], _, _, he, _ => he
  | t :: ts, _, _, he, h => maxTopFrom_le ts (Int.max_le.mpr ⟨he, h t List.mem_cons_self⟩)
      (fun u hu => h u (List.mem_cons_of_mem _ hu))

theorem le_minGridFrom : ∀ (ts : List (ℤ × ℤ)) {e m : ℤ}, m ≤ e → (∀ t ∈ ts, m ≤ t.2) →
    m ≤ minGridFrom e ts
  | [], _, _, he, _ => he
  | t :: ts, _, _, he, h => le_minGridFrom ts (Int.le_min.mpr ⟨he, h t List.mem_cons_self⟩)
      (fun u hu => h u (List.mem_cons_of_mem _ hu))

/-- **The number of ranges is bounded by the exponent span**: for terms on the grid `2^m` below
`2^E`, the fuel of `topDownSumAll` is at most `E − m`. -/
theorem topDownSumAll_fuel_le {ts : List (ℤ × ℤ)} {m E : ℤ}
    (h : ∀ t ∈ ts, m ≤ t.2 ∧ Rat.abs (tval t) < 2 ^ E) :
    (maxTop (nonzero ts) - minGrid (nonzero ts)).toNat ≤ (E - m).toNat := by
  have hn : ∀ t ∈ nonzero ts, m ≤ t.2 ∧ topOf t ≤ E := fun t ht =>
    ⟨(h t (mem_nonzero.mp ht).1).1,
      topOf_le_of_abs_lt (mem_nonzero.mp ht).2 (h t (mem_nonzero.mp ht).1).2⟩
  cases hz : nonzero ts with
  | nil => simp [maxTop, minGrid]
  | cons u us =>
    rw [hz] at hn
    have h1 := maxTopFrom_le us (hn u List.mem_cons_self).2
      (fun t ht => (hn t (List.mem_cons_of_mem _ ht)).2)
    have h2 := le_minGridFrom us (hn u List.mem_cons_self).1
      (fun t ht => (hn t (List.mem_cons_of_mem _ ht)).1)
    show (maxTopFrom (topOf u) us - minGridFrom u.2 us).toNat ≤ _
    omega

/-- `topDownSum` from the top of the nonzero terms, with fuel the exponent span. -/
def topDownSumAll (W T : ℕ) (ts : List (ℤ × ℤ)) : Option (ℤ × ℤ × List (ℤ × ℤ)) :=
  let rs := nonzero ts
  topDownSum W T (maxTop rs - minGrid rs).toNat 0 (maxTop rs) rs

theorem topDownSumAll_spec {W T : ℕ} (hTW : T < W) (ts : List (ℤ × ℤ)) :
    ∃ N q rs', topDownSumAll W T ts = some (N, q, rs') ∧
      tsum ts = (N : ℚ) * 2 ^ q + tsum rs' ∧ (∀ t ∈ rs', t.1 ≠ 0 ∧ topOf t ≤ q) ∧
      (rs' = [] ∨ T < bitlen N.natAbs) ∧ rs'.length ≤ (nonzero ts).length ∧
      (∀ t' ∈ rs', ∃ t ∈ ts, t'.2 = t.2 ∧ t'.1.natAbs ≤ t.1.natAbs) ∧
      N.natAbs ≤ 2 ^ (W + bitlen ((nonzero ts).length + 1)) := by
  obtain ⟨N, q, rs', h, hlen, hsub, hN⟩ := topDownSum_spec hTW (m := minGrid (nonzero ts))
    (maxTop (nonzero ts) - minGrid (nonzero ts)).toNat 0 (maxTop (nonzero ts)) (nonzero ts)
    (by simp [bitlen]) (fun t ht => ⟨(mem_nonzero.mp ht).2, le_maxTop ht, minGrid_le ht⟩)
    (by omega)
  obtain ⟨h1, h2, h3⟩ := topDownSum_sound _ _ _ _ h
  refine ⟨N, q, rs', h, ?_, h2, h3, hlen, fun t' ht' => ?_, hN⟩
  · rw [← tsum_nonzero ts, ← h1, tval_zero, Rat.zero_add]
  · obtain ⟨t, ht, h4, h5⟩ := hsub t' ht'
    exact ⟨t, (mem_nonzero.mp ht).1, h4, h5⟩

/-! ## The sign oracle -/

theorem sgnQ_intCast (N : ℤ) : sgnQ (N : ℚ) = N.sign := by
  unfold sgnQ
  by_cases h1 : N < 0
  · rw [if_pos (by exact_mod_cast h1), Int.sign_eq_neg_one_of_neg h1]
  · by_cases h2 : N = 0
    · subst h2; simp
    · have hp : 0 < N := by omega
      have : ((0 : ℤ) : ℚ) < (N : ℚ) := Rat.intCast_lt_intCast.mpr hp
      rw [if_neg (by simp at this; grind), if_neg (by simp at this; grind),
        Int.sign_eq_one_of_pos hp]

theorem sgnQ_add_of_abs_lt {x y : ℚ} (h : Rat.abs x < Rat.abs y) : sgnQ (y + x) = sgnQ y := by
  rw [abs_def, abs_def] at h
  apply sgnQ_eq_of_iff
  · constructor <;> intro <;> split at h <;> split at h <;> grind
  · constructor <;> intro <;> split at h <;> split at h <;> grind

theorem neg_of_sgnQ {x : ℚ} (h : sgnQ x = -1) : x < 0 := by
  unfold sgnQ at h
  by_cases h1 : x < 0
  · exact h1
  · rw [if_neg h1] at h; split at h <;> omega

theorem pos_of_sgnQ {x : ℚ} (h : sgnQ x = 1) : 0 < x := by
  unfold sgnQ at h
  by_cases h1 : x < 0
  · rw [if_pos h1] at h; omega
  · rw [if_neg h1] at h
    by_cases h2 : x = 0
    · rw [if_pos h2] at h; omega
    · grind

theorem sgnQ_neg (x : ℚ) : sgnQ (-x) = -sgnQ x := by
  unfold sgnQ
  by_cases h1 : x < 0
  · rw [if_neg (by grind), if_neg (by grind), if_pos h1]; rfl
  · by_cases h2 : x = 0
    · subst h2; simp
    · rw [if_pos (by grind), if_neg h1, if_neg h2]

/-- The register sum dominates: `|N| ≥ 2^T` and the residuals, at most `n` terms below `2^q`, are
smaller than `2^T 2^q` when `n < 2^T`. -/
theorem abs_tsum_lt_of_bitlen {N q : ℤ} {T : ℕ} {rs : List (ℤ × ℤ)} {n : ℕ}
    (hrs : ∀ t ∈ rs, topOf t ≤ q) (hlen : rs.length ≤ n) (hT : bitlen n ≤ T)
    (hN : T < bitlen N.natAbs) :
    Rat.abs (tsum rs) < 2 ^ (q + T) ∧ (2 : ℚ) ^ (q + T) ≤ Rat.abs ((N : ℚ) * 2 ^ q) := by
  have hpq := two_pow_pos q
  constructor
  · refine le_lt_trans' (abs_tsum_le hrs) ?_
    have h1 : (rs.length : ℚ) < 2 ^ ((bitlen n : ℕ) : ℤ) :=
      le_lt_trans' (by exact_mod_cast hlen) (natCast_lt_two_pow_bitlen n)
    have h2 := Rat.mul_lt_mul_of_pos_right h1 hpq
    refine lt_le_trans' h2 ?_
    rw [← two_pow_add, Int.add_comm]
    exact two_pow_le (by omega)
  · rw [abs_mul_two_pow, abs_intCast]
    have hA : N.natAbs ≠ 0 := by intro h; rw [h] at hN; simp [bitlen] at hN
    have := Rat.mul_le_mul_of_nonneg_right (two_pow_bitlen_le_natCast hA) (Rat.le_of_lt hpq)
    refine Rat.le_trans ?_ this
    rw [← two_pow_add]
    exact two_pow_le (by omega)

/-- **The sign of a sum of terms**, from ranges of `W` bits. -/
def signSum (W : ℕ) (ts : List (ℤ × ℤ)) : ℤ :=
  match topDownSumAll W (bitlen (nonzero ts).length) ts with
  | some (N, _, _) => N.sign
  | none => 0

/-- **The sign oracle is exact** for ranges wider than `bitlen n`. -/
theorem signSum_eq {W : ℕ} {ts : List (ℤ × ℤ)} (hW : bitlen ts.length < W) :
    signSum W ts = sgnQ (tsum ts) := by
  have hbl : bitlen (nonzero ts).length ≤ bitlen ts.length :=
    bitlen_le_iff.mpr (Nat.lt_of_le_of_lt (length_nonzero ts) (lt_two_pow_bitlen _))
  obtain ⟨N, q, rs', h, hval, htop, hstop, hlen, _⟩ :=
    topDownSumAll_spec (W := W) (T := bitlen (nonzero ts).length) (by omega) ts
  unfold signSum
  rw [h]
  simp only
  rw [hval]
  rcases hstop with h0 | hT
  · subst h0
    rw [tsum_nil, Rat.add_zero, sgnQ_mul_two_pow, sgnQ_intCast]
  · obtain ⟨h1, h2⟩ := abs_tsum_lt_of_bitlen (fun t ht => (htop t ht).2) hlen (Nat.le_refl _) hT
    rw [sgnQ_add_of_abs_lt (lt_le_trans' h1 h2), sgnQ_mul_two_pow, sgnQ_intCast]

/-! ## Correct rounding of a sum -/

theorem rneMag_tiny {p : ℕ} {emin : ℤ} {a : ℚ} (ha : 0 < a) (h : a < 2 ^ (emin - p)) :
    rneMag p emin a = 0 := by
  obtain ⟨f1, f2⟩ := floorLog2_spec ha
  have he : floorLog2 a < emin - p := by
    apply Classical.byContradiction; intro hn
    have := two_pow_le (show emin - (p : ℤ) ≤ floorLog2 a by omega); grind
  have hg : rneGrid p emin a = emin - p + 1 := by unfold rneGrid; omega
  unfold rneMag
  rw [hg]
  have hpg := two_pow_pos (emin - p + 1)
  have ht0 : ((0 : ℤ) : ℚ) ≤ a / 2 ^ (emin - p + 1) := by
    have : (0 : ℚ) ≤ a / 2 ^ (emin - p + 1) := by
      rw [div_two_pow]; exact Rat.mul_nonneg (Rat.le_of_lt ha) (Rat.le_of_lt (two_pow_pos _))
    simpa using this
  have hhalf : 2 * (a / 2 ^ (emin - p + 1)) < 1 := by
    rw [div_two_pow]
    have e1 : 2 * (a * 2 ^ (-(emin - p + 1))) = a * 2 ^ (-(emin - (p : ℤ))) := by
      rw [show -(emin - (p : ℤ)) = -(emin - p + 1) + 1 by omega, two_pow_succ]; grind
    rw [e1]
    have hlt := Rat.mul_lt_mul_of_pos_right h (two_pow_pos (-(emin - (p : ℤ))))
    have e2 : (2 : ℚ) ^ (emin - (p : ℤ)) * 2 ^ (-(emin - (p : ℤ))) = 1 := by
      rw [Rat.mul_comm]; exact two_pow_neg_mul _
    grind
  have ht1 : a / 2 ^ (emin - p + 1) < ((0 : ℤ) : ℚ) + 1 := by simp; grind
  rw [roundNearestEven_eq_of ht0 ht1, if_neg]
  · simp
  · intro hc; rcases hc with hc | ⟨hc, _⟩ <;> simp at hc <;> grind

theorem finishRNE_zero (p : ℕ) (emax s : ℤ) : finishRNE p emax s (0, 0) = some 0 := by
  have h : cmpDy (0 : ℤ).toNat 0 (2 ^ p - 1) (emax - ((p : ℤ) - 1)) ≤ 0 := by
    unfold cmpDy
    rw [if_pos (show Int.toNat 0 = 0 from rfl)]
    split <;> omega
  unfold finishRNE
  simp only
  rw [if_pos h]; simp

/-- The query term of `roundSum`: `N − s K 2^(h−q)` at the grid `q`. -/
def queryTerm (N q s K h : ℤ) : ℤ × ℤ := (N - s * K * 2 ^ (h - q).toNat, q)

/-- **Round to nearest even of a sum of terms** with bounded registers. One top-down summation with
threshold `2^(bitlen n + p + 3)`; if nothing is left over, round `N 2^q` exactly; if the sum is
below half the smallest subnormal, return `0`; otherwise answer the comparisons of `roundByCmp` with
the sign oracle on the residuals and one query term, refusing any query outside the bounds proved to
suffice (so every query term is below `2^(bitlen |N| + p + 6)`). -/
def roundSum (p : ℕ) (emin emax : ℤ) (W : ℕ) (ts : List (ℤ × ℤ)) : Option ℚ :=
  match topDownSumAll W (bitlen (nonzero ts).length + p + 3) ts with
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
              s * signSum W (queryTerm N q s K h :: rs') else 0)
          eH (shiftFloor N.natAbs q))

/-- **Query terms are small**: under the guard of `roundSum`, `|N − s K 2^(h−q)| < 2^(bitlen |N| + p + 6)`. -/
theorem query_natAbs_lt {N q s K h : ℤ} {p : ℕ} (hs : s.natAbs ≤ 1) (hK0 : 0 ≤ K)
    (hK : K < 2 ^ (p + 4)) (hh : h ≤ q + bitlen N.natAbs + 1) :
    (queryTerm N q s K h).1.natAbs < 2 ^ (bitlen N.natAbs + p + 6) := by
  unfold queryTerm; simp only
  have hN := lt_two_pow_bitlen N.natAbs
  generalize hB : bitlen N.natAbs = B at hN hh
  have hd : (h - q).toNat ≤ B + 1 := by omega
  have hKn : K.toNat < 2 ^ (p + 4) := by
    have : ((2 ^ (p + 4) : ℕ) : ℤ) = (2 : ℤ) ^ (p + 4) := by rw [Int.natCast_pow]; rfl
    omega
  have hKd : K.toNat * 2 ^ (h - q).toNat < 2 ^ (B + p + 5) := by
    calc K.toNat * 2 ^ (h - q).toNat < 2 ^ (p + 4) * 2 ^ (h - q).toNat :=
          Nat.mul_lt_mul_of_pos_right hKn (Nat.two_pow_pos _)
      _ = 2 ^ (p + 4 + (h - q).toNat) := (Nat.pow_add _ _ _).symm
      _ ≤ 2 ^ (B + p + 5) := Nat.pow_le_pow_right (by decide) (by omega)
  have hsK : (s * K * 2 ^ (h - q).toNat).natAbs ≤ K.toNat * 2 ^ (h - q).toNat := by
    rw [Int.natAbs_mul, Int.natAbs_mul, Int.natAbs_pow]
    show s.natAbs * K.natAbs * 2 ^ (h - q).toNat ≤ K.toNat * 2 ^ (h - q).toNat
    have : K.natAbs = K.toNat := by omega
    rw [this]
    calc s.natAbs * K.toNat * 2 ^ (h - q).toNat ≤ 1 * K.toNat * 2 ^ (h - q).toNat :=
          Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ hs)
      _ = K.toNat * 2 ^ (h - q).toNat := by rw [Nat.one_mul]
  have hsub := Int.natAbs_sub_le N (s * K * 2 ^ (h - q).toNat)
  have h2 : 2 ^ (B + p + 6) = 2 ^ (B + p + 5) * 2 := Nat.pow_succ ..
  have h3 : 2 ^ B ≤ 2 ^ (B + p + 5) := Nat.pow_le_pow_right (by decide) (by omega)
  omega

theorem tsum_queryTerm (N q s K h : ℤ) (rs : List (ℤ × ℤ)) (hq : q ≤ h) :
    tsum (queryTerm N q s K h :: rs) = (N : ℚ) * 2 ^ q + tsum rs - (s : ℚ) * K * 2 ^ h := by
  rw [tsum_cons]
  unfold queryTerm tval; simp only
  rw [Rat.intCast_sub, Rat.intCast_mul, Rat.intCast_mul, intCast_two_pow]
  have : (2 : ℚ) ^ (((h - q).toNat : ℕ) : ℤ) * 2 ^ q = 2 ^ h := by
    rw [← two_pow_add]; congr 1; omega
  grind

/-- **The bounded rounding of a sum is round to nearest even**, for ranges of
`W > bitlen (n + 1) + p + 3` bits, whatever the exponents. -/
theorem roundSum_eq {p : ℕ} (emin emax : ℤ) {W : ℕ} {ts : List (ℤ × ℤ)}
    (hW : bitlen (ts.length + 1) + p + 3 < W) :
    roundSum p emin emax W ts = roundRNE p emin emax (tsum ts) := by
  have hmono : ∀ {a b : ℕ}, a ≤ b → bitlen a ≤ bitlen b := bitlen_mono
  have hbl : bitlen (nonzero ts).length ≤ bitlen (ts.length + 1) :=
    hmono (Nat.le_trans (length_nonzero ts) (Nat.le_succ _))
  obtain ⟨N, q, rs', h, hval, htop, hstop, hlen, _⟩ :=
    topDownSumAll_spec (W := W) (T := bitlen (nonzero ts).length + p + 3) (by omega) ts
  unfold roundSum
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
              N.sign * signSum W (queryTerm N q N.sign K h :: rs') else 0)
    (eH := eH)
    (fun K h ⟨hK0, hK, hL, hU⟩ => by
      have hqh : q ≤ h := by omega
      have hhU : h ≤ q + B + 1 := by
        have : gridOf p emin (eH + 1) ≤ eH + 2 := by unfold gridOf; omega
        omega
      rw [if_pos ⟨hK0, hK, hqh, hhU⟩]
      have hlen' : bitlen (rs'.length + 1) < W :=
        Nat.lt_of_le_of_lt (hmono (b := ts.length + 1) (by have := length_nonzero ts; omega)) (by omega)
      rw [signSum_eq (by simpa using hlen'), tsum_queryTerm _ _ _ _ _ _ hqh, hx, ← hval]
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

/-- A heavy cancellation: `(2^30 + 1) 2^100 − 2^30 2^100 − 2^100` leaves `5 · 2^-50 + 2^-200`. -/
def cancelTerms : List (ℤ × ℤ) :=
  [(2 ^ 30 + 1, 100), (-(2 ^ 30), 100), (-1, 100), (5, -50), (1, -200)]

example : signSum 8 cancelTerms = 1 := by decide +kernel

example : roundSum 24 (-126) 127 34 cancelTerms = roundRNE 24 (-126) 127 (tsum cancelTerms) := by
  decide +kernel

/-- A tie after cancellation: `2^300 + 1 + 2^-24 − 2^300` is halfway between binary32 neighbours of
`1` and rounds to the even `1`; `2^-200` more rounds up. -/
def tieTerms : List (ℤ × ℤ) := [(1, 300), (1, 0), (1, -24), (-1, 300)]

example : roundSum 24 (-126) 127 34 tieTerms = some 1 := by decide +kernel

example : roundSum 24 (-126) 127 34 tieTerms = roundRNE 24 (-126) 127 (tsum tieTerms) := by
  decide +kernel

example : roundSum 24 (-126) 127 34 ((1, -200) :: tieTerms) =
    roundRNE 24 (-126) 127 (tsum ((1, -200) :: tieTerms)) := by decide +kernel

end Ozaki
