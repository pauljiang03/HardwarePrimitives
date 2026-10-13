import Ozaki.BoundedInt

/-! # One theorem bounding every integer of correctly rounded Ozaki-I

`ozaki1CRI` (in `Ozaki.BoundedInt`) is correctly rounded Ozaki-I in integer operations. This file
gives each of its functions a *checked* twin in `Ozaki.Checked`, in which every integer an
arithmetic operation produces passes through a guard and a failed guard returns `none`:

* data integers must be below `2^R` in magnitude (`Widths.gv`, `Widths.gn`): significands and their
  shifts, the division, remainder and rounded quotient of the integer slicing, engine outputs read
  back, window parts, every partial sum of a register, accumulators, query terms, the operands of
  every comparison by shifting (`cmpDy`), integer parts, rounded significands, the constant
  `2^p − 1`, and the descent's fuel (the potential, a count of bits);
* exponent-like integers must be below `2^X` (`Widths.ge`, `Widths.gi`): exponents, grids, shift
  amounts, bit positions, the window grids of the descent, the exponent guesses of the rounding,
  register widths, the exact path's window width, the slicing's exponent count `s (b + 1)` in the
  check, and the descent's stopping thresholds.

Powers of two occur only as shifts (`x · 2^d`, `⌊x / 2^d⌋`, `x mod 2^d`): the shift amount `d` is
guarded as an exponent and the shifted result as data; no power is formed as an intermediate.
Comparisons, `min`, `max`, signs, absolute values, bit lengths of guarded integers (at most `R`)
and parity tests produce no new magnitude and are not guarded; list lengths are the input's size.
The descent's register width `W + bitlen n + 1` is guarded too: a register may be at most one bit
wider than the data guard (`Widths.gw`). The result value `±M · 2^g` that `finishRNE` assembles is the output, not an
intermediate. The engine's own arithmetic is guarded when it runs through the guarded split-K
engine (`Ozaki.CheckedMultipliers.chunkedC`).

Each `…C_eq` lemma proves that, on inputs within stated bounds, the checked twin returns exactly
what the unchecked function returns: no guard ever fails. They compose into one theorem,
`ozaki1CRIC_eq`: on binary entries with an exact engine, if `R` and `X` meet requirements given by
explicit formulas in `p`, `emin`, `emax`, `b`, the slice counts, the vector length `k`, `W` and the
engine's budget (`testD`, `testX` for the checks, `exactR`, `exactX` for the exact path), the
checked `ozaki1CRIC` equals `ozaki1CRI`. `ozaki1CRISC_eq` does the same for the variant with signed
zeros (one more requirement, `R ≥ 2p`, for the product of two significands in the sign test).

The check's integers need `max (W, s (b + 1)) + …` bits (`testD`), the exact path's
`bitlen budget + 2 (bitlen (smax² + 1) + p + 4) + …` (`exactR`); the descent's fuel is bounded by
`exactR` (`exact_fuel_lt`), so `X` is set by the exponents alone (`exactX`). Concrete widths, for
`11`-bit slices, at most `8` slices in each check, a `96`-bit window and `k ≤ 2^20`: binary64 with at
most `175` slices on the exact path fits `263` bits and `17` bits, binary32 with at most `24` slices
`207` and `15` (`Ozaki.CheckedTight`). The instances stated here at `332`/`24` (`ozaki1CRIC_binary64`,
`ozaki1CRIC_binary64_eq`, `ozaki1CRISC_binary64_eq`) and `303`/`17` (`ozaki1CRIC_binary32`,
`ozaki1CRIC_binary32_eq`) still hold, with room to spare. -/

local notation "ℕ" => Nat
local notation "ℤ" => Int
local notation "ℚ" => Rat

namespace Ozaki

/-- Register widths: data integers below `2^R` in magnitude, exponent-like integers below
`2^X`. -/
structure Widths where
  R : ℕ
  X : ℕ

namespace Widths

/-- The data guard. -/
def gv (B : Widths) (v : ℤ) : Option ℤ := if v.natAbs < 2 ^ B.R then some v else none

/-- The data guard on a natural number. -/
def gn (B : Widths) (n : ℕ) : Option ℕ := if n < 2 ^ B.R then some n else none

/-- The exponent guard. -/
def ge (B : Widths) (e : ℤ) : Option ℤ := if e.natAbs < 2 ^ B.X then some e else none

/-- The exponent guard on a natural number. -/
def gi (B : Widths) (n : ℕ) : Option ℕ := if n < 2 ^ B.X then some n else none

/-- The register-width guard: a two's-complement register of `w` bits holds magnitudes up to
`2^(w−1)`, so it may be at most one bit wider than the data guard. -/
def gw (B : Widths) (w : ℕ) : Option ℕ := if w ≤ B.R + 1 then some w else none

theorem gv_ok {B : Widths} {v : ℤ} (h : v.natAbs < 2 ^ B.R) : B.gv v = some v := if_pos h
theorem gn_ok {B : Widths} {n : ℕ} (h : n < 2 ^ B.R) : B.gn n = some n := if_pos h
theorem ge_ok {B : Widths} {e : ℤ} (h : e.natAbs < 2 ^ B.X) : B.ge e = some e := if_pos h
theorem gi_ok {B : Widths} {n : ℕ} (h : n < 2 ^ B.X) : B.gi n = some n := if_pos h
theorem gw_ok {B : Widths} {w : ℕ} (h : w ≤ B.R + 1) : B.gw w = some w := if_pos h

end Widths

theorem lt_two_pow_of_le {n k R : ℕ} (h : n < 2 ^ k) (hk : k ≤ R) : n < 2 ^ R :=
  Nat.lt_of_lt_of_le h (Nat.pow_le_pow_right (by decide) hk)

/-! ## The slicing -/

namespace Checked

variable (B : Widths)

/-- `clog2Nat`: one power to compare, one increment. -/
def clog2NatC (n : ℕ) : Option ℕ := do
  let P ← B.gn (2 ^ n.log2)
  if n = P then pure n.log2 else B.gi (n.log2 + 1)

def entryExpC (a : ℤ × ℤ) : Option (Option ℤ) :=
  if a.1 = 0 then some none
  else do
    let c ← clog2NatC B a.1.natAbs
    let e ← B.ge ((c : ℤ) + a.2)
    pure (some e)

def maxEntryExpC : List (ℤ × ℤ) → Option (Option ℤ)
  | [] => some none
  | a :: xs => do
    let e ← entryExpC B a
    let m ← maxEntryExpC xs
    pure (optMax e m)

def gridIntC (b : ℕ) (prev : ℤ) (xs : List (ℤ × ℤ)) : Option ℤ := do
  let m ← maxEntryExpC B xs
  match m with
  | none => B.ge (prev - (b + 1))
  | some c => B.ge (c - b)

/-- `rneDiv`: the divisor, remainder, quotient, doubled remainder and rounded quotient. -/
def rneDivC (m : ℤ) (j : ℕ) : Option ℤ := do
  let P ← B.gv ((2 ^ j : ℕ) : ℤ)
  let r ← B.gv (m % P)
  let q ← B.gv (m / P)
  let r2 ← B.gv (2 * r)
  if P < r2 ∨ (r2 = P ∧ q % 2 = 1) then B.gv (q + 1) else pure q

def rneShiftC (m : ℤ) (k : ℕ) : Option ℤ :=
  if m = 0 then some 0
  else do
    let cap ← B.gi (m.natAbs.log2 + 2)
    rneDivC B m (min k cap)

def coeffIntC (b : ℕ) (g : ℤ) (a : ℤ × ℤ) : Option ℤ :=
  if a.1 = 0 then some 0
  else if g ≤ a.2 then do
    let d ← B.ge (a.2 - g)
    B.gv (a.1 * ((2 ^ min d.toNat b : ℕ) : ℤ))
  else do
    let k ← B.ge (g - a.2)
    rneShiftC B a.1 k.toNat

def restIntC (g : ℤ) (a : ℤ × ℤ) : Option (ℤ × ℤ) :=
  if a.1 = 0 ∨ g ≤ a.2 then some (0, a.2)
  else do
    let k ← B.ge (g - a.2)
    let q ← rneShiftC B a.1 k.toNat
    let cap ← B.gi (a.1.natAbs.log2 + 2)
    let qs ← B.gv (q * ((2 ^ min k.toNat cap : ℕ) : ℤ))
    let r ← B.gv (a.1 - qs)
    pure (r, a.2)

def splitIntFromC (b : ℕ) : ℕ → ℤ → List (ℤ × ℤ) → Option (List Slice × List (ℤ × ℤ))
  | 0, _, xs => some ([], xs)
  | s + 1, prev, xs => do
    let g ← gridIntC B b prev xs
    let cs ← xs.mapM (coeffIntC B b g)
    let rest ← xs.mapM (restIntC B g)
    let r ← splitIntFromC b s g rest
    pure (⟨g, cs⟩ :: r.1, r.2)

end Checked

open Checked

/-! ### The slicing never fails a guard -/

theorem log2_le_of_lt {n p : ℕ} (h : n < 2 ^ p) : n.log2 ≤ p := by
  by_cases hn : n = 0
  · subst hn; simp [Nat.log2_zero]
  · exact Nat.le_of_lt ((Nat.log2_lt hn).mpr h)

theorem clog2NatC_eq {B : Widths} {n p : ℕ} (hn : n < 2 ^ p) (hR : p + 1 ≤ B.R)
    (hX : p + 1 < 2 ^ B.X) : clog2NatC B n = some (clog2Nat n) := by
  have hl := log2_le_of_lt hn
  have hP : 2 ^ n.log2 < 2 ^ B.R := Nat.pow_lt_pow_right (by decide) (by omega)
  unfold clog2NatC clog2Nat
  rw [Widths.gn_ok hP]
  simp only [Option.bind_eq_bind, Option.bind_some, Option.pure_def]
  split
  · rfl
  · rw [Widths.gi_ok (by omega)]

theorem entryExpC_eq {B : Widths} {a : ℤ × ℤ} {p EM : ℕ} (ha : a.1.natAbs < 2 ^ p)
    (he : a.2.natAbs ≤ EM) (hR : p + 1 ≤ B.R) (hX : p + 1 + EM < 2 ^ B.X) :
    entryExpC B a = some (entryExp a) := by
  unfold entryExpC entryExp
  split
  · rfl
  · rw [clog2NatC_eq ha hR (by omega)]
    simp only [Option.bind_eq_bind, Option.bind_some, Option.pure_def]
    have hc : clog2Nat a.1.natAbs ≤ p + 1 := by
      have := log2_le_of_lt ha; unfold clog2Nat; split <;> omega
    rw [Widths.ge_ok (by omega)]
    rfl

/-- The entries of a binary vector: significands below `2^p`, exponents at most `EM` in
magnitude. -/
def EntriesIn (p EM : ℕ) (xs : List (ℤ × ℤ)) : Prop :=
  ∀ a ∈ xs, a.1.natAbs < 2 ^ p ∧ a.2.natAbs ≤ EM

theorem maxEntryExpC_eq {B : Widths} {p EM : ℕ} (hR : p + 1 ≤ B.R) (hX : p + 1 + EM < 2 ^ B.X) :
    ∀ {xs : List (ℤ × ℤ)}, EntriesIn p EM xs → maxEntryExpC B xs = some (maxEntryExp xs)
  | [], _ => rfl
  | a :: xs, h => by
    unfold maxEntryExpC maxEntryExp
    rw [entryExpC_eq (h a List.mem_cons_self).1 (h a List.mem_cons_self).2 hR hX,
      maxEntryExpC_eq hR hX fun c hc => h c (List.mem_cons_of_mem _ hc)]
    rfl

/-- An exponent of an entry: `⌈log₂ |m|⌉ + e`, at most `p + 1 + EM` in magnitude. -/
theorem entryExp_natAbs_le {a : ℤ × ℤ} {p EM : ℕ} (ha : a.1.natAbs < 2 ^ p)
    (he : a.2.natAbs ≤ EM) {c : ℤ} (h : entryExp a = some c) : c.natAbs ≤ p + 1 + EM := by
  unfold entryExp at h
  split at h
  · cases h
  · cases h
    have := log2_le_of_lt ha
    have hc : clog2Nat a.1.natAbs ≤ p + 1 := by unfold clog2Nat; split <;> omega
    omega

/-- **Grids are bounded by the entries' exponents and the previous grid.** -/
theorem gridInt_natAbs_le {b p EM : ℕ} {prev : ℤ} {xs : List (ℤ × ℤ)} (hx : EntriesIn p EM xs) :
    (gridInt b prev xs).natAbs ≤ max (p + 1 + EM + b) (prev.natAbs + b + 1) := by
  unfold gridInt
  cases h : maxEntryExp xs with
  | none => simp only; omega
  | some c =>
    simp only
    obtain ⟨_, a, ha, hac⟩ := maxExp_eq_some h
    have := entryExp_natAbs_le (hx a ha).1 (hx a ha).2 hac
    omega

theorem gridIntC_eq {B : Widths} {b p EM : ℕ} {prev : ℤ} {xs : List (ℤ × ℤ)}
    (hx : EntriesIn p EM xs) (hR : p + 1 ≤ B.R)
    (hX : max (p + 1 + EM + b) (prev.natAbs + b + 1) < 2 ^ B.X) :
    gridIntC B b prev xs = some (gridInt b prev xs) := by
  unfold gridIntC
  rw [maxEntryExpC_eq hR (by omega) hx]
  simp only [Option.bind_eq_bind, Option.bind_some]
  have hg := gridInt_natAbs_le (b := b) (prev := prev) hx
  unfold gridInt at hg ⊢
  cases h : maxEntryExp xs with
  | none => simp only [h] at hg ⊢; exact Widths.ge_ok (by omega)
  | some c => simp only [h] at hg ⊢; exact Widths.ge_ok (by omega)

/-- **The rounding error of `rneDiv`**: `|m − rneDiv m j · 2^j| ≤ 2^j / 2`. -/
theorem rneDiv_err (m : ℤ) (j : ℕ) :
    2 * (m - rneDiv m j * ((2 ^ j : ℕ) : ℤ)).natAbs ≤ 2 ^ j := by
  have hD : (0 : ℚ) < ((2 ^ j : ℕ) : ℚ) := Rat.natCast_pos.mpr (Nat.two_pow_pos j)
  have h := roundNearestEven_error ((m : ℚ) / ((2 ^ j : ℕ) : ℚ))
  rw [← rneDiv_eq_nat] at h
  have hc : (m : ℚ) / ((2 ^ j : ℕ) : ℚ) * ((2 ^ j : ℕ) : ℚ) = m :=
    Rat.div_mul_cancel (Rat.ne_of_gt hD)
  have e : (((m - rneDiv m j * ((2 ^ j : ℕ) : ℤ) : ℤ)) : ℚ) =
      ((m : ℚ) / ((2 ^ j : ℕ) : ℚ) - (rneDiv m j : ℚ)) * ((2 ^ j : ℕ) : ℚ) := by
    rw [Rat.intCast_sub, Rat.intCast_mul, Rat.intCast_natCast]; grind
  have h2 : 2 * Rat.abs ((((m - rneDiv m j * ((2 ^ j : ℕ) : ℤ) : ℤ)) : ℚ)) ≤
      ((2 ^ j : ℕ) : ℚ) := by
    rw [e, abs_mul, abs_of_nonneg (Rat.le_of_lt hD)]
    have := Rat.mul_le_mul_of_nonneg_right h (Rat.le_of_lt hD)
    grind
  rw [abs_intCast] at h2
  have : ((2 * (m - rneDiv m j * ((2 ^ j : ℕ) : ℤ)).natAbs : ℕ) : ℚ) ≤ ((2 ^ j : ℕ) : ℚ) := by
    rw [Rat.natCast_mul]; exact h2
  exact Rat.natCast_le_natCast.mp this

theorem rneDivC_eq {B : Widths} {m : ℤ} {j p : ℕ} (hm : m.natAbs < 2 ^ p) (hj : j ≤ p + 1)
    (hR : p + 3 ≤ B.R) : rneDivC B m j = some (rneDiv m j) := by
  have hpj : 2 ^ j ≤ 2 ^ (p + 1) := Nat.pow_le_pow_right (by decide) hj
  have hpR : 2 ^ (p + 3) ≤ 2 ^ B.R := Nat.pow_le_pow_right (by decide) hR
  have e1 : 2 ^ (p + 1) = 2 * 2 ^ p := by rw [Nat.pow_succ]; omega
  have e3 : 2 ^ (p + 3) = 8 * 2 ^ p := by rw [Nat.pow_add]; omega
  have hP0 : (0 : ℤ) < ((2 ^ j : ℕ) : ℤ) := by have := Nat.two_pow_pos j; omega
  unfold rneDivC rneDiv
  rw [Widths.gv_ok (by simp; omega)]
  simp only [Option.bind_eq_bind, Option.bind_some, Option.pure_def]
  have hr0 := Int.emod_nonneg m (Int.ne_of_gt hP0)
  have hr1 := Int.emod_lt_of_pos m hP0
  have hq := Int.natAbs_ediv_le_natAbs m ((2 ^ j : ℕ) : ℤ)
  generalize m % ((2 ^ j : ℕ) : ℤ) = r at hr0 hr1 ⊢
  generalize m / ((2 ^ j : ℕ) : ℤ) = q at hq ⊢
  rw [Widths.gv_ok (by omega)]
  simp only [Option.bind_some]
  rw [Widths.gv_ok (by omega)]
  simp only [Option.bind_some]
  rw [Widths.gv_ok (by omega)]
  simp only [Option.bind_some]
  by_cases hc : ((2 ^ j : ℕ) : ℤ) < 2 * r ∨ 2 * r = ((2 ^ j : ℕ) : ℤ) ∧ q % 2 = 1
  · rw [if_pos hc, if_pos hc, Widths.gv_ok (by omega)]
  · rw [if_neg hc, if_neg hc]

theorem shiftCap_le {m : ℤ} {p : ℕ} (hm : m.natAbs < 2 ^ p) (h0 : m ≠ 0) : shiftCap m ≤ p + 1 := by
  have := (Nat.log2_lt (n := m.natAbs) (by omega)).mpr hm
  unfold shiftCap; omega

theorem rneShiftC_eq {B : Widths} {m : ℤ} {k p : ℕ} (hm : m.natAbs < 2 ^ p) (hR : p + 3 ≤ B.R)
    (hX : p + 2 < 2 ^ B.X) : rneShiftC B m k = some (rneShift m k) := by
  unfold rneShiftC rneShift
  split
  · rfl
  · rename_i h0
    have hc := shiftCap_le hm h0
    unfold shiftCap at hc
    rw [Widths.gi_ok (by omega)]
    simp only [Option.bind_eq_bind, Option.bind_some]
    rw [rneDivC_eq hm (by omega) hR]
    rfl

theorem coeffIntC_eq {B : Widths} {b p : ℕ} {g : ℤ} {a : ℤ × ℤ} (ha : a.1.natAbs < 2 ^ p)
    (hR : p + b + 3 ≤ B.R) (hX : a.2.natAbs + g.natAbs + p + 2 < 2 ^ B.X) :
    coeffIntC B b g a = some (coeffInt b g a) := by
  unfold coeffIntC coeffInt
  split
  · rfl
  · split
    · rename_i h0 hg
      rw [Widths.ge_ok (by omega)]
      simp only [Option.bind_eq_bind, Option.bind_some]
      apply Widths.gv_ok
      rw [Int.natAbs_mul, Int.natAbs_natCast]
      have h1 : 2 ^ min (a.2 - g).toNat b ≤ 2 ^ b := Nat.pow_le_pow_right (by decide) (by omega)
      have h2 := Nat.mul_lt_mul_of_lt_of_le ha h1 (Nat.two_pow_pos _)
      refine Nat.lt_of_lt_of_le h2 ?_
      rw [← Nat.pow_add]; exact Nat.pow_le_pow_right (by decide) (by omega)
    · rename_i h0 hg
      rw [Widths.ge_ok (by omega)]
      simp only [Option.bind_eq_bind, Option.bind_some]
      exact rneShiftC_eq ha (by omega) (by omega)

theorem restIntC_eq {B : Widths} {p : ℕ} {g : ℤ} {a : ℤ × ℤ} (ha : a.1.natAbs < 2 ^ p)
    (hR : p + 3 ≤ B.R) (hX : a.2.natAbs + g.natAbs + p + 2 < 2 ^ B.X) :
    restIntC B g a = some (restInt g a) := by
  unfold restIntC restInt
  split
  · rfl
  · rename_i h
    have h0 : a.1 ≠ 0 := fun h' => h (Or.inl h')
    have hc := shiftCap_le ha h0
    rw [Widths.ge_ok (by omega)]
    simp only [Option.bind_eq_bind, Option.bind_some]
    rw [rneShiftC_eq ha hR (by omega)]
    simp only [Option.bind_some]
    unfold shiftCap at hc
    rw [Widths.gi_ok (by omega)]
    simp only [Option.bind_some]
    -- the rounded quotient times the divisor is within half the divisor of `m`
    have hq : rneShift a.1 (g - a.2).toNat = rneDiv a.1 (min (g - a.2).toNat (shiftCap a.1)) :=
      rneShift_eq_rneDiv h0 _
    unfold shiftCap at hq
    rw [hq]
    unfold shiftCap
    have herr := rneDiv_err a.1 (min (g - a.2).toNat (a.1.natAbs.log2 + 2))
    have hj : 2 ^ min (g - a.2).toNat (a.1.natAbs.log2 + 2) ≤ 2 ^ (p + 1) :=
      Nat.pow_le_pow_right (by decide) (by omega)
    have hpR : 2 ^ (p + 3) ≤ 2 ^ B.R := Nat.pow_le_pow_right (by decide) hR
    have e1 : 2 ^ (p + 1) = 2 * 2 ^ p := by rw [Nat.pow_succ]; omega
    have e3 : 2 ^ (p + 3) = 8 * 2 ^ p := by rw [Nat.pow_add]; omega
    generalize rneDiv a.1 (min (g - a.2).toNat (a.1.natAbs.log2 + 2)) *
      ((2 ^ min (g - a.2).toNat (a.1.natAbs.log2 + 2) : ℕ) : ℤ) = qs at herr ⊢
    rw [Widths.gv_ok (by omega)]
    simp only [Option.bind_some]
    rw [Widths.gv_ok (by omega)]
    rfl

/-- **The slicing never fails a guard**: on entries with significands below `2^p` and exponents at
most `EM` in magnitude, starting from a grid at most `P ≥ p + 1 + EM + b` in magnitude, with
`R ≥ p + b + 3` and `2^X > EM + P + (s + 1)(b + 1) + p + 2`. -/
theorem splitIntFromC_eq {B : Widths} {b p EM : ℕ} (hR : p + b + 3 ≤ B.R) :
    ∀ (s : ℕ) (prev : ℤ) (P : ℕ) (xs : List (ℤ × ℤ)), EntriesIn p EM xs →
      prev.natAbs ≤ P → p + 1 + EM + b ≤ P → EM + P + (s + 1) * (b + 1) + p + 2 < 2 ^ B.X →
      splitIntFromC B b s prev xs = some (splitIntFrom b s prev xs)
  | 0, _, _, _, _, _, _, _ => rfl
  | s + 1, prev, P, xs, hx, hP, hE, hX => by
    have hg := gridInt_natAbs_le (b := b) (prev := prev) hx
    unfold splitIntFromC splitIntFrom
    rw [gridIntC_eq hx (by omega) (by
      have : (s + 1 + 1) * (b + 1) = (s + 1) * (b + 1) + (b + 1) := by rw [Nat.add_mul, Nat.one_mul]
      omega)]
    simp only [Option.bind_eq_bind, Option.bind_some]
    have hgP : (gridInt b prev xs).natAbs ≤ P + (b + 1) := by omega
    have hX' : EM + (P + (b + 1)) + (s + 1) * (b + 1) + p + 2 < 2 ^ B.X := by
      have : (s + 1 + 1) * (b + 1) = (s + 1) * (b + 1) + (b + 1) := by rw [Nat.add_mul, Nat.one_mul]
      omega
    have hidx : ∀ a ∈ xs, a.2.natAbs + (gridInt b prev xs).natAbs + p + 2 < 2 ^ B.X := by
      intro a ha
      have := (hx a ha).2
      have : (s + 1) * (b + 1) ≥ 0 := Nat.zero_le _
      omega
    rw [mapM_eq_some_map fun a ha => coeffIntC_eq (hx a ha).1 hR (hidx a ha),
      mapM_eq_some_map fun a ha => restIntC_eq (hx a ha).1 (by omega) (hidx a ha)]
    simp only [Option.bind_some]
    have hx' : EntriesIn p EM (xs.map (restInt (gridInt b prev xs))) := by
      intro c hc
      obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hc
      obtain ⟨h1, h2⟩ := restInt_natAbs_le (gridInt b prev xs) a
      exact ⟨Nat.lt_of_le_of_lt h1 (hx a ha).1, by rw [h2]; exact (hx a ha).2⟩
    rw [splitIntFromC_eq hR s _ (P + (b + 1)) _ hx' hgP (by omega) hX']
    rfl

/-! ## Rounding with comparisons -/

namespace Checked

variable (B : Widths)

def cmpDyC (A : ℕ) (a : ℤ) (K : ℕ) (b : ℤ) : Option ℤ :=
  if A = 0 then some (if K = 0 then 0 else -1)
  else if K = 0 then some 1
  else do
    let ta ← B.ge (a + bitlen A)
    let tb ← B.ge (b + bitlen K)
    if ta < tb then pure (-1)
    else if tb < ta then pure 1
    else if b ≤ a then do
      let d ← B.ge (a - b)
      let S ← B.gn (A <<< d.toNat)
      pure (cmpZ (S : ℤ) K)
    else do
      let d ← B.ge (b - a)
      let S ← B.gn (K <<< d.toNat)
      pure (cmpZ A (S : ℤ))

def expByCmpC (cmp : ℤ → ℤ → Option ℤ) (eH : ℤ) : Option ℤ := do
  let e1 ← B.ge (eH + 1)
  let c1 ← cmp 1 e1
  if 0 ≤ c1 then pure e1
  else do
    let c0 ← cmp 1 eH
    if 0 ≤ c0 then pure eH else B.ge (eH - 1)

def gridOfC (p : ℕ) (emin e : ℤ) : Option ℤ := B.ge (max e emin - ((p : ℤ) - 1))

def intPartOfC (cmp : ℤ → ℤ → Option ℤ) (F0 g : ℤ) : Option ℤ := do
  let F1 ← B.gv (F0 + 1)
  let c1 ← cmp F1 g
  if 0 ≤ c1 then pure F1
  else do
    let c0 ← cmp F0 g
    if 0 ≤ c0 then pure F0 else B.gv (F0 - 1)

def dirOfC (cmp : ℤ → ℤ → Option ℤ) (F g : ℤ) : Option ℤ := do
  let K ← B.gv (2 * F + 1)
  let h ← B.ge (g - 1)
  let r ← cmp K h
  if 0 < r ∨ (r = 0 ∧ F % 2 = 1) then B.gv (F + 1) else pure F

def roundByCmpC (p : ℕ) (emin : ℤ) (cmp : ℤ → ℤ → Option ℤ) (eH : ℤ) (FH : ℤ → Option ℤ) :
    Option (ℤ × ℤ) := do
  let e ← expByCmpC B cmp eH
  let g ← gridOfC B p emin e
  let F0 ← FH g
  let F ← intPartOfC B cmp F0 g
  let M ← dirOfC B cmp F g
  pure (M, g)

def shiftFloorC (A : ℕ) (q g : ℤ) : Option ℤ :=
  if g ≤ q then do
    let d ← B.ge (q - g)
    let S ← B.gn (A <<< d.toNat)
    pure (S : ℤ)
  else do
    let d ← B.ge (g - q)
    let S ← B.gn (A >>> d.toNat)
    pure (S : ℤ)

def finishRNEC (p : ℕ) (emax : ℤ) (sgn : ℤ) (Mg : ℤ × ℤ) : Option (Option ℚ) := do
  let mx ← B.gn (2 ^ p - 1)
  let ex ← B.ge (emax - ((p : ℤ) - 1))
  let c ← cmpDyC B Mg.1.toNat Mg.2 mx ex
  pure (if c ≤ 0 then some ((sgn : ℚ) * Mg.1 * 2 ^ Mg.2) else none)

def roundExactC (p : ℕ) (emin emax : ℤ) (N q : ℤ) : Option (Option ℚ) :=
  if N = 0 then some (some 0)
  else do
    let eH ← B.ge (q + bitlen N.natAbs - 1)
    let Mg ← roundByCmpC B p emin (fun K h => cmpDyC B N.natAbs q K.toNat h) eH
      (shiftFloorC B N.natAbs q)
    finishRNEC B p emax N.sign Mg

end Checked

theorem bitlen_le_of_lt {n R : ℕ} (h : n < 2 ^ R) : bitlen n ≤ R := bitlen_le_iff.mpr h

theorem shiftLeft_lt {A d : ℕ} : A <<< d < 2 ^ (bitlen A + d) := by
  rw [Nat.shiftLeft_eq, Nat.pow_add]
  exact Nat.mul_lt_mul_of_pos_right (lt_two_pow_bitlen A) (Nat.two_pow_pos d)

theorem cmpDyC_eq {B : Widths} {A K : ℕ} {a b : ℤ} (hA : A < 2 ^ B.R) (hK : K < 2 ^ B.R)
    (hX : a.natAbs + b.natAbs + B.R < 2 ^ B.X) : cmpDyC B A a K b = some (cmpDy A a K b) := by
  have hbA := bitlen_le_of_lt hA
  have hbK := bitlen_le_of_lt hK
  unfold cmpDyC cmpDy
  split
  · rfl
  split
  · rfl
  rw [Widths.ge_ok (by omega), Widths.ge_ok (by omega)]
  simp only [Option.bind_eq_bind, Option.bind_some, Option.pure_def]
  split
  · rfl
  split
  · rfl
  rename_i h1 h2
  split
  · rename_i h3
    rw [Widths.ge_ok (by omega)]
    simp only [Option.bind_some]
    have hs := shiftLeft_lt (A := A) (d := (a - b).toNat)
    rw [Widths.gn_ok (Nat.lt_of_lt_of_le hs (Nat.pow_le_pow_right (by decide) (by omega)))]
    rfl
  · rename_i h3
    rw [Widths.ge_ok (by omega)]
    simp only [Option.bind_some]
    have hs := shiftLeft_lt (A := K) (d := (b - a).toNat)
    rw [Widths.gn_ok (Nat.lt_of_lt_of_le hs (Nat.pow_le_pow_right (by decide) (by omega)))]
    rfl

theorem expByCmp_range (cmp : ℤ → ℤ → ℤ) (eH : ℤ) :
    eH - 1 ≤ expByCmp cmp eH ∧ expByCmp cmp eH ≤ eH + 1 := by
  unfold expByCmp; split
  · omega
  · split <;> omega

theorem intPartOf_range (cmp : ℤ → ℤ → ℤ) (F0 g : ℤ) :
    F0 - 1 ≤ intPartOf cmp F0 g ∧ intPartOf cmp F0 g ≤ F0 + 1 := by
  unfold intPartOf; split
  · omega
  · split <;> omega

theorem dirOf_range (cmp : ℤ → ℤ → ℤ) (F g : ℤ) : F ≤ dirOf cmp F g ∧ dirOf cmp F g ≤ F + 1 := by
  unfold dirOf; simp only; split <;> omega

theorem expByCmpC_eq {B : Widths} {cmpC : ℤ → ℤ → Option ℤ} {cmpU : ℤ → ℤ → ℤ} {eH : ℤ}
    (hX : eH.natAbs + 1 < 2 ^ B.X) (h1 : cmpC 1 (eH + 1) = some (cmpU 1 (eH + 1)))
    (h0 : cmpC 1 eH = some (cmpU 1 eH)) : expByCmpC B cmpC eH = some (expByCmp cmpU eH) := by
  unfold expByCmpC expByCmp
  rw [Widths.ge_ok (by omega)]
  simp only [Option.bind_eq_bind, Option.bind_some, Option.pure_def]
  rw [h1]
  simp only [Option.bind_some]
  split
  · rfl
  · rw [h0]
    simp only [Option.bind_some]
    split
    · rfl
    · exact Widths.ge_ok (by omega)

theorem intPartOfC_eq {B : Widths} {cmpC : ℤ → ℤ → Option ℤ} {cmpU : ℤ → ℤ → ℤ} {F0 g : ℤ}
    (hR : F0.natAbs + 1 < 2 ^ B.R) (h1 : cmpC (F0 + 1) g = some (cmpU (F0 + 1) g))
    (h0 : cmpC F0 g = some (cmpU F0 g)) : intPartOfC B cmpC F0 g = some (intPartOf cmpU F0 g) := by
  unfold intPartOfC intPartOf
  rw [Widths.gv_ok (by omega)]
  simp only [Option.bind_eq_bind, Option.bind_some, Option.pure_def]
  rw [h1]
  simp only [Option.bind_some]
  split
  · rfl
  · rw [h0]
    simp only [Option.bind_some]
    split
    · rfl
    · exact Widths.gv_ok (by omega)

theorem dirOfC_eq {B : Widths} {cmpC : ℤ → ℤ → Option ℤ} {cmpU : ℤ → ℤ → ℤ} {F g : ℤ}
    (hR : 2 * F.natAbs + 1 < 2 ^ B.R) (hX : g.natAbs + 1 < 2 ^ B.X)
    (h : cmpC (2 * F + 1) (g - 1) = some (cmpU (2 * F + 1) (g - 1))) :
    dirOfC B cmpC F g = some (dirOf cmpU F g) := by
  unfold dirOfC dirOf
  rw [Widths.gv_ok (by omega), Widths.ge_ok (by omega)]
  simp only [Option.bind_eq_bind, Option.bind_some, Option.pure_def]
  rw [h]
  simp only [Option.bind_some]
  split
  · exact Widths.gv_ok (by omega)
  · rfl

theorem grid_natAbs_of {p : ℕ} {emin eH g : ℤ} (hg1 : eH - p ≤ g)
    (hg2 : g ≤ max (eH + 1) emin - ((p : ℤ) - 1)) :
    g.natAbs ≤ eH.natAbs + emin.natAbs + p + 2 := by
  rw [Int.max_def] at hg2
  by_cases hc : eH + 1 ≤ emin
  · rw [if_pos hc] at hg2; omega
  · rw [if_neg hc] at hg2; omega

/-- **Rounding through comparisons never fails a guard** when the oracle and the integer-part
guess are exact on the queries it asks, and the guesses are at most `FB`. -/
theorem roundByCmpC_eq {B : Widths} {p : ℕ} {emin eH : ℤ} {cmpC : ℤ → ℤ → Option ℤ}
    {cmpU : ℤ → ℤ → ℤ} {FHC : ℤ → Option ℤ} {FHU : ℤ → ℤ} {FB : ℕ}
    (hX : eH.natAbs + emin.natAbs + p + 4 < 2 ^ B.X) (hR : 2 * FB + 4 < 2 ^ B.R)
    (hF : ∀ g, eH - p ≤ g → g ≤ max (eH + 1) emin - ((p : ℤ) - 1) →
      FHC g = some (FHU g) ∧ (FHU g).natAbs ≤ FB)
    (hcmp : ∀ K h, K.natAbs ≤ 2 * FB + 3 → h.natAbs ≤ eH.natAbs + emin.natAbs + p + 3 →
      cmpC K h = some (cmpU K h)) :
    roundByCmpC B p emin cmpC eH FHC = some (roundByCmp p emin cmpU eH FHU) := by
  unfold roundByCmpC roundByCmp
  rw [expByCmpC_eq (by omega) (hcmp _ _ (by omega) (by omega)) (hcmp _ _ (by omega) (by omega))]
  simp only [Option.bind_eq_bind, Option.bind_some, Option.pure_def]
  obtain ⟨e1, e2⟩ := expByCmp_range cmpU eH
  generalize expByCmp cmpU eH = e at e1 e2
  have hgr : gridOfC B p emin e = some (gridOf p emin e) := by
    unfold gridOfC gridOf; apply Widths.ge_ok
    rw [Int.max_def]
    by_cases hc : e ≤ emin
    · rw [if_pos hc]; omega
    · rw [if_neg hc]; omega
  rw [hgr]
  simp only [Option.bind_some]
  have hg1 : eH - p ≤ gridOf p emin e := by
    unfold gridOf; rw [Int.max_def]
    by_cases hc : e ≤ emin
    · rw [if_pos hc]; omega
    · rw [if_neg hc]; omega
  have hg2 : gridOf p emin e ≤ max (eH + 1) emin - ((p : ℤ) - 1) := by
    unfold gridOf; rw [Int.max_def, Int.max_def]
    by_cases hc : e ≤ emin
    · rw [if_pos hc]
      by_cases hd : eH + 1 ≤ emin
      · rw [if_pos hd]; exact Int.le_refl _
      · rw [if_neg hd]; omega
    · rw [if_neg hc]
      by_cases hd : eH + 1 ≤ emin
      · rw [if_pos hd]; omega
      · rw [if_neg hd]; omega
  generalize gridOf p emin e = g at hg1 hg2 ⊢
  have hgabs : g.natAbs ≤ eH.natAbs + emin.natAbs + p + 2 := by
    have h2 := hg2
    rw [Int.max_def] at h2
    by_cases hc : eH + 1 ≤ emin
    · rw [if_pos hc] at h2; clear hg2; omega
    · rw [if_neg hc] at h2; clear hg2; omega
  obtain ⟨hFg, hFB⟩ := hF g hg1 hg2
  rw [hFg]
  simp only [Option.bind_some]
  rw [intPartOfC_eq (by omega) (hcmp _ _ (by omega) (by omega)) (hcmp _ _ (by omega) (by omega))]
  simp only [Option.bind_some]
  obtain ⟨f1, f2⟩ := intPartOf_range cmpU (FHU g) g
  generalize intPartOf cmpU (FHU g) g = F at f1 f2
  rw [dirOfC_eq (by omega) (by omega) (hcmp _ _ (by omega) (by omega))]
  rfl

theorem shiftFloorC_eq {B : Widths} {A : ℕ} {q g : ℤ} (hA : A < 2 ^ B.R)
    (hX : q.natAbs + g.natAbs < 2 ^ B.X)
    (hshift : g ≤ q → A <<< (q - g).toNat < 2 ^ B.R) :
    shiftFloorC B A q g = some (shiftFloor A q g) := by
  unfold shiftFloorC shiftFloor
  split
  · rename_i h
    rw [Widths.ge_ok (by omega)]
    simp only [Option.bind_eq_bind, Option.bind_some, Option.pure_def]
    rw [Widths.gn_ok (hshift h)]
    rfl
  · rw [Widths.ge_ok (by omega)]
    simp only [Option.bind_eq_bind, Option.bind_some, Option.pure_def]
    rw [Widths.gn_ok (Nat.lt_of_le_of_lt (Nat.shiftRight_le _ _) hA)]
    rfl

theorem finishRNEC_eq {B : Widths} {p : ℕ} {emax sgn : ℤ} {Mg : ℤ × ℤ}
    (hM : Mg.1.toNat < 2 ^ B.R) (hp : p ≤ B.R)
    (hX : Mg.2.natAbs + emax.natAbs + p + 1 + B.R < 2 ^ B.X) :
    finishRNEC B p emax sgn Mg = some (finishRNE p emax sgn Mg) := by
  have hmx : 2 ^ p - 1 < 2 ^ B.R :=
    Nat.lt_of_lt_of_le (Nat.sub_lt (Nat.two_pow_pos p) (by decide))
      (Nat.pow_le_pow_right (by decide) hp)
  unfold finishRNEC finishRNE
  rw [Widths.gn_ok hmx, Widths.ge_ok (by omega)]
  simp only [Option.bind_eq_bind, Option.bind_some, Option.pure_def]
  rw [cmpDyC_eq hM hmx (by omega)]
  rfl

/-- What `roundByCmp` returns: a grid of an exponent within one of the guess, and an integer within
two of the integer-part guess there. -/
theorem roundByCmp_out (p : ℕ) (emin : ℤ) (cmp : ℤ → ℤ → ℤ) (eH : ℤ) (FH : ℤ → ℤ) :
    ∃ e, eH - 1 ≤ e ∧ e ≤ eH + 1 ∧ (roundByCmp p emin cmp eH FH).2 = gridOf p emin e ∧
      FH (gridOf p emin e) - 1 ≤ (roundByCmp p emin cmp eH FH).1 ∧
      (roundByCmp p emin cmp eH FH).1 ≤ FH (gridOf p emin e) + 2 := by
  obtain ⟨e1, e2⟩ := expByCmp_range cmp eH
  refine ⟨expByCmp cmp eH, e1, e2, rfl, ?_, ?_⟩
  · have := dirOf_range cmp (intPartOf cmp (FH (gridOf p emin (expByCmp cmp eH)))
      (gridOf p emin (expByCmp cmp eH))) (gridOf p emin (expByCmp cmp eH))
    have := intPartOf_range cmp (FH (gridOf p emin (expByCmp cmp eH))) (gridOf p emin (expByCmp cmp eH))
    unfold roundByCmp; simp only; omega
  · have := dirOf_range cmp (intPartOf cmp (FH (gridOf p emin (expByCmp cmp eH)))
      (gridOf p emin (expByCmp cmp eH))) (gridOf p emin (expByCmp cmp eH))
    have := intPartOf_range cmp (FH (gridOf p emin (expByCmp cmp eH))) (gridOf p emin (expByCmp cmp eH))
    unfold roundByCmp; simp only; omega

theorem gridOf_bounds {p : ℕ} {emin eH e : ℤ} (e1 : eH - 1 ≤ e) (e2 : e ≤ eH + 1) :
    eH - p ≤ gridOf p emin e ∧ gridOf p emin e ≤ max (eH + 1) emin - ((p : ℤ) - 1) ∧
      (gridOf p emin e).natAbs ≤ eH.natAbs + emin.natAbs + p + 2 := by
  unfold gridOf
  rw [Int.max_def, Int.max_def]
  by_cases hc : e ≤ emin
  · rw [if_pos hc]
    by_cases hd : eH + 1 ≤ emin
    · rw [if_pos hd]; omega
    · rw [if_neg hd]; omega
  · rw [if_neg hc]
    by_cases hd : eH + 1 ≤ emin
    · rw [if_pos hd]; omega
    · rw [if_neg hd]; omega

/-- The integer-part guess of `roundExact` is small on every grid `roundByCmp` can pick. -/
theorem shiftFloor_bound {A : ℕ} {q g : ℤ} {p D : ℕ} (hA : A < 2 ^ D) (hpD : p + 1 ≤ D)
    (hg : q + bitlen A - 1 - p ≤ g) :
    (g ≤ q → A <<< (q - g).toNat < 2 ^ (p + 1)) ∧ (shiftFloor A q g).natAbs < 2 ^ D := by
  have hl : ∀ hgq : g ≤ q, A <<< (q - g).toNat < 2 ^ (p + 1) := fun hgq =>
    Nat.lt_of_lt_of_le shiftLeft_lt (Nat.pow_le_pow_right (by decide) (by omega))
  refine ⟨hl, ?_⟩
  unfold shiftFloor
  split
  · rename_i h
    rw [Int.natAbs_natCast]
    exact Nat.lt_of_lt_of_le (hl h) (Nat.pow_le_pow_right (by decide) hpD)
  · rw [Int.natAbs_natCast]
    exact Nat.lt_of_le_of_lt (Nat.shiftRight_le _ _) hA

/-- **Integer round to nearest never fails a guard** on `N · 2^q` with `|N| < 2^D`, `D ≥ p + 2`,
`R ≥ D + 3`, and `X` above the exponents involved. -/
theorem roundExactC_eq {B : Widths} {p D : ℕ} {emin emax N q : ℤ} (hN : N.natAbs < 2 ^ D)
    (hpD : p + 2 ≤ D) (hR : D + 3 ≤ B.R)
    (hX : 2 * q.natAbs + 2 * D + emin.natAbs + emax.natAbs + 2 * p + 2 * B.R + 8 < 2 ^ B.X) :
    roundExactC B p emin emax N q = some (roundExact p emin emax N q) := by
  unfold roundExactC roundExact
  split
  · rfl
  rename_i hN0
  have hbN := bitlen_le_of_lt hN
  have hD3 : 2 ^ (D + 3) ≤ 2 ^ B.R := Nat.pow_le_pow_right (by decide) hR
  have e3 : 2 ^ (D + 3) = 8 * 2 ^ D := by rw [Nat.pow_add]; omega
  have hpD' : 2 ^ (p + 1) ≤ 2 ^ D := Nat.pow_le_pow_right (by decide) (by omega)
  have hDR : 2 ^ D ≤ 2 ^ B.R := Nat.pow_le_pow_right (by decide) (by omega)
  rw [Widths.ge_ok (by omega)]
  simp only [Option.bind_eq_bind, Option.bind_some]
  generalize heH : q + (bitlen N.natAbs : ℤ) - 1 = eH
  have heHb : eH.natAbs ≤ q.natAbs + D := by omega
  have hFok : ∀ g, eH - p ≤ g → g ≤ max (eH + 1) emin - ((p : ℤ) - 1) →
      shiftFloorC B N.natAbs q g = some (shiftFloor N.natAbs q g) ∧
        (shiftFloor N.natAbs q g).natAbs ≤ 2 ^ D := by
    intro g hg1 hg2
    have hgb := grid_natAbs_of hg1 hg2
    obtain ⟨hl, hb⟩ := shiftFloor_bound (p := p) hN (by omega) (g := g) (q := q) (by omega)
    exact ⟨shiftFloorC_eq (by omega) (by omega)
      (fun h => Nat.lt_of_lt_of_le (hl h) (Nat.le_trans hpD' hDR)), by omega⟩
  have hcmpok : ∀ (K h : ℤ), K.natAbs ≤ 2 * 2 ^ D + 3 → h.natAbs ≤ eH.natAbs + emin.natAbs + p + 3 →
      cmpDyC B N.natAbs q K.toNat h = some (cmpDy N.natAbs q K.toNat h) :=
    fun K h hK hh => cmpDyC_eq (by omega) (by omega) (by omega)
  rw [roundByCmpC_eq (by omega) (by omega) hFok hcmpok]
  simp only [Option.bind_some]
  obtain ⟨e, e1, e2, hg, hM1, hM2⟩ := roundByCmp_out p emin (fun K h => cmpDy N.natAbs q K.toNat h)
    eH (shiftFloor N.natAbs q)
  obtain ⟨g1, _, g3⟩ := gridOf_bounds (p := p) (emin := emin) e1 e2
  have hF := (hFok _ g1 (gridOf_bounds (p := p) (emin := emin) e1 e2).2.1).2
  generalize shiftFloor N.natAbs q (gridOf p emin e) = F0 at hM1 hM2 hF
  generalize (roundByCmp p emin (fun K h => cmpDy N.natAbs q K.toNat h) eH
    (shiftFloor N.natAbs q)) = Mg at hg hM1 hM2 ⊢
  exact finishRNEC_eq (by omega) (by omega) (by rw [hg]; omega)

/-! ## The descent -/

namespace Checked

variable (B : Widths)

def topOfC (t : ℤ × ℤ) : Option ℤ := B.ge (t.2 + bitlen t.1.natAbs)

def maxTopFromC (e : ℤ) : List (ℤ × ℤ) → Option ℤ
  | [] => some e
  | t :: ts => do
    let tt ← topOfC B t
    maxTopFromC (max e tt) ts

def maxTopC : List (ℤ × ℤ) → Option ℤ
  | [] => some 0
  | t :: ts => do
    let tt ← topOfC B t
    maxTopFromC B tt ts

def rangeTopC (A qa : ℤ) (rs : List (ℤ × ℤ)) : Option ℤ :=
  if A = 0 then maxTopC B rs else topOfC B (A, qa)

def tdivPowC (z : ℤ) (d : ℕ) : Option ℤ := do
  let S ← B.gn (z.natAbs >>> d)
  pure (if z < 0 then -(S : ℤ) else (S : ℤ))

def tmodPowC (z : ℤ) (d : ℕ) : Option ℤ := do
  let S ← B.gn (z.natAbs % 2 ^ d)
  pure (if z < 0 then -(S : ℤ) else (S : ℤ))

def hiPartC (q : ℤ) (t : ℤ × ℤ) : Option ℤ :=
  if q ≤ t.2 then do
    let d ← B.ge (t.2 - q)
    B.gv (t.1 * 2 ^ d.toNat)
  else do
    let d ← B.ge (q - t.2)
    tdivPowC B t.1 d.toNat

def loPartC (q : ℤ) (t : ℤ × ℤ) : Option (ℤ × ℤ) :=
  if q ≤ t.2 then some (0, t.2)
  else do
    let d ← B.ge (q - t.2)
    let m ← tmodPowC B t.1 d.toNat
    pure (m, t.2)

def rangeRestC (q : ℤ) (ts : List (ℤ × ℤ)) : Option (List (ℤ × ℤ)) := do
  let ls ← ts.mapM (loPartC B q)
  pure (nonzero ls)

/-- A register: every partial sum is guarded, then wrapped to `w` bits. -/
def fixedSumFromC (w : ℕ) : ℤ → List ℤ → Option ℤ
  | acc, [] => some acc
  | acc, z :: zs => do
    let s ← B.gv (acc + z)
    fixedSumFromC w (wrap w s) zs

def fixedSumC (w : ℕ) (zs : List ℤ) : Option ℤ := fixedSumFromC B w 0 zs

def topDownSumJC (W T : ℕ) : ℕ → ℤ → ℤ → List (ℤ × ℤ) → Option (Option (ℤ × ℤ × List (ℤ × ℤ)))
  | fuel, A, qa, rs => do
    let top ← rangeTopC B A qa rs
    let q ← B.ge (top - W)
    let parts ← ((A, qa) :: rs).mapM (hiPartC B q)
    if parts.all (fun z => decide (z.natAbs < 2 ^ W)) then do
      let w ← B.gw (W + bitlen parts.length + 1)
      let N ← fixedSumC B w parts
      let rs' ← rangeRestC B q ((A, qa) :: rs)
      if rs' = [] ∨ T < bitlen N.natAbs then pure (some (N, q, rs'))
      else match fuel with
        | 0 => pure none
        | k + 1 => topDownSumJC W T k N q rs'
    else pure none

/-- The potential (the descent's fuel), its partial sums guarded by the data width: a counter of
bits, it is a data-sized quantity, not an exponent. -/
def potentialC : List (ℤ × ℤ) → Option ℕ
  | [] => some 0
  | t :: ts => do
    let r ← potentialC ts
    B.gn (bitlen t.1.natAbs + r)

def topDownSumAllJC (W T : ℕ) (ts : List (ℤ × ℤ)) : Option (Option (ℤ × ℤ × List (ℤ × ℤ))) := do
  let rs := nonzero ts
  let f ← potentialC B rs
  let top ← maxTopC B rs
  topDownSumJC B W T f 0 top rs

end Checked

/-! ### Guards of the descent -/

/-- Terms with significands below `2^Z` and grids in `[gL, gU]`. -/
def TermsIn (Z : ℕ) (gL gU : ℤ) (ts : List (ℤ × ℤ)) : Prop :=
  ∀ t ∈ ts, t.1.natAbs < 2 ^ Z ∧ gL ≤ t.2 ∧ t.2 ≤ gU

theorem topOf_bounds {Z : ℕ} {gL gU : ℤ} {t : ℤ × ℤ} (h : t.1.natAbs < 2 ^ Z) (h1 : gL ≤ t.2)
    (h2 : t.2 ≤ gU) : gL ≤ topOf t ∧ topOf t ≤ gU + Z := by
  have := bitlen_le_of_lt h
  unfold topOf; omega

theorem topOfC_eq {B : Widths} {t : ℤ × ℤ} (h : (t.2 + bitlen t.1.natAbs).natAbs < 2 ^ B.X) :
    topOfC B t = some (topOf t) := Widths.ge_ok h

theorem maxTopFromC_eq {B : Widths} {Z : ℕ} {gL gU : ℤ}
    (hX : gL.natAbs + gU.natAbs + Z < 2 ^ B.X) :
    ∀ (ts : List (ℤ × ℤ)) (e : ℤ), TermsIn Z gL gU ts →
      maxTopFromC B e ts = some (maxTopFrom e ts)
  | [], _, _ => rfl
  | t :: ts, e, h => by
    obtain ⟨h0, h1, h2⟩ := h t List.mem_cons_self
    have := bitlen_le_of_lt h0
    unfold maxTopFromC maxTopFrom
    rw [topOfC_eq (by omega)]
    simp only [Option.bind_eq_bind, Option.bind_some]
    exact maxTopFromC_eq hX ts _ fun u hu => h u (List.mem_cons_of_mem _ hu)

theorem maxTopC_eq {B : Widths} {Z : ℕ} {gL gU : ℤ} (hX : gL.natAbs + gU.natAbs + Z < 2 ^ B.X)
    {ts : List (ℤ × ℤ)} (h : TermsIn Z gL gU ts) : maxTopC B ts = some (maxTop ts) := by
  cases ts with
  | nil => rfl
  | cons t ts =>
    obtain ⟨h0, h1, h2⟩ := h t List.mem_cons_self
    have := bitlen_le_of_lt h0
    show (topOfC B t).bind (fun tt => maxTopFromC B tt ts) = some (maxTopFrom (topOf t) ts)
    rw [topOfC_eq (by omega)]
    simp only [Option.bind_some]
    exact maxTopFromC_eq hX ts _ fun u hu => h u (List.mem_cons_of_mem _ hu)

theorem maxTop_le_of {Z : ℕ} {gL gU : ℤ} {ts : List (ℤ × ℤ)} (h : TermsIn Z gL gU ts) :
    maxTop ts ≤ max (gU + Z) 0 := by
  cases ts with
  | nil => exact Int.le_max_right _ _
  | cons t ts =>
    have := maxTopFrom_le ts (e := topOf t) (E := gU + Z)
      (topOf_bounds (h t List.mem_cons_self).1 (h t List.mem_cons_self).2.1
        (h t List.mem_cons_self).2.2).2
      (fun u hu => (topOf_bounds (h u (List.mem_cons_of_mem _ hu)).1
        (h u (List.mem_cons_of_mem _ hu)).2.1 (h u (List.mem_cons_of_mem _ hu)).2.2).2)
    show maxTopFrom (topOf t) ts ≤ max (gU + Z) 0
    exact Int.le_trans this (Int.le_max_left _ _)

theorem maxTop_ge_of {Z : ℕ} {gL gU : ℤ} {ts : List (ℤ × ℤ)} (h : TermsIn Z gL gU ts)
    (hne : ∀ t ∈ ts, t.1 ≠ 0) (hts : ts ≠ []) : gL + 1 ≤ maxTop ts := by
  obtain ⟨t, ht, htop⟩ := exists_maxTop hts
  have hb := bitlen_pos (n := t.1.natAbs) (by have := hne t ht; omega)
  have := (h t ht).2.1
  unfold topOf at htop; omega

theorem tdivPowC_eq {B : Widths} {z : ℤ} {d : ℕ} (hz : z.natAbs < 2 ^ B.R) :
    tdivPowC B z d = some (tdivPow z d) := by
  unfold tdivPowC tdivPow
  rw [Widths.gn_ok (Nat.lt_of_le_of_lt (Nat.shiftRight_le _ _) hz)]
  rfl

theorem tmodPowC_eq {B : Widths} {z : ℤ} {d : ℕ} (hz : z.natAbs < 2 ^ B.R) :
    tmodPowC B z d = some (tmodPow z d) := by
  unfold tmodPowC tmodPow
  rw [Widths.gn_ok (Nat.lt_of_le_of_lt (Nat.mod_le _ _) hz)]
  rfl

theorem hiPartC_eq {B : Widths} {q : ℤ} {t : ℤ × ℤ} {W : ℕ} (hz : t.1.natAbs < 2 ^ B.R)
    (hW : W ≤ B.R) (htop : t.1 = 0 ∨ topOf t ≤ q + W)
    (hX : t.2.natAbs + q.natAbs < 2 ^ B.X) : hiPartC B q t = some (hiPart q t) := by
  unfold hiPartC
  split
  · rename_i h
    rw [Widths.ge_ok (by omega)]
    simp only [Option.bind_eq_bind, Option.bind_some]
    have hp : (hiPart q t).natAbs < 2 ^ W := by
      rcases htop with h0 | htop
      · unfold hiPart; rw [if_pos h, h0]; simp; exact Nat.two_pow_pos W
      · exact natAbs_hiPart_lt htop
    have e : hiPart q t = t.1 * 2 ^ (t.2 - q).toNat := by unfold hiPart; rw [if_pos h]
    rw [e] at hp ⊢
    exact Widths.gv_ok (Nat.lt_of_lt_of_le hp (Nat.pow_le_pow_right (by decide) hW))
  · rename_i h
    rw [Widths.ge_ok (by omega)]
    simp only [Option.bind_eq_bind, Option.bind_some]
    rw [tdivPowC_eq hz]
    unfold hiPart; rw [if_neg h]

theorem loPartC_eq {B : Widths} {q : ℤ} {t : ℤ × ℤ} (hz : t.1.natAbs < 2 ^ B.R)
    (hX : t.2.natAbs + q.natAbs < 2 ^ B.X) : loPartC B q t = some (loPart q t) := by
  unfold loPartC loPart
  split
  · rfl
  · rw [Widths.ge_ok (by omega)]
    simp only [Option.bind_eq_bind, Option.bind_some]
    rw [tmodPowC_eq hz]
    rfl

theorem rangeRestC_eq {B : Widths} {q : ℤ} {ts : List (ℤ × ℤ)}
    (h : ∀ t ∈ ts, t.1.natAbs < 2 ^ B.R ∧ t.2.natAbs + q.natAbs < 2 ^ B.X) :
    rangeRestC B q ts = some (rangeRest q ts) := by
  unfold rangeRestC rangeRest
  rw [mapM_eq_some_map fun t ht => loPartC_eq (h t ht).1 (h t ht).2]
  rfl

theorem fixedSumFromC_eq {B : Widths} {w : ℕ} (hw : 0 < w) (hR : w - 1 ≤ B.R) :
    ∀ (zs : List ℤ) (acc : ℤ), acc.natAbs + (zs.map Int.natAbs).sum < 2 ^ (w - 1) →
      fixedSumFromC B w acc zs = some (fixedSumFrom w acc zs)
  | [], _, _ => rfl
  | z :: zs, acc, h => by
    simp only [List.map_cons, List.sum_cons] at h
    have hz := Int.natAbs_add_le acc z
    unfold fixedSumFromC fixedSumFrom
    rw [Widths.gv_ok (Nat.lt_of_lt_of_le (by omega) (Nat.pow_le_pow_right (by decide) hR))]
    simp only [Option.bind_eq_bind, Option.bind_some]
    rw [wrap_eq hw (by omega)]
    exact fixedSumFromC_eq hw hR zs (acc + z) (by omega)

theorem fixedSumC_eq {B : Widths} {w : ℕ} (hw : 0 < w) (hR : w - 1 ≤ B.R) {zs : List ℤ}
    (h : (zs.map Int.natAbs).sum < 2 ^ (w - 1)) : fixedSumC B w zs = some (fixedSum w zs) :=
  fixedSumFromC_eq hw hR zs 0 (by simpa using h)

/-- The guards of one window of the descent pass. -/
theorem topDownSumJ_guards {B : Widths} {W T Z : ℕ} {gL gU : ℤ} (hTW : T < W) (hZ : Z + 1 ≤ B.R)
    (hX : 2 * (gL.natAbs + gU.natAbs + Z + T + W + 1) < 2 ^ B.X) {A qa : ℤ} {rs : List (ℤ × ℤ)}
    {n : ℕ} (hn : rs.length ≤ n) (hRn : W + bitlen (n + 1) ≤ B.R) (hA : bitlen A.natAbs ≤ T)
    (hrs : TermsIn Z gL gU rs) (hne : ∀ t ∈ rs, t.1 ≠ 0 ∧ topOf t ≤ qa)
    (hq1 : min (gL + 1) 0 ≤ qa) (hq2 : qa ≤ max (gU + Z) 0) :
    rangeTopC B A qa rs = some (rangeTop A qa rs) ∧
      B.ge (rangeTop A qa rs - W) = some (rangeTop A qa rs - W) ∧
      ((A, qa) :: rs).mapM (hiPartC B (rangeTop A qa rs - W)) =
        some (((A, qa) :: rs).map (hiPart (rangeTop A qa rs - W))) ∧
      (((A, qa) :: rs).map (hiPart (rangeTop A qa rs - W))).all
        (fun z => decide (z.natAbs < 2 ^ W)) = true ∧
      fixedSumC B (W + bitlen (((A, qa) :: rs).map (hiPart (rangeTop A qa rs - W))).length + 1)
          (((A, qa) :: rs).map (hiPart (rangeTop A qa rs - W))) =
        some (fixedSum (W + bitlen (((A, qa) :: rs).map (hiPart (rangeTop A qa rs - W))).length + 1)
          (((A, qa) :: rs).map (hiPart (rangeTop A qa rs - W)))) ∧
      rangeRestC B (rangeTop A qa rs - W) ((A, qa) :: rs) =
        some (rangeRest (rangeTop A qa rs - W) ((A, qa) :: rs)) ∧
      rangeTop A qa rs - W ≤ max (gU + Z) 0 := by
  have hAR : A.natAbs < 2 ^ T := Nat.lt_of_lt_of_le (lt_two_pow_bitlen A.natAbs)
    (Nat.pow_le_pow_right (by decide) hA)
  have hqa : qa.natAbs ≤ gL.natAbs + gU.natAbs + Z + 1 := by
    rw [Int.max_def] at hq2; rw [Int.min_def] at hq1
    split at hq2 <;> split at hq1 <;> omega
  have hwt : rangeTopC B A qa rs = some (rangeTop A qa rs) := by
    unfold rangeTopC rangeTop
    split
    · exact maxTopC_eq (by omega) hrs
    · exact topOfC_eq (by
        show (qa + (bitlen A.natAbs : ℤ)).natAbs < 2 ^ B.X
        have := Int.natAbs_add_le qa (bitlen A.natAbs : ℤ); omega)
  have hwt1 : min (gL + 1) 0 ≤ rangeTop A qa rs := by
    unfold rangeTop; split
    · by_cases hrs0 : rs = []
      · subst hrs0; simp [maxTop]; exact Int.min_le_right _ _
      · have := maxTop_ge_of hrs (fun t ht => (hne t ht).1) hrs0
        exact Int.le_trans (Int.min_le_left _ _) this
    · unfold topOf; simp only; omega
  have hwt2 : rangeTop A qa rs ≤ max (gU + Z) 0 + T := by
    unfold rangeTop; split
    · have := maxTop_le_of hrs; omega
    · unfold topOf; simp only; omega
  have hqb : (rangeTop A qa rs - W).natAbs ≤ gL.natAbs + gU.natAbs + Z + T + W + 1 := by
    rw [Int.max_def] at hwt2; rw [Int.min_def] at hwt1
    split at hwt2 <;> split at hwt1 <;> omega
  have htops : ∀ t ∈ (A, qa) :: rs, t.1 = 0 ∨ topOf t ≤ rangeTop A qa rs - W + W := by
    intro t ht
    rw [show rangeTop A qa rs - (W : ℤ) + W = rangeTop A qa rs by omega]
    rcases List.mem_cons.mp ht with rfl | ht
    · by_cases hA0 : A = 0
      · exact Or.inl hA0
      · right; unfold rangeTop; rw [if_neg hA0]; exact Int.le_refl _
    · right
      unfold rangeTop; split
      · exact le_maxTop ht
      · exact Int.le_trans (hne t ht).2 (by unfold topOf; simp only; omega)
  have hbnd : ∀ t ∈ (A, qa) :: rs, t.1.natAbs < 2 ^ B.R ∧
      t.2.natAbs + (rangeTop A qa rs - W).natAbs < 2 ^ B.X := by
    intro t ht
    rcases List.mem_cons.mp ht with rfl | ht
    · exact ⟨Nat.lt_of_lt_of_le hAR (Nat.pow_le_pow_right (by decide) (by omega)),
        by simp only; omega⟩
    · have h := hrs t ht
      have hb : t.2.natAbs ≤ gL.natAbs + gU.natAbs := by omega
      exact ⟨Nat.lt_of_lt_of_le h.1 (Nat.pow_le_pow_right (by decide) (by omega)), by omega⟩
  have hparts := topDownSumJ_parts_lt (W := W) (A := A) (qa := qa) (rs := rs) (by omega)
    (fun t ht => (hne t ht).2)
  have hsum := sum_natAbs_le hparts
  have hlen' : (((A, qa) :: rs).map (hiPart (rangeTop A qa rs - W))).length = rs.length + 1 := by
    simp
  have hb1 := lt_two_pow_bitlen (rs.length + 1)
  have hb2 := bitlen_mono (Nat.add_le_add_right hn 1)
  refine ⟨hwt, Widths.ge_ok (by omega),
    mapM_eq_some_map fun t ht => hiPartC_eq (hbnd t ht).1 (by omega) (htops t ht) (hbnd t ht).2,
    List.all_eq_true.mpr fun z hz => decide_eq_true (hparts z hz), ?_, rangeRestC_eq hbnd, ?_⟩
  · rw [hlen'] at hsum ⊢
    exact fixedSumC_eq (by omega) (by omega) (by
      rw [show W + bitlen (rs.length + 1) + 1 - 1 = bitlen (rs.length + 1) + W by omega, Nat.pow_add]
      exact Nat.lt_of_le_of_lt hsum (Nat.mul_lt_mul_of_pos_right hb1 (Nat.two_pow_pos W)))
  · unfold rangeTop; split
    · have := maxTop_le_of hrs; omega
    · unfold topOf; simp only; omega

/-- The descent's register-width guard passes: the register has `W + bitlen (n + 1) + 1` bits at
most, and `W + bitlen (n + 1) ≤ R`. -/
theorem topDownSumJ_reg_guard {B : Widths} {W : ℕ} {A qa q : ℤ} {rs : List (ℤ × ℤ)} {n : ℕ}
    (hn : rs.length ≤ n) (hRn : W + bitlen (n + 1) ≤ B.R) :
    B.gw (W + bitlen (((A, qa) :: rs).map (hiPart q)).length + 1) =
      some (W + bitlen (((A, qa) :: rs).map (hiPart q)).length + 1) := by
  apply Widths.gw_ok
  have hlen : (((A, qa) :: rs).map (hiPart q)).length = rs.length + 1 := by simp
  rw [hlen]
  have := bitlen_mono (Nat.add_le_add_right hn 1)
  omega

/-- **The descent never fails a guard**: on terms with significands below `2^Z` and grids in
`[gL, gU]`, at most `n` of them, with `R ≥ Z + 1`, `R ≥ W + bitlen (n + 1)` and `X` above twice the
exponent span plus `Z + T + W`, for any fuel. -/
theorem topDownSumJC_eq {B : Widths} {W T Z : ℕ} {gL gU : ℤ} (hTW : T < W) (hZ : Z + 1 ≤ B.R)
    (hX : 2 * (gL.natAbs + gU.natAbs + Z + T + W + 1) < 2 ^ B.X) :
    ∀ (fuel : ℕ) (A qa : ℤ) (rs : List (ℤ × ℤ)) (n : ℕ), rs.length ≤ n →
      W + bitlen (n + 1) ≤ B.R → bitlen A.natAbs ≤ T → TermsIn Z gL gU rs →
      (∀ t ∈ rs, t.1 ≠ 0 ∧ topOf t ≤ qa) → min (gL + 1) 0 ≤ qa → qa ≤ max (gU + Z) 0 →
      topDownSumJC B W T fuel A qa rs = some (topDownSumJ W T fuel A qa rs) := by
  intro fuel
  induction fuel with
  | zero =>
    intro A qa rs n hn hRn hA hrs hne hq1 hq2
    obtain ⟨h1, h2, h3, h4, h5, h6, _⟩ := topDownSumJ_guards hTW hZ hX hn hRn hA hrs hne hq1 hq2
    unfold topDownSumJC topDownSumJ
    rw [h1]
    simp only [Option.bind_eq_bind, Option.bind_some]
    rw [h2]
    simp only [Option.bind_some]
    rw [h3]
    simp only [Option.bind_some]
    rw [if_pos h4, if_pos h4, topDownSumJ_reg_guard hn hRn]
    simp only [Option.bind_some]
    rw [h5]
    simp only [Option.bind_some]
    rw [h6]
    simp only [Option.bind_some]
    split <;> rfl
  | succ k ih =>
    intro A qa rs n hn hRn hA hrs hne hq1 hq2
    obtain ⟨h1, h2, h3, h4, h5, h6, hq2'⟩ := topDownSumJ_guards hTW hZ hX hn hRn hA hrs hne hq1 hq2
    unfold topDownSumJC topDownSumJ
    rw [h1]
    simp only [Option.bind_eq_bind, Option.bind_some]
    rw [h2]
    simp only [Option.bind_some]
    rw [h3]
    simp only [Option.bind_some]
    rw [if_pos h4, if_pos h4, topDownSumJ_reg_guard hn hRn]
    simp only [Option.bind_some]
    rw [h5]
    simp only [Option.bind_some]
    rw [h6]
    simp only [Option.bind_some]
    split
    · rfl
    · rename_i hstop
      have hacc : A = 0 ∨ rangeTop A qa rs - W ≤ qa := by
        by_cases hA0 : A = 0
        · exact Or.inl hA0
        · right; unfold rangeTop topOf; rw [if_neg hA0]; simp only; omega
      rw [rangeRest_acc hacc] at hstop ⊢
      have hN := Nat.le_of_not_lt (fun h => hstop (Or.inr h))
      have hne' : rangeRest (rangeTop A qa rs - W) rs ≠ [] := fun h => hstop (Or.inl h)
      have hrs' : TermsIn Z gL gU (rangeRest (rangeTop A qa rs - W) rs) := by
        intro t' ht'
        obtain ⟨_, _, t, ht, h1, h2, _⟩ := mem_rangeRest ht'
        exact ⟨Nat.lt_of_le_of_lt h2 (hrs t ht).1, by rw [h1]; exact (hrs t ht).2.1,
          by rw [h1]; exact (hrs t ht).2.2⟩
      have hq1' : min (gL + 1) 0 ≤ rangeTop A qa rs - W := by
        obtain ⟨t', ht'⟩ := List.exists_mem_of_ne_nil _ hne'
        obtain ⟨h0, htop, t, ht, h1, _, _⟩ := mem_rangeRest ht'
        have hb := bitlen_pos (n := t'.1.natAbs) (by omega)
        have := (hrs t ht).2.1
        unfold topOf at htop
        exact Int.le_trans (Int.min_le_left _ _) (by omega)
      exact ih _ _ _ n (Nat.le_trans (length_rangeRest _ _) hn) hRn hN hrs'
        (fun t' ht' => by obtain ⟨h0, htop, _⟩ := mem_rangeRest ht'; exact ⟨h0, htop⟩) hq1' hq2'

/-- **The descent's last grid is bounded** by the terms' exponent span. -/
theorem topDownSumJ_q_bound {W T Z : ℕ} {gL gU : ℤ} (hTW : T < W) :
    ∀ (fuel : ℕ) (A qa : ℤ) (rs : List (ℤ × ℤ)), bitlen A.natAbs ≤ T → TermsIn Z gL gU rs →
      (∀ t ∈ rs, t.1 ≠ 0 ∧ topOf t ≤ qa) → min (gL + 1) 0 ≤ qa → qa ≤ max (gU + Z) 0 →
      ∀ {N q : ℤ} {rs' : List (ℤ × ℤ)}, topDownSumJ W T fuel A qa rs = some (N, q, rs') →
        q.natAbs ≤ gL.natAbs + gU.natAbs + Z + T + W + 1 := by
  intro fuel
  induction fuel with
  | zero =>
    intro A qa rs hA hrs hne hq1 hq2 N q rs' h
    have hwt1 : min (gL + 1) 0 ≤ rangeTop A qa rs := by
      unfold rangeTop; split
      · by_cases hrs0 : rs = []
        · subst hrs0; simp [maxTop]; exact Int.min_le_right _ _
        · exact Int.le_trans (Int.min_le_left _ _)
            (maxTop_ge_of hrs (fun t ht => (hne t ht).1) hrs0)
      · unfold topOf; simp only; omega
    have hwt2 : rangeTop A qa rs ≤ max (gU + Z) 0 + T := by
      unfold rangeTop; split
      · have := maxTop_le_of hrs; omega
      · unfold topOf; simp only; omega
    unfold topDownSumJ at h
    simp only at h
    split at h
    · split at h
      · simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨_, rfl, _⟩ := h
        rw [Int.max_def] at hwt2; rw [Int.min_def] at hwt1
        split at hwt2 <;> split at hwt1 <;> omega
      · simp at h
    · simp at h
  | succ k ih =>
    intro A qa rs hA hrs hne hq1 hq2 N q rs' h
    have hwt1 : min (gL + 1) 0 ≤ rangeTop A qa rs := by
      unfold rangeTop; split
      · by_cases hrs0 : rs = []
        · subst hrs0; simp [maxTop]; exact Int.min_le_right _ _
        · exact Int.le_trans (Int.min_le_left _ _)
            (maxTop_ge_of hrs (fun t ht => (hne t ht).1) hrs0)
      · unfold topOf; simp only; omega
    have hwt2 : rangeTop A qa rs ≤ max (gU + Z) 0 + T := by
      unfold rangeTop; split
      · have := maxTop_le_of hrs; omega
      · unfold topOf; simp only; omega
    unfold topDownSumJ at h
    simp only at h
    split at h
    · split at h
      · simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨_, rfl, _⟩ := h
        rw [Int.max_def] at hwt2; rw [Int.min_def] at hwt1
        split at hwt2 <;> split at hwt1 <;> omega
      · rename_i hstop
        have hacc : A = 0 ∨ rangeTop A qa rs - W ≤ qa := by
          by_cases hA0 : A = 0
          · exact Or.inl hA0
          · right; unfold rangeTop topOf; rw [if_neg hA0]; simp only; omega
        rw [rangeRest_acc hacc] at hstop h
        have hN := Nat.le_of_not_lt (fun h => hstop (Or.inr h))
        have hne' : rangeRest (rangeTop A qa rs - W) rs ≠ [] := fun h => hstop (Or.inl h)
        have hrs' : TermsIn Z gL gU (rangeRest (rangeTop A qa rs - W) rs) := by
          intro t' ht'
          obtain ⟨_, _, t, ht, h1, h2, _⟩ := mem_rangeRest ht'
          exact ⟨Nat.lt_of_le_of_lt h2 (hrs t ht).1, by rw [h1]; exact (hrs t ht).2.1,
            by rw [h1]; exact (hrs t ht).2.2⟩
        have hq1' : min (gL + 1) 0 ≤ rangeTop A qa rs - W := by
          obtain ⟨t', ht'⟩ := List.exists_mem_of_ne_nil _ hne'
          obtain ⟨h0, htop, t, ht, h1, _, _⟩ := mem_rangeRest ht'
          have hb := bitlen_pos (n := t'.1.natAbs) (by omega)
          have := (hrs t ht).2.1
          unfold topOf at htop
          exact Int.le_trans (Int.min_le_left _ _) (by omega)
        have hq2' : rangeTop A qa rs - W ≤ max (gU + Z) 0 := by
          unfold rangeTop; split
          · have := maxTop_le_of hrs; omega
          · unfold topOf; simp only; omega
        exact ih _ _ _ hN hrs'
          (fun t' ht' => by obtain ⟨h0, htop, _⟩ := mem_rangeRest ht'; exact ⟨h0, htop⟩) hq1' hq2' h
    · simp at h

theorem potential_le_mul {Z : ℕ} : ∀ {ts : List (ℤ × ℤ)}, (∀ t ∈ ts, t.1.natAbs < 2 ^ Z) →
    potential ts ≤ ts.length * Z
  | [], _ => by simp [potential]
  | t :: ts, h => by
    rw [potential_cons, List.length_cons, Nat.succ_mul]
    have h1 := bitlen_le_of_lt (h t List.mem_cons_self)
    have h2 := potential_le_mul (ts := ts) fun u hu => h u (List.mem_cons_of_mem _ hu)
    omega

theorem potentialC_eq {B : Widths} {Z : ℕ} : ∀ {ts : List (ℤ × ℤ)},
    (∀ t ∈ ts, t.1.natAbs < 2 ^ Z) → ts.length * Z < 2 ^ B.R →
      potentialC B ts = some (potential ts)
  | [], _, _ => rfl
  | t :: ts, h, hX => by
    have hle := potential_le_mul (ts := t :: ts) h
    have hX' : ts.length * Z < 2 ^ B.R := by
      have : ts.length * Z ≤ (t :: ts).length * Z := Nat.mul_le_mul_right _ (by simp)
      omega
    show (potentialC B ts).bind (fun r => B.gn (bitlen t.1.natAbs + r)) = some (potential (t :: ts))
    rw [potentialC_eq (fun u hu => h u (List.mem_cons_of_mem _ hu)) hX']
    simp only [Option.bind_some]
    rw [potential_cons] at hle ⊢
    exact Widths.gn_ok (by omega)

theorem TermsIn.nonzero {Z : ℕ} {gL gU : ℤ} {ts : List (ℤ × ℤ)} (h : TermsIn Z gL gU ts) :
    TermsIn Z gL gU (nonzero ts) := fun t ht => h t (mem_nonzero.mp ht).1

/-- **The descent from the top never fails a guard.** -/
theorem topDownSumAllJC_eq {B : Widths} {W T Z : ℕ} {gL gU : ℤ} (hTW : T < W) (hZ : Z + 1 ≤ B.R)
    (hX : 2 * (gL.natAbs + gU.natAbs + Z + T + W + 1) < 2 ^ B.X) {ts : List (ℤ × ℤ)}
    (hts : TermsIn Z gL gU ts) (hRn : W + bitlen (ts.length + 1) ≤ B.R)
    (hXn : ts.length * Z < 2 ^ B.R) :
    topDownSumAllJC B W T ts = some (topDownSumAllJ W T ts) := by
  have hnz := hts.nonzero
  have hlen := length_nonzero ts
  unfold topDownSumAllJC topDownSumAllJ
  simp only
  rw [potentialC_eq (fun t ht => (hnz t ht).1)
    (Nat.lt_of_le_of_lt (Nat.mul_le_mul_right _ hlen) hXn)]
  simp only [Option.bind_eq_bind, Option.bind_some]
  rw [maxTopC_eq (by omega) hnz]
  simp only [Option.bind_some]
  have hq1 : min (gL + 1) 0 ≤ maxTop (nonzero ts) := by
    by_cases h0 : nonzero ts = []
    · rw [h0]; simp [maxTop]; exact Int.min_le_right _ _
    · exact Int.le_trans (Int.min_le_left _ _)
        (maxTop_ge_of hnz (fun t ht => (mem_nonzero.mp ht).2) h0)
  exact topDownSumJC_eq hTW hZ hX _ 0 _ _ ts.length hlen hRn (by simp [bitlen]) hnz
    (fun t ht => ⟨(mem_nonzero.mp ht).2, le_maxTop ht⟩) hq1 (maxTop_le_of hnz)

theorem topDownSumAllJ_q_bound {W T Z : ℕ} {gL gU : ℤ} (hTW : T < W) {ts : List (ℤ × ℤ)}
    (hts : TermsIn Z gL gU ts) {N q : ℤ} {rs' : List (ℤ × ℤ)}
    (h : topDownSumAllJ W T ts = some (N, q, rs')) :
    q.natAbs ≤ gL.natAbs + gU.natAbs + Z + T + W + 1 := by
  have hnz := hts.nonzero
  have hq1 : min (gL + 1) 0 ≤ maxTop (nonzero ts) := by
    by_cases h0 : nonzero ts = []
    · rw [h0]; simp [maxTop]; exact Int.min_le_right _ _
    · exact Int.le_trans (Int.min_le_left _ _)
        (maxTop_ge_of hnz (fun t ht => (mem_nonzero.mp ht).2) h0)
  exact topDownSumJ_q_bound hTW _ 0 _ _ (by simp [bitlen]) hnz
    (fun t ht => ⟨(mem_nonzero.mp ht).2, le_maxTop ht⟩) hq1 (maxTop_le_of hnz) h

/-! ## The sign and the round to nearest even of a sum -/

namespace Checked

variable (B : Widths)

def signSumJC (W : ℕ) (ts : List (ℤ × ℤ)) : Option ℤ := do
  let T ← B.gi (bitlen (nonzero ts).length)
  let r ← topDownSumAllJC B W T ts
  pure (match r with
    | some (N, _, _) => N.sign
    | none => 0)

def queryTermC (N q s K h : ℤ) : Option (ℤ × ℤ) := do
  let sK ← B.gv (s * K)
  let d ← B.ge (h - q)
  let P ← B.gv (sK * 2 ^ d.toNat)
  let v ← B.gv (N - P)
  pure (v, q)

def roundSumJC (p : ℕ) (emin emax : ℤ) (W : ℕ) (ts : List (ℤ × ℤ)) : Option (Option ℚ) := do
  let T ← B.gi (bitlen (nonzero ts).length + p + 3)
  let r ← topDownSumAllJC B W T ts
  match r with
  | none => pure none
  | some (N, q, rs') =>
    if rs' = [] then roundExactC B p emin emax N q
    else do
      let eH ← B.ge (q + bitlen N.natAbs - 1)
      let eH2 ← B.ge (eH + 2)
      let lo ← B.ge (emin - p)
      if eH2 ≤ lo then pure (some 0)
      else do
        let hiH ← B.ge (q + bitlen N.natAbs + 1)
        let Kmax ← B.gv (2 ^ (p + 4))
        let s := N.sign
        let Mg ← roundByCmpC B p emin
          (fun K h => if 0 ≤ K ∧ K < Kmax ∧ q ≤ h ∧ h ≤ hiH then do
              let t ← queryTermC B N q s K h
              let v ← signSumJC B W (t :: rs')
              B.gv (s * v)
            else some 0)
          eH (shiftFloorC B N.natAbs q)
        finishRNEC B p emax s Mg

end Checked

theorem signSumJC_eq {B : Widths} {W Z : ℕ} {gL gU : ℤ} {ts : List (ℤ × ℤ)}
    (hTW : bitlen ts.length < W) (hZ : Z + 1 ≤ B.R)
    (hX : 2 * (gL.natAbs + gU.natAbs + Z + W + W + 1) < 2 ^ B.X)
    (hts : TermsIn Z gL gU ts) (hRn : W + bitlen (ts.length + 1) ≤ B.R)
    (hXn : ts.length * Z < 2 ^ B.R) : signSumJC B W ts = some (signSumJ W ts) := by
  have hbl : bitlen (nonzero ts).length ≤ bitlen ts.length := bitlen_mono (length_nonzero ts)
  unfold signSumJC signSumJ
  rw [Widths.gi_ok (by omega)]
  simp only [Option.bind_eq_bind, Option.bind_some]
  rw [topDownSumAllJC_eq (T := bitlen (nonzero ts).length) (by omega) hZ (by omega) hts hRn hXn]
  rfl

theorem queryTermC_eq {B : Widths} {N q s K h : ℤ} {p : ℕ} (hs : s.natAbs ≤ 1) (hK0 : 0 ≤ K)
    (hK : K < 2 ^ (p + 4)) (hh1 : q ≤ h) (hh : h ≤ q + bitlen N.natAbs + 1)
    (hR : bitlen N.natAbs + p + 6 ≤ B.R) (hX : bitlen N.natAbs + 1 < 2 ^ B.X) :
    queryTermC B N q s K h = some (queryTerm N q s K h) := by
  have hKn : K.toNat < 2 ^ (p + 4) := by
    have : ((2 ^ (p + 4) : ℕ) : ℤ) = (2 : ℤ) ^ (p + 4) := by rw [Int.natCast_pow]; rfl
    omega
  have hsK : (s * K).natAbs ≤ K.toNat := by
    rw [Int.natAbs_mul]
    have : K.natAbs = K.toNat := by omega
    rw [this]
    calc s.natAbs * K.toNat ≤ 1 * K.toNat := Nat.mul_le_mul_right _ hs
      _ = K.toNat := Nat.one_mul _
  have hR1 : 2 ^ (p + 4) ≤ 2 ^ B.R := Nat.pow_le_pow_right (by decide) (by omega)
  unfold queryTermC queryTerm
  rw [Widths.gv_ok (by omega), Widths.ge_ok (by omega)]
  simp only [Option.bind_eq_bind, Option.bind_some]
  have hP : (s * K * 2 ^ (h - q).toNat).natAbs < 2 ^ (bitlen N.natAbs + p + 5) := by
    rw [Int.natAbs_mul, Int.natAbs_pow]
    have hd : (h - q).toNat ≤ bitlen N.natAbs + 1 := by omega
    calc (s * K).natAbs * Int.natAbs 2 ^ (h - q).toNat ≤ K.toNat * 2 ^ (h - q).toNat :=
          Nat.mul_le_mul_right _ hsK
      _ < 2 ^ (p + 4) * 2 ^ (h - q).toNat := Nat.mul_lt_mul_of_pos_right hKn (Nat.two_pow_pos _)
      _ = 2 ^ (p + 4 + (h - q).toNat) := (Nat.pow_add _ _ _).symm
      _ ≤ 2 ^ (bitlen N.natAbs + p + 5) := Nat.pow_le_pow_right (by decide) (by omega)
  rw [Widths.gv_ok (Nat.lt_of_lt_of_le hP (Nat.pow_le_pow_right (by decide) (by omega)))]
  simp only [Option.bind_some]
  have hQ := query_natAbs_lt (N := N) (q := q) (s := s) (K := K) (h := h) (p := p) hs hK0 hK hh
  unfold queryTerm at hQ
  rw [Widths.gv_ok (Nat.lt_of_lt_of_le hQ (Nat.pow_le_pow_right (by decide) hR))]
  rfl

/-- The integer-part guess `shiftFloor |N| q` passes its guards on every grid `roundByCmp` can
pick, and is at most `2^D`. -/
theorem shiftFloorC_ok {B : Widths} {p D : ℕ} {N q eH emin : ℤ} (hN : N.natAbs < 2 ^ D)
    (hpD : p + 2 ≤ D) (hR : D + 3 ≤ B.R) (heH : q + (bitlen N.natAbs : ℤ) - 1 = eH)
    (hX : 2 * q.natAbs + D + emin.natAbs + p + 3 < 2 ^ B.X) :
    ∀ g, eH - p ≤ g → g ≤ max (eH + 1) emin - ((p : ℤ) - 1) →
      shiftFloorC B N.natAbs q g = some (shiftFloor N.natAbs q g) ∧
        (shiftFloor N.natAbs q g).natAbs ≤ 2 ^ D := by
  intro g hg1 hg2
  have hbN := bitlen_le_of_lt hN
  have hpD' : 2 ^ (p + 1) ≤ 2 ^ D := Nat.pow_le_pow_right (by decide) (by omega)
  have hDR : 2 ^ D ≤ 2 ^ B.R := Nat.pow_le_pow_right (by decide) (by omega)
  have hgb := grid_natAbs_of hg1 hg2
  obtain ⟨hl, hb⟩ := shiftFloor_bound (p := p) hN (by omega) (g := g) (q := q) (by omega)
  exact ⟨shiftFloorC_eq (by omega) (by omega)
    (fun h => Nat.lt_of_lt_of_le (hl h) (Nat.le_trans hpD' hDR)), by omega⟩

theorem sign_natAbs_le (N : ℤ) : N.sign.natAbs ≤ 1 := by
  rcases Int.lt_trichotomy N 0 with h' | h' | h'
  · rw [Int.sign_eq_neg_one_of_neg h']; decide
  · rw [h']; decide
  · rw [Int.sign_eq_one_of_pos h']; decide

theorem signSumJ_natAbs_le (W : ℕ) (ts : List (ℤ × ℤ)) : (signSumJ W ts).natAbs ≤ 1 := by
  unfold signSumJ
  split
  · exact sign_natAbs_le _
  · decide

/-- **The sign oracle of `roundSumJ` never fails a guard.** -/
theorem sumOracleC_eq {B : Widths} {p Z W D n : ℕ} {gL gU N q : ℤ} {rs' : List (ℤ × ℤ)}
    (hrs' : TermsIn Z gL gU rs') (hlen : rs'.length ≤ n) (hW : bitlen (n + 1) < W)
    (hbN : bitlen N.natAbs ≤ D) (hR1 : Z + D + p + 7 ≤ B.R) (hR2 : W + bitlen (n + 2) ≤ B.R)
    (hX : 2 * (2 * (gL.natAbs + gU.natAbs + q.natAbs) + (Z + D + p + 6) + W + W + 1) +
      D + 2 < 2 ^ B.X)
    (hXn : (n + 1) * (Z + D + p + 6) < 2 ^ B.R) (K h : ℤ) :
    (if 0 ≤ K ∧ K < 2 ^ (p + 4) ∧ q ≤ h ∧ h ≤ q + (bitlen N.natAbs : ℤ) + 1 then
        (queryTermC B N q N.sign K h).bind fun t =>
          (signSumJC B W (t :: rs')).bind fun v => B.gv (N.sign * v)
      else some 0) =
    some (if 0 ≤ K ∧ K < 2 ^ (p + 4) ∧ q ≤ h ∧ h ≤ q + (bitlen N.natAbs : ℤ) + 1 then
        N.sign * signSumJ W (queryTerm N q N.sign K h :: rs') else 0) := by
  split
  · rename_i hc
    obtain ⟨hK0, hK, hh1, hh2⟩ := hc
    have hs := sign_natAbs_le N
    rw [queryTermC_eq hs hK0 hK hh1 hh2 (by omega) (by omega)]
    simp only [Option.bind_some]
    have hQ := query_natAbs_lt (N := N) (q := q) (s := N.sign) (K := K) (h := h) (p := p)
      hs hK0 hK hh2
    have hQ' : (queryTerm N q N.sign K h).1.natAbs < 2 ^ (Z + D + p + 6) :=
      Nat.lt_of_lt_of_le hQ (Nat.pow_le_pow_right (by decide) (by omega))
    have hterms : TermsIn (Z + D + p + 6) (-(gL.natAbs + gU.natAbs + q.natAbs : ℤ))
        (gL.natAbs + gU.natAbs + q.natAbs : ℤ) (queryTerm N q N.sign K h :: rs') := by
      intro t ht
      rcases List.mem_cons.mp ht with rfl | ht
      · refine ⟨hQ', ?_, ?_⟩ <;> unfold queryTerm <;> simp only <;> omega
      · have := hrs' t ht
        refine ⟨Nat.lt_of_lt_of_le this.1 (Nat.pow_le_pow_right (by decide) (by omega)),
          by omega, by omega⟩
    have hl : (queryTerm N q N.sign K h :: rs').length ≤ n + 1 := by
      simp only [List.length_cons]; omega
    have hbl' := bitlen_mono hl
    have hbl'' : bitlen ((queryTerm N q N.sign K h :: rs').length + 1) ≤ bitlen (n + 2) :=
      bitlen_mono (by omega)
    have hXn' : (queryTerm N q N.sign K h :: rs').length * (Z + D + p + 6) < 2 ^ B.R :=
      Nat.lt_of_le_of_lt (Nat.mul_le_mul_right _ hl) hXn
    rw [signSumJC_eq (Z := Z + D + p + 6) (by omega) (by omega) (by omega) hterms
      (by omega) hXn']
    simp only [Option.bind_some]
    apply Widths.gv_ok
    rw [Int.natAbs_mul]
    have : N.sign.natAbs * (signSumJ W (queryTerm N q N.sign K h :: rs')).natAbs ≤ 1 :=
      Nat.le_trans (Nat.mul_le_mul hs (signSumJ_natAbs_le _ _)) (by decide)
    exact Nat.lt_of_le_of_lt this (Nat.one_lt_two_pow (by omega))
  · rfl

set_option maxHeartbeats 4000000 in
/-- **Correct rounding of a sum never fails a guard**: on `n` terms with significands below `2^Z`
and grids in `[gL, gU]`, with `W > bitlen (n + 1) + p + 3`, `D = W + bitlen (n + 1) + 1`,
`R ≥ Z + D + p + 7`, `R ≥ W + bitlen (n + 2)` and `X` as stated. -/
theorem roundSumJC_eq {B : Widths} {p Z W : ℕ} {emin emax gL gU : ℤ} {ts : List (ℤ × ℤ)}
    (hW : bitlen (ts.length + 1) + p + 3 < W) (hts : TermsIn Z gL gU ts)
    (hR1 : Z + (W + bitlen (ts.length + 1) + 1) + p + 7 ≤ B.R)
    (hR2 : W + bitlen (ts.length + 2) ≤ B.R)
    (hX : 8 * (gL.natAbs + gU.natAbs) + 6 * Z + 12 * W + 4 * (W + bitlen (ts.length + 1) + 1) +
      4 * p + emin.natAbs + emax.natAbs + 2 * B.R + 40 < 2 ^ B.X)
    (hRn : (ts.length + 1) * (Z + (W + bitlen (ts.length + 1) + 1) + p + 6) < 2 ^ B.R) :
    roundSumJC B p emin emax W ts = some (roundSumJ p emin emax W ts) := by
  generalize hDdef : W + bitlen (ts.length + 1) + 1 = D at hR1 hX hRn
  generalize hPdef : (ts.length + 1) * (Z + D + p + 6) = Pn at hRn
  have hbl : bitlen (nonzero ts).length ≤ bitlen ts.length := bitlen_mono (length_nonzero ts)
  have hbl1 : bitlen ts.length ≤ bitlen (ts.length + 1) := bitlen_mono (Nat.le_succ _)
  have hbl2 : bitlen (ts.length + 1) ≤ bitlen (ts.length + 2) := bitlen_mono (Nat.le_succ _)
  have hXn : ts.length * Z < 2 ^ B.R := by
    have : ts.length * Z ≤ (ts.length + 1) * (Z + D + p + 6) :=
      Nat.mul_le_mul (Nat.le_succ _) (by omega)
    omega
  unfold roundSumJC roundSumJ
  rw [Widths.gi_ok (by omega)]
  simp only [Option.bind_eq_bind, Option.bind_some]
  rw [topDownSumAllJC_eq (T := bitlen (nonzero ts).length + p + 3) (by omega) (by omega) (by omega)
    hts (by omega) hXn]
  simp only [Option.bind_some]
  cases hd : topDownSumAllJ W (bitlen (nonzero ts).length + p + 3) ts with
  | none => rfl
  | some r =>
    obtain ⟨N, q, rs'⟩ := r
    simp only
    obtain ⟨N', q', rs'', hd', _, htop, hstop, hlen, hsub, hNb⟩ :=
      topDownSumAllJ_spec (W := W) (T := bitlen (nonzero ts).length + p + 3) (by omega) ts
    rw [hd] at hd'
    simp only [Option.some.injEq, Prod.mk.injEq] at hd'
    obtain ⟨rfl, rfl, rfl⟩ := hd'
    have hqb := topDownSumAllJ_q_bound (by omega) hts hd
    have hN : N.natAbs < 2 ^ D := by
      have := bitlen_mono (Nat.add_le_add_right (length_nonzero ts) 1)
      exact Nat.lt_of_le_of_lt hNb (Nat.pow_lt_pow_right (by decide) (by omega))
    have hbN := bitlen_le_of_lt hN
    have hrs' : TermsIn Z gL gU rs' := by
      intro t' ht'
      obtain ⟨t, ht, h1, h2⟩ := hsub t' ht'
      exact ⟨Nat.lt_of_le_of_lt h2 (hts t ht).1, by rw [h1]; exact (hts t ht).2.1,
        by rw [h1]; exact (hts t ht).2.2⟩
    have hlen' : rs'.length ≤ ts.length := Nat.le_trans hlen (length_nonzero ts)
    clear hd htop hsub hstop hNb hlen
    split
    · exact roundExactC_eq hN (by omega) (by omega) (by omega)
    · rw [Widths.ge_ok (by omega)]
      simp only [Option.bind_some]
      rw [Widths.ge_ok (by omega), Widths.ge_ok (by omega)]
      simp only [Option.bind_some]
      split
      · rfl
      · rw [Widths.ge_ok (by omega)]
        simp only [Option.bind_some]
        have hK4 : ((2 : ℤ) ^ (p + 4)).natAbs < 2 ^ B.R := by
          rw [Int.natAbs_pow]
          exact Nat.pow_lt_pow_right (by decide) (by omega)
        rw [Widths.gv_ok hK4]
        simp only [Option.bind_some]
        generalize heH : q + (bitlen N.natAbs : ℤ) - 1 = eH
        have heHb : eH.natAbs ≤ q.natAbs + D := by omega
        have hW1 : bitlen (ts.length + 1) < W := by omega
        have hXo : 2 * (2 * (gL.natAbs + gU.natAbs + q.natAbs) + (Z + D + p + 6) + W + W + 1) +
            D + 2 < 2 ^ B.X := by omega
        have hXp : (ts.length + 1) * (Z + D + p + 6) < 2 ^ B.R := by omega
        have hcmp : ∀ (K h : ℤ), K.natAbs ≤ 2 * 2 ^ D + 3 →
            h.natAbs ≤ eH.natAbs + emin.natAbs + p + 3 →
            (if 0 ≤ K ∧ K < 2 ^ (p + 4) ∧ q ≤ h ∧ h ≤ q + (bitlen N.natAbs : ℤ) + 1 then
              (queryTermC B N q N.sign K h).bind fun t =>
                (signSumJC B W (t :: rs')).bind fun v => B.gv (N.sign * v)
              else some 0) =
            some (if 0 ≤ K ∧ K < 2 ^ (p + 4) ∧ q ≤ h ∧ h ≤ q + (bitlen N.natAbs : ℤ) + 1 then
              N.sign * signSumJ W (queryTerm N q N.sign K h :: rs') else 0) :=
          fun K h _ _ => sumOracleC_eq (n := ts.length) hrs' hlen' hW1 hbN hR1 hR2 hXo hXp K h
        have hRF : 2 * 2 ^ D + 4 < 2 ^ B.R := by
          have := Nat.pow_le_pow_right (n := 2) (by decide) (show D + 3 ≤ B.R by omega)
          have e3 : 2 ^ (D + 3) = 8 * 2 ^ D := by rw [Nat.pow_add]; omega
          omega
        have hXe : eH.natAbs + emin.natAbs + p + 4 < 2 ^ B.X := by omega
        have hXs : 2 * q.natAbs + D + emin.natAbs + p + 3 < 2 ^ B.X := by omega
        rw [roundByCmpC_eq (FB := 2 ^ D) hXe hRF
          (shiftFloorC_ok hN (by omega) (by omega) heH hXs) hcmp]
        simp only [Option.bind_some]
        obtain ⟨e, e1, e2, hg, hM1, hM2⟩ := roundByCmp_out p emin
          (fun K h => if 0 ≤ K ∧ K < 2 ^ (p + 4) ∧ q ≤ h ∧ h ≤ q + (bitlen N.natAbs : ℤ) + 1 then
            N.sign * signSumJ W (queryTerm N q N.sign K h :: rs') else 0)
          eH (shiftFloor N.natAbs q)
        obtain ⟨g1, _, g3⟩ := gridOf_bounds (p := p) (emin := emin) e1 e2
        have hF := (shiftFloorC_ok (B := B) hN (by omega) (by omega) heH (by omega) _ g1
          (gridOf_bounds (p := p) (emin := emin) e1 e2).2.1).2
        generalize shiftFloor N.natAbs q (gridOf p emin e) = F0 at hM1 hM2 hF
        generalize (roundByCmp p emin _ eH (shiftFloor N.natAbs q)) = Mg at hg hM1 hM2 ⊢
        have hDR : 2 ^ D + 2 < 2 ^ B.R := by
          have := Nat.pow_le_pow_right (n := 2) (by decide) (show D + 3 ≤ B.R by omega)
          have e3 : 2 ^ (D + 3) = 8 * 2 ^ D := by rw [Nat.pow_add]; omega
          omega
        exact finishRNEC_eq (by omega) (by omega) (by rw [hg]; omega)

/-! ## The check and the exact path -/

namespace Checked

variable (B : Widths)

def splitExpIntC (b : ℕ) (xs : List (ℤ × ℤ)) : Option ℤ := do
  let g ← gridIntC B b b xs
  B.ge (g + b)

def truncationGridIntC (b W : ℕ) (xs ys : List (ℤ × ℤ)) : Option ℤ := do
  let ex ← splitExpIntC B b xs
  let ey ← splitExpIntC B b ys
  let e ← B.ge (ex + ey)
  B.ge (e - W)

/-- An engine output read back: the integer is guarded, and so is the grid sum. -/
def sliceProductIntC (mult : MatrixMultiplier) (sl sl' : Slice) : Option (Option (ℤ × ℤ)) :=
  match mult sl.coeffs sl'.coeffs with
  | none => some none
  | some v =>
    if v.den = 1 then do
      let z ← B.gv v.num
      let g ← B.ge (sl.grid + sl'.grid)
      pure (some (z, g))
    else some none

def pairIntC (mult : MatrixMultiplier) (sx sy : List Slice) (pr : ℕ × ℕ) : Option (Option (ℤ × ℤ)) :=
  sliceProductIntC B mult (sx.getD pr.1 default) (sy.getD pr.2 default)

def floorPartC (q : ℤ) (t : ℤ × ℤ) : Option ℤ :=
  if q ≤ t.2 then do
    let d ← B.ge (t.2 - q)
    B.gv (t.1 * 2 ^ d.toNat)
  else do
    let d ← B.ge (q - t.2)
    B.gv (t.1 / 2 ^ d.toNat)

def roundEnclosureBC (p : ℕ) (emin emax : ℤ) (N q K c : ℤ) (n : ℕ) : Option (Option ℚ) := do
  let q0 := min q c
  let dq ← B.ge (q - q0)
  let dc ← B.ge (c - q0)
  let H ← B.gv (N * 2 ^ dq.toNat)
  let Kc ← B.gv (K * 2 ^ dc.toNat)
  let nq ← B.gv ((n : ℤ) * 2 ^ dq.toNat)
  let Bd ← B.gv (Kc + nq)
  let lo ← B.gv (H - Bd)
  let hi ← B.gv (H + Bd)
  let r1 ← roundExactC B p emin emax lo q0
  let r2 ← roundExactC B p emin emax hi q0
  pure (match r1, r2 with
    | some w, some w' => if w = w' then some w else none
    | _, _ => none)

def ozaki1TestIC (mult : MatrixMultiplier) (p : ℕ) (emin emax : ℤ) (b s W : ℕ) (xs ys : List (ℤ × ℤ)) :
    Option (Option ℚ) := do
  let sx ← splitIntFromC B b s b xs
  let sy ← splitIntFromC B b s b ys
  let lo ← (trianglePairs s).mapM (pairIntC B mult sx.1 sy.1)
  match lo.mapM id with
  | none => pure none
  | some ts => do
    let q ← truncationGridIntC B b W xs ys
    let parts ← ts.mapM (floorPartC B q)
    let w ← B.gi (W + bitlen (ts.length * (xs.length + 2)) + 1)
    let N ← fixedSumC B w parts
    let ex ← splitExpIntC B b xs
    let ey ← splitExpIntC B b ys
    let e ← B.ge (ex + ey)
    let sb ← B.gi (s * (b + 1))
    let c ← B.ge (e - (sb : ℤ))
    let K ← B.gv (((s + 1) * xs.length : ℕ) : ℤ)
    roundEnclosureBC B p emin emax N q K c ts.length

def vanishIntC (b s : ℕ) (xs ys : List (ℤ × ℤ)) : Option Bool := do
  let sx ← splitIntFromC B b s b xs
  let sy ← splitIntFromC B b s b ys
  pure (sx.2.all (fun r => r.1 == 0) && sy.2.all (fun r => r.1 == 0))

/-- `find?` with a guarded predicate. -/
def findC (f : ℕ → Option Bool) : List ℕ → Option (Option ℕ)
  | [] => some none
  | a :: l => do
    let v ← f a
    if v then pure (some a) else findC f l

def ozaki1ExactFallbackIC (mult : MatrixMultiplier) (p : ℕ) (emin emax : ℤ) (b smax : ℕ)
    (xs ys : List (ℤ × ℤ)) : Option (Option ℚ) := do
  let so ← findC (fun s => vanishIntC B b s xs ys) (List.range' 1 smax)
  match so with
  | none => pure none
  | some s => do
    let sx ← splitIntFromC B b s b xs
    let sy ← splitIntFromC B b s b ys
    let lo ← (slicePairs sx.1 sy.1).mapM (fun pr => sliceProductIntC B mult pr.1 pr.2)
    match lo.mapM id with
    | none => pure none
    | some ts => do
      let W' ← B.gi (bitlen (ts.length + 1) + p + 4)
      roundSumJC B p emin emax W' ts

/-- **Correctly rounded Ozaki-I in integers, every integer guarded.** -/
def ozaki1CRIC (mult : MatrixMultiplier) (p : ℕ) (emin emax : ℤ) (b W : ℕ) (ss : List ℕ) (smax : ℕ)
    (xs ys : List (ℤ × ℤ)) : Option (Option ℚ) :=
  match ss with
  | [] => ozaki1ExactFallbackIC B mult p emin emax b smax xs ys
  | s :: ss => do
    let r ← ozaki1TestIC B mult p emin emax b s W xs ys
    match r with
    | some w => pure (some w)
    | none => ozaki1CRIC mult p emin emax b W ss smax xs ys

end Checked

/-- The slice grids are bounded by the entries' exponents, the starting grid and the slice count. -/
theorem splitIntFrom_grid_bound {b p EM : ℕ} : ∀ (s : ℕ) (prev : ℤ) (xs : List (ℤ × ℤ)),
    EntriesIn p EM xs → ∀ sl ∈ (splitIntFrom b s prev xs).1,
      sl.grid.natAbs ≤ max (p + 1 + EM + b) prev.natAbs + s * (b + 1)
  | 0, _, _, _ => by simp [splitIntFrom]
  | s + 1, prev, xs, hx => by
    intro sl hsl
    simp only [splitIntFrom, List.mem_cons] at hsl
    have hg := gridInt_natAbs_le (b := b) (prev := prev) hx
    have hx' : EntriesIn p EM (xs.map (restInt (gridInt b prev xs))) := by
      intro c hc
      obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hc
      obtain ⟨h1, h2⟩ := restInt_natAbs_le (gridInt b prev xs) a
      exact ⟨Nat.lt_of_le_of_lt h1 (hx a ha).1, by rw [h2]; exact (hx a ha).2⟩
    have e : (s + 1) * (b + 1) = s * (b + 1) + (b + 1) := by rw [Nat.add_mul, Nat.one_mul]
    rcases hsl with rfl | hsl
    · simp only; rw [e]; omega
    · have := splitIntFrom_grid_bound s _ _ hx' sl hsl
      rw [e]; omega

theorem splitExpInt_natAbs_le {b p EM : ℕ} {xs : List (ℤ × ℤ)} (hx : EntriesIn p EM xs) :
    (splitExpInt b xs).natAbs ≤ p + 1 + EM + 3 * b + 1 := by
  unfold splitExpInt
  have := gridInt_natAbs_le (b := b) (prev := (b : ℤ)) hx
  have hb : ((b : ℤ)).natAbs = b := by simp
  omega

theorem splitExpIntC_eq {B : Widths} {b p EM : ℕ} {xs : List (ℤ × ℤ)} (hx : EntriesIn p EM xs)
    (hR : p + 1 ≤ B.R) (hX : p + 1 + EM + 3 * b + 2 < 2 ^ B.X) :
    splitExpIntC B b xs = some (splitExpInt b xs) := by
  unfold splitExpIntC
  have hb : ((b : ℤ)).natAbs = b := by simp
  rw [gridIntC_eq hx hR (by rw [hb]; omega)]
  simp only [Option.bind_eq_bind, Option.bind_some]
  have := splitExpInt_natAbs_le (b := b) hx
  unfold splitExpInt at this
  exact Widths.ge_ok (by omega)

theorem truncationGridIntC_eq {B : Widths} {b p EM W : ℕ} {xs ys : List (ℤ × ℤ)}
    (hx : EntriesIn p EM xs) (hy : EntriesIn p EM ys) (hR : p + 1 ≤ B.R)
    (hX : 2 * (p + 1 + EM + 3 * b + 2) + W < 2 ^ B.X) :
    truncationGridIntC B b W xs ys = some (truncationGridInt b W xs ys) := by
  unfold truncationGridIntC truncationGridInt
  rw [splitExpIntC_eq hx hR (by omega), splitExpIntC_eq hy hR (by omega)]
  simp only [Option.bind_eq_bind, Option.bind_some]
  have h1 := splitExpInt_natAbs_le (b := b) hx
  have h2 := splitExpInt_natAbs_le (b := b) hy
  rw [Widths.ge_ok (by omega)]
  simp only [Option.bind_some]
  exact Widths.ge_ok (by omega)

theorem sliceProductIntC_eq {B : Widths} {mult : MatrixMultiplier} {sl sl' : Slice} {z : ℤ}
    (h : mult sl.coeffs sl'.coeffs = some (z : ℚ)) (hz : z.natAbs < 2 ^ B.R)
    (hg : (sl.grid + sl'.grid).natAbs < 2 ^ B.X) :
    sliceProductIntC B mult sl sl' = some (sliceProductInt mult sl sl') := by
  unfold sliceProductIntC sliceProductInt
  rw [h]
  simp only [Option.bind_some, Rat.den_intCast, Rat.num_intCast, ↓reduceIte]
  rw [Widths.gv_ok hz]
  simp only [Option.bind_eq_bind, Option.bind_some]
  rw [Widths.ge_ok hg]
  rfl

theorem findC_eq {f : ℕ → Option Bool} {g : ℕ → Bool} : ∀ {l : List ℕ},
    (∀ a ∈ l, f a = some (g a)) → findC f l = some (l.find? g)
  | [], _ => rfl
  | a :: l, h => by
    unfold findC
    rw [h a List.mem_cons_self]
    simp only [Option.bind_eq_bind, Option.bind_some, Option.pure_def, List.find?_cons]
    cases g a with
    | true => rfl
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte]
      exact findC_eq fun c hc => h c (List.mem_cons_of_mem _ hc)

theorem mapM_id_map {α : Type} (l : List α) : (l.map some).mapM id = some l := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    simp only [List.map_cons, List.mapM_cons, id, ih]
    rfl

theorem floorPartC_eq {B : Widths} {q : ℤ} {t : ℤ × ℤ} (hz : (floorPart q t).natAbs < 2 ^ B.R)
    (hX : t.2.natAbs + q.natAbs < 2 ^ B.X) : floorPartC B q t = some (floorPart q t) := by
  unfold floorPartC
  split
  · rename_i h
    rw [Widths.ge_ok (by omega)]
    simp only [Option.bind_eq_bind, Option.bind_some]
    have e : floorPart q t = t.1 * 2 ^ (t.2 - q).toNat := by unfold floorPart; rw [if_pos h]
    rw [e] at hz ⊢
    exact Widths.gv_ok hz
  · rename_i h
    rw [Widths.ge_ok (by omega)]
    simp only [Option.bind_eq_bind, Option.bind_some]
    have e : floorPart q t = t.1 / 2 ^ (q - t.2).toNat := by unfold floorPart; rw [if_neg h]
    rw [e] at hz ⊢
    exact Widths.gv_ok hz

theorem mul_two_pow_lt {a x d y : ℕ} (ha : a < 2 ^ x) (hd : d ≤ y) : a * 2 ^ d < 2 ^ (x + y) := by
  rw [Nat.pow_add]
  exact Nat.lt_of_lt_of_le (Nat.mul_lt_mul_of_pos_right ha (Nat.two_pow_pos d))
    (Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by decide) hd))

theorem sum_map_const_nat {α : Type} (l : List α) (c : ℕ) :
    (l.map fun _ => c).sum = l.length * c := by
  induction l with
  | nil => simp
  | cons a l ih => simp only [List.map_cons, List.sum_cons, List.length_cons, ih, Nat.succ_mul]; omega

theorem natAbs_listSum_le : ∀ zs : List ℤ, zs.sum.natAbs ≤ (zs.map Int.natAbs).sum
  | [] => by simp
  | z :: zs => by
    simp only [List.sum_cons, List.map_cons]
    have := Int.natAbs_add_le z zs.sum
    have := natAbs_listSum_le zs
    omega

theorem natAbs_mul_two_pow (x : ℤ) (d : ℕ) : (x * 2 ^ d).natAbs = x.natAbs * 2 ^ d := by
  rw [Int.natAbs_mul, Int.natAbs_pow]; rfl

/-- **The enclosure test never fails a guard** when `|N| 2^dq`, `|K| 2^dc` and `n 2^dq` are below
`2^E`, with `D ≥ E + 2`, `D ≥ p + 2`, `R ≥ D + 3`. -/
theorem roundEnclosureBC_eq {B : Widths} {p E D : ℕ} {emin emax N q K c : ℤ} {n : ℕ}
    (hN : N.natAbs * 2 ^ (q - min q c).toNat < 2 ^ E)
    (hK : K.natAbs * 2 ^ (c - min q c).toNat < 2 ^ E)
    (hn : n * 2 ^ (q - min q c).toNat < 2 ^ E) (hED : E + 2 ≤ D) (hpD : p + 2 ≤ D)
    (hR : D + 3 ≤ B.R)
    (hX : 2 * (q.natAbs + c.natAbs) + 2 * D + emin.natAbs + emax.natAbs + 2 * p + 2 * B.R + 8 <
      2 ^ B.X) :
    roundEnclosureBC B p emin emax N q K c n = some (roundEnclosureB p emin emax N q K c n) := by
  have hE2 : 2 ^ (E + 2) ≤ 2 ^ D := Nat.pow_le_pow_right (by decide) hED
  have hDR : 2 ^ D ≤ 2 ^ B.R := Nat.pow_le_pow_right (by decide) (by omega)
  have e2 : 2 ^ (E + 2) = 4 * 2 ^ E := by rw [Nat.pow_add]; omega
  have hq0 : (min q c).natAbs ≤ q.natAbs + c.natAbs := by
    rw [Int.min_def]; split <;> omega
  unfold roundEnclosureBC roundEnclosureB
  simp only
  rw [Widths.ge_ok (by rw [Int.min_def]; split <;> omega),
    Widths.ge_ok (by rw [Int.min_def]; split <;> omega)]
  simp only [Option.bind_eq_bind, Option.bind_some]
  have hH : (N * 2 ^ (q - min q c).toNat).natAbs < 2 ^ E := by rw [natAbs_mul_two_pow]; exact hN
  have hKc : (K * 2 ^ (c - min q c).toNat).natAbs < 2 ^ E := by
    rw [natAbs_mul_two_pow]; exact hK
  have hnq : ((n : ℤ) * 2 ^ (q - min q c).toNat).natAbs < 2 ^ E := by
    rw [natAbs_mul_two_pow, Int.natAbs_natCast]; exact hn
  rw [Widths.gv_ok (by omega), Widths.gv_ok (by omega), Widths.gv_ok (by omega)]
  simp only [Option.bind_some]
  have hBd := Int.natAbs_add_le (K * 2 ^ (c - min q c).toNat) ((n : ℤ) * 2 ^ (q - min q c).toNat)
  rw [Widths.gv_ok (by omega)]
  simp only [Option.bind_some]
  generalize N * 2 ^ (q - min q c).toNat = H at hH ⊢
  generalize K * 2 ^ (c - min q c).toNat + (n : ℤ) * 2 ^ (q - min q c).toNat = Bd at hBd ⊢
  have hlo := Int.natAbs_sub_le H Bd
  have hhi := Int.natAbs_add_le H Bd
  rw [Widths.gv_ok (by omega), Widths.gv_ok (by omega)]
  simp only [Option.bind_some]
  rw [roundExactC_eq (D := D) (by omega) hpD hR (by omega),
    roundExactC_eq (D := D) (by omega) hpD hR (by omega)]
  rfl

theorem sliceProductIntC_exact {B : Widths} {mult : MatrixMultiplier} {b bound s : ℕ}
    (hmult : mult.ExactOn b bound) {x y : List ℚ} (hlen : x.length = y.length)
    (hbound : x.length * (2 ^ b * 2 ^ b) ≤ bound) {sl sl' : Slice}
    (hsl : sl ∈ (split b s x).1) (hsl' : sl' ∈ (split b s y).1) (hRb : bound < 2 ^ B.R)
    (hg : (sl.grid + sl'.grid).natAbs < 2 ^ B.X) :
    sliceProductIntC B mult sl sl' = some (some (exactSliceInt sl sl')) := by
  obtain ⟨he, hb⟩ := multiplier_exact hmult hlen hbound hsl hsl'
  rw [sliceProductIntC_eq he (Nat.lt_of_le_of_lt (Nat.le_trans (natAbs_dotZ_le _ _) hb) hRb) hg,
    sliceProductInt_of_eq he]
  rfl

/-- Every slice grid of a binary vector's integer split is at most `P + s (b + 1)` in magnitude,
`P = p + 1 + EM + b`. -/
theorem splitInt_grid_bound {b p EM s : ℕ} {xs : List (ℤ × ℤ)} (hx : EntriesIn p EM xs) :
    ∀ sl ∈ (split b s (entryVals xs)).1, sl.grid.natAbs ≤ p + 1 + EM + b + s * (b + 1) := by
  intro sl hsl
  rw [← (splitInt_eq b s xs).1] at hsl
  have := splitIntFrom_grid_bound (b := b) s (b : ℤ) xs hx sl hsl
  have hb : ((b : ℤ)).natAbs = b := by simp
  rw [hb] at this
  omega

/-- The requirement on `R` for the check with `s` slices: `D + b + 3`, where `D` bounds the
enclosure's integers. -/
def testD (p b s W k : ℕ) : ℕ :=
  max W (s * (b + 1)) + bitlen ((trianglePairs s).length * (k + 2)) + bitlen ((s + 1) * k) + p +
    bitlen (k + 2) + 2

set_option maxHeartbeats 4000000 in
/-- **The check never fails a guard**: on binary entries (significands below `2^p`, exponents at
most `EM` in magnitude), with an exact engine, `R ≥ testD + b + 3`, `budget < 2^R`, and `X` as
stated. -/
theorem ozaki1TestIC_eq {B : Widths} {mult : MatrixMultiplier} {b bound : ℕ} (hmult : mult.ExactOn b bound)
    {p EM s W : ℕ} {emin emax : ℤ} {xs ys : List (ℤ × ℤ)} (hlen : xs.length = ys.length)
    (hbound : xs.length * (2 ^ b * 2 ^ b) ≤ bound) (hx : EntriesIn p EM xs)
    (hy : EntriesIn p EM ys) (hR : testD p b s W xs.length + b + 3 ≤ B.R)
    (hRb : bound < 2 ^ B.R)
    (hX : 8 * (p + 1 + EM + 3 * b + 2 + s * (b + 1)) + 4 * W + 2 * testD p b s W xs.length +
      emin.natAbs + emax.natAbs + 2 * p + 2 * B.R + 8 < 2 ^ B.X) :
    ozaki1TestIC B mult p emin emax b s W xs ys = some (ozaki1TestI mult p emin emax b s W xs ys) := by
  generalize hDdef : testD p b s W xs.length = D at hR hX
  have hD := hDdef
  unfold testD at hD
  have hl : (entryVals xs).length = (entryVals ys).length := by
    rw [length_entryVals, length_entryVals, hlen]
  have hb' : (entryVals xs).length * (2 ^ b * 2 ^ b) ≤ bound := by
    rw [length_entryVals]; exact hbound
  have hsplit : ∀ zs : List (ℤ × ℤ), EntriesIn p EM zs →
      splitIntFromC B b s (b : ℤ) zs = some (splitInt b s zs) := fun zs hz =>
    splitIntFromC_eq (by omega) s (b : ℤ) (p + 1 + EM + b) zs hz (by rw [Int.natAbs_natCast]; omega)
      (by omega)
      (by have : (s + 1) * (b + 1) = s * (b + 1) + (b + 1) := by rw [Nat.add_mul, Nat.one_mul]
          omega)
  unfold ozaki1TestIC ozaki1TestI
  rw [hsplit xs hx, hsplit ys hy]
  simp only [Option.bind_eq_bind, Option.bind_some]
  rw [(splitInt_eq b s xs).1, (splitInt_eq b s ys).1]
  -- the engine's slice products
  have hpairs : ∀ pr ∈ trianglePairs s, pairIntC B mult (split b s (entryVals xs)).1
      (split b s (entryVals ys)).1 pr =
        some (some (exactPairInt (split b s (entryVals xs)).1 (split b s (entryVals ys)).1 pr)) := by
    intro pr hpr
    obtain ⟨t, u⟩ := pr
    have htu := mem_trianglePairs.mp hpr
    obtain ⟨hlx, _, _⟩ := split_length b s (entryVals xs)
    obtain ⟨hly, _, _⟩ := split_length b s (entryVals ys)
    have hm1 := getD_mem (l := (split b s (entryVals xs)).1) (t := t) (by omega)
    have hm2 := getD_mem (l := (split b s (entryVals ys)).1) (t := u) (by omega)
    have g1 := splitInt_grid_bound (s := s) (b := b) hx _ hm1
    have g2 := splitInt_grid_bound (s := s) (b := b) hy _ hm2
    exact sliceProductIntC_exact hmult hl hb' hm1 hm2 hRb (by
      dsimp only
      have := Int.natAbs_add_le ((split b s (entryVals xs)).1.getD t default).grid
        ((split b s (entryVals ys)).1.getD u default).grid
      omega)
  rw [mapM_eq_some_map hpairs]
  simp only [Option.bind_some]
  rw [show (trianglePairs s).map (fun pr => some (exactPairInt (split b s (entryVals xs)).1
      (split b s (entryVals ys)).1 pr)) = ((trianglePairs s).map (exactPairInt
      (split b s (entryVals xs)).1 (split b s (entryVals ys)).1)).map some by rw [List.map_map]; rfl,
    mapM_id_map, mapM_eq_some_map fun _ hp => pairInt_exact hmult hl hb' hp]
  simp only
  generalize hts : (trianglePairs s).map (exactPairInt (split b s (entryVals xs)).1
    (split b s (entryVals ys)).1) = ts
  -- the window grid and the window parts
  have hsx := splitExpInt_natAbs_le (b := b) hx
  have hsy := splitExpInt_natAbs_le (b := b) hy
  rw [truncationGridIntC_eq hx hy (by omega) (by omega)]
  simp only [Option.bind_some]
  have hwg : truncationGridInt b W xs ys = truncationGrid b W (entryVals xs) (entryVals ys) :=
    truncationGridInt_eq b W xs ys
  have hqb : (truncationGridInt b W xs ys).natAbs ≤ 2 * (p + 1 + EM + 3 * b + 1) + W := by
    unfold truncationGridInt; omega
  have hpart : ∀ t ∈ ts, (floorPart (truncationGridInt b W xs ys) t).natAbs < xs.length * 2 ^ W + 2 ∧
      t.2.natAbs ≤ 2 * (p + 1 + EM + b + s * (b + 1)) := by
    intro t ht
    rw [← hts] at ht
    obtain ⟨pr, hpr, rfl⟩ := List.mem_map.mp ht
    obtain ⟨tt, u⟩ := pr
    have htu := mem_trianglePairs.mp hpr
    obtain ⟨hlx, _, _⟩ := split_length b s (entryVals xs)
    obtain ⟨hly, _, _⟩ := split_length b s (entryVals ys)
    have g1 := splitInt_grid_bound (s := s) (b := b) hx _
      (getD_mem (l := (split b s (entryVals xs)).1) (t := tt) (by omega))
    have g2 := splitInt_grid_bound (s := s) (b := b) hy _
      (getD_mem (l := (split b s (entryVals ys)).1) (t := u) (by omega))
    refine ⟨?_, ?_⟩
    · rw [← length_entryVals xs]
      apply natAbs_floorPart_lt
      rw [tval_exactPairInt, hwg]
      have := abs_exactTerm_le b s (entryVals xs) (entryVals ys) hpr
      rw [show truncationGrid b W (entryVals xs) (entryVals ys) + (W : ℤ) =
        splitExp b (entryVals xs) + splitExp b (entryVals ys) by unfold truncationGrid; omega]
      exact this
    · unfold exactPairInt exactSliceInt
      simp only
      have := Int.natAbs_add_le ((split b s (entryVals xs)).1.getD tt default).grid
        ((split b s (entryVals ys)).1.getD u default).grid
      omega
  have hk2 : xs.length * 2 ^ W + 2 ≤ 2 ^ (W + bitlen (xs.length + 2)) := by
    rw [Nat.add_comm W, Nat.pow_add]
    have := lt_two_pow_bitlen (xs.length + 2)
    have h2 : 2 ≤ 2 * 2 ^ W := by have := Nat.two_pow_pos W; omega
    calc xs.length * 2 ^ W + 2 ≤ xs.length * 2 ^ W + 2 * 2 ^ W := by omega
      _ = (xs.length + 2) * 2 ^ W := by rw [Nat.add_mul]
      _ ≤ 2 ^ bitlen (xs.length + 2) * 2 ^ W := Nat.mul_le_mul_right _ (by omega)
  have hWR : 2 ^ (W + bitlen (xs.length + 2)) ≤ 2 ^ B.R :=
    Nat.pow_le_pow_right (by decide) (by omega)
  rw [mapM_eq_some_map fun t ht => floorPartC_eq (by have := (hpart t ht).1; omega)
    (by have := (hpart t ht).2; omega)]
  simp only [Option.bind_some]
  have hlts : ts.length = (trianglePairs s).length := by rw [← hts]; simp
  rw [hlts, Widths.gi_ok (by omega)]
  simp only [Option.bind_some]
  -- the register
  have hreg := ozaki1TestB_register b s W (entryVals xs) (entryVals ys)
  rw [hts, ← hwg, length_entryVals] at hreg
  rw [fixedSumC_eq (by omega) (by omega) (by
    rw [show W + bitlen ((trianglePairs s).length * (xs.length + 2)) + 1 - 1 =
      W + bitlen ((trianglePairs s).length * (xs.length + 2)) by omega]
    exact hreg)]
  simp only [Option.bind_some]
  rw [splitExpIntC_eq hx (by omega) (by omega), splitExpIntC_eq hy (by omega) (by omega)]
  simp only [Option.bind_some]
  rw [Widths.ge_ok (by omega)]
  simp only [Option.bind_some]
  have hc : ((s * (b + 1) : ℕ) : ℤ) = (s : ℤ) * ((b : ℤ) + 1) := by simp
  rw [Widths.gi_ok (show s * (b + 1) < 2 ^ B.X by omega)]
  simp only [Option.bind_some]
  rw [hc, Widths.ge_ok (by rw [← hc]; omega)]
  simp only [Option.bind_some]
  have hκ := lt_two_pow_bitlen ((s + 1) * xs.length)
  rw [Widths.gv_ok (by
    rw [Int.natAbs_natCast]
    exact Nat.lt_of_lt_of_le hκ (Nat.pow_le_pow_right (by decide) (by omega)))]
  simp only [Option.bind_some]
  -- the enclosure test
  have hN := fixedSum_eq (w := W + bitlen ((trianglePairs s).length * (xs.length + 2)) + 1)
    (by omega) (zs := ts.map (floorPart (truncationGridInt b W xs ys))) (by
      rw [show W + bitlen ((trianglePairs s).length * (xs.length + 2)) + 1 - 1 =
        W + bitlen ((trianglePairs s).length * (xs.length + 2)) by omega]
      exact hreg)
  have hNb : (fixedSum (W + bitlen ((trianglePairs s).length * (xs.length + 2)) + 1)
      (ts.map (floorPart (truncationGridInt b W xs ys)))).natAbs <
      2 ^ (W + bitlen ((trianglePairs s).length * (xs.length + 2))) := by
    rw [hN]
    exact Nat.lt_of_le_of_lt (natAbs_listSum_le _) hreg
  generalize fixedSum (W + bitlen ((trianglePairs s).length * (xs.length + 2)) + 1)
    (ts.map (floorPart (truncationGridInt b W xs ys))) = N at hNb ⊢
  have hqc : truncationGridInt b W xs ys - (splitExpInt b xs + splitExpInt b ys - s * (b + 1)) =
      (s * (b + 1) : ℤ) - W := by unfold truncationGridInt; omega
  generalize hβ : bitlen ((trianglePairs s).length * (xs.length + 2)) = β at hNb hD hR hX
  generalize hκdef : bitlen ((s + 1) * xs.length) = κ at hκ hD
  have hdq : (truncationGridInt b W xs ys - min (truncationGridInt b W xs ys)
      (splitExpInt b xs + splitExpInt b ys - s * (b + 1))).toNat ≤ s * (b + 1) := by
    rw [Int.min_def]; split <;> omega
  have hdq2 : (truncationGridInt b W xs ys - min (truncationGridInt b W xs ys)
      (splitExpInt b xs + splitExpInt b ys - s * (b + 1))).toNat ≤ max W (s * (b + 1)) - W := by
    rw [Int.min_def, Nat.max_def]; split <;> split <;> omega
  have hdc : (splitExpInt b xs + splitExpInt b ys - s * (b + 1) - min (truncationGridInt b W xs ys)
      (splitExpInt b xs + splitExpInt b ys - s * (b + 1))).toNat ≤ W := by
    rw [Int.min_def]; split <;> omega
  have hn : (trianglePairs s).length < 2 ^ β := by
    rw [← hβ]
    exact Nat.lt_of_le_of_lt (Nat.le_mul_of_pos_right _ (by omega)) (lt_two_pow_bitlen _)
  have hcb : (splitExpInt b xs + splitExpInt b ys - s * (b + 1)).natAbs ≤
      2 * (p + 1 + EM + 3 * b + 1) + s * (b + 1) := by rw [← hc]; omega
  have hmax : W ≤ max W (s * (b + 1)) ∧ s * (b + 1) ≤ max W (s * (b + 1)) :=
    ⟨Nat.le_max_left _ _, Nat.le_max_right _ _⟩
  rw [roundEnclosureBC_eq (E := max W (s * (b + 1)) + β + κ) (D := D)
    (Nat.lt_of_lt_of_le (mul_two_pow_lt hNb hdq2) (Nat.pow_le_pow_right (by decide) (by omega)))
    (by
      rw [Int.natAbs_natCast]
      exact Nat.lt_of_lt_of_le (mul_two_pow_lt hκ hdc)
        (Nat.pow_le_pow_right (by decide) (by omega)))
    (Nat.lt_of_lt_of_le (mul_two_pow_lt hn hdq) (Nat.pow_le_pow_right (by decide) (by omega)))
    (by omega) (by omega) (by omega) (by omega)]

theorem vanishIntC_eq {B : Widths} {b p EM s : ℕ} {xs ys : List (ℤ × ℤ)}
    (hx : EntriesIn p EM xs) (hy : EntriesIn p EM ys) (hR : p + b + 3 ≤ B.R)
    (hX : EM + (p + 1 + EM + b) + (s + 1) * (b + 1) + p + 2 < 2 ^ B.X) :
    vanishIntC B b s xs ys = some (vanishInt b s xs ys) := by
  have hsplit : ∀ zs : List (ℤ × ℤ), EntriesIn p EM zs →
      splitIntFromC B b s (b : ℤ) zs = some (splitInt b s zs) := fun zs hz =>
    splitIntFromC_eq hR s (b : ℤ) (p + 1 + EM + b) zs hz (by rw [Int.natAbs_natCast]; omega)
      (by omega) hX
  unfold vanishIntC vanishInt
  rw [hsplit xs hx, hsplit ys hy]
  rfl

/-- The width of the exact path's sum: `bitlen (smax² + 1) + p + 4`. -/
def exactW (p smax : ℕ) : ℕ := bitlen (smax * smax + 1) + p + 4

/-- The requirement on `R` for the exact path. -/
def exactR (p smax bound : ℕ) : ℕ :=
  bitlen bound + 2 * exactW p smax + bitlen (smax * smax + 2) + p + 8

/-- The requirement on `X` for the exact path. -/
def exactX (p b EM smax bound : ℕ) (emin emax : ℤ) (R : ℕ) : ℕ :=
  32 * (p + 1 + EM + b + (smax + 1) * (b + 1)) + 6 * bitlen bound + 20 * exactW p smax +
    4 * p + emin.natAbs + emax.natAbs + 2 * R + 48

theorem mul_lt_two_pow_bitlen_add (A Z : ℕ) : A * Z < 2 ^ (bitlen A + Z) := by
  rw [Nat.pow_add]
  have h1 := lt_two_pow_bitlen A
  have h2 : Z < 2 ^ Z := Nat.lt_two_pow_self
  rcases Nat.eq_zero_or_pos Z with rfl | hZ
  · simp; exact Nat.two_pow_pos _
  · calc A * Z ≤ A * 2 ^ Z := Nat.mul_le_mul_left _ (Nat.le_of_lt h2)
      _ < 2 ^ bitlen A * 2 ^ Z := Nat.mul_lt_mul_of_pos_right h1 (Nat.two_pow_pos _)

/-- **The descent's fuel fits the data width**: the potential of the exact path's terms is at most
`(smax² + 1)` terms times their bit length, below `2^R` whenever `R ≥ exactR`. -/
theorem exact_fuel_lt {p smax bound R : ℕ} (hR : exactR p smax bound ≤ R) :
    (smax * smax + 1) * (bitlen bound + 2 * exactW p smax + p + 7) < 2 ^ R := by
  refine Nat.lt_of_lt_of_le (mul_lt_two_pow_bitlen_add _ _) (Nat.pow_le_pow_right (by decide) ?_)
  have := bitlen_mono (show smax * smax + 1 ≤ smax * smax + 2 by omega)
  unfold exactR at hR
  omega

set_option maxHeartbeats 4000000 in
/-- **The exact path never fails a guard**: on binary entries with an exact engine, with
`R ≥ exactR` (and `R ≥ p + b + 3`), `budget < 2^R` and `2^X > exactX`. -/
theorem ozaki1ExactFallbackIC_eq {B : Widths} {mult : MatrixMultiplier} {b bound : ℕ}
    (hmult : mult.ExactOn b bound) {p EM smax : ℕ} {emin emax : ℤ} {xs ys : List (ℤ × ℤ)}
    (hlen : xs.length = ys.length) (hbound : xs.length * (2 ^ b * 2 ^ b) ≤ bound)
    (hx : EntriesIn p EM xs) (hy : EntriesIn p EM ys) (hR : exactR p smax bound ≤ B.R)
    (hRb : p + b + 3 ≤ B.R) (hX : exactX p b EM smax bound emin emax B.R < 2 ^ B.X) :
    ozaki1ExactFallbackIC B mult p emin emax b smax xs ys =
      some (ozaki1ExactFallbackI mult p emin emax b smax xs ys) := by
  have hfuel := exact_fuel_lt hR
  unfold exactW at hfuel
  unfold exactR exactW at hR
  unfold exactX exactW at hX
  have hl : (entryVals xs).length = (entryVals ys).length := by
    rw [length_entryVals, length_entryVals, hlen]
  have hb' : (entryVals xs).length * (2 ^ b * 2 ^ b) ≤ bound := by
    rw [length_entryVals]; exact hbound
  have hbud : bound < 2 ^ B.R :=
    Nat.lt_of_lt_of_le (lt_two_pow_bitlen bound) (Nat.pow_le_pow_right (by decide) (by omega))
  have hXs : ∀ s, s ≤ smax → EM + (p + 1 + EM + b) + (s + 1) * (b + 1) + p + 2 < 2 ^ B.X := by
    intro s hs
    have : (s + 1) * (b + 1) ≤ (smax + 1) * (b + 1) := Nat.mul_le_mul_right _ (by omega)
    omega
  unfold ozaki1ExactFallbackIC ozaki1ExactFallbackI
  rw [findC_eq (g := fun s => vanishInt b s xs ys) fun s hs =>
    vanishIntC_eq hx hy hRb (hXs s (by simp [List.mem_range'] at hs; omega))]
  simp only [Option.bind_eq_bind, Option.bind_some]
  cases hfind : (List.range' 1 smax).find? (fun s => vanishInt b s xs ys) with
  | none => rfl
  | some s =>
    have hs : s ≤ smax := by
      have := List.mem_of_find?_eq_some hfind
      simp [List.mem_range'] at this; omega
    simp only
    have hsplit : ∀ zs : List (ℤ × ℤ), EntriesIn p EM zs →
        splitIntFromC B b s (b : ℤ) zs = some (splitInt b s zs) := fun zs hz =>
      splitIntFromC_eq hRb s (b : ℤ) (p + 1 + EM + b) zs hz (by rw [Int.natAbs_natCast]; omega)
        (by omega) (hXs s hs)
    rw [hsplit xs hx, hsplit ys hy]
    simp only [Option.bind_some]
    rw [(splitInt_eq b s xs).1, (splitInt_eq b s ys).1]
    have hsb : s * (b + 1) ≤ (smax + 1) * (b + 1) := Nat.mul_le_mul_right _ (by omega)
    have hprs : ∀ pr ∈ slicePairs (split b s (entryVals xs)).1 (split b s (entryVals ys)).1,
        sliceProductIntC B mult pr.1 pr.2 = some (some (exactSliceInt pr.1 pr.2)) := by
      intro pr hpr
      obtain ⟨m1, m2⟩ := mem_slicePairs hpr
      have g1 := splitInt_grid_bound (s := s) (b := b) hx _ m1
      have g2 := splitInt_grid_bound (s := s) (b := b) hy _ m2
      exact sliceProductIntC_exact hmult hl hb' m1 m2 hbud (by
        have := Int.natAbs_add_le pr.1.grid pr.2.grid
        omega)
    rw [mapM_eq_some_map hprs]
    simp only [Option.bind_some]
    rw [show (slicePairs (split b s (entryVals xs)).1 (split b s (entryVals ys)).1).map
        (fun pr => some (exactSliceInt pr.1 pr.2)) =
        ((slicePairs (split b s (entryVals xs)).1 (split b s (entryVals ys)).1).map
          (fun pr => exactSliceInt pr.1 pr.2)).map some by rw [List.map_map]; rfl,
      mapM_id_map, mapM_eq_some_map (g := fun pr => exactSliceInt pr.1 pr.2) fun pr hpr =>
        sliceProductInt_exact hmult hl hb' (mem_slicePairs hpr).1 (mem_slicePairs hpr).2]
    simp only
    -- the terms of the exact path
    have hplen : (slicePairs (split b s (entryVals xs)).1 (split b s (entryVals ys)).1).length =
        s * s := by
      obtain ⟨hlx, _, _⟩ := split_length b s (entryVals xs)
      obtain ⟨hly, _, _⟩ := split_length b s (entryVals ys)
      unfold slicePairs
      rw [List.length_flatMap]
      simp only [List.length_map, hly]
      rw [sum_map_const_nat, hlx]
    obtain ⟨GE, hGE⟩ : ∃ GE : ℕ, GE = 2 * (p + 1 + EM + b + (smax + 1) * (b + 1)) := ⟨_, rfl⟩
    have hterms : TermsIn (bitlen bound) (-(GE : ℤ)) (GE : ℤ)
        ((slicePairs (split b s (entryVals xs)).1 (split b s (entryVals ys)).1).map
          (fun pr => exactSliceInt pr.1 pr.2)) := by
      intro t ht
      obtain ⟨pr, hpr, rfl⟩ := List.mem_map.mp ht
      obtain ⟨m1, m2⟩ := mem_slicePairs hpr
      have g1 := splitInt_grid_bound (s := s) (b := b) hx _ m1
      have g2 := splitInt_grid_bound (s := s) (b := b) hy _ m2
      have hv := sliceProductInt_natAbs_le hmult hl hb' m1 m2
      have hgs := Int.natAbs_add_le pr.1.grid pr.2.grid
      unfold exactSliceInt at hv ⊢
      exact ⟨Nat.lt_of_le_of_lt hv (lt_two_pow_bitlen bound), by simp only; omega,
        by simp only; omega⟩
    rw [← List.length_map (f := fun pr => exactSliceInt pr.1 pr.2)] at hplen
    generalize (slicePairs (split b s (entryVals xs)).1 (split b s (entryVals ys)).1).map
      (fun pr => exactSliceInt pr.1 pr.2) = ts at hterms hplen ⊢
    have hss : s * s ≤ smax * smax := Nat.mul_le_mul hs hs
    have hb1 : bitlen (ts.length + 1) ≤ bitlen (smax * smax + 1) := bitlen_mono (by omega)
    have hb2 : bitlen (ts.length + 2) ≤ bitlen (smax * smax + 2) := bitlen_mono (by omega)
    rw [Widths.gi_ok (by omega)]
    simp only [Option.bind_some]
    have hprod : (ts.length + 1) * (bitlen bound + (bitlen (ts.length + 1) + p + 4 +
        bitlen (ts.length + 1) + 1) + p + 6) ≤ (smax * smax + 1) *
        (bitlen bound + 2 * (bitlen (smax * smax + 1) + p + 4) + p + 7) :=
      Nat.mul_le_mul (by omega) (by omega)
    have hGE' : (-(GE : ℤ)).natAbs = GE := by simp
    have hGE'' : ((GE : ℤ)).natAbs = GE := by simp
    exact roundSumJC_eq (W := bitlen (ts.length + 1) + p + 4) (by omega) hterms (by omega)
      (by omega) (by rw [hGE', hGE'']; omega) (Nat.lt_of_le_of_lt hprod hfuel)

/-- The requirement on `X` for the check with `s` slices. -/
def testX (p b EM s W k : ℕ) (emin emax : ℤ) (R : ℕ) : ℕ :=
  8 * (p + 1 + EM + 3 * b + 2 + s * (b + 1)) + 4 * W + 2 * testD p b s W k +
    emin.natAbs + emax.natAbs + 2 * p + 2 * R + 8

/-- **One theorem bounding every integer of correctly rounded Ozaki-I.** On binary entries
(significands below `2^p`, exponents at most `EM` in magnitude), with an exact engine, if `R` and
`X` meet the requirements of the checks (`testD`, `testX`, for every slice count in `ss`) and of
the exact path (`exactR`, `exactX`), the checked function returns exactly what `ozaki1CRI`
returns: no guard ever fails. -/
theorem ozaki1CRIC_eq {B : Widths} {mult : MatrixMultiplier} {b bound : ℕ} (hmult : mult.ExactOn b bound)
    {p EM W smax : ℕ} {emin emax : ℤ} {xs ys : List (ℤ × ℤ)} (hlen : xs.length = ys.length)
    (hbound : xs.length * (2 ^ b * 2 ^ b) ≤ bound) (hx : EntriesIn p EM xs)
    (hy : EntriesIn p EM ys) (hRe : exactR p smax bound ≤ B.R) (hRb : p + b + 3 ≤ B.R)
    (hXe : exactX p b EM smax bound emin emax B.R < 2 ^ B.X) :
    ∀ ss : List ℕ, (∀ s ∈ ss, testD p b s W xs.length + b + 3 ≤ B.R) →
      (∀ s ∈ ss, testX p b EM s W xs.length emin emax B.R < 2 ^ B.X) →
      ozaki1CRIC B mult p emin emax b W ss smax xs ys =
        some (ozaki1CRI mult p emin emax b W ss smax xs ys)
  | [], _, _ => by
    unfold ozaki1CRIC ozaki1CRI
    exact ozaki1ExactFallbackIC_eq hmult hlen hbound hx hy hRe hRb hXe
  | s :: ss, hRc, hXc => by
    have hbud : bound < 2 ^ B.R := by
      unfold exactR at hRe
      exact Nat.lt_of_lt_of_le (lt_two_pow_bitlen bound)
        (Nat.pow_le_pow_right (by decide) (by omega))
    unfold ozaki1CRIC ozaki1CRI
    rw [ozaki1TestIC_eq hmult hlen hbound hx hy (hRc s List.mem_cons_self) hbud
      (hXc s List.mem_cons_self)]
    simp only [Option.bind_eq_bind, Option.bind_some]
    cases ozaki1TestI mult p emin emax b s W xs ys with
    | some w => rfl
    | none =>
      exact ozaki1CRIC_eq hmult hlen hbound hx hy hRe hRb hXe ss
        (fun t ht => hRc t (List.mem_cons_of_mem _ ht))
        (fun t ht => hXc t (List.mem_cons_of_mem _ ht))

/-! ## Concrete widths -/

theorem entriesIn_of_format {p : ℕ} {emin emax : ℤ} {EM : ℕ} {xs : List (ℤ × ℤ)}
    (hE : (emin - ((p : ℤ) - 1)).natAbs ≤ EM ∧ (emax - ((p : ℤ) - 1)).natAbs ≤ EM)
    (hx : ∀ a ∈ xs, FormatEntry p emin emax a) : EntriesIn p EM xs := by
  intro a ha
  obtain ⟨h1, h2, h3⟩ := hx a ha
  exact ⟨h1, by omega⟩

theorem trianglePairs_length_le {s S : ℕ} (hs : s ≤ S) :
    (trianglePairs s).length ≤ S * (S + 1) / 2 := by
  have h := trianglePairs_length s
  have : s * (s + 1) ≤ S * (S + 1) := Nat.mul_le_mul hs (by omega)
  omega

/-- The check's requirement for at most `8` slices of `11` bits, a `96`-bit window and
`k ≤ 2^20`: `testD ≤ 169 + p`. -/
theorem testD_le_8 {p s k : ℕ} (hs : s ≤ 8) (hk : k ≤ 2 ^ 20) :
    testD p 11 s 96 k ≤ 169 + p := by
  have hn := trianglePairs_length_le hs
  have h1 : bitlen ((trianglePairs s).length * (k + 2)) ≤ 26 := bitlen_le_iff.mpr (by
    have : (trianglePairs s).length * (k + 2) ≤ 36 * (2 ^ 20 + 2) :=
      Nat.mul_le_mul (by omega) (by omega)
    omega)
  have h2 : bitlen ((s + 1) * k) ≤ 24 := bitlen_le_iff.mpr (by
    have : (s + 1) * k ≤ 9 * 2 ^ 20 := Nat.mul_le_mul (by omega) hk
    omega)
  have h3 : bitlen (k + 2) ≤ 21 := bitlen_le_iff.mpr (by omega)
  have h4 : s * (11 + 1) ≤ 96 := by omega
  unfold testD; rw [Nat.max_eq_left h4]; omega

theorem bitlen_dotAbsBound_le {k : ℕ} (hk : k ≤ 2 ^ 20) : bitlen (k * (2 ^ 11 * 2 ^ 11)) ≤ 43 :=
  bitlen_le_iff.mpr (by omega)

/-- **Every integer of correctly rounded FP64 Ozaki-I fits 332 bits, every exponent and counter
24 bits**: on binary64 entries, `k ≤ 2^20`, `11`-bit slices with at most `8` in each check, a
`96`-bit window and at most `175` slices on the exact path, with an exact engine. -/
theorem ozaki1CRIC_binary64 {mult : MatrixMultiplier} {xs ys : List (ℤ × ℤ)}
    (hmult : mult.ExactOn 11 (xs.length * (2 ^ 11 * 2 ^ 11))) (hlen : xs.length = ys.length)
    (hk : xs.length ≤ 2 ^ 20) (hx : ∀ a ∈ xs, FormatEntry 53 (-1022) 1023 a)
    (hy : ∀ a ∈ ys, FormatEntry 53 (-1022) 1023 a) {ss : List ℕ} (hss : ∀ s ∈ ss, s ≤ 8) :
    ozaki1CRIC ⟨332, 24⟩ mult 53 (-1022) 1023 11 96 ss 175 xs ys =
      some (ozaki1CRI mult 53 (-1022) 1023 11 96 ss 175 xs ys) := by
  have hE : ((-1022 : ℤ) - ((53 : ℕ) - 1 : ℤ)).natAbs ≤ 1074 ∧
      ((1023 : ℤ) - ((53 : ℕ) - 1 : ℤ)).natAbs ≤ 1074 := by decide
  have hbud := bitlen_dotAbsBound_le hk
  have hW : exactW 53 175 = 72 := by decide
  have hb2 : bitlen (175 * 175 + 2) = 15 := by decide
  refine ozaki1CRIC_eq hmult hlen (Nat.le_refl _) (entriesIn_of_format hE hx)
    (entriesIn_of_format hE hy) ?_ (by decide) ?_ ss
    (fun s hs => by have := testD_le_8 (p := 53) (hss s hs) hk; simp only; omega)
    (fun s hs => by
      have := testD_le_8 (p := 53) (hss s hs) hk
      have h8 := hss s hs
      unfold testX; simp only
      have : (-1022 : ℤ).natAbs = 1022 := by decide
      have : (1023 : ℤ).natAbs = 1023 := by decide
      omega)
  · unfold exactR; rw [hW, hb2]; simp only; omega
  · unfold exactX; rw [hW]; simp only
    have : (-1022 : ℤ).natAbs = 1022 := by decide
    have : (1023 : ℤ).natAbs = 1023 := by decide
    omega

/-- **Every integer of correctly rounded binary32 Ozaki-I fits 303 bits, every exponent and counter
17 bits**: on binary32 entries, `k ≤ 2^20`, `11`-bit slices with at most `8` in each check, a
`96`-bit window and at most `24` slices on the exact path. -/
theorem ozaki1CRIC_binary32 {mult : MatrixMultiplier} {xs ys : List (ℤ × ℤ)}
    (hmult : mult.ExactOn 11 (xs.length * (2 ^ 11 * 2 ^ 11))) (hlen : xs.length = ys.length)
    (hk : xs.length ≤ 2 ^ 20) (hx : ∀ a ∈ xs, FormatEntry 24 (-126) 127 a)
    (hy : ∀ a ∈ ys, FormatEntry 24 (-126) 127 a) {ss : List ℕ} (hss : ∀ s ∈ ss, s ≤ 8) :
    ozaki1CRIC ⟨303, 17⟩ mult 24 (-126) 127 11 96 ss 24 xs ys =
      some (ozaki1CRI mult 24 (-126) 127 11 96 ss 24 xs ys) := by
  have hE : ((-126 : ℤ) - ((24 : ℕ) - 1 : ℤ)).natAbs ≤ 149 ∧
      ((127 : ℤ) - ((24 : ℕ) - 1 : ℤ)).natAbs ≤ 149 := by decide
  have hbud := bitlen_dotAbsBound_le hk
  have hW : exactW 24 24 = 38 := by decide
  have hb2 : bitlen (24 * 24 + 2) = 10 := by decide
  refine ozaki1CRIC_eq hmult hlen (Nat.le_refl _) (entriesIn_of_format hE hx)
    (entriesIn_of_format hE hy) ?_ (by decide) ?_ ss
    (fun s hs => by have := testD_le_8 (p := 24) (hss s hs) hk; simp only; omega)
    (fun s hs => by
      have := testD_le_8 (p := 24) (hss s hs) hk
      have h8 := hss s hs
      unfold testX; simp only
      have : (-126 : ℤ).natAbs = 126 := by decide
      have : (127 : ℤ).natAbs = 127 := by decide
      omega)
  · unfold exactR; rw [hW, hb2]; simp only; omega
  · unfold exactX; rw [hW]; simp only
    have : (-126 : ℤ).natAbs = 126 := by decide
    have : (127 : ℤ).natAbs = 127 := by decide
    omega

/-- **FP64, every integer within 332 bits, correctly rounded**: the checked function returns the
IEEE binary64 round to nearest of `x · y`. -/
theorem ozaki1CRIC_binary64_eq {mult : MatrixMultiplier} {xs ys : List (ℤ × ℤ)}
    (hmult : mult.ExactOn 11 (xs.length * (2 ^ 11 * 2 ^ 11))) (hlen : xs.length = ys.length)
    (hk : xs.length ≤ 2 ^ 20) (hx : ∀ a ∈ xs, FormatEntry 53 (-1022) 1023 a)
    (hy : ∀ a ∈ ys, FormatEntry 53 (-1022) 1023 a) {ss : List ℕ} (hss : ∀ s ∈ ss, s ≤ 8) :
    ozaki1CRIC ⟨332, 24⟩ mult 53 (-1022) 1023 11 96 ss 175 xs ys =
      some (rne64 (dot (entryVals xs) (entryVals ys))) := by
  rw [ozaki1CRIC_binary64 hmult hlen hk hx hy hss,
    ozaki1CRI64_eq hmult 96 ss (by decide) (by decide) hlen (Nat.le_refl _)
      (fun a ha => (hx a ha).formatValue) (fun a ha => (hy a ha).formatValue)]

/-- **Binary32, every integer within 303 bits, correctly rounded.** -/
theorem ozaki1CRIC_binary32_eq {mult : MatrixMultiplier} {xs ys : List (ℤ × ℤ)}
    (hmult : mult.ExactOn 11 (xs.length * (2 ^ 11 * 2 ^ 11))) (hlen : xs.length = ys.length)
    (hk : xs.length ≤ 2 ^ 20) (hx : ∀ a ∈ xs, FormatEntry 24 (-126) 127 a)
    (hy : ∀ a ∈ ys, FormatEntry 24 (-126) 127 a) {ss : List ℕ} (hss : ∀ s ∈ ss, s ≤ 8) :
    ozaki1CRIC ⟨303, 17⟩ mult 24 (-126) 127 11 96 ss 24 xs ys =
      some (rne32Q (dot (entryVals xs) (entryVals ys))) := by
  rw [ozaki1CRIC_binary32 hmult hlen hk hx hy hss,
    ozaki1CRI32_eq hmult 96 ss (by decide) (by decide) hlen (Nat.le_refl _)
      (fun a ha => (hx a ha).formatValue) (fun a ha => (hy a ha).formatValue)]

namespace Checked

variable (B : Widths)

def exactSignIC (mult : MatrixMultiplier) (b smax : ℕ) (xs ys : List (ℤ × ℤ)) : Option (Option ℤ) := do
  let so ← findC (fun s => vanishIntC B b s xs ys) (List.range' 1 smax)
  match so with
  | none => pure none
  | some s => do
    let sx ← splitIntFromC B b s b xs
    let sy ← splitIntFromC B b s b ys
    let lo ← (slicePairs sx.1 sy.1).mapM (fun pr => sliceProductIntC B mult pr.1 pr.2)
    match lo.mapM id with
    | none => pure none
    | some ts => do
      let W ← B.gi (bitlen ts.length + 1)
      let v ← signSumJC B W ts
      pure (some v)

/-- `allNegZeroI` with the significands' products guarded. -/
def allNegZeroIC (xs ys : List SEntry) : Option Bool := do
  let ps ← (List.zipWith (fun a c => (a, c)) xs ys).mapM fun (a, c) => do
    let m ← B.gv (a.1.1 * c.1.1)
    pure (m == 0 && xor a.2 c.2)
  pure (!ps.isEmpty && ps.all id)

/-- **Correctly rounded Ozaki-I in integers with signed zeros, every integer guarded.** -/
def ozaki1CRISC (mult : MatrixMultiplier) (p : ℕ) (emin emax : ℤ) (b W : ℕ) (ss : List ℕ) (smax : ℕ)
    (xs ys : List SEntry) : Option (Option Signed) := do
  let r ← ozaki1CRIC B mult p emin emax b W ss smax (xs.map (·.1)) (ys.map (·.1))
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

end Checked

set_option maxHeartbeats 4000000 in
/-- **The sign of the exact sum never fails a guard**, under the requirements of the exact path. -/
theorem exactSignIC_eq {B : Widths} {mult : MatrixMultiplier} {b bound : ℕ}
    (hmult : mult.ExactOn b bound) {p EM smax : ℕ} {emin emax : ℤ} {xs ys : List (ℤ × ℤ)}
    (hlen : xs.length = ys.length) (hbound : xs.length * (2 ^ b * 2 ^ b) ≤ bound)
    (hx : EntriesIn p EM xs) (hy : EntriesIn p EM ys) (hR : exactR p smax bound ≤ B.R)
    (hRb : p + b + 3 ≤ B.R) (hX : exactX p b EM smax bound emin emax B.R < 2 ^ B.X) :
    exactSignIC B mult b smax xs ys = some (exactSignI mult b smax xs ys) := by
  have hfuel := exact_fuel_lt hR
  unfold exactW at hfuel
  unfold exactR exactW at hR
  unfold exactX exactW at hX
  have hl : (entryVals xs).length = (entryVals ys).length := by
    rw [length_entryVals, length_entryVals, hlen]
  have hb' : (entryVals xs).length * (2 ^ b * 2 ^ b) ≤ bound := by
    rw [length_entryVals]; exact hbound
  have hbud : bound < 2 ^ B.R :=
    Nat.lt_of_lt_of_le (lt_two_pow_bitlen bound) (Nat.pow_le_pow_right (by decide) (by omega))
  have hXs : ∀ s, s ≤ smax → EM + (p + 1 + EM + b) + (s + 1) * (b + 1) + p + 2 < 2 ^ B.X := by
    intro s hs
    have : (s + 1) * (b + 1) ≤ (smax + 1) * (b + 1) := Nat.mul_le_mul_right _ (by omega)
    omega
  unfold exactSignIC exactSignI
  rw [findC_eq (g := fun s => vanishInt b s xs ys) fun s hs =>
    vanishIntC_eq hx hy hRb (hXs s (by simp [List.mem_range'] at hs; omega))]
  simp only [Option.bind_eq_bind, Option.bind_some]
  cases hfind : (List.range' 1 smax).find? (fun s => vanishInt b s xs ys) with
  | none => rfl
  | some s =>
    have hs : s ≤ smax := by
      have := List.mem_of_find?_eq_some hfind
      simp [List.mem_range'] at this; omega
    simp only
    have hsplit : ∀ zs : List (ℤ × ℤ), EntriesIn p EM zs →
        splitIntFromC B b s (b : ℤ) zs = some (splitInt b s zs) := fun zs hz =>
      splitIntFromC_eq hRb s (b : ℤ) (p + 1 + EM + b) zs hz (by rw [Int.natAbs_natCast]; omega)
        (by omega) (hXs s hs)
    rw [hsplit xs hx, hsplit ys hy]
    simp only [Option.bind_some]
    rw [(splitInt_eq b s xs).1, (splitInt_eq b s ys).1]
    have hsb : s * (b + 1) ≤ (smax + 1) * (b + 1) := Nat.mul_le_mul_right _ (by omega)
    have hprs : ∀ pr ∈ slicePairs (split b s (entryVals xs)).1 (split b s (entryVals ys)).1,
        sliceProductIntC B mult pr.1 pr.2 = some (some (exactSliceInt pr.1 pr.2)) := by
      intro pr hpr
      obtain ⟨m1, m2⟩ := mem_slicePairs hpr
      have g1 := splitInt_grid_bound (s := s) (b := b) hx _ m1
      have g2 := splitInt_grid_bound (s := s) (b := b) hy _ m2
      exact sliceProductIntC_exact hmult hl hb' m1 m2 hbud (by
        have := Int.natAbs_add_le pr.1.grid pr.2.grid
        omega)
    rw [mapM_eq_some_map hprs]
    simp only [Option.bind_some]
    rw [show (slicePairs (split b s (entryVals xs)).1 (split b s (entryVals ys)).1).map
        (fun pr => some (exactSliceInt pr.1 pr.2)) =
        ((slicePairs (split b s (entryVals xs)).1 (split b s (entryVals ys)).1).map
          (fun pr => exactSliceInt pr.1 pr.2)).map some by rw [List.map_map]; rfl,
      mapM_id_map, mapM_eq_some_map (g := fun pr => exactSliceInt pr.1 pr.2) fun pr hpr =>
        sliceProductInt_exact hmult hl hb' (mem_slicePairs hpr).1 (mem_slicePairs hpr).2]
    simp only [Option.map_some]
    -- the terms of the exact path
    have hplen : (slicePairs (split b s (entryVals xs)).1 (split b s (entryVals ys)).1).length =
        s * s := by
      obtain ⟨hlx, _, _⟩ := split_length b s (entryVals xs)
      obtain ⟨hly, _, _⟩ := split_length b s (entryVals ys)
      unfold slicePairs
      rw [List.length_flatMap]
      simp only [List.length_map, hly]
      rw [sum_map_const_nat, hlx]
    obtain ⟨GE, hGE⟩ : ∃ GE : ℕ, GE = 2 * (p + 1 + EM + b + (smax + 1) * (b + 1)) := ⟨_, rfl⟩
    have hterms : TermsIn (bitlen bound) (-(GE : ℤ)) (GE : ℤ)
        ((slicePairs (split b s (entryVals xs)).1 (split b s (entryVals ys)).1).map
          (fun pr => exactSliceInt pr.1 pr.2)) := by
      intro t ht
      obtain ⟨pr, hpr, rfl⟩ := List.mem_map.mp ht
      obtain ⟨m1, m2⟩ := mem_slicePairs hpr
      have g1 := splitInt_grid_bound (s := s) (b := b) hx _ m1
      have g2 := splitInt_grid_bound (s := s) (b := b) hy _ m2
      have hv := sliceProductInt_natAbs_le hmult hl hb' m1 m2
      have hgs := Int.natAbs_add_le pr.1.grid pr.2.grid
      unfold exactSliceInt at hv ⊢
      exact ⟨Nat.lt_of_le_of_lt hv (lt_two_pow_bitlen bound), by simp only; omega,
        by simp only; omega⟩
    rw [← List.length_map (f := fun pr => exactSliceInt pr.1 pr.2)] at hplen
    generalize (slicePairs (split b s (entryVals xs)).1 (split b s (entryVals ys)).1).map
      (fun pr => exactSliceInt pr.1 pr.2) = ts at hterms hplen ⊢
    have hss : s * s ≤ smax * smax := Nat.mul_le_mul hs hs
    have hb1 : bitlen (ts.length + 1) ≤ bitlen (smax * smax + 1) := bitlen_mono (by omega)
    have hb2 : bitlen (ts.length + 2) ≤ bitlen (smax * smax + 2) := bitlen_mono (by omega)
    have hbl0 : bitlen ts.length ≤ bitlen (ts.length + 1) := bitlen_mono (by omega)
    rw [Widths.gi_ok (by omega)]
    simp only [Option.bind_some]
    have hGE' : (-(GE : ℤ)).natAbs = GE := by simp
    have hGE'' : ((GE : ℤ)).natAbs = GE := by simp
    have hprod : ts.length * bitlen bound ≤ (smax * smax + 1) *
        (bitlen bound + 2 * (bitlen (smax * smax + 1) + p + 4) + p + 7) :=
      Nat.mul_le_mul (by omega) (by omega)
    rw [signSumJC_eq (W := bitlen ts.length + 1) (by omega) (by omega)
      (by rw [hGE', hGE'']; omega) hterms (by omega) (Nat.lt_of_le_of_lt hprod hfuel)]
    rfl

theorem allNegZeroIC_eq {B : Widths} {p : ℕ} {xs ys : List SEntry} (hR : 2 * p ≤ B.R)
    (hx : ∀ a ∈ xs, a.1.1.natAbs < 2 ^ p) (hy : ∀ a ∈ ys, a.1.1.natAbs < 2 ^ p) :
    allNegZeroIC B xs ys = some (allNegZeroI xs ys) := by
  unfold allNegZeroIC allNegZeroI
  have h : ∀ q ∈ List.zipWith (fun a c => (a, c)) xs ys,
      (fun (q : SEntry × SEntry) => (B.gv (q.1.1.1 * q.2.1.1)).bind fun m =>
        some (m == 0 && xor q.1.2 q.2.2)) q =
        some ((fun (q : SEntry × SEntry) => q.1.1.1 * q.2.1.1 == 0 && xor q.1.2 q.2.2) q) := by
    intro q hq
    obtain ⟨a, c⟩ := q
    have hm := List.of_mem_zip (by simpa [List.zip] using hq)
    simp only
    rw [Widths.gv_ok (by
      rw [Int.natAbs_mul]
      have h1 := hx a hm.1
      have h2 := hy c hm.2
      calc a.1.1.natAbs * c.1.1.natAbs < 2 ^ p * 2 ^ p :=
            Nat.mul_lt_mul_of_lt_of_le h1 (Nat.le_of_lt h2) (by omega)
        _ = 2 ^ (2 * p) := by rw [← Nat.pow_add]; congr 1; omega
        _ ≤ 2 ^ B.R := Nat.pow_le_pow_right (by decide) hR)]
    rfl
  simp only [Option.bind_eq_bind, Option.pure_def]
  rw [mapM_eq_some_map h]
  simp only [Option.bind_some, List.map_zipWith]

/-- **The signed function never fails a guard** under the requirements of the unsigned one and
`R ≥ 2p` (the sign-bit test multiplies two significands). -/
theorem ozaki1CRISC_eq {B : Widths} {mult : MatrixMultiplier} {b bound : ℕ} (hmult : mult.ExactOn b bound)
    {p EM W smax : ℕ} {emin emax : ℤ} {xs ys : List SEntry} (hlen : xs.length = ys.length)
    (hbound : xs.length * (2 ^ b * 2 ^ b) ≤ bound) (hx : EntriesIn p EM (xs.map (·.1)))
    (hy : EntriesIn p EM (ys.map (·.1))) (hRe : exactR p smax bound ≤ B.R)
    (hRb : p + b + 3 ≤ B.R) (hR2 : 2 * p ≤ B.R)
    (hXe : exactX p b EM smax bound emin emax B.R < 2 ^ B.X) {ss : List ℕ}
    (hRc : ∀ s ∈ ss, testD p b s W xs.length + b + 3 ≤ B.R)
    (hXc : ∀ s ∈ ss, testX p b EM s W xs.length emin emax B.R < 2 ^ B.X) :
    ozaki1CRISC B mult p emin emax b W ss smax xs ys =
      some (ozaki1CRIS mult p emin emax b W ss smax xs ys) := by
  have hl : (xs.map (·.1)).length = (ys.map (·.1)).length := by simp [hlen]
  have hb : (xs.map (·.1)).length * (2 ^ b * 2 ^ b) ≤ bound := by simpa using hbound
  have hlx : (xs.map (·.1)).length = xs.length := by simp
  unfold ozaki1CRISC ozaki1CRIS
  rw [ozaki1CRIC_eq hmult hl hb hx hy hRe hRb hXe ss (by rw [hlx]; exact hRc)
    (by rw [hlx]; exact hXc)]
  simp only [Option.bind_eq_bind, Option.bind_some]
  cases ozaki1CRI mult p emin emax b W ss smax (xs.map (·.1)) (ys.map (·.1)) with
  | none => rfl
  | some r =>
    simp only
    split
    · rfl
    · rw [exactSignIC_eq hmult hl hb hx hy hRe hRb hXe]
      simp only [Option.bind_some]
      cases exactSignI mult b smax (xs.map (·.1)) (ys.map (·.1)) with
      | none => rfl
      | some sg =>
        simp only [Option.map_some]
        rw [allNegZeroIC_eq (p := p) hR2
          (fun a ha => (hx a.1 (List.mem_map_of_mem ha)).1)
          (fun a ha => (hy a.1 (List.mem_map_of_mem ha)).1)]
        rfl

/-- **FP64 with signed zeros, every integer within 332 bits.** -/
theorem ozaki1CRISC_binary64_eq {mult : MatrixMultiplier} {xs ys : List SEntry}
    (hmult : mult.ExactOn 11 (xs.length * (2 ^ 11 * 2 ^ 11))) (hlen : xs.length = ys.length)
    (hk : xs.length ≤ 2 ^ 20) (hx : ∀ a ∈ xs, FormatEntry 53 (-1022) 1023 a.1)
    (hy : ∀ a ∈ ys, FormatEntry 53 (-1022) 1023 a.1) {ss : List ℕ} (hss : ∀ s ∈ ss, s ≤ 8) :
    ozaki1CRISC ⟨332, 24⟩ mult 53 (-1022) 1023 11 96 ss 175 xs ys =
      some (crSigned rne64 (xs.map toSigned) (ys.map toSigned)) := by
  have hE : ((-1022 : ℤ) - ((53 : ℕ) - 1 : ℤ)).natAbs ≤ 1074 ∧
      ((1023 : ℤ) - ((53 : ℕ) - 1 : ℤ)).natAbs ≤ 1074 := by decide
  have hx' : ∀ a ∈ xs.map (·.1), FormatEntry 53 (-1022) 1023 a := by
    intro a ha; obtain ⟨c, hc, rfl⟩ := List.mem_map.mp ha; exact hx c hc
  have hy' : ∀ a ∈ ys.map (·.1), FormatEntry 53 (-1022) 1023 a := by
    intro a ha; obtain ⟨c, hc, rfl⟩ := List.mem_map.mp ha; exact hy c hc
  have hbud := bitlen_dotAbsBound_le hk
  have hW : exactW 53 175 = 72 := by decide
  have hb2 : bitlen (175 * 175 + 2) = 15 := by decide
  rw [ozaki1CRISC_eq hmult hlen (Nat.le_refl _) (entriesIn_of_format hE hx')
    (entriesIn_of_format hE hy') (by unfold exactR; rw [hW, hb2]; simp only; omega) (by decide)
    (by decide) (by
      unfold exactX; rw [hW]; simp only
      have : (-1022 : ℤ).natAbs = 1022 := by decide
      have : (1023 : ℤ).natAbs = 1023 := by decide
      omega)
    (fun s hs => by have := testD_le_8 (p := 53) (hss s hs) hk; simp only; omega)
    (fun s hs => by
      have := testD_le_8 (p := 53) (hss s hs) hk
      have h8 := hss s hs
      unfold testX; simp only
      have : (-1022 : ℤ).natAbs = 1022 := by decide
      have : (1023 : ℤ).natAbs = 1023 := by decide
      omega)]
  exact congrArg some (ozaki1CRIS64_eq hmult 96 ss (by decide) (by decide) hlen (Nat.le_refl _)
    (fun a ha => (hx a ha).formatValue) (fun a ha => (hy a ha).formatValue))

/-! ## Examples, checked by the kernel -/

/-- Binary64 entries spanning the exponent range, with a subnormal and a large value. -/
def ckXs : List (ℤ × ℤ) := [(5000000000000001, -60), (-7000000000000003, -55), (3, -1074),
  (9007199254740991, 900)]
def ckYs : List (ℤ × ℤ) := [(4503599627370497, -52), (6000000000000007, -70), (-1, -1074),
  (1, -950)]

/-- At the proved widths the checked function agrees with the unchecked one, through the check and
through the exact path. -/
example : Checked.ozaki1CRIC ⟨332, 24⟩ exactMultiplier 53 (-1022) 1023 11 96 [5, 6] 175 ckXs ckYs =
    some (ozaki1CRI exactMultiplier 53 (-1022) 1023 11 96 [5, 6] 175 ckXs ckYs) := by decide +kernel

example : Checked.ozaki1CRIC ⟨332, 24⟩ exactMultiplier 53 (-1022) 1023 11 96 [] 175 ckXs ckYs =
    some (ozaki1CRI exactMultiplier 53 (-1022) 1023 11 96 [] 175 ckXs ckYs) := by decide +kernel

/-- The guards are real: a `64`-bit data register is too narrow for the `96`-bit window, and an
`11`-bit exponent register too narrow for the grids of the slicing. -/
example : Checked.ozaki1CRIC ⟨64, 24⟩ exactMultiplier 53 (-1022) 1023 11 96 [5, 6] 175 ckXs ckYs =
    none := by decide +kernel

example : Checked.ozaki1CRIC ⟨332, 11⟩ exactMultiplier 53 (-1022) 1023 11 96 [5, 6] 175 ckXs ckYs =
    none := by decide +kernel

end Ozaki
