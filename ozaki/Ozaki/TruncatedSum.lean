import Ozaki.Correct

/-! # Correct rounding with a two-word accumulator

Correct rounding only has to decide on which side of the nearest rounding boundary `x · y` lies, so
the sum `H` of the slice products need not be exact. Keep it in a window of `W` bits below the bound
`2^(E+F)` of the largest product: round every scaled slice product down to the grid
`2^q`, `q = E + F − W`, and add the results exactly. The window sum is an integer multiple of
`2^q` (`truncatedSum_register`), it is within `n · 2^q` of the exact sum for `n` terms
(`truncatedSum_error`), and that is added to the bound. The correctly rounded scheme stays correct for
every input (`ozaki1CRW_eq`), and its accumulator holds
`|N| ≤ (s(s+1)/2) · (k 2^W + 1)` (`ozaki1Truncated_register`): for `W = 96`, `s = 6` and `k ≤ 2^14`
that is about `115` bits, under two 64-bit words, independent of the inputs' exponent range.

The window costs nothing in the check when `W` exceeds `s (b + 1)` by a few bits: the added
`n · 2^q` is then far below the slicing bound `(s + 1) k 2^(E + F − s(b+1))`. Only the exact path,
taken for entries the check cannot settle, adds slice products exactly. -/

local notation "ℕ" => Nat
local notation "ℤ" => Int
local notation "ℚ" => Rat

namespace Ozaki

/-! ## The window -/

/-- `t` rounded down to a multiple of `2^q`. -/
def floorGrid (q : ℤ) (t : ℚ) : ℚ := ((t * 2 ^ (-q)).floor : ℚ) * 2 ^ q

theorem floorGrid_error (q : ℤ) (t : ℚ) :
    0 ≤ t - floorGrid q t ∧ t - floorGrid q t < 2 ^ q := by
  obtain ⟨h1, h2⟩ := floor_frac (t * 2 ^ (-q))
  have hp := two_pow_pos q
  have ht : t = (t * 2 ^ (-q)) * 2 ^ q := by
    rw [Rat.mul_assoc, two_pow_neg_mul, Rat.mul_one]
  unfold floorGrid
  generalize ((t * 2 ^ (-q)).floor : ℚ) = f at h1 h2
  generalize t * 2 ^ (-q) = u at h1 h2 ht
  subst ht
  constructor
  · have := Rat.mul_le_mul_of_nonneg_right h1 (Rat.le_of_lt hp); grind
  · have := Rat.mul_lt_mul_of_pos_right h2 hp; grind

/-- The window sum: every term rounded down to the grid `2^q`, then added exactly. -/
def truncatedSum (q : ℤ) (ts : List ℚ) : ℚ := (ts.map (floorGrid q)).sum

theorem truncatedSum_error (q : ℤ) : ∀ ts : List ℚ,
    Rat.abs (ts.sum - truncatedSum q ts) ≤ ts.length * 2 ^ q
  | [] => by
    simp only [truncatedSum, List.map_nil, List.sum_nil, List.length_nil]
    rw [show (0 : ℚ) - 0 = 0 by grind, abs_zero]
    have := two_pow_pos q
    simp
  | t :: ts => by
    have ih := truncatedSum_error q ts
    obtain ⟨h1, h2⟩ := floorGrid_error q t
    have hsplit : (t :: ts).sum - truncatedSum q (t :: ts) =
        (t - floorGrid q t) + (ts.sum - truncatedSum q ts) := by
      simp only [truncatedSum, List.sum_cons, List.map_cons]; grind
    rw [hsplit]
    refine Rat.le_trans (abs_add_le _ _) ?_
    rw [abs_of_nonneg h1, List.length_cons, natCast_succ]
    grind

/-- The window sum is an integer multiple of `2^q`, with `|N| ≤ Σ|tᵢ| / 2^q + n`. -/
theorem truncatedSum_register (q : ℤ) : ∀ ts : List ℚ, ∃ N : ℤ,
    truncatedSum q ts = (N : ℚ) * 2 ^ q ∧
      ((N.natAbs : ℕ) : ℚ) ≤ (ts.map Rat.abs).sum * 2 ^ (-q) + ts.length
  | [] => ⟨0, by simp [truncatedSum], by simp <;> grind⟩
  | t :: ts => by
    obtain ⟨M, hM, hMb⟩ := truncatedSum_register q ts
    refine ⟨(t * 2 ^ (-q)).floor + M, ?_, ?_⟩
    · simp only [truncatedSum, List.map_cons, List.sum_cons] at hM ⊢
      rw [hM, Rat.intCast_add]; unfold floorGrid; grind
    · obtain ⟨f1, f2⟩ := floor_frac (t * 2 ^ (-q))
      have habs : Rat.abs (((t * 2 ^ (-q)).floor : ℤ) : ℚ) ≤ Rat.abs t * 2 ^ (-q) + 1 := by
        rw [← abs_mul_two_pow, abs_le_iff]
        have := neg_abs_le (t * 2 ^ (-q))
        have := le_abs_self (t * 2 ^ (-q))
        constructor <;> grind
      have hN : ((((t * 2 ^ (-q)).floor + M).natAbs : ℕ) : ℚ) ≤
          Rat.abs (((t * 2 ^ (-q)).floor : ℤ) : ℚ) + ((M.natAbs : ℕ) : ℚ) := by
        rw [← abs_intCast, ← abs_intCast, Rat.intCast_add]; exact abs_add_le _ _
      simp only [List.map_cons, List.sum_cons, List.length_cons, natCast_succ]
      grind

/-! ## Ozaki-I with a window -/

/-- The engine's scaled slice products, one per slice pair with `t + u < s`. -/
def ozaki1Terms (mult : MatrixMultiplier) (b s : ℕ) (x y : List ℚ) : Option (List ℚ) :=
  (trianglePairs s).mapM (pairTerm mult (split b s x).1 (split b s y).1)

theorem ozaki1Terms_eq {mult : MatrixMultiplier} {b bound : ℕ} (hmult : mult.ExactOn b bound) (s : ℕ)
    {x y : List ℚ} (hlen : x.length = y.length) (hbound : x.length * (2 ^ b * 2 ^ b) ≤ bound) :
    ozaki1Terms mult b s x y = some (exactTerms b s x y) :=
  mapM_eq_some_map fun _ hp => pairTerm_exact hmult hlen hbound hp

/-- The window grid: `W` bits below `2^(E + F)`, the bound of the largest scaled slice product. -/
def truncationGrid (b W : ℕ) (x y : List ℚ) : ℤ := splitExp b x + splitExp b y - W

/-- The enclosure from `s` slices with a `W`-bit window: the window sum of the engine's slice
products, and the slicing bound plus the window's loss. -/
def ozaki1TruncatedEnclosure (mult : MatrixMultiplier) (b s W : ℕ) (x y : List ℚ) : Option (ℚ × ℚ) :=
  (ozaki1Terms mult b s x y).map fun ts =>
    (truncatedSum (truncationGrid b W x y) ts,
      ozaki1Bound b s x y + ts.length * 2 ^ truncationGrid b W x y)

/-- **Correctly rounded Ozaki-I with a `W`-bit accumulator**: slice counts `ss` in turn, each checked
on the window sum, then the exact path on the engine. -/
def ozaki1CRW (mult : MatrixMultiplier) (rnd : ℚ → Option ℚ) (b W : ℕ) (ss : List ℕ) (smax : ℕ)
    (x y : List ℚ) : Option ℚ :=
  roundingTest rnd (ss.map fun s => ozaki1TruncatedEnclosure mult b s W x y) (ozaki1ExactFallback mult b smax x y)

theorem ozaki1TruncatedEnclosure_sound {mult : MatrixMultiplier} {b bound : ℕ} (hmult : mult.ExactOn b bound)
    (s W : ℕ) {x y : List ℚ} (hlen : x.length = y.length)
    (hbound : x.length * (2 ^ b * 2 ^ b) ≤ bound) {H B : ℚ}
    (he : ozaki1TruncatedEnclosure mult b s W x y = some (H, B)) : Rat.abs (dot x y - H) ≤ B := by
  unfold ozaki1TruncatedEnclosure at he
  rw [ozaki1Terms_eq hmult s hlen hbound] at he
  simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at he
  obtain ⟨rfl, rfl⟩ := he
  have h1 := exactTerms_error b s x y
  have h2 := truncatedSum_error (truncationGrid b W x y) (exactTerms b s x y)
  have hsplit : dot x y - truncatedSum (truncationGrid b W x y) (exactTerms b s x y) =
      (dot x y - (exactTerms b s x y).sum) +
        ((exactTerms b s x y).sum - truncatedSum (truncationGrid b W x y) (exactTerms b s x y)) := by
    grind
  rw [hsplit]
  refine Rat.le_trans (abs_add_le _ _) ?_
  unfold ozaki1Bound
  grind

/-- **Ozaki-I with a `W`-bit accumulator, correctly rounded**: on an exact engine, for every input
whose exact path ends within `smax` slices. -/
theorem ozaki1CRW_eq {R : ℚ → Prop} {rnd : ℚ → Option ℚ} (h : RoundsToNearest R rnd)
    (hI : RoundsOnIntervals rnd) {mult : MatrixMultiplier} {b bound : ℕ} (hmult : mult.ExactOn b bound)
    (W : ℕ) (ss : List ℕ) {smax : ℕ} {x y : List ℚ} (hlen : x.length = y.length)
    (hbound : x.length * (2 ^ b * 2 ^ b) ≤ bound)
    (hvanish : ∃ s ∈ List.range' 1 smax, residualsVanish b s x y = true) :
    ozaki1CRW mult rnd b W ss smax x y = rnd (dot x y) := by
  apply roundingTest_eq h hI _ _ _ (ozaki1ExactFallback_eq hmult hlen hbound hvanish)
  intro c hc H B hcB
  obtain ⟨s, _, rfl⟩ := List.mem_map.mp hc
  exact ozaki1TruncatedEnclosure_sound hmult s W hlen hbound hcB

/-- **The accumulator is small.** The window sum from `s` slices is `N · 2^q` with
`|N| ≤ (s(s+1)/2) · (k 2^W + 1)`: `W + log₂ (s(s+1)/2 · (k + 1)) + 1` bits with the sign, whatever
the inputs' exponents. -/
theorem ozaki1Truncated_register {mult : MatrixMultiplier} {b bound : ℕ} (hmult : mult.ExactOn b bound)
    (s W : ℕ) {x y : List ℚ} (hlen : x.length = y.length)
    (hbound : x.length * (2 ^ b * 2 ^ b) ≤ bound) :
    ∃ N : ℤ, (ozaki1TruncatedEnclosure mult b s W x y).map Prod.fst =
        some ((N : ℚ) * 2 ^ truncationGrid b W x y) ∧
      ((N.natAbs : ℕ) : ℚ) ≤ (trianglePairs s).length * (x.length * 2 ^ (W : ℤ) + 1) := by
  obtain ⟨N, hN, hNb⟩ := truncatedSum_register (truncationGrid b W x y) (exactTerms b s x y)
  refine ⟨N, ?_, ?_⟩
  · unfold ozaki1TruncatedEnclosure
    rw [ozaki1Terms_eq hmult s hlen hbound]
    simp [hN]
  · refine Rat.le_trans hNb ?_
    have hsum : ((exactTerms b s x y).map Rat.abs).sum ≤
        (trianglePairs s).length * (x.length * 2 ^ (splitExp b x + splitExp b y)) := by
      have := sum_le_length_mul (l := trianglePairs s)
        (f := Rat.abs ∘ exactTerm (split b s x).1 (split b s y).1)
        (B := x.length * 2 ^ (splitExp b x + splitExp b y))
        (fun p hp => abs_exactTerm_le b s x y hp)
      simpa [exactTerms, List.map_map] using this
    have hq : (2 : ℚ) ^ (splitExp b x + splitExp b y) * 2 ^ (-truncationGrid b W x y) =
        2 ^ (W : ℤ) := by
      rw [← two_pow_add]; congr 1; unfold truncationGrid; omega
    have hlenT : ((exactTerms b s x y).length : ℚ) = (trianglePairs s).length := by
      simp [exactTerms]
    have hpos := two_pow_pos (-truncationGrid b W x y)
    have hmul := Rat.mul_le_mul_of_nonneg_right hsum (Rat.le_of_lt hpos)
    rw [hlenT]
    have : ((trianglePairs s).length : ℚ) * (x.length * 2 ^ (splitExp b x + splitExp b y)) *
        2 ^ (-truncationGrid b W x y) = (trianglePairs s).length * (x.length * 2 ^ (W : ℤ)) := by
      rw [← hq]; grind
    grind

/-- **The window's check settles an entry with margin**, as with the exact sum: whenever `x · y` is
`2B` from every rounding boundary, `B` now including the window's loss `n 2^q`. -/
theorem ozaki1TruncatedEnclosure_succeeds {R : ℚ → Prop} {rnd : ℚ → Option ℚ}
    (h : RoundsToNearest R rnd) (hI : RoundsOnIntervals rnd) {mult : MatrixMultiplier} {b bound : ℕ}
    (hmult : mult.ExactOn b bound) (s W : ℕ) {x y : List ℚ} (hlen : x.length = y.length)
    (hbound : x.length * (2 ^ b * 2 ^ b) ≤ bound) {w : ℚ}
    (hlo : rnd (dot x y - 2 * (ozaki1Bound b s x y +
      (trianglePairs s).length * 2 ^ truncationGrid b W x y)) = some w)
    (hhi : rnd (dot x y + 2 * (ozaki1Bound b s x y +
      (trianglePairs s).length * 2 ^ truncationGrid b W x y)) = some w) :
    (ozaki1TruncatedEnclosure mult b s W x y).bind (fun p => roundEnclosure rnd p.1 p.2) = some w := by
  have hlenT : ((exactTerms b s x y).length : ℚ) = (trianglePairs s).length := by
    simp [exactTerms]
  have he : ozaki1TruncatedEnclosure mult b s W x y =
      some (truncatedSum (truncationGrid b W x y) (exactTerms b s x y),
        ozaki1Bound b s x y + (trianglePairs s).length * 2 ^ truncationGrid b W x y) := by
    unfold ozaki1TruncatedEnclosure
    rw [ozaki1Terms_eq hmult s hlen hbound, Option.map_some, hlenT]
  rw [he, Option.bind_some]
  exact roundEnclosure_of_margin h hI (ozaki1TruncatedEnclosure_sound hmult s W hlen hbound he) hlo hhi

end Ozaki
