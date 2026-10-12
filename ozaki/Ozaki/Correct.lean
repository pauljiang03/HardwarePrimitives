import Ozaki.Ozaki1
import Ozaki.Ozaki2

/-! # Correct rounding by enclosure

Before its last rounding, each Ozaki scheme holds an exact value `H` (the exactly added slice
products, or the reconstructed product of the truncated inputs), and a proved bound
`B ≥ |x · y − H|`. If `H − B` and `H + B` round to the same value `w`, every value between them
rounds to `w`, the exact product `x · y` included, because rounding to nearest is monotone
(`round_monotone`). Monotonicity needs only that every result is a nearest representable value; the
tie rule plays no part. If the two ends disagree, the next enclosure (more slices, more moduli) is
tried, and after the last one the exact product is rounded (`certify`, `certify_eq`).

This is the structure of TC-EFT: an exact identity (here the error identity of the scheme), a cheap
check that proves the fast result, and an exact fallback. The check itself is Ziv's rounding test.
The schemes supply the enclosures:

* Ozaki-I: `H` the exact sum of the `s (s+1)/2` slice products, `B` the slicing bound
  (`exactTerms_error`); `ozaki1CR_eq`.
* Ozaki-II: `H` the CRT-reconstructed product of the truncated inputs, `B` the truncation bound
  (`dot_approx_error`); `ozaki2CR_eq`.

Both return the correctly rounded `x · y` for every input, on any engine that is exact on the slices
or residues. Everything the check adds is integer arithmetic on `H` and `B`. -/

local notation "ℕ" => Nat
local notation "ℤ" => Int
local notation "ℚ" => Rat

namespace Ozaki

/-! ## Monotone rounding -/

/-- `rnd` rounds to nearest in the set `R` of representable values: every result lies in `R`, and no
element of `R` is closer to the input. -/
def RoundsToNearest (R : ℚ → Prop) (rnd : ℚ → Option ℚ) : Prop :=
  ∀ q v, rnd q = some v → R v ∧ ∀ w, R w → Rat.abs (q - v) ≤ Rat.abs (q - w)

/-- `rnd` succeeds on intervals: between two inputs where it succeeds, it succeeds. -/
def RoundsOnIntervals (rnd : ℚ → Option ℚ) : Prop :=
  ∀ a b q, a ≤ q → q ≤ b → (rnd a).isSome → (rnd b).isSome → (rnd q).isSome

/-- A point at least as close to `v` as to a smaller `w` lies above their midpoint. -/
theorem nearest_ge_mid {q v w : ℚ} (hwv : w < v) (h : Rat.abs (q - v) ≤ Rat.abs (q - w)) :
    v + w ≤ 2 * q := by
  rw [abs_def, abs_def] at h; split at h <;> split at h <;> grind

/-- A point at least as close to `v` as to a larger `w` lies below their midpoint. -/
theorem nearest_le_mid {q v w : ℚ} (hvw : v < w) (h : Rat.abs (q - v) ≤ Rat.abs (q - w)) :
    2 * q ≤ v + w := by
  rw [abs_def, abs_def] at h; split at h <;> split at h <;> grind

/-- **Rounding to nearest is monotone.** If `a ≤ b`, the rounding of `a` is at most that of `b`.
Were it larger, `a` would lie above and `b` below the midpoint of the two results, so `a = b`, and
one input has one rounding. -/
theorem round_monotone {R : ℚ → Prop} {rnd : ℚ → Option ℚ} (h : RoundsToNearest R rnd)
    {a b va vb : ℚ} (hab : a ≤ b) (ha : rnd a = some va) (hb : rnd b = some vb) : va ≤ vb := by
  apply Rat.not_lt.mp
  intro hlt
  obtain ⟨hRa, hna⟩ := h a va ha
  obtain ⟨hRb, hnb⟩ := h b vb hb
  have h1 := nearest_ge_mid hlt (hna vb hRb)
  have h2 := nearest_le_mid hlt (hnb va hRa)
  have heq : a = b := by grind
  subst heq
  rw [ha] at hb
  cases hb
  grind

/-- **The enclosure test.** If `|v − H| ≤ B` and both `H − B` and `H + B` round to `w`, then `v`
rounds to `w`. -/
theorem round_eq_of_enclosure {R : ℚ → Prop} {rnd : ℚ → Option ℚ} (h : RoundsToNearest R rnd)
    (hI : RoundsOnIntervals rnd) {H B v w : ℚ} (hv : Rat.abs (v - H) ≤ B)
    (hlo : rnd (H - B) = some w) (hhi : rnd (H + B) = some w) : rnd v = some w := by
  obtain ⟨h1, h2⟩ := (abs_le_iff _ _).mp hv
  have hl : H - B ≤ v := by grind
  have hu : v ≤ H + B := by grind
  have hs := hI _ _ _ hl hu (by simp [hlo]) (by simp [hhi])
  obtain ⟨r, hr⟩ := Option.isSome_iff_exists.mp hs
  have hwr := round_monotone h hl hlo hr
  have hrw := round_monotone h hu hr hhi
  rw [hr]
  congr 1
  grind

/-! ## Certifying a rounding -/

/-- The rounding both ends of `[H − B, H + B]` agree on, if they agree. -/
def roundEnclosure (rnd : ℚ → Option ℚ) (H B : ℚ) : Option ℚ :=
  match rnd (H - B), rnd (H + B) with
  | some w, some w' => if w = w' then some w else none
  | _, _ => none

theorem roundEnclosure_eq {R : ℚ → Prop} {rnd : ℚ → Option ℚ} (h : RoundsToNearest R rnd)
    (hI : RoundsOnIntervals rnd) {H B v w : ℚ} (hv : Rat.abs (v - H) ≤ B)
    (he : roundEnclosure rnd H B = some w) : rnd v = some w := by
  unfold roundEnclosure at he
  cases hlo : rnd (H - B) with
  | none => simp [hlo] at he
  | some w1 =>
    cases hhi : rnd (H + B) with
    | none => simp [hlo, hhi] at he
    | some w2 =>
      simp only [hlo, hhi] at he
      split at he
      · rename_i heq
        cases he
        subst heq
        exact round_eq_of_enclosure h hI hv hlo hhi
      · cases he

/-- Try the enclosures in order (`none` for one that could not be computed) and return the rounding
the first one certifies; after the last, round the exact value. -/
def certify (rnd : ℚ → Option ℚ) : List (Option (ℚ × ℚ)) → Option ℚ → Option ℚ
  | [], exact => exact.bind rnd
  | c :: cs, exact =>
    match c.bind fun p => roundEnclosure rnd p.1 p.2 with
    | some w => some w
    | none => certify rnd cs exact

/-- **Certified rounding is correct rounding.** If every enclosure contains `v` and the fallback is
`v` itself, `certify` returns the rounding of `v`, whichever enclosure, if any, certifies it. -/
theorem certify_eq {R : ℚ → Prop} {rnd : ℚ → Option ℚ} (h : RoundsToNearest R rnd)
    (hI : RoundsOnIntervals rnd) {v : ℚ} :
    ∀ (cs : List (Option (ℚ × ℚ))) (exact : Option ℚ),
      (∀ c ∈ cs, ∀ H B, c = some (H, B) → Rat.abs (v - H) ≤ B) → exact = some v →
      certify rnd cs exact = rnd v
  | [], exact, _, hex => by subst hex; rfl
  | c :: cs, exact, hcs, hex => by
    unfold certify
    split
    · rename_i w hw
      cases c with
      | none => simp at hw
      | some p =>
        obtain ⟨H, B⟩ := p
        simp only [Option.bind_some] at hw
        exact (roundEnclosure_eq h hI (hcs _ List.mem_cons_self H B rfl) hw).symm
    · exact certify_eq h hI cs exact (fun c' hc' => hcs c' (List.mem_cons_of_mem _ hc')) hex

/-! ## The error of an approximate product -/

/-- The sum of the magnitudes. -/
def absSum (v : List ℚ) : ℚ := (v.map Rat.abs).sum

theorem absSum_nonneg (v : List ℚ) : 0 ≤ absSum v :=
  sum_nonneg fun a _ => abs_nonneg a

theorem abs_dot_le_mul_absSum {M : ℚ} (hM0 : 0 ≤ M) :
    ∀ (u v : List ℚ), (∀ a ∈ u, Rat.abs a ≤ M) → Rat.abs (dot u v) ≤ M * absSum v
  | [], v, _ => by
    rw [dot_nil_left, abs_zero]; exact Rat.mul_nonneg hM0 (absSum_nonneg v)
  | _ :: _, [], _ => by
    rw [dot_nil_right, abs_zero]; exact Rat.mul_nonneg hM0 (absSum_nonneg [])
  | a :: u, b :: v, hu => by
    rw [dot_cons]
    have ih := abs_dot_le_mul_absSum hM0 u v fun c hc => hu c (List.mem_cons_of_mem _ hc)
    have ha := hu a List.mem_cons_self
    have hab : Rat.abs (a * b) ≤ M * Rat.abs b := by
      rw [abs_mul]; exact Rat.mul_le_mul_of_nonneg_right ha (abs_nonneg b)
    have hsum : absSum (b :: v) = Rat.abs b + absSum v := by simp [absSum]
    rw [hsum]
    have := abs_add_le (a * b) (dot u v)
    grind

/-- `|u · v| ≤ max|uᵢ| Σ|vᵢ|`. -/
theorem abs_dot_le_maxAbs (u v : List ℚ) : Rat.abs (dot u v) ≤ maxAbs u * absSum v :=
  abs_dot_le_mul_absSum (maxAbs_nonneg u) u v fun _ ha => abs_le_maxAbs ha

/-- **The error of an approximate product.** For approximations `x'` of `x` and `y'` of `y`:
`|x · y − x' · y'| ≤ max|x − x'| Σ|y| + max|y − y'| Σ|x'|`. Per output entry this costs two products
of numbers kept per row and column. -/
theorem dot_approx_error (x x' y y' : List ℚ) (hx : x.length = x'.length)
    (hy : y.length = y'.length) :
    Rat.abs (dot x y - dot x' y') ≤
      maxAbs (List.zipWith (· - ·) x x') * absSum y +
        maxAbs (List.zipWith (· - ·) y y') * absSum x' := by
  have e1 := dot_zipWith_sub x x' y hx
  have e2 := dot_zipWith_sub y y' x' hy
  rw [dot_comm (List.zipWith (· - ·) y y') x', dot_comm y x', dot_comm y' x'] at e2
  have hsplit : dot x y - dot x' y' =
      dot (List.zipWith (· - ·) x x') y + dot x' (List.zipWith (· - ·) y y') := by
    rw [e1, e2]; grind
  rw [hsplit]
  refine Rat.le_trans (abs_add_le _ _) ?_
  have h1 := abs_dot_le_maxAbs (List.zipWith (· - ·) x x') y
  have h2 := abs_dot_le_maxAbs (List.zipWith (· - ·) y y') x'
  rw [dot_comm] at h2
  grind

/-! ## Correctly rounded Ozaki-I -/

/-- The slicing bound `(s + 1) k 2^(E + F − s(b+1))` of `exactTerms_error`. -/
def ozaki1Bound (b s : ℕ) (x y : List ℚ) : ℚ :=
  ((s + 1 : ℕ) : ℚ) * x.length * 2 ^ (splitExp b x + splitExp b y - s * (b + 1))

/-- The enclosure from `s` slices: the slice products from the engine, added exactly, and the
slicing bound. -/
def ozaki1Enclosure (eng : Engine) (b s : ℕ) (x y : List ℚ) : Option (ℚ × ℚ) :=
  (ozaki1 eng exactAdd b s x y).map fun H => (H, ozaki1Bound b s x y)

/-- **Correctly rounded Ozaki-I** for one output entry: the slice counts `ss` in turn, each checked
by the enclosure test, then the exact product. -/
def ozaki1CR (eng : Engine) (rnd : ℚ → Option ℚ) (b : ℕ) (ss : List ℕ) (x y : List ℚ) :
    Option ℚ :=
  certify rnd (ss.map fun s => ozaki1Enclosure eng b s x y) (some (dot x y))

/-- On an exact engine, the enclosure from `s` slices contains `x · y`. -/
theorem ozaki1Enclosure_sound {eng : Engine} {b budget : ℕ} (heng : eng.ExactOn b budget)
    (s : ℕ) {x y : List ℚ} (hlen : x.length = y.length)
    (hbudget : x.length * (2 ^ b * 2 ^ b) ≤ budget) {H B : ℚ}
    (he : ozaki1Enclosure eng b s x y = some (H, B)) : Rat.abs (dot x y - H) ≤ B := by
  unfold ozaki1Enclosure at he
  rw [ozaki1_eq_sumWith heng exactAdd s hlen hbudget, sumWith_exactAdd] at he
  simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at he
  obtain ⟨rfl, rfl⟩ := he
  have := exactTerms_error b s x y
  rw [show (0 : ℚ) + (exactTerms b s x y).sum = (exactTerms b s x y).sum by grind]
  exact this

/-- **Ozaki-I, correctly rounded.** On an engine exact on `b`-bit slices, `ozaki1CR` returns the
correctly rounded `x · y` for every input and every list of slice counts. -/
theorem ozaki1CR_eq {R : ℚ → Prop} {rnd : ℚ → Option ℚ} (h : RoundsToNearest R rnd)
    (hI : RoundsOnIntervals rnd) {eng : Engine} {b budget : ℕ} (heng : eng.ExactOn b budget)
    (ss : List ℕ) {x y : List ℚ} (hlen : x.length = y.length)
    (hbudget : x.length * (2 ^ b * 2 ^ b) ≤ budget) :
    ozaki1CR eng rnd b ss x y = rnd (dot x y) := by
  apply certify_eq h hI _ _ _ rfl
  intro c hc H B hcB
  obtain ⟨s, _, rfl⟩ := List.mem_map.mp hc
  exact ozaki1Enclosure_sound heng s hlen hbudget hcB

/-! ## Correctly rounded Ozaki-II -/

/-- `x` after scaling to `P` bits and truncation, as values `aᵢ 2^(−s)`. -/
def truncVals (P : ℕ) (x : List ℚ) : List ℚ :=
  (scaleTrunc (scaleShift P x) x).map fun z : ℤ => (z : ℚ) * 2 ^ (-scaleShift P x)

theorem truncVals_length (P : ℕ) (x : List ℚ) : (truncVals P x).length = x.length := by
  simp [truncVals, scaleTrunc_length]

/-- The truncation bound: `max|x − x̃| Σ|y| + max|y − ỹ| Σ|x̃|` (`dot_approx_error`). It vanishes
when both truncations are exact. -/
def ozaki2Bound (P : ℕ) (x y : List ℚ) : ℚ :=
  maxAbs (List.zipWith (· - ·) x (truncVals P x)) * absSum y +
    maxAbs (List.zipWith (· - ·) y (truncVals P y)) * absSum (truncVals P x)

/-- The enclosure from one CRT basis and precision: Ozaki-II without its final rounding, and the
truncation bound. -/
def ozaki2Enclosure (eng : Engine) (B : CRTBasis) (P : ℕ) (x y : List ℚ) : Option (ℚ × ℚ) :=
  (ozaki2 eng some B P x y).map fun H => (H, ozaki2Bound P x y)

/-- **Correctly rounded Ozaki-II** for one output entry: the configurations `(basis, P)` in turn,
each checked by the enclosure test, then the exact product. -/
def ozaki2CR (eng : Engine) (rnd : ℚ → Option ℚ) (cfgs : List (CRTBasis × ℕ)) (x y : List ℚ) :
    Option ℚ :=
  certify rnd (cfgs.map fun c => ozaki2Enclosure eng c.1 c.2 x y) (some (dot x y))

/-- Integers scaled by powers of two multiply to the rescaled integer product:
`(a 2^(−s)) · (c 2^(−t)) = (a · c) 2^(−(s+t))`. -/
theorem dot_scaledInts (a c : List ℤ) (s t : ℤ) :
    dot (a.map fun z : ℤ => (z : ℚ) * 2 ^ (-s)) (c.map fun z : ℤ => (z : ℚ) * 2 ^ (-t)) =
      (dotZ a c : ℚ) * 2 ^ (-(s + t)) := by
  have ha : (a.map fun z : ℤ => (z : ℚ) * 2 ^ (-s)) = (ofInts a).map fun q => q * 2 ^ (-s) := by
    simp [ofInts]
  have hc : (c.map fun z : ℤ => (z : ℚ) * 2 ^ (-t)) = (ofInts c).map fun q => q * 2 ^ (-t) := by
    simp [ofInts]
  rw [ha, hc, dot_map_mul_right, dot_comm, dot_map_mul_right, dot_comm, dot_ofInts,
    show -(s + t) = -s + -t by omega, two_pow_add]
  grind

/-- The product of the truncated values is the rescaled integer product. -/
theorem dot_truncVals (P : ℕ) (x y : List ℚ) :
    dot (truncVals P x) (truncVals P y) =
      (dotZ (scaleTrunc (scaleShift P x) x) (scaleTrunc (scaleShift P y) y) : ℚ) *
        2 ^ (-(scaleShift P x + scaleShift P y)) :=
  dot_scaledInts _ _ _ _

/-- On an exact engine, the enclosure from a valid basis contains `x · y`. -/
theorem ozaki2Enclosure_sound {eng : Engine} {b budget : ℕ} (heng : eng.ExactOn b budget)
    {B : CRTBasis} (hB : B.Valid) (hmb : ∀ m ∈ B.moduli, m ≤ 2 ^ (b + 1)) (P : ℕ) {x y : List ℚ}
    (hlen : x.length = y.length) (hbudget : x.length * (2 ^ b * 2 ^ b) ≤ budget)
    (hrange : 2 * x.length * (2 ^ P * 2 ^ P) < B.modulus) {H Bd : ℚ}
    (he : ozaki2Enclosure eng B P x y = some (H, Bd)) : Rat.abs (dot x y - H) ≤ Bd := by
  unfold ozaki2Enclosure at he
  rw [ozaki2_eq heng some hB hmb P hlen hbudget hrange] at he
  simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at he
  obtain ⟨rfl, rfl⟩ := he
  rw [← dot_truncVals]
  exact dot_approx_error x (truncVals P x) y (truncVals P y) (truncVals_length P x).symm
    (truncVals_length P y).symm

/-- **Ozaki-II, correctly rounded.** On an engine exact on `b`-bit residues, with configurations
whose bases are valid, whose moduli are at most `2^(b+1)`, and whose products stay within CRT
range, `ozaki2CR` returns the correctly rounded `x · y` for every input. -/
theorem ozaki2CR_eq {R : ℚ → Prop} {rnd : ℚ → Option ℚ} (h : RoundsToNearest R rnd)
    (hI : RoundsOnIntervals rnd) {eng : Engine} {b budget : ℕ} (heng : eng.ExactOn b budget)
    {cfgs : List (CRTBasis × ℕ)} {x y : List ℚ}
    (hcfg : ∀ c ∈ cfgs, c.1.Valid ∧ (∀ m ∈ c.1.moduli, m ≤ 2 ^ (b + 1)) ∧
      2 * x.length * (2 ^ c.2 * 2 ^ c.2) < c.1.modulus)
    (hlen : x.length = y.length) (hbudget : x.length * (2 ^ b * 2 ^ b) ≤ budget) :
    ozaki2CR eng rnd cfgs x y = rnd (dot x y) := by
  apply certify_eq h hI _ _ _ rfl
  intro c hc H Bd hcB
  obtain ⟨cfg, hmem, rfl⟩ := List.mem_map.mp hc
  obtain ⟨hB, hmb, hrange⟩ := hcfg cfg hmem
  exact ozaki2Enclosure_sound heng hB hmb cfg.2 hlen hbudget hrange hcB

/-! ## When the check settles an entry

The theorems above hold whatever the check does, because the last resort is exact. The check's own
content: if `v − 2B` and `v + 2B` round to the same value, in particular if the exact value `v` lies
more than `2B` from every rounding boundary, the enclosure `[H − B, H + B]` around any `H` within
`B` of `v` settles the entry, with no exact path. (At a distance of exactly `2B` an endpoint can be a
tie that rounds the other way, so "at least `2B`" would not suffice.) With Ozaki-I's bound `B` this
says the fast path settles every entry whose product is more than `2 (s + 1) k 2^(E + F − s(b+1))`
from a rounding boundary. -/

/-- **The check settles an entry with margin.** If `v − 2B` and `v + 2B` round to the same `w`, the
enclosure of any `H` within `B` of `v` returns `w`. -/
theorem roundEnclosure_of_margin {R : ℚ → Prop} {rnd : ℚ → Option ℚ} (h : RoundsToNearest R rnd)
    (hI : RoundsOnIntervals rnd) {H B v w : ℚ} (hv : Rat.abs (v - H) ≤ B)
    (hlo : rnd (v - 2 * B) = some w) (hhi : rnd (v + 2 * B) = some w) :
    roundEnclosure rnd H B = some w := by
  have hB : 0 ≤ B := Rat.le_trans (abs_nonneg _) hv
  obtain ⟨h1, h2⟩ := (abs_le_iff _ _).mp hv
  have hl : rnd (H - B) = some w := by
    refine round_eq_of_enclosure h hI (H := v) (B := 2 * B) ?_ ?_ ?_
    · rw [abs_le_iff]; constructor <;> grind
    · rw [show v - 2 * B = v - 2 * B by rfl]; exact hlo
    · exact hhi
  have hu : rnd (H + B) = some w := by
    refine round_eq_of_enclosure h hI (H := v) (B := 2 * B) ?_ hlo hhi
    rw [abs_le_iff]; constructor <;> grind
  unfold roundEnclosure
  rw [hl, hu]
  simp

/-- **Ozaki-I's fast path settles an entry** whenever `x · y` is `2B` away from every rounding
boundary, `B` the slicing bound of `s` slices: the enclosure from the engine's slice products
returns the correct rounding, and the exact path is not needed. -/
theorem ozaki1Enclosure_settles {R : ℚ → Prop} {rnd : ℚ → Option ℚ} (h : RoundsToNearest R rnd)
    (hI : RoundsOnIntervals rnd) {eng : Engine} {b budget : ℕ} (heng : eng.ExactOn b budget)
    (s : ℕ) {x y : List ℚ} (hlen : x.length = y.length)
    (hbudget : x.length * (2 ^ b * 2 ^ b) ≤ budget) {w : ℚ}
    (hlo : rnd (dot x y - 2 * ozaki1Bound b s x y) = some w)
    (hhi : rnd (dot x y + 2 * ozaki1Bound b s x y) = some w) :
    (ozaki1Enclosure eng b s x y).bind (fun p => roundEnclosure rnd p.1 p.2) = some w := by
  have he : ozaki1Enclosure eng b s x y =
      some ((exactTerms b s x y).sum, ozaki1Bound b s x y) := by
    unfold ozaki1Enclosure
    rw [ozaki1_eq_sumWith heng exactAdd s hlen hbudget, sumWith_exactAdd]
    simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq, and_true]
    grind
  rw [he, Option.bind_some]
  exact roundEnclosure_of_margin h hI (ozaki1Enclosure_sound heng s hlen hbudget he) hlo hhi

/-! ## The exact path on the engine

When the check fails, the exact product can itself come from the engine: with all `s²` slice
products (not only `t + u < s`) and enough slices that nothing is left over, Ozaki-I is exact
(`ozaki1Full_eq`). Inputs on a grid `2^m`, such as binary32 values (`m = −149`), leave nothing over
once the slicing bound drops below `2^m` (`split_residual_zero`). `ozaki1CRE` uses the smallest
such slice count as its fallback, so the whole correctly rounded scheme runs on the engine plus
integer additions (`ozaki1CRE_eq`). -/

/-- `a` is an integer multiple of `2^m`. -/
def GridMultiple (m : ℤ) (a : ℚ) : Prop := ∃ z : ℤ, a = (z : ℚ) * 2 ^ m

theorem two_pow_eq_natCast_mul {m g : ℤ} (h : m ≤ g) :
    (2 : ℚ) ^ g = ((2 ^ (g - m).toNat : ℕ) : ℚ) * 2 ^ m := by
  rw [← two_pow_natCast, ← two_pow_add]; congr 1; omega

/-- Slicing keeps a grid: what a slice leaves of a multiple of `2^m` is a multiple of `2^m`. On a
coarser grid the subtraction keeps it; on a finer one the rounding is exact and nothing is left. -/
theorem gridMultiple_sliceRest {m g : ℤ} {a : ℚ} (ha : GridMultiple m a) :
    GridMultiple m (a - (roundNearestEven (a / 2 ^ g) : ℚ) * 2 ^ g) := by
  obtain ⟨z, rfl⟩ := ha
  by_cases hgm : m ≤ g
  · refine ⟨z - roundNearestEven ((z : ℚ) * 2 ^ m / 2 ^ g) * ((2 ^ (g - m).toNat : ℕ) : ℤ), ?_⟩
    rw [two_pow_eq_natCast_mul hgm, Rat.intCast_sub, Rat.intCast_mul, Rat.intCast_natCast]
    grind
  · have hgm' : g ≤ m := by omega
    have hq : (z : ℚ) * 2 ^ m / 2 ^ g = ((z * ((2 ^ (m - g).toNat : ℕ) : ℤ) : ℤ) : ℚ) := by
      have hone : (2 : ℚ) ^ g * 2 ^ (-g) = 1 := by rw [Rat.mul_comm]; exact two_pow_neg_mul g
      rw [Rat.intCast_mul, Rat.intCast_natCast, two_pow_eq_natCast_mul hgm', div_two_pow,
        Rat.mul_assoc, Rat.mul_assoc, hone]
      grind
    refine ⟨0, ?_⟩
    rw [hq, roundNearestEven_intCast, ← hq, Rat.div_mul_cancel (two_pow_ne_zero g)]
    grind

theorem splitFrom_gridMultiple (b : ℕ) {m : ℤ} :
    ∀ (s : ℕ) (prev : ℤ) (x : List ℚ), (∀ a ∈ x, GridMultiple m a) →
      ∀ r ∈ (splitFrom b s prev x).2, GridMultiple m r
  | 0, _, x, hx => by simpa [splitFrom] using hx
  | s + 1, prev, x, hx => by
    simp only [splitFrom]
    refine splitFrom_gridMultiple b s _ _ ?_
    intro r hr
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hr
    exact gridMultiple_sliceRest (hx a ha)

theorem eq_zero_of_gridMultiple {m : ℤ} {a : ℚ} (ha : GridMultiple m a) (hlt : Rat.abs a < 2 ^ m) : a = 0 := by
  obtain ⟨z, rfl⟩ := ha
  rw [abs_mul_two_pow, abs_intCast] at hlt
  have hpos := two_pow_pos m
  have h1 : ((z.natAbs : ℕ) : ℚ) < 1 := by
    have : ((z.natAbs : ℕ) : ℚ) * 2 ^ m < 1 * 2 ^ m := by grind
    exact (Rat.mul_lt_mul_right hpos).mp this
  have h2 : z.natAbs < 1 := by exact_mod_cast h1
  have hz : z = 0 := by omega
  subst hz; simp

/-- **Nothing is left over.** If every entry of `x` is a multiple of `2^m` and the slicing bound
`2^(E − s(b+1))` is below `2^m`, the residual after `s` slices is zero. -/
theorem split_residual_zero {b s : ℕ} {m : ℤ} {x : List ℚ} (hx : ∀ a ∈ x, GridMultiple m a)
    (hs : splitExp b x - s * (b + 1) < m) : ∀ r ∈ (split b s x).2, r = 0 := fun r hr =>
  eq_zero_of_gridMultiple (splitFrom_gridMultiple b s b x hx r hr)
    (lt_of_le_of_lt' (split_residual_le b s x r hr) (two_pow_lt hs))

/-- All pairs of slices of `x` and `y`. -/
def slicePairs (sx sy : List Slice) : List (Slice × Slice) :=
  sx.flatMap fun sl => sy.map fun sl' => (sl, sl')

/-- The engine's product of two slices, scaled by `2^(g + h)`. -/
def fullTerm (eng : Engine) (sl sl' : Slice) : Option ℚ :=
  (eng sl.coeffs sl'.coeffs).map fun v => 2 ^ (sl.grid + sl'.grid) * v

/-- **Ozaki-I with all `s²` slice products**, added exactly. -/
def ozaki1Full (eng : Engine) (b s : ℕ) (x y : List ℚ) : Option ℚ :=
  ((slicePairs (split b s x).1 (split b s y).1).mapM fun p => fullTerm eng p.1 p.2).map List.sum

theorem sum_slicePairs (sx sy : List Slice) (f : Slice → Slice → ℚ) :
    ((slicePairs sx sy).map fun p => f p.1 p.2).sum = (sx.map fun sl => (sy.map (f sl)).sum).sum := by
  induction sx with
  | nil => simp [slicePairs]
  | cons sl sx ih =>
    simp only [slicePairs, List.flatMap_cons, List.map_append, sum_append_q, List.map_map,
      List.map_cons, List.sum_cons] at ih ⊢
    rw [← ih]; rfl

theorem dot_zero_left {r : List ℚ} (hr : ∀ a ∈ r, a = 0) (y : List ℚ) : dot r y = 0 := by
  induction r generalizing y with
  | nil => simp
  | cons a r ih =>
    cases y with
    | nil => simp
    | cons b y =>
      rw [dot_cons, hr a List.mem_cons_self, ih (fun c hc => hr c (List.mem_cons_of_mem _ hc))]
      grind

/-- With nothing left over, the `s²` scaled slice products add up to `x · y`. -/
theorem dot_eq_full {b s : ℕ} {x y : List ℚ} (hx0 : ∀ r ∈ (split b s x).2, r = 0)
    (hy0 : ∀ r ∈ (split b s y).2, r = 0) :
    dot x y = ((split b s x).1.map fun sl => ((split b s y).1.map fun sl' =>
      2 ^ (sl.grid + sl'.grid) * (dotZ sl.coeffs sl'.coeffs : ℚ)).sum).sum := by
  rw [split_dot b s x y, dot_zero_left hx0, Rat.add_zero]
  congr 1
  apply List.map_congr_left
  intro sl _
  rw [dot_comm, split_dot b s y (ofInts sl.coeffs), dot_zero_left hy0, Rat.add_zero,
    ← sum_map_mul_left]
  congr 1
  apply List.map_congr_left
  intro sl' _
  rw [dot_ofInts, dotZ_comm, two_pow_add]
  grind

/-- **The exact path.** On an exact engine, with nothing left over after `s` slices, Ozaki-I with
all `s²` slice products is `x · y`. -/
theorem ozaki1Full_eq {eng : Engine} {b budget : ℕ} (heng : eng.ExactOn b budget) {s : ℕ}
    {x y : List ℚ} (hlen : x.length = y.length) (hbudget : x.length * (2 ^ b * 2 ^ b) ≤ budget)
    (hx0 : ∀ r ∈ (split b s x).2, r = 0) (hy0 : ∀ r ∈ (split b s y).2, r = 0) :
    ozaki1Full eng b s x y = some (dot x y) := by
  unfold ozaki1Full
  obtain ⟨_, hcx, _⟩ := split_length b s x
  obtain ⟨_, hcy, _⟩ := split_length b s y
  rw [mapM_eq_some_map (g := fun p : Slice × Slice =>
    2 ^ (p.1.grid + p.2.grid) * (dotZ p.1.coeffs p.2.coeffs : ℚ))]
  · rw [Option.map_some, dot_eq_full hx0 hy0]
    exact congrArg some (sum_slicePairs _ _ fun sl sl' =>
      2 ^ (sl.grid + sl'.grid) * (dotZ sl.coeffs sl'.coeffs : ℚ))
  · intro p hp
    obtain ⟨sl, hsl, hp⟩ := List.mem_flatMap.mp hp
    obtain ⟨sl', hsl', rfl⟩ := List.mem_map.mp hp
    unfold fullTerm
    rw [heng _ _ (by rw [hcx _ hsl, hcy _ hsl', hlen]) (split_coeff_bound b s x _ hsl)
      (split_coeff_bound b s y _ hsl')]
    · rfl
    · refine Nat.le_trans (dotAbs_le _ _ _ _ (split_coeff_bound b s x _ hsl)
        (split_coeff_bound b s y _ hsl')) ?_
      rw [hcx _ hsl]; exact hbudget

/-- Nothing is left over in `x` or `y` after `s` slices. -/
def residualsVanish (b s : ℕ) (x y : List ℚ) : Bool :=
  (split b s x).2.all (· == 0) && (split b s y).2.all (· == 0)

/-- The exact path: Ozaki-I with all slice products, at the smallest slice count up to `smax` that
leaves nothing over. -/
def ozaki1ExactPath (eng : Engine) (b smax : ℕ) (x y : List ℚ) : Option ℚ :=
  match (List.range' 1 smax).find? fun s => residualsVanish b s x y with
  | some s => ozaki1Full eng b s x y
  | none => none

theorem ozaki1ExactPath_eq {eng : Engine} {b budget smax : ℕ} (heng : eng.ExactOn b budget)
    {x y : List ℚ} (hlen : x.length = y.length) (hbudget : x.length * (2 ^ b * 2 ^ b) ≤ budget)
    (hvanish : ∃ s ∈ List.range' 1 smax, residualsVanish b s x y = true) :
    ozaki1ExactPath eng b smax x y = some (dot x y) := by
  unfold ozaki1ExactPath
  obtain ⟨s, hs⟩ := Option.isSome_iff_exists.mp (List.find?_isSome.mpr hvanish)
  rw [hs]
  have hv := List.find?_some hs
  simp only [residualsVanish, Bool.and_eq_true, List.all_eq_true, beq_iff_eq] at hv
  exact ozaki1Full_eq heng hlen hbudget hv.1 hv.2

/-- **Correctly rounded Ozaki-I with its exact path on the engine**: slice counts `ss` in turn, each checked
by the enclosure test, then the exact path. -/
def ozaki1CRE (eng : Engine) (rnd : ℚ → Option ℚ) (b : ℕ) (ss : List ℕ) (smax : ℕ)
    (x y : List ℚ) : Option ℚ :=
  certify rnd (ss.map fun s => ozaki1Enclosure eng b s x y) (ozaki1ExactPath eng b smax x y)

theorem ozaki1CRE_eq {R : ℚ → Prop} {rnd : ℚ → Option ℚ} (h : RoundsToNearest R rnd)
    (hI : RoundsOnIntervals rnd) {eng : Engine} {b budget : ℕ} (heng : eng.ExactOn b budget)
    (ss : List ℕ) {smax : ℕ} {x y : List ℚ} (hlen : x.length = y.length)
    (hbudget : x.length * (2 ^ b * 2 ^ b) ≤ budget)
    (hvanish : ∃ s ∈ List.range' 1 smax, residualsVanish b s x y = true) :
    ozaki1CRE eng rnd b ss smax x y = rnd (dot x y) := by
  apply certify_eq h hI _ _ _ (ozaki1ExactPath_eq heng hlen hbudget hvanish)
  intro c hc H B hcB
  obtain ⟨s, _, rfl⟩ := List.mem_map.mp hc
  exact ozaki1Enclosure_sound heng s hlen hbudget hcB

/-- **Correctly rounded Ozaki-II with its exact path on the engine**: the configurations `(basis, P)` in turn,
each checked by the enclosure test, then Ozaki-I's exact path on the same engine. -/
def ozaki2CRE (eng : Engine) (rnd : ℚ → Option ℚ) (cfgs : List (CRTBasis × ℕ)) (b smax : ℕ)
    (x y : List ℚ) : Option ℚ :=
  certify rnd (cfgs.map fun c => ozaki2Enclosure eng c.1 c.2 x y) (ozaki1ExactPath eng b smax x y)

theorem ozaki2CRE_eq {R : ℚ → Prop} {rnd : ℚ → Option ℚ} (h : RoundsToNearest R rnd)
    (hI : RoundsOnIntervals rnd) {eng : Engine} {b budget : ℕ} (heng : eng.ExactOn b budget)
    {cfgs : List (CRTBasis × ℕ)} {smax : ℕ} {x y : List ℚ}
    (hcfg : ∀ c ∈ cfgs, c.1.Valid ∧ (∀ m ∈ c.1.moduli, m ≤ 2 ^ (b + 1)) ∧
      2 * x.length * (2 ^ c.2 * 2 ^ c.2) < c.1.modulus)
    (hlen : x.length = y.length) (hbudget : x.length * (2 ^ b * 2 ^ b) ≤ budget)
    (hvanish : ∃ s ∈ List.range' 1 smax, residualsVanish b s x y = true) :
    ozaki2CRE eng rnd cfgs b smax x y = rnd (dot x y) := by
  apply certify_eq h hI _ _ _ (ozaki1ExactPath_eq heng hlen hbudget hvanish)
  intro c hc H Bd hcB
  obtain ⟨cfg, hmem, rfl⟩ := List.mem_map.mp hc
  obtain ⟨hB, hmb, hrange⟩ := hcfg cfg hmem
  exact ozaki2Enclosure_sound heng hB hmb cfg.2 hlen hbudget hrange hcB

/-- Inputs on the grid `2^m` with exponent at most `E` leave nothing over after `smax` slices when
`E − smax (b+1) < m`. -/
theorem residualsVanish_of_gridMultiple {b smax : ℕ} {m : ℤ} {x y : List ℚ} (hsmax : 0 < smax)
    (hx : ∀ a ∈ x, GridMultiple m a) (hy : ∀ a ∈ y, GridMultiple m a)
    (hex : splitExp b x - smax * (b + 1) < m) (hey : splitExp b y - smax * (b + 1) < m) :
    ∃ s ∈ List.range' 1 smax, residualsVanish b s x y = true := by
  refine ⟨smax, List.mem_range'.mpr ⟨smax - 1, by omega, by omega⟩, ?_⟩
  simp only [residualsVanish, Bool.and_eq_true, List.all_eq_true, beq_iff_eq]
  exact ⟨split_residual_zero hx hex, split_residual_zero hy hey⟩

end Ozaki
