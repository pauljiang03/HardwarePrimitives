import Ozaki.SliceRuleCR
import Ozaki.Window
import Ozaki.BoundedInt

/-! # Two design rules for correctly rounded Ozaki-I, from the simulation

A simulation of the correctly rounded schemes at realistic sizes (`scripts/fallback_sim.py`)
suggested two rules. Both keep correct rounding for free, because the check is correct for any
list of slice counts (`ozaki1CRE_eq`, `ozaki1CRW_eq`, `ozaki1CRI_eq`); what they change is cost.

* **Slice counts that grow with `k`.** `crSlices b t k r` starts at `slicesForCR b t k` (the slice
  rule with `⌈log₂ k⌉` more bits, `Ozaki.SliceRuleCR`) and tries `r` more. Its first check's bound
  is at most `2^-t · max|x| · max|y|`, without the factor `k` (`crSlices_head_bound`). The schemes
  `ozaki1CRK`, `ozaki1CRWK` and `ozaki1CRIK` (rational, window, integer) take `k` from the inputs.
* **The adaptive shortcut.** The exact path's slice count `sₑ`, the least that leaves nothing over,
  is known once the inputs are sliced (`exactCount`). When `sₑ²`, the exact path's engine products,
  is at most the first check's `s(s+1)/2`, `ozaki1CRA` goes straight to the exact path; otherwise it
  is `ozaki1CRE`. Low-precision inputs, which leave nothing over after a few slices, take the
  shortcut.

**The cost model.** `creCost` counts the engine products of an implementation that computes each
check's slice products afresh: `s(s+1)/2` for every check tried, up to and including the first that
settles, plus `sₑ²` for the exact path if none settles (`certifyCost` follows `certify`'s control
flow). The exact path takes `sₑ²` products (`slicePairs_split_length`) and a check `s(s+1)/2`
(`trianglePairs_length`). Then:

* `ozaki1CRA_cost_le`: the adaptive scheme never costs more than `ozaki1CRE` with the same list;
* `ozaki1CRA_cost_shortcut`: when `sₑ² ≤ s(s+1)/2` for the first check, it costs exactly `sₑ²`,
  and when the first check settles, `ozaki1CRE` costs exactly `s(s+1)/2` (`creCost_first_settles`).

An implementation that reuses the products of one check in the next (the triangles are nested,
`split_prefix`) costs less for both; the comparison is the same. The costs are engine products per
output entry, not time. -/

local notation "ℕ" => Nat
local notation "ℤ" => Int
local notation "ℚ" => Rat

namespace Ozaki

/-! ## Slice counts that grow with `k` -/

/-- The slice counts for correct rounding at inner dimension `k`: `slicesForCR b t k`, then `r`
more. -/
def crSlices (b t k r : ℕ) : List ℕ := List.range' (slicesForCR b t k) (r + 1)

theorem crSlices_head (b t k r : ℕ) : (crSlices b t k r).head? = some (slicesForCR b t k) := by
  simp [crSlices, List.range'_succ]

/-- **The first check of `crSlices` has a bound without the factor `k`.** -/
theorem crSlices_head_bound {b t k r : ℕ} (hs : 0 < slicesForCR b t k) {x y : List ℚ}
    (hk : x.length ≤ k) (hx : maxAbs x ≠ 0) (hy : maxAbs y ≠ 0) :
    ∃ s, (crSlices b t k r).head? = some s ∧ ozaki1Bound b s x y ≤ maxAbs x * maxAbs y * 2 ^ (-(t : ℤ)) :=
  ⟨_, crSlices_head b t k r, ozaki1Bound_le_cr hs hk hx hy⟩

/-- Correctly rounded Ozaki-I with slice counts from `crSlices`, `k` taken from the inputs. -/
def ozaki1CRK (eng : Engine) (rnd : ℚ → Option ℚ) (b t r smax : ℕ) (x y : List ℚ) : Option ℚ :=
  ozaki1CRE eng rnd b (crSlices b t x.length r) smax x y

theorem ozaki1CRK_eq {R : ℚ → Prop} {rnd : ℚ → Option ℚ} (h : RoundsToNearest R rnd)
    (hI : RoundsOnIntervals rnd) {eng : Engine} {b budget : ℕ} (heng : eng.ExactOn b budget)
    (t r : ℕ) {smax : ℕ} {x y : List ℚ} (hlen : x.length = y.length)
    (hbudget : x.length * (2 ^ b * 2 ^ b) ≤ budget)
    (hvanish : ∃ s ∈ List.range' 1 smax, residualsVanish b s x y = true) :
    ozaki1CRK eng rnd b t r smax x y = rnd (dot x y) :=
  ozaki1CRE_eq h hI heng _ hlen hbudget hvanish

/-- The same with the window accumulator. -/
def ozaki1CRWK (eng : Engine) (rnd : ℚ → Option ℚ) (b W t r smax : ℕ) (x y : List ℚ) :
    Option ℚ :=
  ozaki1CRW eng rnd b W (crSlices b t x.length r) smax x y

theorem ozaki1CRWK_eq {R : ℚ → Prop} {rnd : ℚ → Option ℚ} (h : RoundsToNearest R rnd)
    (hI : RoundsOnIntervals rnd) {eng : Engine} {b budget : ℕ} (heng : eng.ExactOn b budget)
    (W t r : ℕ) {smax : ℕ} {x y : List ℚ} (hlen : x.length = y.length)
    (hbudget : x.length * (2 ^ b * 2 ^ b) ≤ budget)
    (hvanish : ∃ s ∈ List.range' 1 smax, residualsVanish b s x y = true) :
    ozaki1CRWK eng rnd b W t r smax x y = rnd (dot x y) :=
  ozaki1CRW_eq h hI heng W _ hlen hbudget hvanish

/-- The same as one integer function from `(significand, exponent)` inputs. -/
def ozaki1CRIK (eng : Engine) (p : ℕ) (emin emax : ℤ) (b W t r smax : ℕ)
    (xs ys : List (ℤ × ℤ)) : Option ℚ :=
  ozaki1CRI eng p emin emax b W (crSlices b t xs.length r) smax xs ys

theorem ozaki1CRIK_eq {p : ℕ} {emin emax : ℤ} (hp : 0 < p) (hle : emin ≤ emax) {eng : Engine}
    {b budget : ℕ} (heng : eng.ExactOn b budget) (W t r : ℕ) {smax : ℕ}
    {xs ys : List (ℤ × ℤ)} (hlen : xs.length = ys.length)
    (hbudget : xs.length * (2 ^ b * 2 ^ b) ≤ budget)
    (hvanish : ∃ s ∈ List.range' 1 smax, vanishInt b s xs ys = true) :
    ozaki1CRIK eng p emin emax b W t r smax xs ys =
      roundRNE p emin emax (dot (entryVals xs) (entryVals ys)) :=
  ozaki1CRI_eq hp hle heng W _ hlen hbudget hvanish

/-! ## The adaptive shortcut -/

/-- The exact path's slice count: the least `s` up to `smax` that leaves nothing over. -/
def exactCount (b smax : ℕ) (x y : List ℚ) : Option ℕ :=
  (List.range' 1 smax).find? fun s => residualsVanish b s x y

/-- The same on `(significand, exponent)` inputs, with integer operations. -/
def exactCountI (b smax : ℕ) (xs ys : List (ℤ × ℤ)) : Option ℕ :=
  (List.range' 1 smax).find? fun s => vanishInt b s xs ys

theorem exactCountI_eq (b smax : ℕ) (xs ys : List (ℤ × ℤ)) :
    exactCountI b smax xs ys = exactCount b smax (entryVals xs) (entryVals ys) := by
  simp only [exactCountI, exactCount, vanishInt_eq]

/-- The engine products of the first check of a list. -/
def firstCost : List ℕ → ℕ
  | [] => 0
  | s :: _ => (trianglePairs s).length

/-- **The adaptive list**: none at all, so straight to the exact path, when the exact path's `sₑ²`
products are at most the first check's. -/
def adaptList (se : Option ℕ) (ss : List ℕ) : List ℕ :=
  match se with
  | some n => if n * n ≤ firstCost ss then [] else ss
  | none => ss

/-- Correctly rounded Ozaki-I with the adaptive shortcut. -/
def ozaki1CRA (eng : Engine) (rnd : ℚ → Option ℚ) (b : ℕ) (ss : List ℕ) (smax : ℕ)
    (x y : List ℚ) : Option ℚ :=
  ozaki1CRE eng rnd b (adaptList (exactCount b smax x y) ss) smax x y

/-- **The shortcut keeps correct rounding.** -/
theorem ozaki1CRA_eq {R : ℚ → Prop} {rnd : ℚ → Option ℚ} (h : RoundsToNearest R rnd)
    (hI : RoundsOnIntervals rnd) {eng : Engine} {b budget : ℕ} (heng : eng.ExactOn b budget)
    (ss : List ℕ) {smax : ℕ} {x y : List ℚ} (hlen : x.length = y.length)
    (hbudget : x.length * (2 ^ b * 2 ^ b) ≤ budget)
    (hvanish : ∃ s ∈ List.range' 1 smax, residualsVanish b s x y = true) :
    ozaki1CRA eng rnd b ss smax x y = rnd (dot x y) :=
  ozaki1CRE_eq h hI heng _ hlen hbudget hvanish

/-- With the window accumulator. -/
def ozaki1CRWA (eng : Engine) (rnd : ℚ → Option ℚ) (b W : ℕ) (ss : List ℕ) (smax : ℕ)
    (x y : List ℚ) : Option ℚ :=
  ozaki1CRW eng rnd b W (adaptList (exactCount b smax x y) ss) smax x y

theorem ozaki1CRWA_eq {R : ℚ → Prop} {rnd : ℚ → Option ℚ} (h : RoundsToNearest R rnd)
    (hI : RoundsOnIntervals rnd) {eng : Engine} {b budget : ℕ} (heng : eng.ExactOn b budget)
    (W : ℕ) (ss : List ℕ) {smax : ℕ} {x y : List ℚ} (hlen : x.length = y.length)
    (hbudget : x.length * (2 ^ b * 2 ^ b) ≤ budget)
    (hvanish : ∃ s ∈ List.range' 1 smax, residualsVanish b s x y = true) :
    ozaki1CRWA eng rnd b W ss smax x y = rnd (dot x y) :=
  ozaki1CRW_eq h hI heng W _ hlen hbudget hvanish

/-- As one integer function: the exact path's slice count by integer operations, then the integer
scheme with the adaptive list. -/
def ozaki1CRIA (eng : Engine) (p : ℕ) (emin emax : ℤ) (b W : ℕ) (ss : List ℕ) (smax : ℕ)
    (xs ys : List (ℤ × ℤ)) : Option ℚ :=
  ozaki1CRI eng p emin emax b W (adaptList (exactCountI b smax xs ys) ss) smax xs ys

theorem ozaki1CRIA_eq {p : ℕ} {emin emax : ℤ} (hp : 0 < p) (hle : emin ≤ emax) {eng : Engine}
    {b budget : ℕ} (heng : eng.ExactOn b budget) (W : ℕ) (ss : List ℕ) {smax : ℕ}
    {xs ys : List (ℤ × ℤ)} (hlen : xs.length = ys.length)
    (hbudget : xs.length * (2 ^ b * 2 ^ b) ≤ budget)
    (hvanish : ∃ s ∈ List.range' 1 smax, vanishInt b s xs ys = true) :
    ozaki1CRIA eng p emin emax b W ss smax xs ys =
      roundRNE p emin emax (dot (entryVals xs) (entryVals ys)) :=
  ozaki1CRI_eq hp hle heng W _ hlen hbudget hvanish

/-- Both rules together: slice counts from `k`, and the shortcut. -/
def ozaki1CRKA (eng : Engine) (rnd : ℚ → Option ℚ) (b t r smax : ℕ) (x y : List ℚ) :
    Option ℚ :=
  ozaki1CRA eng rnd b (crSlices b t x.length r) smax x y

theorem ozaki1CRKA_eq {R : ℚ → Prop} {rnd : ℚ → Option ℚ} (h : RoundsToNearest R rnd)
    (hI : RoundsOnIntervals rnd) {eng : Engine} {b budget : ℕ} (heng : eng.ExactOn b budget)
    (t r : ℕ) {smax : ℕ} {x y : List ℚ} (hlen : x.length = y.length)
    (hbudget : x.length * (2 ^ b * 2 ^ b) ≤ budget)
    (hvanish : ∃ s ∈ List.range' 1 smax, residualsVanish b s x y = true) :
    ozaki1CRKA eng rnd b t r smax x y = rnd (dot x y) :=
  ozaki1CRA_eq h hI heng _ hlen hbudget hvanish

/-- Both rules as one integer function. -/
def ozaki1CRIKA (eng : Engine) (p : ℕ) (emin emax : ℤ) (b W t r smax : ℕ)
    (xs ys : List (ℤ × ℤ)) : Option ℚ :=
  ozaki1CRIA eng p emin emax b W (crSlices b t xs.length r) smax xs ys

theorem ozaki1CRIKA_eq {p : ℕ} {emin emax : ℤ} (hp : 0 < p) (hle : emin ≤ emax) {eng : Engine}
    {b budget : ℕ} (heng : eng.ExactOn b budget) (W t r : ℕ) {smax : ℕ}
    {xs ys : List (ℤ × ℤ)} (hlen : xs.length = ys.length)
    (hbudget : xs.length * (2 ^ b * 2 ^ b) ≤ budget)
    (hvanish : ∃ s ∈ List.range' 1 smax, vanishInt b s xs ys = true) :
    ozaki1CRIKA eng p emin emax b W t r smax xs ys =
      roundRNE p emin emax (dot (entryVals xs) (entryVals ys)) :=
  ozaki1CRIA_eq hp hle heng W _ hlen hbudget hvanish

/-! ## The cost model -/

theorem slicePairs_length : ∀ (sx sy : List Slice), (slicePairs sx sy).length = sx.length * sy.length
  | [], _ => by simp [slicePairs]
  | _ :: sx, sy => by
    simp only [slicePairs, List.flatMap_cons, List.length_append, List.length_map,
      List.length_cons] at *
    rw [show (sx.flatMap fun sl => sy.map fun sl' => (sl, sl')) = slicePairs sx sy from rfl,
      slicePairs_length sx sy, Nat.succ_mul]; omega

/-- **The exact path at `sₑ` slices takes `sₑ²` engine products.** -/
theorem slicePairs_split_length (b s : ℕ) (x y : List ℚ) :
    (slicePairs (split b s x).1 (split b s y).1).length = s * s := by
  rw [slicePairs_length, (split_length b s x).1, (split_length b s y).1]

/-- Engine products of `certify` over checks given as (settles, products), then the exact path's
`e`: each check tried until one settles; the exact path only if none does. -/
def certifyCost : List (Bool × ℕ) → ℕ → ℕ
  | [], e => e
  | (settled, w) :: cs, e => w + if settled then 0 else certifyCost cs e

/-- Whether the enclosure from `s` slices settles the entry. -/
def checkSettles (eng : Engine) (rnd : ℚ → Option ℚ) (b s : ℕ) (x y : List ℚ) : Bool :=
  ((ozaki1Enclosure eng b s x y).bind fun p => roundEnclosure rnd p.1 p.2).isSome

/-- **The engine products of `ozaki1CRE`**: `s(s+1)/2` per check tried, and `sₑ²` for the exact path
if no check settles. -/
def creCost (eng : Engine) (rnd : ℚ → Option ℚ) (b : ℕ) (ss : List ℕ) (smax : ℕ)
    (x y : List ℚ) : ℕ :=
  certifyCost (ss.map fun s => (checkSettles eng rnd b s x y, (trianglePairs s).length))
    ((exactCount b smax x y).elim 0 fun se => se * se)

/-- The engine products of `ozaki1CRA`. -/
def craCost (eng : Engine) (rnd : ℚ → Option ℚ) (b : ℕ) (ss : List ℕ) (smax : ℕ)
    (x y : List ℚ) : ℕ :=
  creCost eng rnd b (adaptList (exactCount b smax x y) ss) smax x y

theorem firstCost_le_creCost (eng : Engine) (rnd : ℚ → Option ℚ) (b : ℕ) (ss : List ℕ)
    (smax : ℕ) (x y : List ℚ) : firstCost ss ≤ creCost eng rnd b ss smax x y := by
  cases ss with
  | nil => simp [firstCost]
  | cons s ss => simp only [firstCost, creCost, List.map_cons, certifyCost]; omega

/-- **The shortcut never costs more.** -/
theorem ozaki1CRA_cost_le (eng : Engine) (rnd : ℚ → Option ℚ) (b : ℕ) (ss : List ℕ) (smax : ℕ)
    (x y : List ℚ) : craCost eng rnd b ss smax x y ≤ creCost eng rnd b ss smax x y := by
  unfold craCost
  cases hse : exactCount b smax x y with
  | none => simp [adaptList]
  | some se =>
    simp only [adaptList]
    split
    · rename_i hle
      have h1 : creCost eng rnd b [] smax x y = se * se := by
        simp [creCost, certifyCost, hse]
      rw [h1]
      exact Nat.le_trans hle (firstCost_le_creCost eng rnd b ss smax x y)
    · exact Nat.le_refl _

/-- **When it takes the shortcut, it costs exactly `sₑ²`**, which is at most the first check's
`s(s+1)/2`. -/
theorem ozaki1CRA_cost_shortcut (eng : Engine) (rnd : ℚ → Option ℚ) (b : ℕ) (ss : List ℕ)
    {smax : ℕ} {x y : List ℚ} {se : ℕ} (hse : exactCount b smax x y = some se)
    (hle : se * se ≤ firstCost ss) : craCost eng rnd b ss smax x y = se * se := by
  unfold craCost
  rw [hse]
  simp only [adaptList, if_pos hle]
  simp [creCost, certifyCost, hse]

/-- **When the first check settles, `ozaki1CRE` costs exactly its `s(s+1)/2`.** -/
theorem creCost_first_settles (eng : Engine) (rnd : ℚ → Option ℚ) (b s : ℕ) (ss : List ℕ)
    (smax : ℕ) (x y : List ℚ) (hs : checkSettles eng rnd b s x y = true) :
    creCost eng rnd b (s :: ss) smax x y = (trianglePairs s).length := by
  simp [creCost, certifyCost, hs]

/-- Without the shortcut the two schemes and their costs coincide. -/
theorem ozaki1CRA_noshortcut (eng : Engine) (rnd : ℚ → Option ℚ) (b : ℕ) (ss : List ℕ)
    {smax : ℕ} {x y : List ℚ}
    (hno : ∀ se, exactCount b smax x y = some se → firstCost ss < se * se) :
    ozaki1CRA eng rnd b ss smax x y = ozaki1CRE eng rnd b ss smax x y ∧
      craCost eng rnd b ss smax x y = creCost eng rnd b ss smax x y := by
  unfold ozaki1CRA craCost
  cases hse : exactCount b smax x y with
  | none => simp [adaptList]
  | some se =>
    have := hno se hse
    simp only [adaptList, if_neg (Nat.not_le.mpr this)]
    exact ⟨trivial, trivial⟩

end Ozaki
