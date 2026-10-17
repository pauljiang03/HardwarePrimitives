import OzakiTC.ADPFix
import Ozaki.BoundedOzaki2

/-! # ADP's rounding test in bounded integer arithmetic, and signed zeros for ADP

`adpCRE` applies the rounding test to a rational enclosure: the recombined INT8 slice products `H`
and the fixed-point bound `adpBound`, a rational computed from the inputs. Here the rounding test is
integer arithmetic:

* **ADP's integer enclosure** (`adpEnclosureB`): `H = R 2^q` with `R` the recombined split-K INT8
  slice products and `q = −(fₓ + f_y)` the fixed-point shifts, and `B = K 2^q` with `K` of the
  fixed-point integers (`adpK`, `Ozaki.boundK`): every entry loses less than one unit of the fixed
  grid, nothing when no bits are dropped, so `adpBound ≤ B` (`adpBound_le`) and the enclosure
  contains `x · y` (`adpEnclosureB_sound`);
* `adpCRB`: the integer rounding tests for the configurations `(s, W)` in turn, then Ozaki-I's
  bounded exact fallback on the split-K INT8 matrix multiplier with `6`-bit slices. It is the
  binary64 round to nearest of `x · y` for binary64 inputs of any length (`adpCRB_eq`).

**Widths** (`adpEnclosureB_width`): `|R| ≤ k 2^(2W)` and `0 ≤ K ≤ k (2^(W+1) + 1)`, both on the grid
`2^q`, so the integers `R ± K` the test rounds depend on the configuration's width `W` and on `k`,
not on the inputs' exponents.

**Signed zeros**: `adpCRES` (rational enclosures, `fp64Round`) and `adpCRBS` (integer enclosures
and the bounded exact fallback) return the IEEE-signed correctly rounded product `crSigned`
(`adpCRES_eq`, `adpCRBS_eq`). -/

open TensorCore

namespace Ozaki.TC

/-! ## ADP's integer enclosure -/

theorem floor_close (t : ℚ) : Rat.abs (t - (t.floor : ℚ)) ≤ 1 := by
  obtain ⟨h1, h2⟩ := floor_frac t
  rw [abs_le_iff]; constructor <;> grind

/-- ADP's integer bound: `K` of the fixed-point integers (`boundK`). -/
def adpK (W : ℕ) (x y : List ℚ) : ℤ :=
  boundK (toFixed (fixedShift W x) x) (toFixed (fixedShift W y) y)
    (drops (fun t => t.floor) (fixedShift W x) x) (drops (fun t => t.floor) (fixedShift W y) y)
    x.length

/-- **The fixed-point bound is at most `K 2^q`**, `q = −(fₓ + f_y)`. -/
theorem adpBound_le (W : ℕ) {x y : List ℚ} (hlen : x.length = y.length) :
    adpBound W x y ≤ (adpK W x y : ℚ) * 2 ^ (-(fixedShift W x + fixedShift W y)) := by
  have hfv : ∀ z : List ℚ, fixedVals W z =
      z.map fun a => ((a * 2 ^ fixedShift W z).floor : ℚ) * 2 ^ (-fixedShift W z) := by
    intro z; unfold fixedVals toFixed; rw [List.map_map]; rfl
  unfold adpBound adpK
  rw [hfv x, hfv y]
  exact scaledBound_le (g := fun t => t.floor) floor_close _ _ hlen

/-- **ADP's integer enclosure** for `s` slices of width `W`: `H = R 2^q` with `R` the recombined
split-K INT8 slice products and `q = −(fₓ + f_y)`, and `B = K 2^q` on the same grid. -/
def adpEnclosureB (s W : ℕ) (x y : List ℚ) : ℤ × ℤ × ℤ × ℤ :=
  (int8RecombineK s (toFixed (fixedShift W x) x) (toFixed (fixedShift W y) y),
    -(fixedShift W x + fixedShift W y), adpK W x y, -(fixedShift W x + fixedShift W y))

/-- **ADP's integer enclosure contains `x · y`.** -/
theorem adpEnclosureB_sound {s W : ℕ} (hs : 0 < s) (hfit : ADP.remapFits W s = true)
    {x y : List ℚ} (hlen : x.length = y.length) :
    Rat.abs (dot x y - (enclVal (adpEnclosureB s W x y)).1) ≤ (enclVal (adpEnclosureB s W x y)).2 :=
  Rat.le_trans (adpEnclosureK_sound hs hfit hlen) (adpBound_le W hlen)

theorem toFixed_natAbs_le (W : ℕ) (x : List ℚ) :
    ∀ a ∈ toFixed (fixedShift W x) x, a.natAbs ≤ 2 ^ W := by
  intro a ha
  obtain ⟨h1, h2⟩ := toFixed_range W x a ha
  have : ((2 ^ W : ℕ) : ℤ) = (2 : ℤ) ^ W := by simp
  omega

/-- **The widths of ADP's integer enclosure**, independent of the exponents: `|R| ≤ k 2^(2W)`,
`0 ≤ K ≤ k (2^(W+1) + 1)`, the bound on `H`'s grid; so the integers `R ± K` the test rounds are at
most `k 2^(2W) + k (2^(W+1) + 1)`. They depend on the configuration's width `W` and on `k`. -/
theorem adpEnclosureB_width {s W : ℕ} (hs : 0 < s) (hfit : ADP.remapFits W s = true)
    {x y : List ℚ} (hlen : x.length = y.length) :
    (adpEnclosureB s W x y).1.natAbs ≤ x.length * (2 ^ W * 2 ^ W) ∧
      (adpEnclosureB s W x y).2.2.2 = (adpEnclosureB s W x y).2.1 ∧
      0 ≤ (adpEnclosureB s W x y).2.2.1 ∧
      (adpEnclosureB s W x y).2.2.1.natAbs ≤ x.length * (2 * 2 ^ W + 1) ∧
      ((adpEnclosureB s W x y).1 - (adpEnclosureB s W x y).2.2.1).natAbs ≤
        x.length * (2 ^ W * 2 ^ W) + x.length * (2 * 2 ^ W + 1) ∧
      ((adpEnclosureB s W x y).1 + (adpEnclosureB s W x y).2.2.1).natAbs ≤
        x.length * (2 ^ W * 2 ^ W) + x.length * (2 * 2 ^ W + 1) := by
  have hR : (adpEnclosureB s W x y).1.natAbs ≤ x.length * (2 ^ W * 2 ^ W) := by
    unfold adpEnclosureB
    simp only
    rw [int8RecombineK_eq hs (by simp [toFixed, hlen]) (toFixed_remap hfit x) (toFixed_remap hfit y)]
    refine Nat.le_trans (natAbs_dotZ_le _ _)
      (Nat.le_trans (dotAbs_le _ _ _ _ (toFixed_natAbs_le W x) (toFixed_natAbs_le W y)) ?_)
    simp [toFixed]
  obtain ⟨hK0, hK⟩ := boundK_le (dx := drops (fun t => t.floor) (fixedShift W x) x)
    (dy := drops (fun t => t.floor) (fixedShift W y) y) (k := x.length) (by simp [toFixed])
    (by simp [toFixed, hlen]) (toFixed_natAbs_le W x) (toFixed_natAbs_le W y)
  have hK0' : 0 ≤ (adpEnclosureB s W x y).2.2.1 := hK0
  have hK' : (adpEnclosureB s W x y).2.2.1.natAbs ≤ x.length * (2 * 2 ^ W + 1) := hK
  refine ⟨hR, rfl, hK0', hK', ?_, ?_⟩
  · have := Int.natAbs_sub_le (adpEnclosureB s W x y).1 (adpEnclosureB s W x y).2.2.1; omega
  · have := Int.natAbs_add_le (adpEnclosureB s W x y).1 (adpEnclosureB s W x y).2.2.1; omega

/-! ## Correctly rounded ADP-style slicing in bounded integer arithmetic -/

/-- **ADP's slicing, correctly rounded, with bounded registers**: the integer rounding tests for the
configurations `(s, W)` in turn, then Ozaki-I's bounded exact fallback on the split-K INT8 matrix
multiplier with `6`-bit slices. -/
def adpCRB (cfgs : List (ℕ × ℕ)) (smax : ℕ) (x y : List ℚ) : Option ℚ :=
  roundingTestB 53 (-1022) 1023 (cfgs.map fun c => some (adpEnclosureB c.1 c.2 x y))
    (ozaki1ExactFallbackB int8SplitK 53 (-1022) 1023 6 smax x y)

/-- **ADP's slicing with bounded registers is correctly rounded** for binary64 inputs of any
length. -/
theorem adpCRB_eq {cfgs : List (ℕ × ℕ)} (hcfg : ∀ c ∈ cfgs, 0 < c.1 ∧ ADP.remapFits c.2 c.1 = true)
    {smax : ℕ} (hsmax : 2098 < smax * 7) {x y : List ℚ} (hx : ∀ a ∈ x, Binary64Value a)
    (hy : ∀ a ∈ y, Binary64Value a) (hlen : x.length = y.length) :
    adpCRB cfgs smax x y = rne64 (dot x y) := by
  apply roundingTestB_eq (by decide) (by decide)
  · intro e he t het
    obtain ⟨cfg, hmem, rfl⟩ := List.mem_map.mp he
    obtain ⟨hs, hfit⟩ := hcfg cfg hmem
    cases het
    exact adpEnclosureB_sound hs hfit hlen
  · rw [ozaki1ExactFallbackB_eq (int8SplitK_exactOn _) 53 (-1022) 1023 smax hlen (Nat.le_refl _),
      ozaki1ExactFallback_eq (int8SplitK_exactOn _) hlen (Nat.le_refl _)
        (vanish64 (by decide) (by simpa using hsmax) hx hy)]
    rfl

/-! ## Signed zeros for ADP -/

theorem fp64Round_zero : fp64Round 0 = some 0 := by decide +kernel

/-- **ADP's slicing, correctly rounded, with signed zeros**: the enclosures of `adpCRE`, then its
exact fallback on the INT8 matrix multiplier, the sign of a zero result from the enclosure or the
exact value. -/
def adpCRES (cfgs : List (ℕ × ℕ)) (smax : ℕ) (xs ys : List Signed) : Option Signed :=
  roundingTestSigned fp64Round (cfgs.map fun c => some (adpEnclosureK c.1 c.2 (vals xs) (vals ys)))
    (ozaki1ExactFallback int8SplitK 6 smax (vals xs) (vals ys)) (allNegZero xs ys)

theorem adpCRES_eq {cfgs : List (ℕ × ℕ)} (hcfg : ∀ c ∈ cfgs, 0 < c.1 ∧ ADP.remapFits c.2 c.1 = true)
    {smax : ℕ} (hsmax : 2098 < smax * 7) {xs ys : List Signed}
    (hx : ∀ a ∈ xs, Binary64Value a.val) (hy : ∀ a ∈ ys, Binary64Value a.val)
    (hlen : xs.length = ys.length) :
    adpCRES cfgs smax xs ys = crSigned fp64Round xs ys := by
  have hl : (vals xs).length = (vals ys).length := by rw [vals_length, vals_length, hlen]
  unfold adpCRES crSigned
  apply roundingTestSigned_eq fp64Round_nearest fp64Round_intervals fp64Round_zero _ _ _ _
    (ozaki1ExactFallback_eq (int8SplitK_exactOn _) hl (Nat.le_refl _)
      (vanish64 (by decide) (by simpa using hsmax) (vals_all hx) (vals_all hy)))
  intro c hc H B hcB
  obtain ⟨cfg, hmem, rfl⟩ := List.mem_map.mp hc
  obtain ⟨hs, hfit⟩ := hcfg cfg hmem
  cases hcB
  exact adpEnclosureK_sound hs hfit hl

/-- **ADP's slicing, correctly rounded, with signed zeros and bounded registers.** -/
def adpCRBS (cfgs : List (ℕ × ℕ)) (smax : ℕ) (xs ys : List Signed) : Option Signed :=
  roundingTestSignedB 53 (-1022) 1023 (cfgs.map fun c => some (adpEnclosureB c.1 c.2 (vals xs) (vals ys)))
    (ozaki1ExactFallbackBS int8SplitK 53 (-1022) 1023 6 smax (vals xs) (vals ys)) (allNegZero xs ys)

theorem adpCRBS_eq {cfgs : List (ℕ × ℕ)} (hcfg : ∀ c ∈ cfgs, 0 < c.1 ∧ ADP.remapFits c.2 c.1 = true)
    {smax : ℕ} (hsmax : 2098 < smax * 7) {xs ys : List Signed}
    (hx : ∀ a ∈ xs, Binary64Value a.val) (hy : ∀ a ∈ ys, Binary64Value a.val)
    (hlen : xs.length = ys.length) :
    adpCRBS cfgs smax xs ys = crSigned rne64 xs ys := by
  have hl : (vals xs).length = (vals ys).length := by rw [vals_length, vals_length, hlen]
  unfold adpCRBS crSigned
  apply roundingTestSignedB_eq (by decide) (by decide)
  · intro e he t het
    obtain ⟨cfg, hmem, rfl⟩ := List.mem_map.mp he
    obtain ⟨hs, hfit⟩ := hcfg cfg hmem
    cases het
    exact adpEnclosureB_sound hs hfit hl
  · exact ozaki1ExactFallbackBS_eq (int8SplitK_exactOn _) 53 (-1022) 1023 smax hl (Nat.le_refl _)
      (vanish64 (by decide) (by simpa using hsmax) (vals_all hx) (vals_all hy))

end Ozaki.TC
