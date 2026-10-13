import OzakiTC.ADPBounded
import Ozaki.BoundedOzaki2Int

/-! # ADP's correctly rounded slicing as an integer pipeline

`adpCRB` takes rational inputs: its fixed point (`fixedShift`, `toFixed`) and its exact fallback's
slicing are rational definitions. Here the inputs are integer pairs `(m, e)` worth `m 2^e`, and
every step is integer arithmetic:

* **the fixed-point shift from bit lengths**: `fixedShiftZ W xs = W − 1 − ⌊log₂ max|xᵢ|⌋` with the
  floor exponent from `maxFloorExp` (`fixedShiftZ_eq`);
* **the fixed-point integers by floor shifts** of the significands (`toFixedZ_eq`), and whether they
  drop bits by remainders (`dropsZ_floor_eq`);
* **ADP's integer enclosure** from them (`adpEnclosureZ`, equal to `adpEnclosureB` on the values,
  `adpEnclosureZ_eq`): the remapped byte slices, the split-K INT8 products, the recombination, and
  the bound `K`;
* the exact fallback with integer slicing on the split-K INT8 matrix multiplier
  (`Ozaki.ozaki1ExactFallbackZ`).

`adpCRZ` is the binary64 round to nearest of `x · y` for binary64 inputs of any length given as
integer pairs (`adpCRZ_eq`).

**Widths**, none depending on the inputs' exponents: inputs `|m| < 2^53`; a fixed-point integer at
most `2^W` (`toFixedZ_natAbs_le`); a right shift divides by at most `|m|`
(`Ozaki.truncShiftZ_divisor_le`); byte slices at most `128` (`sliceVec_s8`); a split-K INT8
product at most `k 2^14`, each chunk below `2^31` in the 32-bit register (`int8DotK_natAbs_le`); a
recombination term `256^(t+u)` times a slice product at most `256^(2(s−1)) k 2^14`
(`int8RecombineK_term_le`); `R`, `K` and `R ± K` (`adpEnclosureB_width`). -/

open TensorCore

namespace Ozaki.TC

/-- ADP's fixed-point shift from bit lengths: `W − 1 − ⌊log₂ max|xᵢ|⌋`, with `−1` for a zero
vector as in `fixedShift`. -/
def fixedShiftZ (W : ℕ) (xs : List (ℤ × ℤ)) : ℤ := (W : ℤ) - 1 - (maxFloorExp xs).getD (-1)

theorem fixedShiftZ_eq (W : ℕ) (xs : List (ℤ × ℤ)) :
    fixedShiftZ W xs = fixedShift W (entryVals xs) := by
  unfold fixedShiftZ fixedShift
  rw [maxFloorExp_floorLog2]

/-- The fixed-point integers `⌊xᵢ 2^f⌋` from the significands. -/
def toFixedZ (f : ℤ) (xs : List (ℤ × ℤ)) : List ℤ := xs.map fun a => floorShiftZ a.1 (a.2 + f)

theorem toFixedZ_eq (f : ℤ) (xs : List (ℤ × ℤ)) : toFixedZ f xs = toFixed f (entryVals xs) := by
  unfold toFixedZ toFixed entryVals
  rw [List.map_map]
  apply List.map_congr_left
  intro a _
  simp only [Function.comp]
  rw [floorShiftZ_eq, entryVal_mul_two_pow]

theorem dropsZ_floor_eq (f : ℤ) (xs : List (ℤ × ℤ)) :
    dropsZ f xs = drops (fun t => t.floor) f (entryVals xs) := by
  unfold dropsZ drops entryVals
  rw [List.any_map]
  congr 1
  funext a
  simp only [Function.comp]
  rw [dropsBits_eq (g := fun t => t.floor) (fun z => Rat.floor_intCast z), entryVal_mul_two_pow]

/-- **ADP's integer enclosure from integer inputs** for `s` slices of width `W`. -/
def adpEnclosureZ (s W : ℕ) (xs ys : List (ℤ × ℤ)) : ℤ × ℤ × ℤ × ℤ :=
  (int8RecombineK s (toFixedZ (fixedShiftZ W xs) xs) (toFixedZ (fixedShiftZ W ys) ys),
    -(fixedShiftZ W xs + fixedShiftZ W ys),
    boundK (toFixedZ (fixedShiftZ W xs) xs) (toFixedZ (fixedShiftZ W ys) ys)
      (dropsZ (fixedShiftZ W xs) xs) (dropsZ (fixedShiftZ W ys) ys) xs.length,
    -(fixedShiftZ W xs + fixedShiftZ W ys))

theorem adpEnclosureZ_eq (s W : ℕ) (xs ys : List (ℤ × ℤ)) :
    adpEnclosureZ s W xs ys = adpEnclosureB s W (entryVals xs) (entryVals ys) := by
  unfold adpEnclosureZ adpEnclosureB adpK
  rw [fixedShiftZ_eq, fixedShiftZ_eq, toFixedZ_eq, toFixedZ_eq, dropsZ_floor_eq, dropsZ_floor_eq,
    entryVals_length]

/-- **ADP's slicing, correctly rounded, as an integer pipeline**: integer pairs in, the integer
enclosures of the configurations in turn, then the exact fallback with integer slicing on the
split-K INT8 matrix multiplier. -/
def adpCRZ (cfgs : List (ℕ × ℕ)) (smax : ℕ) (xs ys : List (ℤ × ℤ)) : Option ℚ :=
  roundingTestB 53 (-1022) 1023 (cfgs.map fun c => some (adpEnclosureZ c.1 c.2 xs ys))
    (ozaki1ExactFallbackZ int8SplitK 53 (-1022) 1023 6 smax xs ys)

theorem adpCRZ_eq_CRB (cfgs : List (ℕ × ℕ)) (smax : ℕ) (xs ys : List (ℤ × ℤ)) :
    adpCRZ cfgs smax xs ys = adpCRB cfgs smax (entryVals xs) (entryVals ys) := by
  unfold adpCRZ adpCRB
  rw [ozaki1ExactFallbackZ_eq]
  congr 1
  apply List.map_congr_left
  intro c _
  rw [adpEnclosureZ_eq]

/-- **The ADP integer pipeline is correctly rounded** for binary64 inputs of any length. -/
theorem adpCRZ_eq {cfgs : List (ℕ × ℕ)} (hcfg : ∀ c ∈ cfgs, 0 < c.1 ∧ ADP.remapFits c.2 c.1 = true)
    {smax : ℕ} (hsmax : 2098 < smax * 7) {xs ys : List (ℤ × ℤ)}
    (hx : ∀ v ∈ entryVals xs, Binary64Value v) (hy : ∀ v ∈ entryVals ys, Binary64Value v)
    (hlen : xs.length = ys.length) :
    adpCRZ cfgs smax xs ys = rne64 (dot (entryVals xs) (entryVals ys)) := by
  rw [adpCRZ_eq_CRB]
  exact adpCRB_eq hcfg hsmax hx hy (by rw [entryVals_length, entryVals_length, hlen])

/-! ## Widths -/

/-- **A fixed-point integer is at most `2^W`**, whatever the exponents. -/
theorem toFixedZ_natAbs_le (W : ℕ) (xs : List (ℤ × ℤ)) :
    ∀ z ∈ toFixedZ (fixedShiftZ W xs) xs, z.natAbs ≤ 2 ^ W := by
  rw [fixedShiftZ_eq, toFixedZ_eq]
  exact toFixed_natAbs_le W (entryVals xs)

/-- **A split-K INT8 product of bytes is at most `k 2^14`**; each chunk of at most `2^16` products
stays below `2^31` in the 32-bit register (`int8DotK_exact`). -/
theorem int8DotK_natAbs_le {x y : List ℤ} (hlen : x.length = y.length)
    (hx : ∀ a ∈ x, a.natAbs ≤ 128) (hy : ∀ b ∈ y, b.natAbs ≤ 128) :
    (int8DotK x y).natAbs ≤ x.length * (128 * 128) := by
  rw [int8DotK_exact hlen hx hy]
  exact Nat.le_trans (natAbs_dotZ_le _ _) (dotAbs_le _ _ _ _ hx hy)

/-- **A recombination term** `256^(t+u)` times a slice product is at most
`256^(2(s−1)) k 2^14` for slice indices below `s`. -/
theorem int8RecombineK_term_le {s : ℕ} (hs : 0 < s) {Na Nb : List ℤ}
    (hlen : Na.length = Nb.length)
    (hx : ∀ z ∈ Na, ADP.remapLo s ≤ z ∧ z ≤ ADP.remapHi s)
    (hy : ∀ z ∈ Nb, ADP.remapLo s ≤ z ∧ z ≤ ADP.remapHi s) {t u : ℕ} (ht : t < s) (hu : u < s) :
    (256 ^ (t + u) * int8DotK (ADP.sliceVec s t Na) (ADP.sliceVec s u Nb)).natAbs ≤
      256 ^ (2 * (s - 1)) * (Na.length * (128 * 128)) := by
  rw [Int.natAbs_mul, Int.natAbs_pow]
  have h1 := int8DotK_natAbs_le (by simp [ADP.sliceVec, hlen]) (sliceVec_s8 hs hx t)
    (sliceVec_s8 hs hy u)
  have hl : (ADP.sliceVec s t Na).length = Na.length := by simp [ADP.sliceVec]
  rw [hl] at h1
  have h2 : (256 : ℤ).natAbs ^ (t + u) ≤ 256 ^ (2 * (s - 1)) :=
    Nat.pow_le_pow_right (by decide) (by omega)
  exact Nat.mul_le_mul h2 h1

end Ozaki.TC
