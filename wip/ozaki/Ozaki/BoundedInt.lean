import Ozaki.TopDownSummation
import Ozaki.BoundedOzaki
import Ozaki.SliceInt
import Ozaki.SignedZero

/-! # Correctly rounded Ozaki-I, entirely in integers

`ozaki1CRB` (in `Ozaki.BoundedOzaki`) runs the rounding test, the exact fallback and the final
rounding in bounded integer registers, but it slices with the rational `split`. `ozaki1CRI` takes
its inputs as a binary format stores them, integer pairs `(m, e)` worth `m · 2^e`, and every step is
an integer operation:

* the slicing is `splitInt` (integer shifts and a round-half-even division), with the exponent
  `⌈log₂ max|xᵢ|⌉` from bit lengths (`splitExpInt`);
* the slice products of the matrix multiplier are read back as integer terms;
* the rounding test is that of `ozaki1TestB`: truncated parts of terms by shifts, a
  two's-complement register, the enclosure test by `roundExact` (`ozaki1TestI`);
* the exact fallback asks whether the rests vanish by testing integers, and rounds the `s²` slice
  products with the jumping top-down summation `roundSumJ` (`ozaki1ExactFallbackI`).

`ozaki1CRI_eq_CRB` proves it is `ozaki1CRB` on the values `m · 2^e`, so it is correctly rounded
(`ozaki1CRI_eq`), for binary64 and binary32 inputs in particular (`ozaki1CRI64_eq`,
`ozaki1CRI32_eq`).

`ozaki1CRIS` adds IEEE's signed zeros (`ozaki1CRIS_eq`): inputs carry their sign bits; a nonzero
result keeps its sign; a zero result takes the sign of the exact sum, decided by the integer sign
oracle on the exact fallback (`exactSignI`), and an exact zero is `−0` only when every product is
`−0` (`allNegZeroI`). -/

local notation "ℕ" => Nat
local notation "ℤ" => Int
local notation "ℚ" => Rat

namespace Ozaki

/-! ## Entries of a binary format -/

/-- An entry as a binary format with `p`-bit significands and exponents `emin … emax` stores it:
`|m| < 2^p` and `emin − (p − 1) ≤ e ≤ emax − (p − 1)`. -/
def FormatEntry (p : ℕ) (emin emax : ℤ) (a : ℤ × ℤ) : Prop :=
  a.1.natAbs < 2 ^ p ∧ emin - ((p : ℤ) - 1) ≤ a.2 ∧ a.2 ≤ emax - ((p : ℤ) - 1)

/-- A stored entry is a value of the format. -/
theorem FormatEntry.formatValue {p : ℕ} {emin emax : ℤ} {a : ℤ × ℤ}
    (h : FormatEntry p emin emax a) : FormatValue p emin emax (entryVal a) :=
  ⟨a.1, a.2 + ((p : ℤ) - 1), by have := h.2.1; omega, by have := h.2.2; omega, h.1, by
    unfold entryVal; congr 2; omega⟩

theorem length_entryVals (xs : List (ℤ × ℤ)) : (entryVals xs).length = xs.length := by
  simp [entryVals]

theorem entryVal_eq_zero_iff (a : ℤ × ℤ) : entryVal a = 0 ↔ a.1 = 0 := by
  unfold entryVal
  constructor
  · intro h
    rcases Rat.mul_eq_zero.mp h with h | h
    · have : ((a.1 : ℤ) : ℚ) = ((0 : ℤ) : ℚ) := by rw [h, Rat.intCast_zero]
      exact Rat.intCast_inj.mp this
    · exact absurd h (two_pow_ne_zero _)
  · intro h; rw [h, Rat.intCast_zero, Rat.zero_mul]

theorem all_entryVals_zero (l : List (ℤ × ℤ)) :
    (entryVals l).all (· == 0) = l.all fun r => r.1 == 0 := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    unfold entryVals at ih ⊢
    rw [List.map_cons, List.all_cons, List.all_cons, ih]
    congr 1
    rw [Bool.eq_iff_iff, beq_iff_eq, beq_iff_eq]
    exact entryVal_eq_zero_iff a

/-! ## The exponent of a split -/

/-- `splitExp` with integer operations: `⌈log₂ max|xᵢ|⌉` from bit lengths and exponents. -/
def splitExpInt (b : ℕ) (xs : List (ℤ × ℤ)) : ℤ := gridInt b b xs + b

theorem splitExpInt_eq (b : ℕ) (xs : List (ℤ × ℤ)) :
    splitExpInt b xs = splitExp b (entryVals xs) := by
  unfold splitExpInt splitExp; rw [gridInt_eq]

/-- The truncation grid with integer operations. -/
def truncationGridInt (b W : ℕ) (xs ys : List (ℤ × ℤ)) : ℤ := splitExpInt b xs + splitExpInt b ys - W

theorem truncationGridInt_eq (b W : ℕ) (xs ys : List (ℤ × ℤ)) :
    truncationGridInt b W xs ys = truncationGrid b W (entryVals xs) (entryVals ys) := by
  unfold truncationGridInt truncationGrid; rw [splitExpInt_eq, splitExpInt_eq]

/-! ## The rounding test -/

/-- **The rounding test for `s` slices, in integers**: `ozaki1TestB` with the integer slicing. -/
def ozaki1TestI (mult : MatrixMultiplier) (p : ℕ) (emin emax : ℤ) (b s W : ℕ) (xs ys : List (ℤ × ℤ)) :
    Option ℚ :=
  match (trianglePairs s).mapM (pairInt mult (splitInt b s xs).1 (splitInt b s ys).1) with
  | none => none
  | some ts =>
    roundEnclosureB p emin emax
      (fixedSum (W + bitlen (ts.length * (xs.length + 2)) + 1)
        (ts.map (floorPart (truncationGridInt b W xs ys))))
      (truncationGridInt b W xs ys) (((s + 1) * xs.length : ℕ) : ℤ)
      (splitExpInt b xs + splitExpInt b ys - s * (b + 1)) ts.length

theorem ozaki1TestI_eq (mult : MatrixMultiplier) (p : ℕ) (emin emax : ℤ) (b s W : ℕ)
    (xs ys : List (ℤ × ℤ)) :
    ozaki1TestI mult p emin emax b s W xs ys =
      ozaki1TestB mult p emin emax b s W (entryVals xs) (entryVals ys) := by
  unfold ozaki1TestI ozaki1TestB
  rw [(splitInt_eq b s xs).1, (splitInt_eq b s ys).1, truncationGridInt_eq, splitExpInt_eq,
    splitExpInt_eq, length_entryVals]
  cases (trianglePairs s).mapM (pairInt mult (split b s (entryVals xs)).1
    (split b s (entryVals ys)).1) <;> rfl

/-! ## The exact fallback -/

/-- Nothing is left over after `s` slices, by testing the rests' significands. -/
def vanishInt (b s : ℕ) (xs ys : List (ℤ × ℤ)) : Bool :=
  (splitInt b s xs).2.all (fun r => r.1 == 0) && (splitInt b s ys).2.all (fun r => r.1 == 0)

theorem vanishInt_eq (b s : ℕ) (xs ys : List (ℤ × ℤ)) :
    vanishInt b s xs ys = residualsVanish b s (entryVals xs) (entryVals ys) := by
  unfold vanishInt residualsVanish
  rw [← (splitInt_eq b s xs).2, ← (splitInt_eq b s ys).2, all_entryVals_zero, all_entryVals_zero]

/-- **The exact fallback in integers**: the first slice count up to `smax` that leaves nothing over,
all `s²` slice products from the matrix multiplier as integer terms, rounded by the jumping
top-down summation. -/
def ozaki1ExactFallbackI (mult : MatrixMultiplier) (p : ℕ) (emin emax : ℤ) (b smax : ℕ)
    (xs ys : List (ℤ × ℤ)) : Option ℚ :=
  match (List.range' 1 smax).find? fun s => vanishInt b s xs ys with
  | some s =>
    match (slicePairs (splitInt b s xs).1 (splitInt b s ys).1).mapM
        (fun pr => sliceProductInt mult pr.1 pr.2) with
    | some ts => roundSumJ p emin emax (bitlen (ts.length + 1) + p + 4) ts
    | none => none
  | none => none

theorem ozaki1ExactFallbackI_eq (mult : MatrixMultiplier) (p : ℕ) (emin emax : ℤ) (b smax : ℕ)
    (xs ys : List (ℤ × ℤ)) :
    ozaki1ExactFallbackI mult p emin emax b smax xs ys =
      ozaki1ExactFallbackB mult p emin emax b smax (entryVals xs) (entryVals ys) := by
  unfold ozaki1ExactFallbackI ozaki1ExactFallbackB
  have hf : (fun s => vanishInt b s xs ys) =
      fun s => residualsVanish b s (entryVals xs) (entryVals ys) :=
    funext fun s => vanishInt_eq b s xs ys
  rw [hf]
  cases (List.range' 1 smax).find? fun s => residualsVanish b s (entryVals xs) (entryVals ys) with
  | none => rfl
  | some s =>
    simp only
    rw [(splitInt_eq b s xs).1, (splitInt_eq b s ys).1]
    cases (slicePairs (split b s (entryVals xs)).1 (split b s (entryVals ys)).1).mapM
        (fun pr => sliceProductInt mult pr.1 pr.2) with
    | none => rfl
    | some ts =>
      simp only
      rw [roundSumJ_eq _ _ (by omega), roundSum_eq _ _ (by omega)]

/-! ## The scheme -/

/-- **Correctly rounded Ozaki-I in integers**: the integer rounding tests for the slice counts `ss`
in turn, then the integer exact fallback. -/
def ozaki1CRI (mult : MatrixMultiplier) (p : ℕ) (emin emax : ℤ) (b W : ℕ) (ss : List ℕ) (smax : ℕ)
    (xs ys : List (ℤ × ℤ)) : Option ℚ :=
  match ss with
  | [] => ozaki1ExactFallbackI mult p emin emax b smax xs ys
  | s :: ss =>
    match ozaki1TestI mult p emin emax b s W xs ys with
    | some w => some w
    | none => ozaki1CRI mult p emin emax b W ss smax xs ys

/-- **The integer scheme is the bounded one** on the values of the entries. -/
theorem ozaki1CRI_eq_CRB (mult : MatrixMultiplier) (p : ℕ) (emin emax : ℤ) (b W : ℕ) (smax : ℕ)
    (xs ys : List (ℤ × ℤ)) : ∀ ss : List ℕ,
    ozaki1CRI mult p emin emax b W ss smax xs ys =
      ozaki1CRB mult p emin emax b W ss smax (entryVals xs) (entryVals ys)
  | [] => by
    unfold ozaki1CRI ozaki1CRB
    exact ozaki1ExactFallbackI_eq mult p emin emax b smax xs ys
  | s :: ss => by
    unfold ozaki1CRI ozaki1CRB
    rw [ozaki1TestI_eq, ozaki1CRI_eq_CRB mult p emin emax b W smax xs ys ss]
    cases ozaki1TestB mult p emin emax b s W (entryVals xs) (entryVals ys) <;> rfl

/-- **Correctly rounded Ozaki-I in integers is correctly rounded**: on an exact matrix multiplier,
for every input whose exact fallback ends within `smax` slices. -/
theorem ozaki1CRI_eq {p : ℕ} {emin emax : ℤ} (hp : 0 < p) (hle : emin ≤ emax) {mult : MatrixMultiplier}
    {b bound : ℕ} (hmult : mult.ExactOn b bound) (W : ℕ) (ss : List ℕ) {smax : ℕ}
    {xs ys : List (ℤ × ℤ)} (hlen : xs.length = ys.length)
    (hbound : xs.length * (2 ^ b * 2 ^ b) ≤ bound)
    (hvanish : ∃ s ∈ List.range' 1 smax, vanishInt b s xs ys = true) :
    ozaki1CRI mult p emin emax b W ss smax xs ys =
      roundRNE p emin emax (dot (entryVals xs) (entryVals ys)) := by
  rw [ozaki1CRI_eq_CRB]
  obtain ⟨s, hs, hv⟩ := hvanish
  exact ozaki1CRB_eq hp hle hmult W ss (by rw [length_entryVals, length_entryVals, hlen])
    (by rw [length_entryVals]; exact hbound) ⟨s, hs, by rw [← vanishInt_eq]; exact hv⟩

theorem binary64_entries {xs : List (ℤ × ℤ)} (h : ∀ a ∈ xs, Binary64Value (entryVal a)) :
    ∀ v ∈ entryVals xs, Binary64Value v := by
  intro v hv
  obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hv
  exact h a ha

theorem binary32_entries {xs : List (ℤ × ℤ)} (h : ∀ a ∈ xs, Binary32Value (entryVal a)) :
    ∀ v ∈ entryVals xs, Binary32Value v := by
  intro v hv
  obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hv
  exact h a ha

/-- **Binary64 entries**: correctly rounded to binary64 in integers, when `smax (b + 1) > 2098`. -/
theorem ozaki1CRI64_eq {mult : MatrixMultiplier} {b bound : ℕ} (hmult : mult.ExactOn b bound) (W : ℕ)
    (ss : List ℕ) {smax : ℕ} (hb : b ≤ 1025) (hsmax : 2098 < smax * (b + 1))
    {xs ys : List (ℤ × ℤ)} (hlen : xs.length = ys.length)
    (hbound : xs.length * (2 ^ b * 2 ^ b) ≤ bound)
    (hx : ∀ a ∈ xs, Binary64Value (entryVal a)) (hy : ∀ a ∈ ys, Binary64Value (entryVal a)) :
    ozaki1CRI mult 53 (-1022) 1023 b W ss smax xs ys = rne64 (dot (entryVals xs) (entryVals ys)) := by
  rw [ozaki1CRI_eq_CRB]
  exact ozaki1CRB64_eq hmult W ss hb hsmax (by rw [length_entryVals, length_entryVals, hlen])
    (by rw [length_entryVals]; exact hbound) (binary64_entries hx) (binary64_entries hy)

/-- **Binary32 entries**: correctly rounded to binary32 in integers, when `smax (b + 1) > 277`. -/
theorem ozaki1CRI32_eq {mult : MatrixMultiplier} {b bound : ℕ} (hmult : mult.ExactOn b bound) (W : ℕ)
    (ss : List ℕ) {smax : ℕ} (hb : b ≤ 129) (hsmax : 277 < smax * (b + 1))
    {xs ys : List (ℤ × ℤ)} (hlen : xs.length = ys.length)
    (hbound : xs.length * (2 ^ b * 2 ^ b) ≤ bound)
    (hx : ∀ a ∈ xs, Binary32Value (entryVal a)) (hy : ∀ a ∈ ys, Binary32Value (entryVal a)) :
    ozaki1CRI mult 24 (-126) 127 b W ss smax xs ys = rne32Q (dot (entryVals xs) (entryVals ys)) := by
  rw [ozaki1CRI_eq_CRB]
  exact ozaki1CRB32_eq hmult W ss hb hsmax (by rw [length_entryVals, length_entryVals, hlen])
    (by rw [length_entryVals]; exact hbound) (binary32_entries hx) (binary32_entries hy)

/-! ## Signed zeros -/

/-- An entry with its sign bit, as a binary format stores a value: `((m, e), sign)`. -/
abbrev SEntry := (ℤ × ℤ) × Bool

/-- The signed value of an entry. -/
def toSigned (a : SEntry) : Signed := ⟨entryVal a.1, a.2⟩

/-- Every product is `−0`, tested on the significands and sign bits. -/
def allNegZeroI (xs ys : List SEntry) : Bool :=
  let ps := List.zipWith (fun a c => a.1.1 * c.1.1 == 0 && xor a.2 c.2) xs ys
  !ps.isEmpty && ps.all id

theorem entryVal_mul_eq_zero (a c : ℤ × ℤ) : entryVal a * entryVal c = 0 ↔ a.1 * c.1 = 0 := by
  rw [Rat.mul_eq_zero, entryVal_eq_zero_iff, entryVal_eq_zero_iff, Int.mul_eq_zero]

theorem allNegZeroI_eq (xs ys : List SEntry) :
    allNegZeroI xs ys = allNegZero (xs.map toSigned) (ys.map toSigned) := by
  unfold allNegZeroI allNegZero
  simp only [List.zipWith_map]
  have : (fun a c : SEntry => a.1.1 * c.1.1 == 0 && xor a.2 c.2) =
      fun a c => (toSigned a).val * (toSigned c).val == 0 && prodNeg (toSigned a) (toSigned c) := by
    funext a c
    unfold toSigned prodNeg
    simp only
    congr 1
    rw [Bool.eq_iff_iff, beq_iff_eq, beq_iff_eq]
    exact (entryVal_mul_eq_zero a.1 c.1).symm
  rw [this]

theorem vals_toSigned (xs : List SEntry) : vals (xs.map toSigned) = entryVals (xs.map (·.1)) := by
  simp [vals, toSigned, entryVals]

/-- With nothing left over, the exact integer slice products add up to `x · y`. -/
theorem tsum_exactFallback {b s : ℕ} {x y : List ℚ} (hv : residualsVanish b s x y = true) :
    tsum ((slicePairs (split b s x).1 (split b s y).1).map fun pr => exactSliceInt pr.1 pr.2) =
      dot x y := by
  simp only [residualsVanish, Bool.and_eq_true, List.all_eq_true, beq_iff_eq] at hv
  rw [dot_eq_full hv.1 hv.2]
  unfold tsum
  rw [List.map_map]
  have := sum_slicePairs (split b s x).1 (split b s y).1 fun sl sl' =>
    2 ^ (sl.grid + sl'.grid) * (dotZ sl.coeffs sl'.coeffs : ℚ)
  rw [← this]
  congr 1
  apply List.map_congr_left
  intro pr _
  show (dotZ pr.1.coeffs pr.2.coeffs : ℚ) * 2 ^ (pr.1.grid + pr.2.grid) = _
  rw [Rat.mul_comm]

/-- **The sign of the exact sum**, by the integer sign oracle on the slice products of the exact
fallback. -/
def exactSignI (mult : MatrixMultiplier) (b smax : ℕ) (xs ys : List (ℤ × ℤ)) : Option ℤ :=
  match (List.range' 1 smax).find? fun s => vanishInt b s xs ys with
  | some s =>
    ((slicePairs (splitInt b s xs).1 (splitInt b s ys).1).mapM
        (fun pr => sliceProductInt mult pr.1 pr.2)).map
      fun ts => signSumJ (bitlen ts.length + 1) ts
  | none => none

theorem exactSignI_eq {mult : MatrixMultiplier} {b bound smax : ℕ} (hmult : mult.ExactOn b bound)
    {xs ys : List (ℤ × ℤ)} (hlen : xs.length = ys.length)
    (hbound : xs.length * (2 ^ b * 2 ^ b) ≤ bound)
    (hvanish : ∃ s ∈ List.range' 1 smax, vanishInt b s xs ys = true) :
    exactSignI mult b smax xs ys = some (sgnQ (dot (entryVals xs) (entryVals ys))) := by
  unfold exactSignI
  obtain ⟨s, hs⟩ := Option.isSome_iff_exists.mp (List.find?_isSome.mpr hvanish)
  rw [hs]
  have hv := List.find?_some hs
  rw [vanishInt_eq] at hv
  simp only
  have hl : (entryVals xs).length = (entryVals ys).length := by
    rw [length_entryVals, length_entryVals, hlen]
  have hb : (entryVals xs).length * (2 ^ b * 2 ^ b) ≤ bound := by
    rw [length_entryVals]; exact hbound
  rw [(splitInt_eq b s xs).1, (splitInt_eq b s ys).1,
    mapM_eq_some_map (g := fun pr => exactSliceInt pr.1 pr.2) fun pr hpr =>
      sliceProductInt_exact hmult hl hb (mem_slicePairs hpr).1 (mem_slicePairs hpr).2,
    Option.map_some, signSumJ_eq (by omega), tsum_exactFallback hv]

/-- **Correctly rounded Ozaki-I in integers, with signed zeros.** -/
def ozaki1CRIS (mult : MatrixMultiplier) (p : ℕ) (emin emax : ℤ) (b W : ℕ) (ss : List ℕ) (smax : ℕ)
    (xs ys : List SEntry) : Option Signed :=
  match ozaki1CRI mult p emin emax b W ss smax (xs.map (·.1)) (ys.map (·.1)) with
  | none => none
  | some r =>
    if r ≠ 0 then some ⟨r, decide (r < 0)⟩
    else (exactSignI mult b smax (xs.map (·.1)) (ys.map (·.1))).map fun sg =>
      ⟨0, if sg = 0 then allNegZeroI xs ys else decide (sg < 0)⟩

theorem sgnQ_neg_iff (x : ℚ) : sgnQ x < 0 ↔ x < 0 := by
  have := sgnQ_nonneg_iff x
  constructor
  · intro h; apply Classical.byContradiction; intro hn
    have := this.mpr (Rat.not_lt.mp hn); omega
  · intro h; apply Classical.byContradiction; intro hn
    have := this.mp (by omega); grind

/-- **Signed correct rounding in integers**: the round to nearest even of `x · y` with IEEE's sign
for zero results. -/
theorem ozaki1CRIS_eq {p : ℕ} {emin emax : ℤ} (hp : 0 < p) (hle : emin ≤ emax) {mult : MatrixMultiplier}
    {b bound : ℕ} (hmult : mult.ExactOn b bound) (W : ℕ) (ss : List ℕ) {smax : ℕ}
    {xs ys : List SEntry} (hlen : xs.length = ys.length)
    (hbound : xs.length * (2 ^ b * 2 ^ b) ≤ bound)
    (hvanish : ∃ s ∈ List.range' 1 smax, vanishInt b s (xs.map (·.1)) (ys.map (·.1)) = true) :
    ozaki1CRIS mult p emin emax b W ss smax xs ys =
      crSigned (roundRNE p emin emax) (xs.map toSigned) (ys.map toSigned) := by
  have hl : (xs.map (·.1)).length = (ys.map (·.1)).length := by simp [hlen]
  have hb : (xs.map (·.1)).length * (2 ^ b * 2 ^ b) ≤ bound := by simpa using hbound
  unfold ozaki1CRIS crSigned
  rw [ozaki1CRI_eq hp hle hmult W ss hl hb hvanish, vals_toSigned, vals_toSigned,
    ← allNegZeroI_eq]
  generalize hv : dot (entryVals (xs.map (·.1))) (entryVals (ys.map (·.1))) = v
  cases hr : roundRNE p emin emax v with
  | none => rfl
  | some r =>
    simp only [Option.map_some]
    by_cases hr0 : r = 0
    · subst hr0
      rw [if_neg (by simp), exactSignI_eq hmult hl hb hvanish, hv, Option.map_some]
      unfold sumNeg
      by_cases hz : v = 0
      · rw [if_pos ((sgnQ_eq_zero_iff v).mpr hz), if_pos hz]
      · rw [if_neg (fun h => hz ((sgnQ_eq_zero_iff v).mp h)), if_neg hz]
        congr 2
        exact decide_eq_decide.mpr (sgnQ_neg_iff v)
    · rw [if_pos hr0]
      obtain ⟨hv0, hsign⟩ := sign_of_round (roundRNE_nearest hp hle) (roundRNE_zero' p emin emax)
        hr hr0
      unfold sumNeg
      rw [if_neg hv0, hsign]

/-- **Binary64 entries with signed zeros**: the IEEE binary64 result, sign of zero included. -/
theorem ozaki1CRIS64_eq {mult : MatrixMultiplier} {b bound : ℕ} (hmult : mult.ExactOn b bound) (W : ℕ)
    (ss : List ℕ) {smax : ℕ} (hb : b ≤ 1025) (hsmax : 2098 < smax * (b + 1))
    {xs ys : List SEntry} (hlen : xs.length = ys.length)
    (hbound : xs.length * (2 ^ b * 2 ^ b) ≤ bound)
    (hx : ∀ a ∈ xs, Binary64Value (entryVal a.1)) (hy : ∀ a ∈ ys, Binary64Value (entryVal a.1)) :
    ozaki1CRIS mult 53 (-1022) 1023 b W ss smax xs ys =
      crSigned rne64 (xs.map toSigned) (ys.map toSigned) := by
  have hx' : ∀ v ∈ entryVals (xs.map (·.1)), Binary64Value v := by
    intro v hv; simp only [entryVals, List.map_map, List.mem_map] at hv
    obtain ⟨a, ha, rfl⟩ := hv; exact hx a ha
  have hy' : ∀ v ∈ entryVals (ys.map (·.1)), Binary64Value v := by
    intro v hv; simp only [entryVals, List.map_map, List.mem_map] at hv
    obtain ⟨a, ha, rfl⟩ := hv; exact hy a ha
  exact ozaki1CRIS_eq (by decide) (by decide) hmult W ss hlen hbound
    (vanish64 hb hsmax hx' hy' |>.imp fun s h => ⟨h.1, by rw [vanishInt_eq]; exact h.2⟩)

/-- **Binary32 entries with signed zeros.** -/
theorem ozaki1CRIS32_eq {mult : MatrixMultiplier} {b bound : ℕ} (hmult : mult.ExactOn b bound) (W : ℕ)
    (ss : List ℕ) {smax : ℕ} (hb : b ≤ 129) (hsmax : 277 < smax * (b + 1))
    {xs ys : List SEntry} (hlen : xs.length = ys.length)
    (hbound : xs.length * (2 ^ b * 2 ^ b) ≤ bound)
    (hx : ∀ a ∈ xs, Binary32Value (entryVal a.1)) (hy : ∀ a ∈ ys, Binary32Value (entryVal a.1)) :
    ozaki1CRIS mult 24 (-126) 127 b W ss smax xs ys =
      crSigned rne32Q (xs.map toSigned) (ys.map toSigned) := by
  have hx' : ∀ v ∈ entryVals (xs.map (·.1)), Binary32Value v := by
    intro v hv; simp only [entryVals, List.map_map, List.mem_map] at hv
    obtain ⟨a, ha, rfl⟩ := hv; exact hx a ha
  have hy' : ∀ v ∈ entryVals (ys.map (·.1)), Binary32Value v := by
    intro v hv; simp only [entryVals, List.map_map, List.mem_map] at hv
    obtain ⟨a, ha, rfl⟩ := hv; exact hy a ha
  exact ozaki1CRIS_eq (by decide) (by decide) hmult W ss hlen hbound
    (vanish32Q hb hsmax hx' hy' |>.imp fun s h => ⟨h.1, by rw [vanishInt_eq]; exact h.2⟩)

end Ozaki
