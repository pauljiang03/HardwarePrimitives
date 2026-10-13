import OzakiTC.ADPIntJ
import OzakiTC.Int8Checked
import Ozaki.BoundedChecked2

/-! # One theorem bounding every integer of ADP's correctly rounded slicing

`adpCRJ` (in `OzakiTC.ADPIntJ`) is ADP's correctly rounded slicing in integer operations. Its
checked twin `adpCRJC` passes every integer an arithmetic operation produces through a guard (data
below `2^R`, exponent-like integers below `2^X`), as `Ozaki.BoundedChecked` does for Ozaki-I:

* the floor exponents of the entries (`floorEntryExpC`), the fixed-point shift
  (`fixedShiftZC`), each shift amount and the shifted significand (`floorShiftZC`, `toFixedZC`),
  and the test for dropped bits (`Ozaki.Checked.dropsZC`);
* the remapped digits (`remapFromC`: the low digit with its carry, the remapped digit, the rest),
  each INT8 engine output read back, each weight `256^(t+u)`, each weighted product and every
  partial sum of the recombination (`int8RecombineKC`);
* the sums of the bound `K`, the enclosure's exponent, the enclosure test, and the exact path on
  the split-K INT8 engine (the checked jumping exact path of `Ozaki.BoundedChecked`).

The INT8 engine's own arithmetic is guarded too (`OzakiTC.Int8Checked`): every byte product,
every partial sum of each chunk's 32-bit register, checked against the register's own range so that
it never wraps, and every chunk sum of split-K, both in the recombination (`int8DotKC`) and on the
exact path (`int8SplitKC`).

`adpCRJC_eq`: on binary entries, for configurations `(s, W)` that fit, if `R` and `X` meet
`adpR`, `adpX` for each configuration and `exactR`, `exactX` for the exact path, the checked
function returns exactly what `adpCRJ` returns. `adpCRJC_binary64`: for binary64 entries,
`k ≤ 2^20`, configurations with `s ≤ 11` and `W ≤ 81` (as `(8, 56)` and `(11, 81)`) and at most
`300` slices on the exact path, every data integer fits `264` bits and every exponent and counter
`25` bits; `adpCRJC_binary64_eq` adds that the result is the binary64 round to nearest of `x · y`.
The tighter `259` and `17` bits are in `OzakiTC.CheckedTight`.

The same on Tensor Core blocks for Ozaki-II (`v100_fp64CRJ_widths`, `v100_binary32CRJ_widths`). -/

open TensorCore
open Ozaki.Checked

namespace Ozaki.TC

/-! ## The checked functions -/

/-- `floorEntryExp`: the exponent `⌊log₂ |m|⌋ + e`. -/
def floorEntryExpC (B : Widths) (a : ℤ × ℤ) : Option (Option ℤ) :=
  if a.1 = 0 then some none else (B.ge ((a.1.natAbs.log2 : ℤ) + a.2)).map some

def maxFloorExpC (B : Widths) : List (ℤ × ℤ) → Option (Option ℤ)
  | [] => some none
  | a :: xs => do
    let e ← floorEntryExpC B a
    let m ← maxFloorExpC B xs
    pure (optMax e m)

/-- `fixedShiftZ`: the largest floor exponent and the shift. -/
def fixedShiftZC (B : Widths) (W : ℕ) (xs : List (ℤ × ℤ)) : Option ℤ := do
  let m ← maxFloorExpC B xs
  B.ge ((W : ℤ) - 1 - m.getD (-1))

/-- `floorShiftZ`: the left-shifted significand or the floor quotient. -/
def floorShiftZC (B : Widths) (m j : ℤ) : Option ℤ :=
  if m = 0 then some 0
  else if 0 ≤ j then B.gv (m * 2 ^ j.toNat)
  else if m.natAbs.log2 < (-j).toNat then some (if m < 0 then -1 else 0)
  else B.gv (m / ((2 ^ (-j).toNat : ℕ) : ℤ))

def toFixedZC (B : Widths) (f : ℤ) (xs : List (ℤ × ℤ)) : Option (List ℤ) :=
  xs.mapM fun a => do
    let j ← B.ge (a.2 + f)
    floorShiftZC B a.1 j

/-- `remapFrom`: the low digit with its carry, its remap, and the rest. -/
def remapFromC (B : Widths) (carry : ℤ) : ℕ → ℤ → Option (List ℤ)
  | 0, _ => some []
  | 1, N => do
    let d ← B.gv (N + carry)
    pure [d]
  | s + 2, N => do
    let lo ← B.gv (N % 256 + carry)
    let hi ← B.gv (N / 256)
    if 128 ≤ lo then do
      let d ← B.gv (lo - 256)
      let rest ← remapFromC B 1 (s + 1) hi
      pure (d :: rest)
    else do
      let rest ← remapFromC B 0 (s + 1) hi
      pure (lo :: rest)

def sliceVecC (B : Widths) (s t : ℕ) (N : List ℤ) : Option (List ℤ) :=
  N.mapM fun z => do
    let ds ← remapFromC B 0 s z
    pure (ds.getD t 0)

/-- `int8RecombineK`: the slices, each INT8 engine output read back, each weight, each weighted
product, and the partial sums of the rows and of the whole. -/
def int8RecombineKC (B : Widths) (s : ℕ) (Na Nb : List ℤ) : Option ℤ := do
  let rows ← (List.range s).mapM fun t => do
    let terms ← (List.range s).mapM fun u => do
      let sa ← sliceVecC B s t Na
      let sb ← sliceVecC B s u Nb
      let d ← int8DotKC B sa sb
      let P ← B.gv (256 ^ (t + u))
      B.gv (P * d)
    sumC B terms
  sumC B rows

/-- `adpEnclosureZ`: the fixed point, the recombined product, its exponent, and the bound. -/
def adpEnclosureZC (B : Widths) (s W : ℕ) (xs ys : List (ℤ × ℤ)) :
    Option (ℤ × ℤ × ℤ × ℤ) := do
  let fx ← fixedShiftZC B W xs
  let fy ← fixedShiftZC B W ys
  let Na ← toFixedZC B fx xs
  let Nb ← toFixedZC B fy ys
  let N ← int8RecombineKC B s Na Nb
  let ff ← B.ge (fx + fy)
  let q ← B.ge (-ff)
  let dx ← dropsZC B fx xs
  let dy ← dropsZC B fy ys
  let K ← boundKC B Na Nb dx dy xs.length
  pure (N, q, K, q)

/-- **ADP's correctly rounded slicing in integers, every integer guarded.** -/
def adpCRJC (B : Widths) (cfgs : List (ℕ × ℕ)) (smax : ℕ) (xs ys : List (ℤ × ℤ)) :
    Option (Option ℚ) := do
  let es ← cfgs.mapM fun c => (adpEnclosureZC B c.1 c.2 xs ys).map some
  let ex ← ozaki1ExactFallbackIC B (int8SplitKC B) 53 (-1022) 1023 6 smax xs ys
  roundingTestBC B 53 (-1022) 1023 es ex

/-! ## No guard fails -/

theorem floorEntryExp_natAbs_le {a : ℤ × ℤ} {p EM : ℕ} (ha : a.1.natAbs < 2 ^ p)
    (he : a.2.natAbs ≤ EM) {c : ℤ} (h : floorEntryExp a = some c) : c.natAbs ≤ p + EM := by
  unfold floorEntryExp at h
  split at h
  · cases h
  · cases h
    have := log2_le_of_lt ha
    omega

theorem maxFloorExpC_eq {B : Widths} {p EM : ℕ} (hX : p + EM < 2 ^ B.X) :
    ∀ {xs : List (ℤ × ℤ)}, EntriesIn p EM xs → maxFloorExpC B xs = some (maxFloorExp xs)
  | [], _ => rfl
  | a :: xs, h => by
    have ha := h a List.mem_cons_self
    have he : floorEntryExpC B a = some (floorEntryExp a) := by
      unfold floorEntryExpC floorEntryExp
      split
      · rfl
      · have := log2_le_of_lt ha.1
        rw [Widths.ge_ok (by have := Int.natAbs_add_le (a.1.natAbs.log2 : ℤ) a.2; omega)]
        rfl
    unfold maxFloorExpC maxFloorExp
    rw [he, maxFloorExpC_eq hX fun c hc => h c (List.mem_cons_of_mem _ hc)]
    rfl

theorem fixedShiftZ_natAbs_le {W p EM : ℕ} {xs : List (ℤ × ℤ)} (hx : EntriesIn p EM xs) :
    (fixedShiftZ W xs).natAbs ≤ W + 1 + p + EM := by
  unfold fixedShiftZ
  cases h : maxFloorExp xs with
  | none => simp only [Option.getD_none]; omega
  | some c =>
    simp only [Option.getD_some]
    obtain ⟨_, a, ha, hac⟩ := maxFloorExp_eq_some h
    have := floorEntryExp_natAbs_le (hx a ha).1 (hx a ha).2 hac
    omega

theorem fixedShiftZC_eq {B : Widths} {W p EM : ℕ} {xs : List (ℤ × ℤ)} (hx : EntriesIn p EM xs)
    (hX : W + 1 + p + EM < 2 ^ B.X) : fixedShiftZC B W xs = some (fixedShiftZ W xs) := by
  have hb := fixedShiftZ_natAbs_le (W := W) hx
  unfold fixedShiftZC
  rw [maxFloorExpC_eq (by omega) hx]
  simp only [Option.bind_eq_bind, Option.bind_some]
  exact Widths.ge_ok (by unfold fixedShiftZ at hb; omega)

theorem floorShiftZC_eq {B : Widths} {m j : ℤ} (hm : m.natAbs < 2 ^ B.R)
    (hres : (floorShiftZ m j).natAbs < 2 ^ B.R) : floorShiftZC B m j = some (floorShiftZ m j) := by
  unfold floorShiftZC
  unfold floorShiftZ at hres ⊢
  split
  · rfl
  · rename_i hm0
    rw [if_neg hm0] at hres
    split
    · rename_i hj
      rw [if_pos hj] at hres
      exact Widths.gv_ok hres
    · rename_i hj
      rw [if_neg hj] at hres
      split
      · rfl
      · exact Widths.gv_ok (Nat.lt_of_le_of_lt (Int.natAbs_ediv_le_natAbs _ _) hm)

theorem toFixedZC_eq {B : Widths} {W p EM : ℕ} {xs : List (ℤ × ℤ)} (hx : EntriesIn p EM xs)
    (hpR : p ≤ B.R) (hWR : W < B.R) (hX : EM + (W + 1 + p + EM) < 2 ^ B.X) :
    toFixedZC B (fixedShiftZ W xs) xs = some (toFixedZ (fixedShiftZ W xs) xs) := by
  have hb := fixedShiftZ_natAbs_le (W := W) hx
  have hres := toFixedZ_natAbs_le W xs
  have hW : 2 ^ W < 2 ^ B.R := Nat.pow_lt_pow_right (by decide) hWR
  unfold toFixedZC toFixedZ
  apply mapM_eq_some_map
  intro a ha
  have hj : (a.2 + fixedShiftZ W xs).natAbs < 2 ^ B.X := by
    have := (hx a ha).2
    have := Int.natAbs_add_le a.2 (fixedShiftZ W xs)
    omega
  rw [Widths.ge_ok hj]
  simp only [Option.bind_eq_bind, Option.bind_some]
  have hr := hres _ (List.mem_map_of_mem ha)
  exact floorShiftZC_eq (lt_two_pow_of_le (hx a ha).1 hpR) (by omega)

theorem dropsZC_eq_of {B : Widths} {s : ℤ} {S p EM : ℕ} {xs : List (ℤ × ℤ)}
    (hx : EntriesIn p EM xs) (hpR : p ≤ B.R) (hs : s.natAbs ≤ S) (hX : EM + S < 2 ^ B.X) :
    dropsZC B s xs = some (dropsZ s xs) := by
  unfold dropsZC dropsZ
  rw [mapM_eq_some_map (g := fun a => dropsBits a.1 (a.2 + s)) fun a ha => by
    have hj : (a.2 + s).natAbs < 2 ^ B.X := by
      have := (hx a ha).2
      have := Int.natAbs_add_le a.2 s
      omega
    rw [Widths.ge_ok hj]
    simp only [Option.bind_eq_bind, Option.bind_some]
    exact dropsBitsC_eq (lt_two_pow_of_le (hx a ha).1 hpR)]
  simp only [Option.bind_eq_bind, Option.bind_some, Option.pure_def, List.any_map]
  rfl

theorem remapFromC_eq {B : Widths} {D : ℕ} (hD : D + 10 ≤ B.R) :
    ∀ (s : ℕ) (carry N : ℤ), N.natAbs ≤ 2 ^ D → 0 ≤ carry → carry ≤ 1 →
      remapFromC B carry s N = some (ADP.remapFrom carry s N)
  | 0, _, _, _, _, _ => rfl
  | 1, carry, N, hN, hc0, hc1 => by
    have : 2 ^ D * 1024 ≤ 2 ^ B.R := by
      rw [show 1024 = 2 ^ 10 by rfl, ← Nat.pow_add]; exact Nat.pow_le_pow_right (by decide) hD
    have hp := Nat.two_pow_pos D
    have hc : carry.natAbs ≤ 1 := by omega
    unfold remapFromC ADP.remapFrom
    rw [Widths.gv_ok (by have := Int.natAbs_add_le N carry; omega)]
    rfl
  | s + 2, carry, N, hN, hc0, hc1 => by
    have h1024 : 2 ^ D * 1024 ≤ 2 ^ B.R := by
      rw [show 1024 = 2 ^ 10 by rfl, ← Nat.pow_add]; exact Nat.pow_le_pow_right (by decide) hD
    have hp := Nat.two_pow_pos D
    have e1 := Int.emod_nonneg N (show (256 : ℤ) ≠ 0 by decide)
    have e2 := Int.emod_lt_of_pos N (show (0 : ℤ) < 256 by decide)
    have hhi : (N / 256).natAbs ≤ 2 ^ D :=
      Nat.le_trans (Int.natAbs_ediv_le_natAbs _ _) hN
    unfold remapFromC ADP.remapFrom
    rw [Widths.gv_ok (by omega), Widths.gv_ok (by omega)]
    simp only [Option.bind_eq_bind, Option.bind_some]
    split
    · rw [Widths.gv_ok (by omega)]
      simp only [Option.bind_some]
      rw [remapFromC_eq hD (s + 1) 1 (N / 256) hhi (by decide) (by decide)]
      rfl
    · rw [remapFromC_eq hD (s + 1) 0 (N / 256) hhi (by decide) (by decide)]
      rfl

theorem sliceVecC_eq {B : Widths} {D : ℕ} (hD : D + 10 ≤ B.R) (s t : ℕ) {N : List ℤ}
    (hN : ∀ z ∈ N, z.natAbs ≤ 2 ^ D) : sliceVecC B s t N = some (ADP.sliceVec s t N) := by
  unfold sliceVecC ADP.sliceVec
  apply mapM_eq_some_map
  intro z hz
  rw [remapFromC_eq hD s 0 z (hN z hz) (by decide) (by decide)]
  rfl

/-- The recombination's bound: `s² · 256^(2(s−1)) · k · 2^14 < 2^(16 s + 2 bitlen s + bitlen k +
14)`. -/
theorem recombine_bound (s k : ℕ) :
    s * s * (256 ^ (2 * (s - 1)) * (k * (128 * 128))) <
      2 ^ (16 * s + 2 * bitlen s + bitlen k + 14) := by
  have hs := lt_two_pow_bitlen s
  have hk := lt_two_pow_bitlen k
  have h256 : 256 ^ (2 * (s - 1)) ≤ 2 ^ (16 * s) := by
    rw [show (256 : ℕ) = 2 ^ 8 by rfl, ← Nat.pow_mul]
    exact Nat.pow_le_pow_right (by decide) (by omega)
  have e : 2 ^ (16 * s + 2 * bitlen s + bitlen k + 14) =
      2 ^ bitlen s * 2 ^ bitlen s * (2 ^ (16 * s) * (2 ^ bitlen k * (128 * 128))) := by
    rw [show (128 * 128 : ℕ) = 2 ^ 14 by rfl]
    simp only [← Nat.pow_add]
    congr 1; omega
  rw [e]
  have h1 : s * s ≤ 2 ^ bitlen s * 2 ^ bitlen s := Nat.mul_le_mul (Nat.le_of_lt hs) (Nat.le_of_lt hs)
  have h2 : 256 ^ (2 * (s - 1)) * (k * (128 * 128)) < 2 ^ (16 * s) * (2 ^ bitlen k * (128 * 128)) :=
    Nat.lt_of_le_of_lt (Nat.mul_le_mul_right _ h256)
      (Nat.mul_lt_mul_of_pos_left (Nat.mul_lt_mul_of_pos_right hk (by decide)) (Nat.two_pow_pos _))
  by_cases h0 : s = 0
  · subst h0
    simp only [Nat.zero_mul]
    exact Nat.mul_pos (Nat.mul_pos (Nat.two_pow_pos _) (Nat.two_pow_pos _))
      (Nat.mul_pos (Nat.two_pow_pos _) (Nat.mul_pos (Nat.two_pow_pos _) (by decide)))
  · exact Nat.lt_of_le_of_lt (Nat.mul_le_mul_right _ h1)
      (Nat.mul_lt_mul_of_pos_left h2 (Nat.mul_pos (Nat.two_pow_pos _) (Nat.two_pow_pos _)))

theorem int8RecombineKC_eq {B : Widths} {s W : ℕ} (hs : 0 < s) {Na Nb : List ℤ}
    (hlen : Na.length = Nb.length)
    (hx : ∀ z ∈ Na, ADP.remapLo s ≤ z ∧ z ≤ ADP.remapHi s)
    (hy : ∀ z ∈ Nb, ADP.remapLo s ≤ z ∧ z ≤ ADP.remapHi s)
    (hNa : ∀ z ∈ Na, z.natAbs ≤ 2 ^ W) (hNb : ∀ z ∈ Nb, z.natAbs ≤ 2 ^ W) (hWR : W + 10 ≤ B.R)
    (hR : 16 * s + 2 * bitlen s + bitlen Na.length + 14 ≤ B.R) :
    int8RecombineKC B s Na Nb = some (int8RecombineK s Na Nb) := by
  obtain ⟨T, hT⟩ : ∃ T, T = 256 ^ (2 * (s - 1)) * (Na.length * (128 * 128)) := ⟨_, rfl⟩
  have hbig : s * s * T < 2 ^ B.R := by
    rw [hT]
    exact Nat.lt_of_lt_of_le (recombine_bound s Na.length) (Nat.pow_le_pow_right (by decide) hR)
  have hsT : s * T ≤ s * s * T := by
    rw [Nat.mul_assoc s s T]; exact Nat.le_mul_of_pos_left _ hs
  have hTs : T ≤ s * T := Nat.le_mul_of_pos_left _ hs
  have hterm : ∀ t ∈ List.range s, ∀ u ∈ List.range s,
      (256 ^ (t + u) * int8DotK (ADP.sliceVec s t Na) (ADP.sliceVec s u Nb)).natAbs ≤ T := by
    intro t ht u hu
    rw [hT]
    exact int8RecombineK_term_le hs hlen hx hy (List.mem_range.mp ht) (List.mem_range.mp hu)
  have hd : ∀ t ∈ List.range s, ∀ u ∈ List.range s,
      (int8DotK (ADP.sliceVec s t Na) (ADP.sliceVec s u Nb)).natAbs ≤ T := by
    intro t ht u hu
    have h1 := int8DotK_natAbs_le (by simp [ADP.sliceVec, hlen]) (sliceVec_s8 hs hx t)
      (sliceVec_s8 hs hy u)
    have hl : (ADP.sliceVec s t Na).length = Na.length := by simp [ADP.sliceVec]
    rw [hl] at h1
    rw [hT]
    exact Nat.le_trans h1 (Nat.le_mul_of_pos_left _ (Nat.pow_pos (by decide)))
  have hPR : ∀ t ∈ List.range s, ∀ u ∈ List.range s, ((256 : ℤ) ^ (t + u)).natAbs < 2 ^ B.R := by
    intro t ht u hu
    have h1 := List.mem_range.mp ht
    have h2 := List.mem_range.mp hu
    rw [Int.natAbs_pow, show (256 : ℤ).natAbs = 2 ^ 8 by rfl, ← Nat.pow_mul]
    exact Nat.pow_lt_pow_right (by decide) (by omega)
  have hrowb : ∀ t ∈ List.range s, (((List.range s).map fun u =>
      256 ^ (t + u) * int8DotK (ADP.sliceVec s t Na) (ADP.sliceVec s u Nb)).map Int.natAbs).sum ≤
      s * T := by
    intro t ht
    have := sum_natAbs_le_mul (a := (List.range s).map fun u =>
      256 ^ (t + u) * int8DotK (ADP.sliceVec s t Na) (ADP.sliceVec s u Nb)) (n := T) (by
        intro z hz
        obtain ⟨u, hu, rfl⟩ := List.mem_map.mp hz
        exact hterm t ht u hu)
    simpa using this
  unfold int8RecombineKC int8RecombineK
  rw [mapM_eq_some_map (g := fun t => ((List.range s).map fun u =>
      256 ^ (t + u) * int8DotK (ADP.sliceVec s t Na) (ADP.sliceVec s u Nb)).sum) fun t ht => by
    rw [mapM_eq_some_map (g := fun u =>
        256 ^ (t + u) * int8DotK (ADP.sliceVec s t Na) (ADP.sliceVec s u Nb)) fun u hu => by
      rw [sliceVecC_eq hWR s t hNa, sliceVecC_eq hWR s u hNb]
      simp only [Option.bind_eq_bind, Option.bind_some]
      have hsl : (ADP.sliceVec s t Na).length = (ADP.sliceVec s u Nb).length := by
        simp [ADP.sliceVec, hlen]
      have hdot : dotAbs (ADP.sliceVec s t Na) (ADP.sliceVec s u Nb) < 2 ^ B.R := by
        have h1 := dotAbs_le _ _ 128 128 (sliceVec_s8 hs hx t) (sliceVec_s8 hs hy u)
        have hl : (ADP.sliceVec s t Na).length = Na.length := by simp [ADP.sliceVec]
        rw [hl] at h1
        have h2 : Na.length * (128 * 128) ≤ T := by
          rw [hT]; exact Nat.le_mul_of_pos_left _ (Nat.pow_pos (by decide))
        omega
      have h31 : 31 ≤ B.R := by have := bitlen_pos (Nat.ne_of_gt hs); omega
      rw [int8DotKC_eq h31 hsl (sliceVec_s8 hs hx t) (sliceVec_s8 hs hy u) hdot,
        Widths.gv_ok (hPR t ht u hu)]
      simp only [Option.bind_some]
      exact Widths.gv_ok (Nat.lt_of_le_of_lt (hterm t ht u hu) (by omega))]
    simp only [Option.bind_eq_bind, Option.bind_some]
    exact sumC_eq (Nat.lt_of_le_of_lt (hrowb t ht) (by omega))]
  simp only [Option.bind_eq_bind, Option.bind_some]
  apply sumC_eq
  have := sum_natAbs_le_mul (a := (List.range s).map fun t => ((List.range s).map fun u =>
      256 ^ (t + u) * int8DotK (ADP.sliceVec s t Na) (ADP.sliceVec s u Nb)).sum) (n := s * T) (by
    intro z hz
    obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hz
    exact Nat.le_trans (natAbs_listSum_le _) (hrowb t ht))
  simp only [List.length_map, List.length_range] at this
  have : s * (s * T) = s * s * T := by rw [Nat.mul_assoc]
  omega

/-- The requirement on `R` for one ADP configuration `(s, W)`: the recombination's partial sums
(`s² 256^(2(s−1)) k 2^14`), and the enclosure test on the product (at most `k 2^(2W)`) and the bound
(at most `k (2^(W+1) + 1)`). -/
def adpR (s W p k : ℕ) : ℕ :=
  max (16 * s + 2 * bitlen s + bitlen k + 14) (2 * W + bitlen k + p + 10)

/-- The requirement on `X` for one ADP configuration. -/
def adpX (W p EM k : ℕ) (emin emax : ℤ) (R : ℕ) : ℕ :=
  8 * (W + p + 2 * EM + 3) + 2 * (2 * W + bitlen k + p + 4) + emin.natAbs + emax.natAbs + 2 * p +
    2 * R + 8

theorem toFixedZ_remap {s W : ℕ} (hfit : ADP.remapFits W s = true) (xs : List (ℤ × ℤ)) :
    ∀ z ∈ toFixedZ (fixedShiftZ W xs) xs, ADP.remapLo s ≤ z ∧ z ≤ ADP.remapHi s := by
  rw [fixedShiftZ_eq, toFixedZ_eq]
  exact toFixed_remap hfit (entryVals xs)

theorem toFixedZ_length (f : ℤ) (xs : List (ℤ × ℤ)) : (toFixedZ f xs).length = xs.length := by
  simp [toFixedZ]

theorem two_mul_k_le {k W : ℕ} : 2 * k * (2 ^ W + 1) < 2 ^ (bitlen k + W + 2) := by
  have hk := lt_two_pow_bitlen k
  have e : 2 ^ (bitlen k + W + 2) = 2 ^ bitlen k * 2 ^ W * 4 := by rw [Nat.pow_add, Nat.pow_add]
  rw [e]
  have h1 : 2 * k * (2 ^ W + 1) ≤ 2 * k * (2 * 2 ^ W) :=
    Nat.mul_le_mul_left _ (by have := Nat.one_le_two_pow (n := W); omega)
  have h2 : k * 2 ^ W < 2 ^ bitlen k * 2 ^ W := Nat.mul_lt_mul_of_pos_right hk (Nat.two_pow_pos W)
  grind

theorem adpEnclosureZC_eq {B : Widths} {s W p EM : ℕ} {emin emax : ℤ} (hs : 0 < s)
    (hfit : ADP.remapFits W s = true) {xs ys : List (ℤ × ℤ)} (hlen : xs.length = ys.length)
    (hx : EntriesIn p EM xs) (hy : EntriesIn p EM ys) (hR : adpR s W p xs.length ≤ B.R)
    (hX : adpX W p EM xs.length emin emax B.R < 2 ^ B.X) :
    adpEnclosureZC B s W xs ys = some (adpEnclosureZ s W xs ys) := by
  unfold adpR at hR
  unfold adpX at hX
  have hbx := fixedShiftZ_natAbs_le (W := W) hx
  have hby := fixedShiftZ_natAbs_le (W := W) hy
  unfold adpEnclosureZC adpEnclosureZ
  rw [fixedShiftZC_eq hx (by omega), fixedShiftZC_eq hy (by omega)]
  simp only [Option.bind_eq_bind, Option.bind_some]
  rw [toFixedZC_eq hx (by omega) (by omega) (by omega), toFixedZC_eq hy (by omega) (by omega)
    (by omega)]
  simp only [Option.bind_some]
  rw [int8RecombineKC_eq hs (by rw [toFixedZ_length, toFixedZ_length, hlen]) (toFixedZ_remap hfit xs)
    (toFixedZ_remap hfit ys) (toFixedZ_natAbs_le W xs) (toFixedZ_natAbs_le W ys) (by omega)
    (by rw [toFixedZ_length]; omega)]
  simp only [Option.bind_some]
  have hs2 := Int.natAbs_add_le (fixedShiftZ W xs) (fixedShiftZ W ys)
  rw [Widths.ge_ok (by omega)]
  simp only [Option.bind_some]
  rw [Widths.ge_ok (by rw [Int.natAbs_neg]; omega)]
  simp only [Option.bind_some]
  rw [dropsZC_eq_of hx (by omega) hbx (by omega), dropsZC_eq_of hy (by omega) hby (by omega)]
  simp only [Option.bind_some]
  have hk : 2 * xs.length * (2 ^ W + 1) < 2 ^ B.R :=
    Nat.lt_of_lt_of_le two_mul_k_le (Nat.pow_le_pow_right (by decide) (by omega))
  rw [boundKC_eq (M := 2 ^ W) (toFixedZ_natAbs_le W xs) (toFixedZ_natAbs_le W ys)
    (toFixedZ_length _ xs) (by rw [toFixedZ_length, hlen]) hk]
  rfl

/-- **One theorem bounding every integer of ADP's correctly rounded slicing.** On binary64-style
entries (significands below `2^53`, exponents at most `EM` in magnitude), for configurations that
fit, if `R` and `X` meet `adpR`, `adpX` for every configuration and `exactR`, `exactX` for the
exact path on the INT8 engine, the checked function returns exactly what `adpCRJ` returns: no
guard ever fails. -/
theorem adpCRJC_eq {B : Widths} {EM smax : ℕ} {cfgs : List (ℕ × ℕ)} {xs ys : List (ℤ × ℤ)}
    (hlen : xs.length = ys.length) (hx : EntriesIn 53 EM xs) (hy : EntriesIn 53 EM ys)
    (hcfg : ∀ c ∈ cfgs, 0 < c.1 ∧ ADP.remapFits c.2 c.1 = true ∧
      adpR c.1 c.2 53 xs.length ≤ B.R ∧ adpX c.2 53 EM xs.length (-1022) 1023 B.R < 2 ^ B.X)
    (hRe : exactR 53 smax (xs.length * (2 ^ 6 * 2 ^ 6)) ≤ B.R) (hRb : 53 + 6 + 3 ≤ B.R)
    (hXe : exactX 53 6 EM smax (xs.length * (2 ^ 6 * 2 ^ 6)) (-1022) 1023 B.R < 2 ^ B.X) :
    adpCRJC B cfgs smax xs ys = some (adpCRJ cfgs smax xs ys) := by
  unfold adpCRJC adpCRJ
  rw [mapM_eq_some_map (g := fun c => some (adpEnclosureZ c.1 c.2 xs ys)) fun c hc => by
    obtain ⟨hs, hfit, hR, hX⟩ := hcfg c hc
    rw [adpEnclosureZC_eq hs hfit hlen hx hy hR hX]
    rfl]
  simp only [Option.bind_eq_bind, Option.bind_some]
  have hD : xs.length * (2 ^ 6 * 2 ^ 6) < 2 ^ B.R := by
    unfold exactR at hRe
    exact Nat.lt_of_lt_of_le (lt_two_pow_bitlen _) (Nat.pow_le_pow_right (by decide) (by omega))
  rw [ozaki1ExactFallbackIC_eq (int8SplitKC_exactOn (by omega) hD) hlen (Nat.le_refl _) hx hy hRe hRb
    hXe, ozaki1ExactFallbackI_congr (int8SplitKC_exactOn (by omega) hD) (int8SplitK_exactOn _) _ _ _ _
    hlen (Nat.le_refl _)]
  simp only [Option.bind_some]
  apply roundingTestBC_eq
  intro e he t het
  obtain ⟨c, hc, rfl⟩ := List.mem_map.mp he
  cases het
  obtain ⟨hs, hfit, hR, hX⟩ := hcfg c hc
  unfold adpR at hR
  unfold adpX at hX
  have hbx := fixedShiftZ_natAbs_le (W := c.2) hx
  have hby := fixedShiftZ_natAbs_le (W := c.2) hy
  have hl : (toFixedZ (fixedShiftZ c.2 xs) xs).length = (toFixedZ (fixedShiftZ c.2 ys) ys).length :=
    by rw [toFixedZ_length, toFixedZ_length, hlen]
  have hN : (int8RecombineK c.1 (toFixedZ (fixedShiftZ c.2 xs) xs)
      (toFixedZ (fixedShiftZ c.2 ys) ys)).natAbs < 2 ^ (2 * c.2 + bitlen xs.length + 2) := by
    rw [int8RecombineK_eq hs hl (toFixedZ_remap hfit xs) (toFixedZ_remap hfit ys)]
    have h1 := Nat.le_trans (natAbs_dotZ_le _ _) (dotAbs_le _ _ _ _ (toFixedZ_natAbs_le c.2 xs)
      (toFixedZ_natAbs_le c.2 ys))
    rw [toFixedZ_length] at h1
    have hk := lt_two_pow_bitlen xs.length
    have e : 2 ^ (2 * c.2 + bitlen xs.length + 2) = 2 ^ bitlen xs.length * (2 ^ c.2 * 2 ^ c.2) * 4 := by
      rw [Nat.pow_add, Nat.pow_add, Nat.two_mul, Nat.pow_add]; grind
    have h2 : xs.length * (2 ^ c.2 * 2 ^ c.2) < 2 ^ bitlen xs.length * (2 ^ c.2 * 2 ^ c.2) :=
      Nat.mul_lt_mul_of_pos_right hk (Nat.mul_pos (Nat.two_pow_pos _) (Nat.two_pow_pos _))
    omega
  have hK := (boundK_le (k := xs.length) (n := 2 ^ c.2) (dx := dropsZ (fixedShiftZ c.2 xs) xs)
    (dy := dropsZ (fixedShiftZ c.2 ys) ys) (toFixedZ_length _ xs) (by rw [toFixedZ_length, hlen])
    (toFixedZ_natAbs_le c.2 xs) (toFixedZ_natAbs_le c.2 ys)).2
  have hK' : xs.length * (2 * 2 ^ c.2 + 1) < 2 ^ (2 * c.2 + bitlen xs.length + 2) := by
    have h3 := two_mul_k_le (k := xs.length) (W := c.2)
    have : xs.length * (2 * 2 ^ c.2 + 1) ≤ 2 * xs.length * (2 ^ c.2 + 1) := by grind
    exact Nat.lt_of_lt_of_le (Nat.lt_of_le_of_lt this h3)
      (Nat.pow_le_pow_right (by decide) (by omega))
  have hq : (-(fixedShiftZ c.2 xs + fixedShiftZ c.2 ys)).natAbs ≤ 2 * (c.2 + 1 + 53 + EM) := by
    rw [Int.natAbs_neg]
    have := Int.natAbs_add_le (fixedShiftZ c.2 xs) (fixedShiftZ c.2 ys)
    omega
  have hm1 : (-1022 : ℤ).natAbs = 1022 := by decide
  have hm2 : (1023 : ℤ).natAbs = 1023 := by decide
  exact enclosureTestBC_eq (E := 2 * c.2 + bitlen xs.length + 2)
    (D := 2 * c.2 + bitlen xs.length + 2 + 53 + 2) hN (by omega) (by omega) (by omega)
    (by omega) (by omega)

theorem bitlen_le_four {s : ℕ} (hs : s ≤ 11) : bitlen s ≤ 4 := bitlen_le_iff.mpr (by omega)

/-- **Every integer of ADP's correctly rounded slicing fits 264 bits, every exponent and counter
25 bits**: on binary64 entries, `k ≤ 2^20`, configurations with at most `11` slices and widths at
most `81` that fit, and at most `300` slices of `6` bits on the exact path. -/
theorem adpCRJC_binary64 {cfgs : List (ℕ × ℕ)} {xs ys : List (ℤ × ℤ)} (hlen : xs.length = ys.length)
    (hk : xs.length ≤ 2 ^ 20) (hx : ∀ a ∈ xs, FormatEntry 53 (-1022) 1023 a)
    (hy : ∀ a ∈ ys, FormatEntry 53 (-1022) 1023 a)
    (hcfgs : ∀ c ∈ cfgs, 0 < c.1 ∧ c.1 ≤ 11 ∧ c.2 ≤ 81 ∧ ADP.remapFits c.2 c.1 = true) :
    adpCRJC ⟨264, 25⟩ cfgs 300 xs ys = some (adpCRJ cfgs 300 xs ys) := by
  have hE : ((-1022 : ℤ) - ((53 : ℕ) - 1 : ℤ)).natAbs ≤ 1074 ∧
      ((1023 : ℤ) - ((53 : ℕ) - 1 : ℤ)).natAbs ≤ 1074 := by decide
  have hbk := bitlen_length_le hk
  have hbud : bitlen (xs.length * (2 ^ 6 * 2 ^ 6)) ≤ 33 := bitlen_le_iff.mpr (by omega)
  have hW : exactW 53 300 = 74 := by decide
  have hb2 : bitlen (300 * 300 + 2) = 17 := by decide
  have hm1 : (-1022 : ℤ).natAbs = 1022 := by decide
  have hm2 : (1023 : ℤ).natAbs = 1023 := by decide
  refine adpCRJC_eq hlen (entriesIn_of_format hE hx) (entriesIn_of_format hE hy) ?_ ?_ (by decide) ?_
  · intro c hc
    obtain ⟨h0, h1, h2, h3⟩ := hcfgs c hc
    have := bitlen_le_four h1
    refine ⟨h0, h3, ?_, ?_⟩
    · unfold adpR; simp only; omega
    · unfold adpX; simp only; omega
  · unfold exactR; rw [hW, hb2]; simp only; omega
  · unfold exactX; rw [hW]; simp only; omega

/-- **ADP's slicing, every integer within 264 bits, correctly rounded**: the checked function
returns the binary64 round to nearest of `x · y`. -/
theorem adpCRJC_binary64_eq {cfgs : List (ℕ × ℕ)} {xs ys : List (ℤ × ℤ)}
    (hlen : xs.length = ys.length) (hk : xs.length ≤ 2 ^ 20)
    (hx : ∀ a ∈ xs, FormatEntry 53 (-1022) 1023 a) (hy : ∀ a ∈ ys, FormatEntry 53 (-1022) 1023 a)
    (hcfgs : ∀ c ∈ cfgs, 0 < c.1 ∧ c.1 ≤ 11 ∧ c.2 ≤ 81 ∧ ADP.remapFits c.2 c.1 = true) :
    adpCRJC ⟨264, 25⟩ cfgs 300 xs ys = some (rne64 (dot (entryVals xs) (entryVals ys))) := by
  rw [adpCRJC_binary64 hlen hk hx hy hcfgs,
    adpCRJ_eq (fun c hc => ⟨(hcfgs c hc).1, (hcfgs c hc).2.2.2⟩) (by decide)
      (fun v hv => by obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hv; exact (hx a ha).formatValue)
      (fun v hv => by obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hv; exact (hy a ha).formatValue) hlen]

/-! ## Ozaki-II on Tensor Core blocks, every integer bounded -/

/-- **FP64 by Ozaki-II on V100 fp16, every integer bounded**: `264` bits for data, `24` for
exponents and counters, the twelve moduli at most `4096` with `P ≤ 69`. -/
theorem v100_fp64CRJ_widths {xs ys : List (ℤ × ℤ)} {cfgs : List (CRTBasis × ℕ)}
    (hlen : xs.length = ys.length) (hk : xs.length ≤ 2 ^ 20)
    (hx : ∀ a ∈ xs, FormatEntry 53 (-1022) 1023 a) (hy : ∀ a ∈ ys, FormatEntry 53 (-1022) 1023 a)
    (hcfgs : ∀ c ∈ cfgs, c.1 = fp64Basis ∧ c.2 ≤ 69)
    (hrange : ∀ c ∈ cfgs, 2 * xs.length * (2 ^ c.2 * 2 ^ c.2) < c.1.modulus) :
    ozaki2CRJC ⟨264, 24⟩ (tcSplitK v100F16F32 11) 53 (-1022) 1023 cfgs 11 175 xs ys =
      some (rne64 (dot (entryVals xs) (entryVals ys))) :=
  ozaki2CRJC_binary64_eq (tcSplitK_exactOn v100_exactOn (by decide) _) hlen hk hx hy hcfgs hrange

/-- **Binary32 by Ozaki-II on V100 fp16, every integer bounded**: `161` bits for data, `17` for
exponents and counters, six moduli at most `4096` with `P ≤ 34`. -/
theorem v100_binary32CRJ_widths {xs ys : List (ℤ × ℤ)} {cfgs : List (CRTBasis × ℕ)}
    (hlen : xs.length = ys.length) (hk : xs.length ≤ 2 ^ 20)
    (hx : ∀ a ∈ xs, FormatEntry 24 (-126) 127 a) (hy : ∀ a ∈ ys, FormatEntry 24 (-126) 127 a)
    (hcfgs : ∀ c ∈ cfgs, c.1 = fp32Basis6 ∧ c.2 ≤ 34)
    (hrange : ∀ c ∈ cfgs, 2 * xs.length * (2 ^ c.2 * 2 ^ c.2) < c.1.modulus) :
    ozaki2CRJC ⟨161, 17⟩ (tcSplitK v100F16F32 11) 24 (-126) 127 cfgs 11 24 xs ys =
      some (rne32Q (dot (entryVals xs) (entryVals ys))) :=
  ozaki2CRJC_binary32_eq (tcSplitK_exactOn v100_exactOn (by decide) _) hlen hk hx hy hcfgs hrange

end Ozaki.TC
