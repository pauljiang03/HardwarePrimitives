import OzakiTC.ADPFix
import Ozaki.CheckedMultipliers

/-! # The INT8 engine with its arithmetic guarded

ADP's INT8 engine (`int8Dot 32`, TC-EFT's fixed-width register) multiplies bytes and accumulates
in a 32-bit register; split-K (`int8DotK`, `int8SplitK`) adds the chunk results. Here every integer
of that arithmetic is guarded:

* `regSumC`: the register's partial sums, each checked to stay in the register's own signed range
  `(−2^(w−1), 2^(w−1))`, so the register provably never wraps; `int8DotC` adds the byte products,
  each guarded against `2^R`, in it. It returns the exact dot product, the value of `int8Dot`
  (`int8DotC_eq`).
* `int8DotKC`: split-K over `int8DotC` with the chunk sums guarded (`int8DotKC_eq`), used by the
  checked ADP recombination; `int8SplitKC`: the guarded split-K engine of `Ozaki.CheckedMultipliers`
  over `int8DotC`, used by the checked ADP exact path. Both are exact where the unguarded ones are
  (`int8SplitKC_exactOn`).

`ozaki1ExactFallbackI_congr`: the integer exact path depends only on the engine's values on exact
slices, so it is the same on any two engines exact on them. -/

open TensorCore

namespace Ozaki.TC

open Ozaki.Checked

/-- **A `w`-bit register that refuses to wrap**: each partial sum is checked to stay in the signed
`w`-bit range. -/
def regSumC (w : ℕ) : ℤ → List ℤ → Option ℤ
  | acc, [] => some acc
  | acc, z :: zs => if (acc + z).natAbs < 2 ^ (w - 1) then regSumC w (acc + z) zs else none

theorem regSumC_eq {w : ℕ} : ∀ {acc : ℤ} {zs : List ℤ},
    acc.natAbs + (zs.map Int.natAbs).sum < 2 ^ (w - 1) → regSumC w acc zs = some (acc + zs.sum)
  | acc, [], _ => by simp [regSumC]
  | acc, z :: zs, h => by
    simp only [List.map_cons, List.sum_cons] at h
    unfold regSumC
    have h1 := Int.natAbs_add_le acc z
    rw [if_pos (Nat.lt_of_le_of_lt h1 (by omega)),
      regSumC_eq (Nat.lt_of_le_of_lt (Nat.add_le_add_right h1 _) (by omega))]
    simp only [List.sum_cons, Int.add_assoc]

/-- **The INT8 engine, every integer guarded**: each byte product guarded against `2^R`, every
partial sum of the 32-bit register checked against the register's range. -/
def int8DotC (B : Widths) (x y : List ℤ) : Option ℤ := do
  let ps ← (List.zipWith (· * ·) x y).mapM B.gv
  regSumC 32 0 ps

theorem dotAbs_eq_map_sum (x y : List ℤ) :
    ((List.zipWith (· * ·) x y).map Int.natAbs).sum = dotAbs x y := by
  unfold dotAbs; rw [List.map_zipWith]

theorem dotZ_eq_zipWith_sum (x y : List ℤ) : (List.zipWith (· * ·) x y).sum = dotZ x y := rfl

/-- **The guarded INT8 engine is exact and never wraps** while the products total less than
`2^31`; it returns the 32-bit register's value. -/
theorem int8DotC_eq {B : Widths} {x y : List ℤ} (hR : 31 ≤ B.R) (h : dotAbs x y < 2 ^ 31) :
    int8DotC B x y = some (int8Dot 32 x y) := by
  rw [int8Dot_exact (by decide) h]
  unfold int8DotC
  rw [mapM_gv_eq (fun z hz => by
    have := natSum_le_of_mem (List.mem_map_of_mem (f := Int.natAbs) hz)
    rw [dotAbs_eq_map_sum] at this
    exact Nat.lt_of_le_of_lt this (Nat.lt_of_lt_of_le h (Nat.pow_le_pow_right (by decide) hR)))]
  simp only [Option.bind_eq_bind, Option.bind_some]
  rw [regSumC_eq (by simp only [Int.natAbs_zero, Nat.zero_add, dotAbs_eq_map_sum]; exact h)]
  simp [dotZ_eq_zipWith_sum]

/-- `int8DotK`, split-K over the guarded engine with the chunk sums guarded. -/
def int8DotKC (B : Widths) (x y : List ℤ) : Option ℤ := do
  let ds ← ((chunksOf (2 ^ 16) x).zip (chunksOf (2 ^ 16) y)).mapM fun p => int8DotC B p.1 p.2
  sumC B ds

/-- **The guarded INT8 split-K never fails a guard** on bytes whose products total less than
`2^R`. -/
theorem int8DotKC_eq {B : Widths} {x y : List ℤ} (hR : 31 ≤ B.R) (hlen : x.length = y.length)
    (hx : ∀ a ∈ x, a.natAbs ≤ 128) (hy : ∀ b ∈ y, b.natAbs ≤ 128) (hD : dotAbs x y < 2 ^ B.R) :
    int8DotKC B x y = some (int8DotK x y) := by
  unfold int8DotKC int8DotK chunksOf
  rw [hlen]
  obtain ⟨hpairs, hsum⟩ := chunksAux_pairs (m := 2 ^ 16) (by decide) y.length x y hlen (by omega)
  have habs := chunksAux_dotAbs (m := 2 ^ 16) (by decide) y.length x y hlen (by omega)
  have hchunk : ∀ p ∈ (chunksAux (2 ^ 16) y.length x).zip (chunksAux (2 ^ 16) y.length y),
      dotAbs p.1 p.2 < 2 ^ 31 := by
    intro p hp
    obtain ⟨_, h2, h3, h4⟩ := hpairs p hp
    refine Nat.lt_of_le_of_lt (dotAbs_le _ _ 128 128 (fun a ha => hx a (h3 a ha))
      (fun b hb => hy b (h4 b hb))) ?_
    have : p.1.length * (128 * 128) ≤ 2 ^ 16 * (128 * 128) := Nat.mul_le_mul_right _ h2
    omega
  rw [mapM_eq_some_map (g := fun p : List ℤ × List ℤ => int8Dot 32 p.1 p.2) fun p hp =>
    int8DotC_eq hR (hchunk p hp)]
  simp only [Option.bind_eq_bind, Option.bind_some]
  apply sumC_eq
  have hle := sum_map_le (l := (chunksAux (2 ^ 16) y.length x).zip (chunksAux (2 ^ 16) y.length y))
    (f := fun p => (int8Dot 32 p.1 p.2).natAbs) (g := fun p => dotAbs p.1 p.2) fun p hp => by
      rw [int8Dot_exact (by decide) (hchunk p hp)]; exact natAbs_dotZ_le _ _
  rw [habs] at hle
  rw [List.map_map]
  exact Nat.lt_of_le_of_lt hle hD

/-- The INT8 engine with its arithmetic guarded. -/
def int8MultiplierC (B : Widths) : MatrixMultiplier := fun x y => (int8DotC B x y).map fun z : ℤ => ((z : ℤ) : ℚ)

theorem int8MultiplierC_exactOn {B : Widths} (hR : 31 ≤ B.R) : (int8MultiplierC B).ExactOn 6 (2 ^ 31 - 1) := by
  intro x y _ _ _ hb
  unfold int8MultiplierC
  rw [int8DotC_eq hR (Nat.lt_of_le_of_lt hb (by decide)),
    int8Dot_exact (by decide) (Nat.lt_of_le_of_lt hb (by decide))]
  rfl

/-- **Split-K on the INT8 engine, every integer guarded.** -/
def int8SplitKC (B : Widths) : MatrixMultiplier := chunkedC B (2 ^ 18) (int8MultiplierC B)

theorem int8SplitKC_exactOn {B : Widths} (hR : 31 ≤ B.R) {D : ℕ} (hD : D < 2 ^ B.R) :
    (int8SplitKC B).ExactOn 6 D :=
  chunkedC_exactOn (int8MultiplierC_exactOn hR) (by decide) (by decide)
    (Nat.lt_of_lt_of_le (by decide) (Nat.pow_le_pow_right (by decide) hR)) hD

/-- **The integer exact path is the same on any two engines exact on its slices.** -/
theorem ozaki1ExactFallbackI_congr {e1 e2 : MatrixMultiplier} {b bound : ℕ} (h1 : e1.ExactOn b bound)
    (h2 : e2.ExactOn b bound) (p : ℕ) (emin emax : ℤ) (smax : ℕ) {xs ys : List (ℤ × ℤ)}
    (hlen : xs.length = ys.length) (hbound : xs.length * (2 ^ b * 2 ^ b) ≤ bound) :
    ozaki1ExactFallbackI e1 p emin emax b smax xs ys = ozaki1ExactFallbackI e2 p emin emax b smax xs ys := by
  have hl : (entryVals xs).length = (entryVals ys).length := by
    rw [length_entryVals, length_entryVals, hlen]
  have hb' : (entryVals xs).length * (2 ^ b * 2 ^ b) ≤ bound := by
    rw [length_entryVals]; exact hbound
  unfold ozaki1ExactFallbackI
  split
  · rename_i s _
    rw [(splitInt_eq b s xs).1, (splitInt_eq b s ys).1,
      mapM_eq_some_map (g := fun pr => exactSliceInt pr.1 pr.2) fun pr hpr =>
        sliceProductInt_exact h1 hl hb' (mem_slicePairs hpr).1 (mem_slicePairs hpr).2,
      mapM_eq_some_map (g := fun pr => exactSliceInt pr.1 pr.2) fun pr hpr =>
        sliceProductInt_exact h2 hl hb' (mem_slicePairs hpr).1 (mem_slicePairs hpr).2]
  · rfl

end Ozaki.TC
