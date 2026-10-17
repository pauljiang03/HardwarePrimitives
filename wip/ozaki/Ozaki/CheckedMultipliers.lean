import Ozaki.BoundedChecked2
import Ozaki.SplitK

/-! # Split-K with its own arithmetic guarded

The checked pipelines of `Ozaki.BoundedChecked`, `Ozaki.BoundedChecked2` and the ADP files guard
every integer they compute, and read the outputs of the matrix multiplier back through a guard; the
arithmetic inside the matrix multiplier was its own. Split-K (`chunked`) is software: it cuts both
vectors into chunks, runs the matrix multiplier on each chunk pair, and adds the chunk results.
`chunkedC` is split-K with that software arithmetic guarded too: every chunk result read back as an
integer and guarded, and every partial sum of the chunk results guarded.

`chunkedC_exactOn`: when the matrix multiplier is exact on chunks within its exactness bound, and
the exactness bound and the total product are below `2^R`, the guarded split-K matrix multiplier is
exact, so every checked pipeline runs on it with all its theorems: the block FMA arithmetic of the
matrix multiplier itself (alignment, the hardware accumulator) is then the only arithmetic not
guarded, and it is that of the hardware model. -/

local notation "ℕ" => Nat
local notation "ℤ" => Int
local notation "ℚ" => Rat

namespace Ozaki

namespace Checked

variable (B : Widths)

/-- **Split-K with its arithmetic guarded**: each chunk result read back as an integer and
guarded, and every partial sum of the chunk results guarded. -/
def chunkedC (m : ℕ) (mult : MatrixMultiplier) : MatrixMultiplier := fun x y =>
  match ((chunksOf m x).zip (chunksOf m y)).mapM (fun p => mult p.1 p.2) with
  | none => none
  | some vs =>
    match vs.mapM (fun v => if v.den = 1 then B.gv v.num else none) with
    | none => none
    | some zs => (sumC B zs).map fun s : ℤ => ((s : ℤ) : ℚ)

end Checked

open Checked

theorem readInt_ok {B : Widths} {z : ℤ} (h : z.natAbs < 2 ^ B.R) :
    (fun v : ℚ => if v.den = 1 then B.gv v.num else none) (z : ℚ) = some z := by
  simp only [Rat.den_intCast, Rat.num_intCast, ↓reduceIte]
  exact Widths.gv_ok h

/-- **The guarded split-K matrix multiplier is exact**: if the matrix multiplier is exact on `b`-bit
chunks whose products total at most `bound`, `m · 2^(2b) ≤ bound`, and `bound` and `D` are below
`2^R`, then on `b`-bit vectors whose products total at most `D` no guard fails and the result is
exact. -/
theorem chunkedC_exactOn {B : Widths} {mult : MatrixMultiplier} {b bound m : ℕ}
    (hmult : mult.ExactOn b bound) (hm : 0 < m) (hmb : m * (2 ^ b * 2 ^ b) ≤ bound)
    (hbud : bound < 2 ^ B.R) {D : ℕ} (hD : D < 2 ^ B.R) : (chunkedC B m mult).ExactOn b D := by
  intro x y hlen hx hy hd
  unfold chunkedC chunksOf
  rw [hlen]
  obtain ⟨hpairs, hsum⟩ := chunksAux_pairs hm y.length x y hlen (by omega)
  have habs := chunksAux_dotAbs hm y.length x y hlen (by omega)
  have hchunk : ∀ p ∈ (chunksAux m y.length x).zip (chunksAux m y.length y),
      dotAbs p.1 p.2 ≤ bound := by
    intro p hp
    obtain ⟨h1, h2, h3, h4⟩ := hpairs p hp
    refine Nat.le_trans (dotAbs_le _ _ _ _ (fun a ha => hx a (h3 a ha))
      (fun a ha => hy a (h4 a ha))) ?_
    exact Nat.le_trans (Nat.mul_le_mul_right _ h2) hmb
  rw [mapM_eq_some_map (g := fun p : List ℤ × List ℤ => ((dotZ p.1 p.2 : ℤ) : ℚ)) fun p hp => by
    obtain ⟨h1, _, h3, h4⟩ := hpairs p hp
    exact hmult _ _ h1 (fun a ha => hx a (h3 a ha)) (fun a ha => hy a (h4 a ha)) (hchunk p hp)]
  simp only
  rw [List.mapM_map, mapM_eq_some_map (g := fun p : List ℤ × List ℤ => dotZ p.1 p.2) fun p hp => by
    simp only [Function.comp_def]
    exact readInt_ok (Nat.lt_of_le_of_lt (Nat.le_trans (natAbs_dotZ_le _ _) (hchunk p hp)) hbud)]
  simp only
  have hle := sum_map_le (l := (chunksAux m y.length x).zip (chunksAux m y.length y))
    (f := fun p => (dotZ p.1 p.2).natAbs) (g := fun p => dotAbs p.1 p.2)
    fun p _ => natAbs_dotZ_le _ _
  rw [habs] at hle
  rw [sumC_eq (by rw [List.map_map]; exact Nat.lt_of_le_of_lt hle (Nat.lt_of_le_of_lt hd hD))]
  simp only [Option.map_some, hsum]
  rfl

end Ozaki
