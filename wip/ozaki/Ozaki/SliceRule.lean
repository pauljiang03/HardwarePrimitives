import Ozaki.SplitK
import Ozaki.Split

/-! # The slice rule and the block count, for any matrix multiplier

Two hardware-independent pieces of the per-variant choice of slice width, chunk length and passes
(`OzakiTC.SplitChoice`, `OzakiMC.SplitChoice`):

* **the slice rule** `slicesFor b t`: the least `s` with `(s + 1) 2^(t+2) ≤ 2^(s(b+1))`, which
  makes the slicing term of Ozaki-I's error bound at most `2^-t · k · max|x| · max|y|`
  (`slicing_term_le_maxAbs`); and `exactSlices b`, the slice count at which every binary64 input
  leaves nothing over (`exactSlices_spec`);
* **the block count of split-K** `chunkBlocks n m l`: the chunks of `chunksOf m l`, each taking
  `⌈length / n⌉` blocks of `n` products; it depends only on the length (`chunkBlocks_length`). -/

local notation "ℕ" => Nat
local notation "ℤ" => Int
local notation "ℚ" => Rat

namespace Ozaki

/-! ## The slice rule -/

/-- The least `s ≥ 1` (up to `199`) with `(s + 1) 2^(t+2) ≤ 2^(s(b+1))`; `0` if there is none. -/
def slicesFor (b t : ℕ) : ℕ :=
  ((List.range' 1 199).find? fun s => decide ((s + 1) * 2 ^ (t + 2) ≤ 2 ^ (s * (b + 1)))).getD 0

/-- **The slice rule bounds the slicing term.** When `(s + 1) 2^(t+2) ≤ 2^(s(b+1))`, the slicing
term `(s + 1) k 2^(E_x+E_y−s(b+1))` of Ozaki-I's error bound is at most `2^-t · k · max|x| · max|y|`. -/
theorem slicing_term_le_maxAbs {b s t : ℕ} (h : (s + 1) * 2 ^ (t + 2) ≤ 2 ^ (s * (b + 1)))
    {x y : List ℚ} (hx : maxAbs x ≠ 0) (hy : maxAbs y ≠ 0) :
    ((s + 1 : ℕ) : ℚ) * x.length * 2 ^ (splitExp b x + splitExp b y - s * (b + 1)) ≤
      x.length * maxAbs x * maxAbs y * 2 ^ (-(t : ℤ)) := by
  obtain ⟨_, hx1, _⟩ := splitExp_spec b hx
  obtain ⟨_, hy1, _⟩ := splitExp_spec b hy
  generalize splitExp b x = Ex at hx1
  generalize splitExp b y = Ey at hy1
  have hk : (0 : ℚ) ≤ x.length := Rat.natCast_nonneg
  -- `(s + 1) 2^(−s(b+1)) ≤ 2^(−t−2)`
  have hq : ((s + 1 : ℕ) : ℚ) * 2 ^ (-((s * (b + 1) : ℕ) : ℤ)) ≤ 2 ^ (-(t : ℤ) - 2) := by
    have hc : (((s + 1) * 2 ^ (t + 2) : ℕ) : ℚ) ≤ ((2 ^ (s * (b + 1)) : ℕ) : ℚ) :=
      Rat.natCast_le_natCast.mpr h
    rw [Rat.natCast_mul, ← two_pow_natCast, ← two_pow_natCast] at hc
    have hp := two_pow_pos (-((s * (b + 1) : ℕ) : ℤ) + (-(t : ℤ) - 2))
    have := Rat.mul_le_mul_of_nonneg_right hc (Rat.le_of_lt hp)
    rw [Rat.mul_assoc, ← two_pow_add, ← two_pow_add] at this
    have e1 : (((t + 2 : ℕ) : ℤ) + (-((s * (b + 1) : ℕ) : ℤ) + (-(t : ℤ) - 2))) =
        -((s * (b + 1) : ℕ) : ℤ) := by push_cast; omega
    have e2 : (((s * (b + 1) : ℕ) : ℤ) + (-((s * (b + 1) : ℕ) : ℤ) + (-(t : ℤ) - 2))) =
        -(t : ℤ) - 2 := by omega
    rw [e1, e2] at this; exact this
  have hsplit : (2 : ℚ) ^ (Ex + Ey - ((s * (b + 1) : ℕ) : ℤ)) =
      2 ^ (Ex - 1) * 2 ^ (Ey - 1) * 4 * 2 ^ (-((s * (b + 1) : ℕ) : ℤ)) := by
    rw [show (4 : ℚ) = 2 ^ (2 : ℤ) by rfl, ← two_pow_add, ← two_pow_add, ← two_pow_add]
    congr 1; omega
  have hcast : ((s * (b + 1) : ℕ) : ℤ) = (s : ℤ) * ((b : ℤ) + 1) := by push_cast; rfl
  rw [← hcast, hsplit]
  have hmx : 0 ≤ maxAbs x := Rat.le_trans (Rat.le_of_lt (two_pow_pos _)) (Rat.le_of_lt hx1)
  have hxy : (2 : ℚ) ^ (Ex - 1) * 2 ^ (Ey - 1) ≤ maxAbs x * maxAbs y :=
    Rat.le_trans (Rat.mul_le_mul_of_nonneg_right (Rat.le_of_lt hx1) (Rat.le_of_lt (two_pow_pos _)))
      (Rat.mul_le_mul_of_nonneg_left (Rat.le_of_lt hy1) hmx)
  have ht : (2 : ℚ) ^ (-(t : ℤ)) = 4 * 2 ^ (-(t : ℤ) - 2) := by
    rw [show (4 : ℚ) = 2 ^ (2 : ℤ) by rfl, ← two_pow_add]; congr 1; omega
  rw [ht]
  have hA : (0 : ℚ) ≤ 2 ^ (Ex - 1) * 2 ^ (Ey - 1) :=
    Rat.mul_nonneg (Rat.le_of_lt (two_pow_pos _)) (Rat.le_of_lt (two_pow_pos _))
  have h1 : ((s + 1 : ℕ) : ℚ) * x.length * (2 ^ (Ex - 1) * 2 ^ (Ey - 1) * 4 *
      2 ^ (-((s * (b + 1) : ℕ) : ℤ))) =
      x.length * (2 ^ (Ex - 1) * 2 ^ (Ey - 1)) * 4 *
        (((s + 1 : ℕ) : ℚ) * 2 ^ (-((s * (b + 1) : ℕ) : ℤ))) := by grind
  rw [h1]
  have hX : (0 : ℚ) ≤ x.length * (2 ^ (Ex - 1) * 2 ^ (Ey - 1)) * 4 :=
    Rat.mul_nonneg (Rat.mul_nonneg hk hA) (by decide)
  have h2 : (x.length : ℚ) * (2 ^ (Ex - 1) * 2 ^ (Ey - 1)) * 4 ≤
      x.length * (maxAbs x * maxAbs y) * 4 :=
    Rat.mul_le_mul_of_nonneg_right (Rat.mul_le_mul_of_nonneg_left hxy hk) (by decide)
  calc (x.length : ℚ) * (2 ^ (Ex - 1) * 2 ^ (Ey - 1)) * 4 *
        (((s + 1 : ℕ) : ℚ) * 2 ^ (-((s * (b + 1) : ℕ) : ℤ)))
      ≤ x.length * (2 ^ (Ex - 1) * 2 ^ (Ey - 1)) * 4 * 2 ^ (-(t : ℤ) - 2) :=
        Rat.mul_le_mul_of_nonneg_left hq hX
    _ ≤ x.length * (maxAbs x * maxAbs y) * 4 * 2 ^ (-(t : ℤ) - 2) :=
        Rat.mul_le_mul_of_nonneg_right h2 (Rat.le_of_lt (two_pow_pos _))
    _ = x.length * maxAbs x * maxAbs y * (4 * 2 ^ (-(t : ℤ) - 2)) := by grind

/-- The slice count at which every binary64 input leaves nothing over (`smax (b+1) > 2098`). -/
def exactSlices (b : ℕ) : ℕ := 2098 / (b + 1) + 1

theorem exactSlices_spec (b : ℕ) : 2098 < exactSlices b * (b + 1) := by
  unfold exactSlices
  have := Nat.lt_div_mul_add (a := 2098) (b := b + 1) (by omega)
  rw [Nat.add_mul, Nat.one_mul]; omega

/-- Blocks of `n` products that split-K with chunks of `m` takes on `l`: `⌈length / n⌉` for each chunk
of `chunksOf m l`. -/
def chunkBlocks (n m : ℕ) (l : List α) : ℕ :=
  ((chunksOf m l).map fun c => (c.length + n - 1) / n).sum

theorem chunksAux_lengths (m : ℕ) : ∀ (n : ℕ) (l : List α) (l' : List β), l.length = l'.length →
    (chunksAux m n l).map List.length = (chunksAux m n l').map List.length
  | 0, _, _, _ => rfl
  | _ + 1, [], [], _ => rfl
  | _ + 1, [], _ :: _, h => by simp at h
  | _ + 1, _ :: _, [], h => by simp at h
  | n + 1, a :: l, a' :: l', h => by
    simp only [chunksAux, List.map_cons, List.length_take, h]
    congr 1
    exact chunksAux_lengths m n _ _ (by simp only [List.length_drop, h])

/-- The block count depends only on the length. -/
theorem chunkBlocks_length (n m : ℕ) (l : List α) :
    chunkBlocks n m l = chunkBlocks n m (List.replicate l.length ()) := by
  unfold chunkBlocks chunksOf
  have h := chunksAux_lengths m l.length l (List.replicate l.length ()) (by simp)
  rw [List.length_replicate]
  have e1 : (chunksAux m l.length l).map (fun c => (c.length + n - 1) / n) =
      ((chunksAux m l.length l).map List.length).map (fun L => (L + n - 1) / n) := by simp [Function.comp_def]
  have e2 : (chunksAux m l.length (List.replicate l.length ())).map (fun c => (c.length + n - 1) / n) =
      ((chunksAux m l.length (List.replicate l.length ())).map List.length).map (fun L => (L + n - 1) / n) := by
    simp [Function.comp_def]
  rw [e1, e2, h]

end Ozaki
