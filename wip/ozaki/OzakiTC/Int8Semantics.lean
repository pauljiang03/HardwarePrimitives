import OzakiTC.Int8

/-! # The INT8 matrix multiplier's accumulation: any order, wrapping or saturating

The INT8 matrix multiplier (`int8Dot`) multiplies bytes exactly and adds the products in `TensorCore`'s
`w`-bit two's-complement register (`machineAccumulate w`), one at a time in list order. An INT8
matrix instruction adds its products in some internal order and grouping that the hardware does not
document, and integer instructions come in two flavours: wrapping (`INT32` arithmetic modulo
`2^32`) and saturating (clamped to `[−2^31, 2^31 − 1]`). This file shows that neither choice
matters for ADP:

* **Wrapping is order-free.** The register's result is the exact dot product reduced to `w`-bit
  two's complement (`int8Dot_eq_wrap`), and adding the products in any order and any grouping, a
  binary tree of additions whose leaves are a permutation of the products, gives the same result
  (`AddTree.wrapSum_eq`, `int8Dot_any_order`). So the model's result is the result of every
  wrapping INT32 instruction, whatever its internal order.
* **Saturating agrees whenever nothing overflows.** With a clamp after every addition, in any
  order and grouping, the result is the exact sum when `Σ|xᵢyᵢ| < 2^(w−1)`
  (`AddTree.satSum_exact`, `satAccumulate_exact`); so is a clamp of the final sum alone
  (`clampInt_exact`). Under `int8Dot_bytes`'s hypotheses, which ADP's slice products meet, the
  wrapping register, every saturating order and the exact dot product coincide
  (`int8_wrap_sat_exact`).

The matrix multiplier remains a model of the arithmetic, not of a particular instruction's timing or
operand layout. -/

open TensorCore

namespace Ozaki.TC

/-! ## Wrapping -/

/-- The integer a `w`-bit two's-complement register holds for `z`: `z` reduced into
`[−2^(w−1), 2^(w−1))`. -/
def wrapInt (w : ℕ) (z : ℤ) : ℤ := (BitVec.ofInt w z).toInt

/-- **The INT8 matrix multiplier is the exact dot product, wrapped.** -/
theorem int8Dot_eq_wrap (w : ℕ) (x y : List ℤ) : int8Dot w x y = wrapInt w (dotZ x y) := by
  unfold int8Dot wrapInt
  have h : machineAccumulate w 0 (List.zipWith (· * ·) x y) =
      BitVec.ofInt w (sumZ (List.zipWith (· * ·) x y)) := by
    simpa using machineAccumulate_eq w 0 (List.zipWith (· * ·) x y)
  rw [h, sumZ_zipWith]

/-- A binary tree of additions: any order and grouping in which an instruction might add its
terms. -/
inductive AddTree where
  | leaf (z : ℤ)
  | node (l r : AddTree)
  deriving Repr

/-- The terms a tree adds. -/
def AddTree.leaves : AddTree → List ℤ
  | .leaf z => [z]
  | .node l r => l.leaves ++ r.leaves

/-- The tree's additions in a `w`-bit wrapping register. -/
def AddTree.wrapSum (w : ℕ) : AddTree → BitVec w
  | .leaf z => BitVec.ofInt w z
  | .node l r => l.wrapSum w + r.wrapSum w

theorem sumZ_append : ∀ xs ys : List ℤ, sumZ (xs ++ ys) = sumZ xs + sumZ ys
  | [], ys => by simp [sumZ]
  | x :: xs, ys => by simp only [List.cons_append, sumZ, sumZ_append xs ys]; omega

/-- **Wrapping additions in any grouping** give the exact sum, wrapped. -/
theorem AddTree.wrapSum_eq (w : ℕ) : ∀ t : AddTree, t.wrapSum w = BitVec.ofInt w (sumZ t.leaves)
  | .leaf z => by simp [wrapSum, leaves, sumZ]
  | .node l r => by
    rw [wrapSum, leaves, AddTree.wrapSum_eq w l, AddTree.wrapSum_eq w r, sumZ_append,
      BitVec.ofInt_add]

/-- **The INT8 matrix multiplier's result does not depend on the order of accumulation.** For any
binary tree of wrapping `w`-bit additions whose terms are the products `xᵢyᵢ` in any order, the
result is `int8Dot w x y`. -/
theorem int8Dot_any_order (w : ℕ) {x y : List ℤ} (t : AddTree)
    (h : t.leaves.Perm (List.zipWith (· * ·) x y)) : (t.wrapSum w).toInt = int8Dot w x y := by
  rw [AddTree.wrapSum_eq, sumZ_perm h, sumZ_zipWith, int8Dot_eq_wrap]
  rfl

/-! ## Saturating -/

/-- Clamp to the `w`-bit signed range `[−2^(w−1), 2^(w−1) − 1]`. -/
def clampInt (w : ℕ) (z : ℤ) : ℤ := max (-(2 ^ (w - 1) : ℤ)) (min z (2 ^ (w - 1) - 1))

/-- A value in range is not clamped. -/
theorem clampInt_exact {w : ℕ} {z : ℤ} (h : z.natAbs < 2 ^ (w - 1)) : clampInt w z = z := by
  unfold clampInt
  have hp : ((2 ^ (w - 1) : ℕ) : ℤ) = (2 : ℤ) ^ (w - 1) := by simp
  omega

/-- Saturating accumulation, one term at a time. -/
def satAccumulate (w : ℕ) (acc : ℤ) : List ℤ → ℤ
  | [] => acc
  | z :: zs => satAccumulate w (clampInt w (acc + z)) zs

/-- **Saturating accumulation is exact when nothing can overflow**: `|acc| + Σ|zᵢ| < 2^(w−1)`. -/
theorem satAccumulate_exact (w : ℕ) : ∀ (acc : ℤ) (zs : List ℤ),
    acc.natAbs + magnitudeSum zs < 2 ^ (w - 1) → satAccumulate w acc zs = acc + sumZ zs
  | acc, [], _ => by simp [satAccumulate, sumZ]
  | acc, z :: zs, h => by
    simp only [magnitudeSum] at h
    have hz : (acc + z).natAbs < 2 ^ (w - 1) := by
      have := Int.natAbs_add_le acc z; omega
    rw [satAccumulate, clampInt_exact hz,
      satAccumulate_exact w (acc + z) zs (by have := Int.natAbs_add_le acc z; omega), sumZ]
    omega

/-- The tree's additions with a clamp after every addition (and on every term). -/
def AddTree.satSum (w : ℕ) : AddTree → ℤ
  | .leaf z => clampInt w z
  | .node l r => clampInt w (l.satSum w + r.satSum w)

/-- **Saturating additions in any grouping are exact when nothing can overflow.** -/
theorem AddTree.satSum_exact (w : ℕ) :
    ∀ t : AddTree, magnitudeSum t.leaves < 2 ^ (w - 1) → t.satSum w = sumZ t.leaves
  | .leaf z, h => by
    simp only [leaves, magnitudeSum] at h
    simp only [satSum, leaves, sumZ]
    rw [clampInt_exact (by omega)]; omega
  | .node l r, h => by
    simp only [leaves, magnitudeSum_append] at h
    have hl := AddTree.satSum_exact w l (by omega)
    have hr := AddTree.satSum_exact w r (by omega)
    simp only [satSum, leaves, sumZ_append]
    rw [hl, hr]
    apply clampInt_exact
    have := sumZ_natAbs_le (l.leaves ++ r.leaves)
    rw [sumZ_append, magnitudeSum_append] at this
    omega

/-- **Wrapping and saturating agree on the INT8 matrix multiplier's operands**, in any order and
grouping, and equal the exact dot product: under `int8Dot_bytes`'s hypotheses (signed bytes against
signed or unsigned bytes, `k · 128 · 255 < 2^31`). -/
theorem int8_wrap_sat_exact {x y : List ℤ} (hx : ∀ a ∈ x, a.natAbs ≤ 128)
    (hy : ∀ b ∈ y, b.natAbs ≤ 255) (hk : x.length * (128 * 255) < 2 ^ 31) (t : AddTree)
    (h : t.leaves.Perm (List.zipWith (· * ·) x y)) :
    (t.wrapSum 32).toInt = dotZ x y ∧ t.satSum 32 = dotZ x y ∧
      satAccumulate 32 0 (List.zipWith (· * ·) x y) = dotZ x y := by
  have hm : magnitudeSum (List.zipWith (· * ·) x y) < 2 ^ (32 - 1) := by
    rw [magnitudeSum_zipWith]; exact Nat.lt_of_le_of_lt (dotAbs_le x y 128 255 hx hy) hk
  have hperm := magnitudeSum_perm h
  refine ⟨?_, ?_, ?_⟩
  · rw [int8Dot_any_order 32 t h]; exact int8Dot_bytes hx hy hk
  · rw [AddTree.satSum_exact 32 t (by rw [hperm]; exact hm), sumZ_perm h, sumZ_zipWith]
  · rw [satAccumulate_exact 32 0 _ (by simpa using hm), sumZ_zipWith]; simp

end Ozaki.TC
