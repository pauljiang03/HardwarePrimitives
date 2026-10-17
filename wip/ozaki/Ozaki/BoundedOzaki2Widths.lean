import Ozaki.BoundedOzaki2Int

/-! # The widths of the Ozaki-II and ADP integer pipelines, register by register

Every integer of `ozaki2CRZ` (and of `Ozaki.TC.adpCRZ`) has a width set by the format's precision
`p`, the scaling precision `P` (ADP: the fixed-point width `W`), the slice width `b`, the slice count
`s`, the moduli and the length `k`, never by the inputs' exponents. Register by register:

| Register | Bound | Lemma |
| --- | --- | --- |
| input significand `m` | `|m| < 2^p` | hypothesis (`Ozaki.formatValues_entries`) |
| scaled integer `aᵢ` (Ozaki-II) | `≤ 2^P` | `scaleTruncZ_natAbs_le` |
| fixed-point integer `Nᵢ` (ADP) | `≤ 2^W` | `Ozaki.TC.toFixedZ_natAbs_le` |
| left shift amount (nonzero `m`) | `≤ P` (ADP: `≤ W`) | `truncShift_left_le`, `floorShift_left_le` |
| right shift divisor `2^k` | `≤ |m|` | `truncShiftZ_divisor_le` |
| remainder test `|m| mod 2^k` | `< 2^k ≤ |m|` | `dropsBits_divisor_le` |
| symmetric residue | `≤ m/2` | `natAbs_symMod_le` |
| residue product on the matrix multiplier | `≤ k ⌊m/2⌋²`, within the exactness bound | `natAbs_residueProduct_le` |
| reduced residue `z mod m` | `< m` | `residue_natAbs_lt` |
| CRT sum `Σ wⱼ rⱼ` | `≤ (Σ |wⱼ|) R` for residues `≤ R` | `crtSum_natAbs_le` |
| reconstructed `N` | `2|N| ≤ M` | `ozaki2EnclosureB_width` |
| sums `Σ|aᵢ|`, `Σ|cⱼ| + k`, bound `K` | `0 ≤ K ≤ k (2^(P+1) + 1)` | `boundK_le`, `ozaki2EnclosureB_width` |
| test ends `N ± K` | `≤ M/2 + k (2^(P+1) + 1)` | `ozaki2EnclosureB_width` |
| byte slices (ADP) | `≤ 128` | `Ozaki.TC.sliceVec_s8` |
| split-K INT8 product, chunk register | `≤ k 2^14`; chunks `< 2^31` | `Ozaki.TC.int8DotK_natAbs_le` |
| recombination term `256^(t+u) dᵗᵘ` | `≤ 256^(2(s−1)) k 2^14` | `Ozaki.TC.int8RecombineK_term_le` |
| recombined `R`, bound `K`, ends `R ± K` (ADP) | `≤ k 2^(2W)`, `≤ k (2^(W+1) + 1)` | `Ozaki.TC.adpEnclosureB_width` |
| exact fallback: coefficients, significands | `≤ 2^b`, `< 2^p` | `splitInt_width` |
| exact fallback: slice products | within the exactness bound of the matrix multiplier | `ozaki1ExactFallbackZ_terms` |
| exact fallback: range parts, sums, queries | the bounds of `roundSum` | `topDownSum_parts_lt`, `fixedSum_natAbs_le`, `query_natAbs_lt` |

What depends on the exponents is exponent arithmetic only: the scaling and fixed-point exponents,
the shift amounts `e + s`, the slice grids, and the number of ranges that the top-down summation of
the exact fallback visits. There is no single theorem bounding every intermediate value; the widths
are proved register by register. -/

local notation "ℕ" => Nat
local notation "ℤ" => Int
local notation "ℚ" => Rat

namespace Ozaki

/-- **A floor left shift's amount is at most `W`** for a nonzero significand whose result is at
most `2^W`. -/
theorem floorShift_left_le {W : ℕ} {m j : ℤ} (hm : m ≠ 0) (hj : 0 ≤ j)
    (h : (floorShiftZ m j).natAbs ≤ 2 ^ W) : j.toNat ≤ W := by
  unfold floorShiftZ at h
  rw [if_neg hm, if_pos hj, Int.natAbs_mul, Int.natAbs_pow] at h
  have h1 : 1 ≤ m.natAbs := by omega
  have h2 : 2 ^ j.toNat ≤ 2 ^ W := by
    have := Nat.mul_le_mul_right ((2 : ℤ).natAbs ^ j.toNat) h1
    simp only [Nat.one_mul] at this
    exact Nat.le_trans this h
  exact (Nat.pow_le_pow_iff_right (by decide)).mp h2

/-- **The integer terms of the exact fallback are within the exactness bound of the matrix
multiplier**, with integer slicing. -/
theorem ozaki1ExactFallbackZ_terms {mult : MatrixMultiplier} {b bound : ℕ} (hmult : mult.ExactOn b bound)
    {s : ℕ} {xs ys : List (ℤ × ℤ)} (hlen : xs.length = ys.length)
    (hbound : xs.length * (2 ^ b * 2 ^ b) ≤ bound) :
    (slicePairs (splitInt b s xs).1 (splitInt b s ys).1).mapM
        (fun pr => sliceProductInt mult pr.1 pr.2) =
      some ((slicePairs (splitInt b s xs).1 (splitInt b s ys).1).map
        fun pr => exactSliceInt pr.1 pr.2) ∧
    ∀ pr ∈ slicePairs (splitInt b s xs).1 (splitInt b s ys).1,
      (exactSliceInt pr.1 pr.2).1.natAbs ≤ bound := by
  rw [(splitInt_eq b s xs).1, (splitInt_eq b s ys).1]
  exact ozaki1ExactFallbackB_terms hmult (by rw [entryVals_length, entryVals_length, hlen])
    (by rw [entryVals_length]; exact hbound)

end Ozaki
