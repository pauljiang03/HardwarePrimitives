import OzakiTC.Schemes
import OzakiTC.Native
import OzakiTC.ADP
import OzakiTC.Scaling
import Ozaki.SharpBounds

/-! # Sharper error bounds on the Tensor Core model

The bounds of `Ozaki.SharpBounds` for the Tensor Core schemes, whose roundings are IEEE's
(`round32Value` is `rne32Q`, `fp64Round` is `rne64`):

* native binary32 and binary64 GEMM within `k u Σ|xᵢyᵢ|` when no product underflows, for every
  `k` (Jeannerod and Rump), in place of `γₖ` (`native32_error_jr`, `nativeDot64_error_jr`), and
  with underflow (`native32_error_jr_underflow`);
* Ozaki-I on Tensor Core blocks with its binary32 recombination bounded by Jeannerod and Rump's
  summation and its slicing entry by entry: `(n − 1) 2^-24 Σ|tⱼ| + (s + 1) Σᵢ min(2|xᵢyᵢ|,
  2^(E+F−s(b+1)))`, for grids in binary32's range (`tcOzaki1_error_jr`), in place of
  `tcOzaki1_error`'s `((1 + 2^-24)^n − 1) n k 2^(E+F) + n (1 + 2^-24)^n 2^-150 +
  (s + 1) k 2^(E+F−s(b+1))`. -/

open TensorCore

namespace Ozaki.TC

/-- **Native binary32 GEMM, Jeannerod and Rump**: `|fl(x · y) − x · y| ≤ k 2^-24 Σ|xᵢyᵢ|` when no
product is below `2^-126` (unless it is a binary32 value), for every `k`. -/
theorem native32_error_jr {x y : List ℚ}
    (hz : ∀ z ∈ List.zipWith (· * ·) x y, (2 : ℚ) ^ (-126 : ℤ) ≤ Rat.abs z ∨ Binary32Value z)
    {v : ℚ} (h : native32 x y = some v) :
    Rat.abs (v - dot x y) ≤
      (List.zipWith (· * ·) x y).length * 2 ^ (-24 : ℤ) *
        ((List.zipWith (· * ·) x y).map Rat.abs).sum :=
  nativeDot_error_jr_rne32 hz h

/-- Native binary32 GEMM with underflow: `(k u + (k − 1) u²) Σ|xᵢyᵢ| + k (1 + (k − 1) u) 2^-150`,
`u = 2^-24`, for every `k`. -/
theorem native32_error_jr_underflow {x y : List ℚ} {v : ℚ} (h : native32 x y = some v) :
    Rat.abs (v - dot x y) ≤
      ((List.zipWith (· * ·) x y).length * 2 ^ (-24 : ℤ) +
          (((List.zipWith (· * ·) x y).length : ℚ) - 1) * 2 ^ (-24 : ℤ) * 2 ^ (-24 : ℤ)) *
          ((List.zipWith (· * ·) x y).map Rat.abs).sum +
        (List.zipWith (· * ·) x y).length *
          (1 + (((List.zipWith (· * ·) x y).length : ℚ) - 1) * 2 ^ (-24 : ℤ)) * 2 ^ (-150 : ℤ) :=
  by
  have h' : nativeDot (roundRNE 24 (-126) 127) x y = some v := h
  have := nativeDot_error_jr_rne_underflow (p := 24) (emin := -126) (emax := 127) (by decide)
    (by decide) h'
  have e1 : (2 : ℚ) ^ (-((24 : ℕ) : ℤ)) = 2 ^ (-24 : ℤ) := by
    rw [show (-((24 : ℕ) : ℤ)) = (-24 : ℤ) by omega]
  have e2 : (2 : ℚ) ^ ((-126 : ℤ) - ((24 : ℕ) : ℤ)) = 2 ^ (-150 : ℤ) := by
    rw [show ((-126 : ℤ) - ((24 : ℕ) : ℤ)) = -150 by omega]
  simp only [e1, e2] at this
  exact this

/-- **Native binary64 GEMM (ADP's fallback), Jeannerod and Rump**: `k 2^-53 Σ|xᵢyᵢ|` when no
product is below `2^-1022` (unless it is a binary64 value). -/
theorem nativeDot64_error_jr {x y : List ℚ}
    (hz : ∀ z ∈ List.zipWith (· * ·) x y, (2 : ℚ) ^ (-1022 : ℤ) ≤ Rat.abs z ∨ Binary64Value z)
    {v : ℚ} (h : nativeDot fp64Round x y = some v) :
    Rat.abs (v - dot x y) ≤
      (List.zipWith (· * ·) x y).length * 2 ^ (-53 : ℤ) *
        ((List.zipWith (· * ·) x y).map Rat.abs).sum :=
  nativeDot_error_jr_rne64 hz h

/-- The exact terms of Ozaki-I are binary32 values when `k 2^(2b) ≤ 2^24` and every scale
`2^(gₜ + hᵤ)` of a computed pair lies in `[2^-149, 2^103]`. -/
theorem exactTerms_binary32 {b s : ℕ} {x y : List ℚ} (hk : x.length * (2 ^ b * 2 ^ b) ≤ 2 ^ 24)
    (hg : ∀ t u, t + u < s →
      -149 ≤ ((split b s x).1.getD t default).grid + ((split b s y).1.getD u default).grid ∧
      ((split b s x).1.getD t default).grid + ((split b s y).1.getD u default).grid ≤ 103) :
    ∀ t ∈ exactTerms b s x y, Binary32Value t := by
  intro t ht
  obtain ⟨⟨i, j⟩, hij, rfl⟩ := List.mem_map.mp ht
  have hlt := mem_trianglePairs.mp hij
  obtain ⟨h1, h2⟩ := hg i j hlt
  exact finiteValue32_binary32 (exactTerm_finiteValue32 hk (by omega) (by omega) h1 h2)

/-- **Ozaki-I on the Tensor Core, sharper.** With the scaled slice products binary32 values (for
instance grids in range, `exactTerms_binary32`), the binary32 recombination adds at most
`(n − 1) 2^-24 Σ|tⱼ|` (Jeannerod and Rump), and the slicing at most
`(s + 1) Σᵢ min(2|xᵢyᵢ|, 2^(E+F−s(b+1)))`. -/
theorem tcOzaki1_error_jr {p : Model} {b : ℕ} (hp : IntExact p b) (hh : HoldsInts p b)
    (hK : 0 < p.nfma) (s : ℕ) {x y : List ℚ} (hlen : x.length = y.length)
    (hk : x.length * (2 ^ b * 2 ^ b) ≤ 2 ^ 24)
    (hterms : ∀ t ∈ exactTerms b s x y, Binary32Value t) {v : ℚ}
    (hv : tcOzaki1 p b s x y = some v) :
    Rat.abs (v - dot x y) ≤
      (((trianglePairs s).length - 1 : ℕ) : ℚ) * 2 ^ (-24 : ℤ) *
          ((exactTerms b s x y).map Rat.abs).sum +
        ((s + 1 : ℕ) : ℚ) * capSum (2 ^ (splitExp b x + splitExp b y - s * (b + 1))) x y :=
  ozaki1_error_jr (rnd := rne32Q) (tcMultiplier_exactOn hp hh hK) (Rat.le_of_lt (two_pow_pos _))
    (roundRNE_jrAdd (p := 24) (emin := -126) (emax := 127) (by decide) (by decide)) hlen hk hterms hv

end Ozaki.TC
