import OzakiMC.Schemes
import OzakiMC.Native
import OzakiMC.IEEE
import Ozaki.SharpBounds

/-! # Sharper error bounds on the matrix-core model

MatrixCore's binary32 round to nearest is IEEE's (`round32Value_eq_rne32Q`), so the bounds of
`Ozaki.SharpBounds` apply: native binary32 GEMM within `k 2^-24 Σ|xᵢyᵢ|` when no product
underflows, for every `k` (Jeannerod and Rump, `native32_error_jr`), and Ozaki-I with Jeannerod
and Rump's summation bound for its recombination and the entrywise slicing bound
(`mcOzaki1_error_jr`). -/

open MatrixCore

namespace Ozaki.MC

theorem round32Value_eq_rne32Q_fun : round32Value = rne32Q := funext round32Value_eq_rne32Q

/-- **Native binary32 GEMM, Jeannerod and Rump**, on the matrix-core model's rounding. -/
theorem native32_error_jr {x y : List ℚ}
    (hz : ∀ z ∈ List.zipWith (· * ·) x y, (2 : ℚ) ^ (-126 : ℤ) ≤ Rat.abs z ∨ Binary32Value z)
    {v : ℚ} (h : native32 x y = some v) :
    Rat.abs (v - dot x y) ≤
      (List.zipWith (· * ·) x y).length * 2 ^ (-24 : ℤ) *
        ((List.zipWith (· * ·) x y).map Rat.abs).sum := by
  unfold native32 at h
  rw [round32Value_eq_rne32Q_fun] at h
  exact nativeDot_error_jr_rne32 hz h

/-- **Ozaki-I on the matrix core, sharper**: `(n − 1) 2^-24 Σ|tⱼ| + (s + 1) Σᵢ min(2|xᵢyᵢ|,
2^(E+F−s(b+1)))` when the scaled slice products are binary32 values. -/
theorem mcOzaki1_error_jr {P : Model} {b : ℕ} (hP : ExactMultiplier P b) (s : ℕ) {x y : List ℚ}
    (hlen : x.length = y.length) (hk : x.length * (2 ^ b * 2 ^ b) ≤ 2 ^ 24)
    (hterms : ∀ t ∈ exactTerms b s x y, Binary32Value t) {v : ℚ}
    (hv : mcOzaki1 P b s x y = some v) :
    Rat.abs (v - dot x y) ≤
      (((trianglePairs s).length - 1 : ℕ) : ℚ) * 2 ^ (-24 : ℤ) *
          ((exactTerms b s x y).map Rat.abs).sum +
        ((s + 1 : ℕ) : ℚ) * capSum (2 ^ (splitExp b x + splitExp b y - s * (b + 1))) x y := by
  unfold mcOzaki1 at hv
  rw [fp32Add_eq_addOfRound, round32Value_eq_rne32Q_fun] at hv
  exact ozaki1_error_jr hP.exactOn (Rat.le_of_lt (two_pow_pos _))
    (roundRNE_jrAdd (p := 24) (emin := -126) (emax := 127) (by decide) (by decide)) hlen hk hterms hv

end Ozaki.MC
