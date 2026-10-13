import OzakiMC.Ozaki2Choice
import Ozaki.Adaptive

/-! # The two design rules and the correct-rounding margin on the matrix-core model

`Ozaki.Adaptive`'s rules on matrix-core blocks with split-K (slice counts from the inner dimension,
and the shortcut to the exact path), each correctly rounded for every length, and the per-path
comparison of Ozaki-I and Ozaki-II with the margin of `Ozaki.SliceRuleCR`: at `k = 1024`, `t = 63`
for FP64 and `34` for binary32.

## Results (inner dimension `k = 1024`, blocks)

| path | Ozaki-I FP64 | Ozaki-II FP64 | Ozaki-I binary32 | Ozaki-II binary32 |
| --- | --- | --- | --- | --- |
| SFMA | `b = 24`, two passes, 12288 | `b = 12`, 11264 | 6144 | 7168 |
| CDNA 1 fp16 | `b = 11`, 5376 | 3072 | 2560 | 1792 |
| CDNA 1 bf16 | `b = 8`, 18432 | 8192 | 7680 | 5120 |
| CDNA 2 fp16 | `b = 11`, 5376 | 3072 | 2560 | 1792 |
| CDNA 3 fp16 | `b = 10`, 3584 | 1664 | 1280 | 1024 |
| CDNA 3 bf16 | `b = 8`, 4608 | 2048 | 1920 | 1280 |
| CDNA 3 XF32 | `b = 11`, 5376 | 3072 | 2560 | 1792 |

As on the Tensor Core, Ozaki-II is cheaper for FP64 on every path with the margin, now by `1.1×`
(SFMA) to `2.25×`; for binary32 it is cheaper except on the SFMA, where two-pass Ozaki-I with
`24`-bit slices wins. The counts leave out the work off the engine. -/

open MatrixCore

namespace Ozaki.MC

/-- Correctly rounded FP64 by Ozaki-I with both rules. -/
def mcOzaki1CRDKA (P : Model) (b t r smax : ℕ) (x y : List ℚ) : Option ℚ :=
  ozaki1CRKA (mcSplitK P b) rne64 b t r smax x y

/-- Both rules as one integer function from binary64 entries. -/
def mcOzaki1CRIKA (P : Model) (b W t r smax : ℕ) (xs ys : List (ℤ × ℤ)) : Option ℚ :=
  ozaki1CRIKA (mcSplitK P b) 53 (-1022) 1023 b W t r smax xs ys

theorem mcOzaki1CRDKA_eq {P : Model} {b : ℕ} (hP : ExactMultiplier P b) (hb : 2 * b ≤ 24)
    (t r : ℕ) {smax : ℕ} (hsmax : 2098 < smax * (b + 1)) {x y : List ℚ}
    (hx : ∀ a ∈ x, Binary64Value a) (hy : ∀ a ∈ y, Binary64Value a)
    (hlen : x.length = y.length) :
    mcOzaki1CRDKA P b t r smax x y = rne64 (dot x y) :=
  ozaki1CRKA_eq rne64_nearest rne64_intervals (mcSplitK_exactOn hP hb _) t r hlen
    (Nat.le_refl _) (vanish64 (by omega) hsmax hx hy)

theorem mcOzaki1CRIKA_eq {P : Model} {b : ℕ} (hP : ExactMultiplier P b) (hb : 2 * b ≤ 24)
    (W t r : ℕ) {smax : ℕ} (hsmax : 2098 < smax * (b + 1))
    {xs ys : List (ℤ × ℤ)} (hx : ∀ a ∈ xs, Binary64Value (entryVal a))
    (hy : ∀ a ∈ ys, Binary64Value (entryVal a)) (hlen : xs.length = ys.length) :
    mcOzaki1CRIKA P b W t r smax xs ys = rne64 (dot (entryVals xs) (entryVals ys)) :=
  ozaki1CRI64_eq (mcSplitK_exactOn hP hb _) W _ (by omega) hsmax hlen (Nat.le_refl _) hx hy

theorem sfma_bestCR :
    mcBest1 sfmaF32 12 24 63 1024 = some (.twoPass 24) ∧ (MCRun.twoPass 24).cost1 1 63 1024 = 12288 ∧
    mcBest2 sfmaF32 12 24 63 1024 = some (.splitK 12) ∧ (MCRun.splitK 12).cost2 1 63 1024 = 11264 ∧
    mcBest1 sfmaF32 12 24 34 1024 = some (.splitK 12) ∧ (MCRun.splitK 12).cost1 1 34 1024 = 6144 ∧
    mcBest2 sfmaF32 12 24 34 1024 = some (.splitK 12) ∧ (MCRun.splitK 12).cost2 1 34 1024 = 7168 := by
  decide +kernel

theorem cdna1F16_bestCR :
    mcBest1 cdna1F16 11 11 63 1024 = some (.splitK 11) ∧ (MCRun.splitK 11).cost1 4 63 1024 = 5376 ∧
    mcBest2 cdna1F16 11 11 63 1024 = some (.splitK 11) ∧ (MCRun.splitK 11).cost2 4 63 1024 = 3072 ∧
    (MCRun.splitK 11).cost1 4 34 1024 = 2560 ∧ (MCRun.splitK 11).cost2 4 34 1024 = 1792 := by
  decide +kernel

theorem cdna1BF16_bestCR :
    mcBest1 cdna1BF16 8 8 63 1024 = some (.splitK 8) ∧ (MCRun.splitK 8).cost1 2 63 1024 = 18432 ∧
    mcBest2 cdna1BF16 8 8 63 1024 = some (.splitK 8) ∧ (MCRun.splitK 8).cost2 2 63 1024 = 8192 ∧
    (MCRun.splitK 8).cost1 2 34 1024 = 7680 ∧ (MCRun.splitK 8).cost2 2 34 1024 = 5120 := by
  decide +kernel

theorem cdna2F16_bestCR :
    mcBest1 cdna2F16 11 11 63 1024 = some (.splitK 11) ∧ (MCRun.splitK 11).cost1 4 63 1024 = 5376 ∧
    mcBest2 cdna2F16 11 11 63 1024 = some (.splitK 11) ∧ (MCRun.splitK 11).cost2 4 63 1024 = 3072 := by
  decide +kernel

/-- **CDNA 3 fp16 with the margin**: Ozaki-II with `13` moduli costs `1664` blocks for FP64 against
`3584` for Ozaki-I. -/
theorem cdna3F16_bestCR :
    mcBest1 cdna3F16 11 11 63 1024 = some (.splitK 10) ∧ (MCRun.splitK 10).cost1 8 63 1024 = 3584 ∧
    mcBest2 cdna3F16 11 11 63 1024 = some (.splitK 10) ∧ (MCRun.splitK 10).cost2 8 63 1024 = 1664 ∧
    (MCRun.splitK 10).cost1 8 34 1024 = 1280 ∧ (MCRun.splitK 10).cost2 8 34 1024 = 1024 := by
  decide +kernel

theorem cdna3BF16_bestCR :
    mcBest1 cdna3BF16 8 8 63 1024 = some (.splitK 8) ∧ (MCRun.splitK 8).cost1 8 63 1024 = 4608 ∧
    mcBest2 cdna3BF16 8 8 63 1024 = some (.splitK 8) ∧ (MCRun.splitK 8).cost2 8 63 1024 = 2048 ∧
    (MCRun.splitK 8).cost1 8 34 1024 = 1920 ∧ (MCRun.splitK 8).cost2 8 34 1024 = 1280 := by
  decide +kernel

theorem cdna3XF32_bestCR :
    mcBest1 cdna3XF32 11 11 63 1024 = some (.splitK 11) ∧ (MCRun.splitK 11).cost1 4 63 1024 = 5376 ∧
    mcBest2 cdna3XF32 11 11 63 1024 = some (.splitK 11) ∧ (MCRun.splitK 11).cost2 4 63 1024 = 3072 := by
  decide +kernel

/-- **Correctly rounded FP64 on CDNA 3 fp16 by Ozaki-II with the margin**: `13` moduli at most
`2048`, `P = 65`, inner dimension up to `1024`; the basis is valid by `moduliBasis_valid_all`. -/
theorem cdna3F16_fp64CR2_margin {x y : List ℚ} (hx : ∀ a ∈ x, Binary64Value a)
    (hy : ∀ a ∈ y, Binary64Value a) (hlen : x.length = y.length) (hk : x.length ≤ 1024) :
    mcOzaki2CRD cdna3F16 [(moduliBasis 10 13, 65)] 10 191 x y = rne64 (dot x y) := by
  have hm : moduliForCR 10 53 1024 = 13 := by decide +kernel
  have hc : clog2 1024 = 10 := by decide
  refine mcOzaki2CRD_eq (cdna3F16_exactMultiplier (by decide)) (by decide) (by decide) ?_ hx hy hlen
  intro c hc'
  rw [List.mem_singleton.mp hc']
  refine ⟨moduliBasis_valid_all 10 13, moduliBasis_le 10 13, ?_⟩
  have h := moduliForCR_spec (b := 10) (t := 53) (k := 1024) (by rw [hm]; decide) hk
  rw [hm, hc] at h
  exact h

end Ozaki.MC
