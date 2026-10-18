import OzakiMC.LongDot
import Ozaki.SliceRule

/-! # Choosing the slice width and chunk length per Matrix Core variant

The AMD analogue of `OzakiTC.SplitChoice`. On the Matrix Core model one knob is proven exact:
split-K with `b`-bit slices, chunks of `chunkLen b = 2^(24 − 2b)` products, each chunk on chained
blocks of `N_FMA` products (`mcSplitK_exactOn`); there is no two-pass matrix multiplier on this
model. The candidates are every `b` up to what the operand format holds with `2b ≤ 24`
(`mcCandidates_exact`), and the cost of Ozaki-I for `t` bits is `s(s+1)/2` slice products
(`s = slicesFor b t`, the rule of `Ozaki.SliceRule`) times `⌈chunk / N_FMA⌉` blocks per chunk. As
on the Tensor Core, the cost is in model blocks, not measured time.

## Results (inner dimension `k = 1024`)

| variant | `N_FMA` | FP64 (`t = 53`): best | blocks | binary32 (`t = 24`): best | blocks |
| --- | --- | --- | --- | --- | --- |
| SFMA fp32 | 1 | `b = 12` | 15360 | `b = 12` | 6144 |
| CDNA 1 fp16 | 4 | `b = 11` | 3840 | `b = 11` | 1536 |
| CDNA 1 bf16 | 2 | `b = 8` | 14336 | `b = 8` | 5120 |
| CDNA 2 fp16 | 4 | `b = 11` | 3840 | `b = 11` | 1536 |
| CDNA 2 bf16 | 2 | `b = 8` | 14336 | `b = 8` | 5120 |
| CDNA 2 bf16 `_1k` | 4 | `b = 8` | 7168 | `b = 8` | 2560 |
| CDNA 3 fp16 | 8 | `b = 10` | 2688 | `b = 10` | 768 |
| CDNA 3 bf16 | 8 | `b = 8` | 3584 | `b = 8` | 1280 |
| CDNA 3 XF32 | 4 | `b = 11` | 3840 | `b = 11` | 1536 |

As on A100, CDNA 3 fp16's blocks of eight favor `10`-bit slices: `2688` blocks for FP64 against
`3840` with `11`-bit slices in chunks of four (`cdna3F16_best`). The SFMA multiplies one product per
block, so the widest slices it holds (`b = 12`, `2b ≤ 24`) are best. -/

open MatrixCore

namespace Ozaki.MC

/-- Blocks one slice product of inner dimension `k` takes with `b`-bit slices on blocks of `n`. -/
def mcBlocks (n b k : ℕ) : ℕ := chunkBlocks n (chunkLen b) (List.replicate k ())

/-- The cost of Ozaki-I for `t` bits with `b`-bit slices. -/
def mcCost (n t k b : ℕ) : ℕ := (trianglePairs (slicesFor b t)).length * mcBlocks n b k

/-- Slice widths split-K makes exact: `1 ≤ b ≤ bmax`, `2b ≤ 24`, widest first. -/
def mcCandidates (bmax : ℕ) : List ℕ :=
  (List.range (bmax + 1)).reverse.filter fun b => decide (1 ≤ b) && decide (2 * b ≤ 24)

/-- **Every candidate is exact** on vectors of every length, on a variant exact on `bmax`-bit slices
and below. -/
theorem mcCandidates_exact {P : Model} {bmax : ℕ} (hP : ∀ b ≤ bmax, ExactMultiplier P b) :
    ∀ b ∈ mcCandidates bmax, ∀ B, (mcSplitK P b).ExactOn b B := by
  intro b hb B
  obtain ⟨hbr, hok⟩ := List.mem_filter.mp hb
  simp only [List.mem_reverse, List.mem_range] at hbr
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hok
  exact mcSplitK_exactOn (hP b (by omega)) hok.2 B

/-- The cheapest candidate for `t` bits at inner dimension `k`; the widest on a tie. -/
def mcBest (P : Model) (bmax t k : ℕ) : Option ℕ :=
  (mcCandidates bmax).foldl (fun acc b => match acc with
    | none => some b
    | some a => if mcCost P.nfma t k b < mcCost P.nfma t k a then some b else some a) none

/-! ## The best configuration per variant (`k = 1024`) -/

theorem sfma_best :
    mcBest sfmaF32 12 53 1024 = some 12 ∧ mcCost 1 53 1024 12 = 15360 ∧
    mcBest sfmaF32 12 24 1024 = some 12 ∧ mcCost 1 24 1024 12 = 6144 := by
  decide +kernel

theorem cdna1F16_best :
    mcBest cdna1F16 11 53 1024 = some 11 ∧ mcCost 4 53 1024 11 = 3840 ∧
    mcBest cdna1F16 11 24 1024 = some 11 ∧ mcCost 4 24 1024 11 = 1536 := by
  decide +kernel

theorem cdna1BF16_best :
    mcBest cdna1BF16 8 53 1024 = some 8 ∧ mcCost 2 53 1024 8 = 14336 ∧
    mcBest cdna1BF16 8 24 1024 = some 8 ∧ mcCost 2 24 1024 8 = 5120 := by
  decide +kernel

theorem cdna2F16_best :
    mcBest cdna2F16 11 53 1024 = some 11 ∧ mcCost 4 53 1024 11 = 3840 ∧
    mcBest cdna2F16 11 24 1024 = some 11 ∧ mcCost 4 24 1024 11 = 1536 := by
  decide +kernel

theorem cdna2BF16_best :
    mcBest cdna2BF16 8 53 1024 = some 8 ∧ mcCost 2 53 1024 8 = 14336 ∧
    mcBest cdna2BF16_1k 8 53 1024 = some 8 ∧ mcCost 4 53 1024 8 = 7168 ∧
    mcBest cdna2BF16 8 24 1024 = some 8 ∧ mcBest cdna2BF16_1k 8 24 1024 = some 8 := by
  decide +kernel

/-- **CDNA 3 fp16**: `10`-bit slices in chunks of sixteen (two chained blocks of eight) cost `2688`
blocks for FP64 against `3840` for `11`-bit slices in chunks of four. -/
theorem cdna3F16_best :
    mcBest cdna3F16 11 53 1024 = some 10 ∧ mcCost 8 53 1024 10 = 2688 ∧
      mcCost 8 53 1024 11 = 3840 ∧
    mcBest cdna3F16 11 24 1024 = some 10 ∧ mcCost 8 24 1024 10 = 768 ∧
      mcCost 8 24 1024 11 = 1536 := by
  decide +kernel

theorem cdna3BF16_best :
    mcBest cdna3BF16 8 53 1024 = some 8 ∧ mcCost 8 53 1024 8 = 3584 ∧
    mcBest cdna3BF16 8 24 1024 = some 8 ∧ mcCost 8 24 1024 8 = 1280 := by
  decide +kernel

theorem cdna3XF32_best :
    mcBest cdna3XF32 11 53 1024 = some 11 ∧ mcCost 4 53 1024 11 = 3840 ∧
    mcBest cdna3XF32 11 24 1024 = some 11 ∧ mcCost 4 24 1024 11 = 1536 := by
  decide +kernel

/-! ## The chosen configurations, correctly rounded -/

/-- **Correctly rounded FP64 on CDNA 3 fp16 with the cheapest configuration**: `10`-bit slices, the
exact fallback at up to `191` slices. -/
theorem cdna3F16_fp64CR10 (ss : List ℕ) {x y : List ℚ} (hx : ∀ a ∈ x, Binary64Value a)
    (hy : ∀ a ∈ y, Binary64Value a) (hlen : x.length = y.length) :
    mcOzaki1CRD cdna3F16 10 ss 191 x y = rne64 (dot x y) :=
  mcOzaki1CRD_eq (cdna3F16_exactMultiplier (by decide)) (by decide) ss (by decide) hx hy hlen

theorem cdna3F16_fp32CR10 (ss : List ℕ) {x y : List ℚ} (hx : ∀ a ∈ x, Binary32Value a)
    (hy : ∀ a ∈ y, Binary32Value a) (hlen : x.length = y.length) :
    mcOzaki1CRL cdna3F16 10 ss 26 x y = rne32Q (dot x y) :=
  mcOzaki1CRL_eq (cdna3F16_exactMultiplier (by decide)) (by decide) ss (by decide) hx hy hlen

/-- **Correctly rounded FP64 on the SFMA with `12`-bit slices**, the exact fallback at up to `162`
slices (`162 · 13 > 2098`). -/
theorem sfma_fp64CR12 (ss : List ℕ) {x y : List ℚ} (hx : ∀ a ∈ x, Binary64Value a)
    (hy : ∀ a ∈ y, Binary64Value a) (hlen : x.length = y.length) :
    mcOzaki1CRD sfmaF32 12 ss 162 x y = rne64 (dot x y) :=
  mcOzaki1CRD_eq (sfmaF32_exactMultiplier (by decide)) (by decide) ss (by decide) hx hy hlen

end Ozaki.MC
