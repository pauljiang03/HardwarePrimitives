import OzakiMC.SplitChoice
import OzakiMC.TwoPass
import Ozaki.ModuliRule

/-! # Choosing the configuration per AMD path, with two passes, for Ozaki-I and Ozaki-II

`OzakiMC.SplitChoice` chose Ozaki-I's slice width with split-K. With the two-pass engine of
`OzakiMC.TwoPass` the AMD paths gain a second kind of configuration, and Ozaki-II gets the same
treatment as on the Tensor Core (`OzakiTC.Ozaki2Choice`):

* **split-K** with `b`-bit slices (`2b ≤ 24`), chunks of `chunkLen b` on chained blocks
  (`mcSplitK_exactOn`): `mcBlocks` blocks per product;
* **two passes** with `b`-bit slices wherever `TwoPassOK P b` (`mcMultiplier2_exactOn`): every block of
  `N_FMA` products twice, `2 ⌈k / N_FMA⌉` blocks per product.

Every candidate is exact on vectors of every length (`mcRunCandidates_exact`). Ozaki-I costs
`s(s+1)/2` products with `s = slicesFor b t`, Ozaki-II `moduliFor b t k` products (`Ozaki.ModuliRule`).
The costs are model blocks, with the limits stated in `OzakiTC.SplitChoice` and
`OzakiTC.Ozaki2Choice`.

## Results (inner dimension `k = 1024`, blocks)

| path | `N_FMA` | Ozaki-I FP64 best | Ozaki-II FP64 best | Ozaki-I binary32 | Ozaki-II binary32 |
| --- | --- | --- | --- | --- | --- |
| SFMA | 1 | `b = 24`, two passes, 12288 | `b = 12`, split-K, 10240 | 6144 | 5120 |
| CDNA 1 fp16 | 4 | `b = 11`, split-K, 3840 | `b = 11`, 2816 | 1536 | 1536 |
| CDNA 1 bf16 | 2 | `b = 8`, 14336 | `b = 8`, 7168 | 5120 | 4096 |
| CDNA 2 fp16 | 4 | `b = 11`, 3840 | `b = 11`, 2816 | 1536 | 1536 |
| CDNA 3 fp16 | 8 | `b = 10`, split-K, 2688 | `b = 10`, split-K, 1536 | 768 | 768 |
| CDNA 3 bf16 | 8 | `b = 8`, 3584 | `b = 8`, 1792 | 1280 | 1024 |
| CDNA 3 XF32 | 4 | `b = 11`, 3840 | `b = 11`, 2816 | 1536 | 1536 |

The SFMA is the one place where two passes win: a block holds one product, so one pass allows
`12`-bit slices (`5` for FP64, `15` products), while two passes (TwoProdFMA) allow `24`-bit slices
(`3`, `6` products at two blocks each, `12288` blocks against `15360`). On CDNA 3 fp16 two passes
make full groups of `11`-bit products exact, but `10`-bit slices fill them in one pass more cheaply,
as on the Tensor Core. For FP64, Ozaki-II costs fewer blocks than Ozaki-I on every path. -/

open MatrixCore

namespace Ozaki.MC

/-- How a slice or residue product runs on an AMD path. -/
inductive MCRun where
  | splitK (b : ℕ)
  | twoPass (b : ℕ)
  deriving DecidableEq, Repr

def MCRun.width : MCRun → ℕ
  | .splitK b => b
  | .twoPass b => b

def MCRun.multiplier (P : Model) : MCRun → MatrixMultiplier
  | .splitK b => mcSplitK P b
  | .twoPass _ => mcMultiplier2 P

/-- Blocks per product of inner dimension `k` on blocks of `n` products. -/
def MCRun.blocks (n k : ℕ) : MCRun → ℕ
  | .splitK b => mcBlocks n b k
  | .twoPass _ => 2 * ((k + n - 1) / n)

/-- Ozaki-I's cost for `t` bits. -/
def MCRun.cost1 (n t k : ℕ) (r : MCRun) : ℕ := (trianglePairs (slicesFor r.width t)).length * r.blocks n k

/-- Ozaki-II's cost for `t` bits. -/
def MCRun.cost2 (n t k : ℕ) (r : MCRun) : ℕ := moduliFor r.width t k * r.blocks n k

/-- Every configuration: split-K widths up to `bmax` (`2b ≤ 24`), then two-pass widths up to
`bmax2` with `TwoPassOK`. -/
def mcRunCandidates (P : Model) (bmax bmax2 : ℕ) : List MCRun :=
  (mcCandidates bmax).map .splitK ++
    ((List.range (bmax2 + 1)).reverse.filter fun b => decide (1 ≤ b) && decide (TwoPassOK P b)).map
      .twoPass

/-- **Every candidate is exact** on vectors of every length. -/
theorem mcRunCandidates_exact {P : Model} {bmax bmax2 : ℕ} (hP : ∀ b ≤ bmax, ExactMultiplier P b)
    (hfa : smallSubnormals P.a) (hfb : smallSubnormals P.b) (hn : 0 < P.nfma)
    (henc : ∀ b ≤ bmax2, EncodesInts P.a b ∧ EncodesInts P.b b) :
    ∀ r ∈ mcRunCandidates P bmax bmax2, ∀ B, (r.multiplier P).ExactOn r.width B := by
  intro r hr B
  rcases List.mem_append.mp hr with hr | hr
  · obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hr
    exact mcCandidates_exact hP b hb B
  · obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hr
    obtain ⟨hbr, hok⟩ := List.mem_filter.mp hb
    simp only [List.mem_reverse, List.mem_range] at hbr
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hok
    exact mcMultiplier2_exactOn hok.2 hfa hfb hn (henc b (by omega)).1 (henc b (by omega)).2 B

def mcBest1 (P : Model) (bmax bmax2 t k : ℕ) : Option MCRun :=
  (mcRunCandidates P bmax bmax2).foldl (fun acc r => match acc with
    | none => some r
    | some a => if r.cost1 P.nfma t k < a.cost1 P.nfma t k then some r else some a) none

def mcBest2 (P : Model) (bmax bmax2 t k : ℕ) : Option MCRun :=
  ((mcRunCandidates P bmax bmax2).filter fun r => decide (0 < moduliFor r.width t k)).foldl
    (fun acc r => match acc with
      | none => some r
      | some a => if r.cost2 P.nfma t k < a.cost2 P.nfma t k then some r else some a) none

/-! ## The best configurations per path (`k = 1024`) -/

/-- **The SFMA: two passes win for Ozaki-I.** `24`-bit slices with TwoProdFMA cost `12288` blocks
for FP64 against `15360` for `12`-bit slices in one pass. For Ozaki-II, `12`-bit residues in one
pass and `24`-bit residues in two tie at `10240` (`10` moduli of one block against `5` of two). -/
theorem sfma_best12 :
    mcBest1 sfmaF32 12 24 53 1024 = some (.twoPass 24) ∧ (MCRun.twoPass 24).cost1 1 53 1024 = 12288 ∧
      (MCRun.splitK 12).cost1 1 53 1024 = 15360 ∧
    mcBest2 sfmaF32 12 24 53 1024 = some (.splitK 12) ∧ (MCRun.splitK 12).cost2 1 53 1024 = 10240 ∧
      (MCRun.twoPass 24).cost2 1 53 1024 = 10240 ∧
    (MCRun.splitK 12).cost1 1 24 1024 = 6144 ∧ (MCRun.twoPass 24).cost1 1 24 1024 = 6144 ∧
    mcBest2 sfmaF32 12 24 24 1024 = some (.splitK 12) ∧ (MCRun.splitK 12).cost2 1 24 1024 = 5120 := by
  decide +kernel

theorem cdna1F16_best12 :
    mcBest1 cdna1F16 11 11 53 1024 = some (.splitK 11) ∧ (MCRun.splitK 11).cost1 4 53 1024 = 3840 ∧
    mcBest2 cdna1F16 11 11 53 1024 = some (.splitK 11) ∧ (MCRun.splitK 11).cost2 4 53 1024 = 2816 ∧
    (MCRun.splitK 11).cost1 4 24 1024 = 1536 ∧ (MCRun.splitK 11).cost2 4 24 1024 = 1536 := by
  decide +kernel

theorem cdna1BF16_best12 :
    mcBest1 cdna1BF16 8 8 53 1024 = some (.splitK 8) ∧ (MCRun.splitK 8).cost1 2 53 1024 = 14336 ∧
    mcBest2 cdna1BF16 8 8 53 1024 = some (.splitK 8) ∧ (MCRun.splitK 8).cost2 2 53 1024 = 7168 ∧
    (MCRun.splitK 8).cost1 2 24 1024 = 5120 ∧ (MCRun.splitK 8).cost2 2 24 1024 = 4096 := by
  decide +kernel

theorem cdna2F16_best12 :
    mcBest1 cdna2F16 11 11 53 1024 = some (.splitK 11) ∧ (MCRun.splitK 11).cost1 4 53 1024 = 3840 ∧
    mcBest2 cdna2F16 11 11 53 1024 = some (.splitK 11) ∧ (MCRun.splitK 11).cost2 4 53 1024 = 2816 := by
  decide +kernel

/-- **CDNA 3 fp16**: for both schemes `10`-bit slices or residues in one pass are cheapest;
`11`-bit ones with two passes cost `3840` (Ozaki-I) and `2816` (Ozaki-II). -/
theorem cdna3F16_best12 :
    mcBest1 cdna3F16 11 11 53 1024 = some (.splitK 10) ∧ (MCRun.splitK 10).cost1 8 53 1024 = 2688 ∧
      (MCRun.twoPass 11).cost1 8 53 1024 = 3840 ∧
    mcBest2 cdna3F16 11 11 53 1024 = some (.splitK 10) ∧ (MCRun.splitK 10).cost2 8 53 1024 = 1536 ∧
      (MCRun.twoPass 11).cost2 8 53 1024 = 2816 ∧
    (MCRun.splitK 10).cost1 8 24 1024 = 768 ∧ (MCRun.splitK 10).cost2 8 24 1024 = 768 := by
  decide +kernel

theorem cdna3BF16_best12 :
    mcBest1 cdna3BF16 8 8 53 1024 = some (.splitK 8) ∧ (MCRun.splitK 8).cost1 8 53 1024 = 3584 ∧
    mcBest2 cdna3BF16 8 8 53 1024 = some (.splitK 8) ∧ (MCRun.splitK 8).cost2 8 53 1024 = 1792 ∧
    (MCRun.splitK 8).cost1 8 24 1024 = 1280 ∧ (MCRun.splitK 8).cost2 8 24 1024 = 1024 := by
  decide +kernel

theorem cdna3XF32_best12 :
    mcBest1 cdna3XF32 11 11 53 1024 = some (.splitK 11) ∧ (MCRun.splitK 11).cost1 4 53 1024 = 3840 ∧
    mcBest2 cdna3XF32 11 11 53 1024 = some (.splitK 11) ∧ (MCRun.splitK 11).cost2 4 53 1024 = 2816 := by
  decide +kernel

/-! ## The chosen configurations, correctly rounded -/

/-- **Correctly rounded FP64 on CDNA 3 fp16 by Ozaki-II with the cheapest configuration**: `12`
moduli at most `2048`, `P = 55`, `10`-bit residues, inner dimension up to `1024`. -/
theorem cdna3F16_fp64CR2 {x y : List ℚ} (hx : ∀ a ∈ x, Binary64Value a)
    (hy : ∀ a ∈ y, Binary64Value a) (hlen : x.length = y.length) (hk : x.length ≤ 1024) :
    mcOzaki2CRD cdna3F16 [(moduliBasis 10 12, 55)] 10 191 x y = rne64 (dot x y) := by
  have hv : (moduliBasis 10 12).Valid := by decide +kernel
  have hm : moduliFor 10 53 1024 = 12 := by decide +kernel
  refine mcOzaki2CRD_eq (cdna3F16_exactMultiplier (by decide)) (by decide) (by decide) ?_ hx hy hlen
  intro c hc
  rw [List.mem_singleton.mp hc]
  refine ⟨hv, moduliBasis_le 10 12, ?_⟩
  have := moduliFor_spec (b := 10) (t := 53) (k := 1024) (by rw [hm]; decide) hk
  rwa [hm] at this

/-- **Correctly rounded FP64 on the SFMA with two passes**: `24`-bit slices (TwoProdFMA), the exact
path at up to `84` slices (`84 · 25 > 2098`), every length. -/
theorem sfma_fp64CR2pass (ss : List ℕ) {x y : List ℚ} (hx : ∀ a ∈ x, Binary64Value a)
    (hy : ∀ a ∈ y, Binary64Value a) (hlen : x.length = y.length) :
    ozaki1CRE (mcMultiplier2 sfmaF32) rne64 24 ss 84 x y = rne64 (dot x y) :=
  ozaki1CRE_eq rne64_nearest rne64_intervals (sfma_exactOn2 _) ss hlen (Nat.le_refl _)
    (vanish64 (by omega) (by decide) hx hy)

end Ozaki.MC
