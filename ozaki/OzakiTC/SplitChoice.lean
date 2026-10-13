import OzakiTC.TwoPass
import OzakiTC.LongDot
import OzakiTC.Cancellation
import Ozaki.SliceRule

/-! # Choosing the slice width, chunk length and passes per Tensor Core variant

Ozaki-I on a Tensor Core variant has three knobs, each exact by a theorem of this development:

* the **slice width** `b`: at most what the operand format holds (`11` for fp16 and tf32, `8` for
  bf16) and `2b ≤ F`;
* the **chunk length** of split-K, `m = 2^(24 − 2b)` products per exact call (`tcSplitK`,
  `tcSplitK_exactOn`): four for `11`-bit slices, sixteen for `10`-bit, `256` for `8`-bit; a chunk
  longer than the FMA size `K` runs as chained block FMAs;
* **one or two passes**: the two-pass matrix multiplier runs every block FMA twice (`c = 0`, then
  `c = −D1`) and is exact on full block FMAs when `K · 2^(2b) ≤ 2^(F+1)` (`tcMultiplier2_exactOn`).

`candidates p bmax` lists every configuration these theorems make exact on variant `p`
(`candidates_exact`). `SliceRun.blocks K k` counts the Tensor Core blocks (one block FMA of `K`
products, one evaluation of the block model) a slice product of inner dimension `k` takes:
`⌈m / K⌉` per chunk of split-K, two per block FMA for two passes. A partly filled block FMA costs a
whole block FMA, as a matrix instruction computes `K` products whatever their values.

**The slice rule.** For a target of `t` bits, `slicesFor b t` is the least `s` with
`(s + 1) 2^(t+2) ≤ 2^(s(b+1))`. This makes the slicing term of Ozaki-I's error bound,
`(s + 1) k 2^(E+F−s(b+1))` (`tcOzaki1L_error`), at most `2^-t · k · max|x| · max|y|`
(`slicing_term_le_maxAbs`): `t = 24` for a binary32-level result, `t = 53` for FP64. The Ozaki-I
triangle then has `s(s+1)/2` slice products, and the cost of a configuration is
`s(s+1)/2 · blocks`. For the exact fallback of correctly rounded FP64 (`smax (b+1) > 2098`, all `s²`
products) the worst case is `exactFallbackCost`.

**The cost is in model blocks, not measured time.** It counts block FMAs; it ignores
the integer work off the matrix multiplier (slicing, adding chunk results), memory traffic, and the
fact that a real kernel runs many output entries per instruction.

## Results (inner dimension `k = 1024`)

| variant | `K` | `F` | FP64 (`t = 53`): best | blocks | `b = 11`, split-K | `b = 11`, two passes | binary32 (`t = 24`): best | blocks |
| --- | --- | --- | --- | --- | --- | --- | --- | --- |
| V100 fp16 | 4 | 23 | `b = 11`, split-K | 3840 | 3840 | 7680 | `b = 11`, split-K | 1536 |
| A100 fp16 | 8 | 24 | `b = 10`, split-K | 2688 | 3840 | 3840 | `b = 10`, split-K | 768 |
| A100 bf16 | 8 | 24 | `b = 8`, split-K | 3584 | — | — | `b = 8`, split-K | 1280 |
| A100 tf32 | 4 | 24 | `b = 11`, split-K | 3840 | 3840 | 7680 | `b = 11`, split-K | 1536 |
| H100 fp16 | 16 | 25 | `b = 10`, split-K | 1344 | 3840 | 1920 | `b = 10`, split-K | 384 |
| H100 bf16 | 16 | 25 | `b = 8`, split-K | 1792 | — | — | `b = 8`, split-K | 640 |
| H100 tf32 (wmma) | 4 | 25 | `b = 11`, split-K | 3840 | 3840 | 7680 | `b = 11`, split-K | 1536 |
| H100 tf32 (mma) | 8 | 25 | `b = 10`, split-K | 2688 | 3840 | 3840 | `b = 10`, split-K | 768 |

FP64 needs `5` slices of `11` bits (`15` products) or `6` of `10` bits (`21` products); binary32
needs `3` of either (`6` products). Where `K > 4`, narrower slices with longer chunks win: `10`-bit
slices fill a whole A100 or H100 block FMA (`16 · 2^20 = 2^24`), so one block carries `16` products
instead of `4`. On H100 fp16 this costs `1344` blocks for FP64, against `3840` for `11`-bit slices
with chunks of four and `1920` with two passes; for binary32, `384` against `1536` and `768`. Under
this cost the two-pass matrix multiplier never wins: whenever two passes make a full block FMA of
`11`-bit products exact, `10`-bit slices make it exact in one pass, and the extra slice costs less
than the second pass. Where `K = 4` (V100 fp16, the tf32 `wmma` variants) a block FMA holds only
four products whatever the width, so `11`-bit slices are best. The worst-case exact fallback follows
the same pattern (`h100F16_exactFallback`). -/

open TensorCore

namespace Ozaki.TC

/-! ## Configurations -/

/-- How a slice product runs on a Tensor Core variant: split-K with `b`-bit slices (chunks of
`chunkLen b` products, each on chained block FMAs from `c = 0`), or the two-pass matrix multiplier
(every block FMA of `K` twice). -/
inductive SliceRun where
  | splitK (b : ℕ)
  | twoPass (b : ℕ)
  deriving DecidableEq, Repr

/-- The slice width of a configuration. -/
def SliceRun.width : SliceRun → ℕ
  | .splitK b => b
  | .twoPass b => b

/-- The matrix multiplier of a configuration. -/
def SliceRun.multiplier (p : Model) : SliceRun → MatrixMultiplier
  | .splitK b => tcSplitK p b
  | .twoPass _ => tcMultiplier2 p

/-- **Blocks per slice product** of inner dimension `k` on a variant with an FMA size of `K`:
split-K runs `⌈length / K⌉` block FMAs per chunk (`groupsOf_count`), two passes run every block FMA
twice. -/
def SliceRun.blocks (K k : ℕ) : SliceRun → ℕ
  | .splitK b => chunkBlocks K (chunkLen b) (List.replicate k ())
  | .twoPass _ => 2 * groupCount K k

/-- **The cost of Ozaki-I for `t` bits**: `s(s+1)/2` slice products, `s = slicesFor b t`, each
taking `blocks` Tensor Core blocks. -/
def SliceRun.cost (K t k : ℕ) (r : SliceRun) : ℕ :=
  (trianglePairs (slicesFor r.width t)).length * r.blocks K k

/-- The worst-case exact fallback of correctly rounded FP64: all `s²` slice products. -/
def SliceRun.exactFallbackCost (K k : ℕ) (r : SliceRun) : ℕ :=
  exactSlices r.width * exactSlices r.width * r.blocks K k

/-- Split-K with `b`-bit slices is exact on variant `p`: `1 ≤ b`, `2b ≤ 24`, `2b ≤ F`. -/
def splitOK (p : Model) (b : ℕ) : Bool :=
  decide (1 ≤ b) && decide (2 * b ≤ 24) && decide (2 * (b : ℤ) ≤ p.alignFracBits)

/-- Two passes with `b`-bit slices are exact on variant `p`: `1 ≤ b`, `2b ≤ F ≤ 25`, and
`K · 2^(2b) ≤ 2^(F+1)`. -/
def twoPassOK (p : Model) (b : ℕ) : Bool :=
  decide (1 ≤ b) && decide (2 * (b : ℤ) ≤ p.alignFracBits) &&
    decide (p.alignFracBits ≤ 25) &&
    decide (p.nfma * 2 ^ (2 * b) ≤ 2 ^ (p.alignFracBits.toNat + 1))

/-- **Every configuration the exactness theorems allow** on variant `p` with slices of at most
`bmax` bits, widest first: split-K, then two passes. -/
def candidates (p : Model) (bmax : ℕ) : List SliceRun :=
  ((List.range (bmax + 1)).reverse.filter (splitOK p)).map .splitK ++
    ((List.range (bmax + 1)).reverse.filter (twoPassOK p)).map .twoPass

/-- **Every candidate is exact**, on vectors of every length. -/
theorem candidates_exact {p : Model} {bmax : ℕ}
    (hfloor : ∀ f ∈ p.eAlignMin, f ≤ p.alignFracBits) (hwide : 23 ≤ p.alignFracBits)
    (hemin : 1 - p.input.bias ≤ 1) (hh : HoldsInts p bmax) (hK : 0 < p.nfma) :
    ∀ r ∈ candidates p bmax, ∀ B, (r.multiplier p).ExactOn r.width B := by
  have hint : ∀ b : ℕ, 1 ≤ b → 2 * (b : ℤ) ≤ p.alignFracBits → IntExact p b :=
    fun b hb1 hb => ⟨hb, hwide, hfloor, by omega⟩
  have hholds : ∀ b : ℕ, b ≤ bmax → HoldsInts p b :=
    fun b hb => ⟨hh.wellFormed, Nat.le_trans hb hh.bits, hh.emin, hh.emax⟩
  intro r hr B
  rcases List.mem_append.mp hr with hr | hr
  · obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hr
    obtain ⟨hbr, hok⟩ := List.mem_filter.mp hb
    simp only [List.mem_reverse, List.mem_range] at hbr
    simp only [splitOK, Bool.and_eq_true, decide_eq_true_eq] at hok
    obtain ⟨⟨h1, h24⟩, hF⟩ := hok
    exact tcSplitK_exactOn (tcMultiplier_exactOn (hint b h1 hF) (hholds b (by omega)) hK) h24 B
  · obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hr
    obtain ⟨hbr, hok⟩ := List.mem_filter.mp hb
    simp only [List.mem_reverse, List.mem_range] at hbr
    simp only [twoPassOK, Bool.and_eq_true, decide_eq_true_eq] at hok
    obtain ⟨⟨⟨h1, hF⟩, hF25⟩, hKn⟩ := hok
    refine tcMultiplier2_exactOn (hint b h1 hF) (hholds b (by omega)) h1 hF25 hK ?_ B
    have hc : ((p.nfma * 2 ^ (2 * b) : ℕ) : ℚ) ≤ ((2 ^ (p.alignFracBits.toNat + 1) : ℕ) : ℚ) :=
      Rat.natCast_le_natCast.mpr hKn
    rw [Rat.natCast_mul, ← two_pow_natCast, ← two_pow_natCast] at hc
    have e1 : (2 : ℚ) ^ (b : ℤ) * 2 ^ (b : ℤ) = 2 ^ (((2 * b : ℕ)) : ℤ) := by
      rw [← two_pow_add]; congr 1; push_cast; omega
    have e2 : (((p.alignFracBits.toNat + 1 : ℕ)) : ℤ) = p.alignFracBits + 1 := by
      push_cast; omega
    rw [e1]; rw [e2] at hc; exact hc

/-- **The cheapest candidate** for `t` bits at inner dimension `k`; the first in `candidates` order
on a tie. -/
def best (p : Model) (bmax t k : ℕ) : Option SliceRun :=
  (candidates p bmax).foldl (fun acc r => match acc with
    | none => some r
    | some a => if r.cost p.nfma t k < a.cost p.nfma t k then some r else some a) none

/-! ## The best configuration per variant (`k = 1024`)

Each statement is checked by evaluation: `best` scans every candidate. `t = 53` is FP64, `t = 24`
binary32. -/

theorem v100F16_best :
    best v100F16F32 11 53 1024 = some (.splitK 11) ∧ (SliceRun.splitK 11).cost 4 53 1024 = 3840 ∧
      (SliceRun.twoPass 11).cost 4 53 1024 = 7680 ∧
    best v100F16F32 11 24 1024 = some (.splitK 11) ∧ (SliceRun.splitK 11).cost 4 24 1024 = 1536 := by
  decide +kernel

theorem a100F16_best :
    best ampereF16F32 11 53 1024 = some (.splitK 10) ∧ (SliceRun.splitK 10).cost 8 53 1024 = 2688 ∧
      (SliceRun.splitK 11).cost 8 53 1024 = 3840 ∧ (SliceRun.twoPass 11).cost 8 53 1024 = 3840 ∧
    best ampereF16F32 11 24 1024 = some (.splitK 10) ∧ (SliceRun.splitK 10).cost 8 24 1024 = 768 ∧
      (SliceRun.splitK 11).cost 8 24 1024 = 1536 := by
  decide +kernel

theorem a100BF16_best :
    best a100BF16F32 8 53 1024 = some (.splitK 8) ∧ (SliceRun.splitK 8).cost 8 53 1024 = 3584 ∧
    best a100BF16F32 8 24 1024 = some (.splitK 8) ∧ (SliceRun.splitK 8).cost 8 24 1024 = 1280 := by
  decide +kernel

theorem a100TF32_best :
    best a100TF32F32 11 53 1024 = some (.splitK 11) ∧ (SliceRun.splitK 11).cost 4 53 1024 = 3840 ∧
    best a100TF32F32 11 24 1024 = some (.splitK 11) ∧ (SliceRun.splitK 11).cost 4 24 1024 = 1536 := by
  decide +kernel

/-- **H100 fp16**: `10`-bit slices in full block FMAs of sixteen cost `1344` blocks for FP64,
against `3840` for `11`-bit slices in chunks of four and `1920` with two passes. -/
theorem h100F16_best :
    best hopperF16F32 11 53 1024 = some (.splitK 10) ∧ (SliceRun.splitK 10).cost 16 53 1024 = 1344 ∧
      (SliceRun.splitK 11).cost 16 53 1024 = 3840 ∧ (SliceRun.twoPass 11).cost 16 53 1024 = 1920 ∧
    best hopperF16F32 11 24 1024 = some (.splitK 10) ∧ (SliceRun.splitK 10).cost 16 24 1024 = 384 ∧
      (SliceRun.splitK 11).cost 16 24 1024 = 1536 ∧ (SliceRun.twoPass 11).cost 16 24 1024 = 768 := by
  decide +kernel

theorem h100BF16_best :
    best hopperBF16F32 8 53 1024 = some (.splitK 8) ∧ (SliceRun.splitK 8).cost 16 53 1024 = 1792 ∧
    best hopperBF16F32 8 24 1024 = some (.splitK 8) ∧ (SliceRun.splitK 8).cost 16 24 1024 = 640 := by
  decide +kernel

theorem h100TF32Wmma_best :
    best hopperTF32WmmaF32 11 53 1024 = some (.splitK 11) ∧
      (SliceRun.splitK 11).cost 4 53 1024 = 3840 ∧
    best hopperTF32WmmaF32 11 24 1024 = some (.splitK 11) ∧
      (SliceRun.splitK 11).cost 4 24 1024 = 1536 := by
  decide +kernel

theorem h100TF32Mma_best :
    best hopperTF32MmaF32 11 53 1024 = some (.splitK 10) ∧
      (SliceRun.splitK 10).cost 8 53 1024 = 2688 ∧ (SliceRun.splitK 11).cost 8 53 1024 = 3840 ∧
      (SliceRun.twoPass 11).cost 8 53 1024 = 3840 ∧
    best hopperTF32MmaF32 11 24 1024 = some (.splitK 10) ∧
      (SliceRun.splitK 10).cost 8 24 1024 = 768 := by
  decide +kernel

/-- **The worst-case exact fallback on H100 fp16** (all `s²` products, `s(b+1) > 2098`): `191²`
products of `10`-bit slices in full block FMAs cost `2334784` blocks, `175²` products of `11`-bit
slices `7840000` in chunks of four and `3920000` with two passes. -/
theorem h100F16_exactFallback :
    (SliceRun.splitK 10).exactFallbackCost 16 1024 = 2334784 ∧
      (SliceRun.splitK 11).exactFallbackCost 16 1024 = 7840000 ∧
      (SliceRun.twoPass 11).exactFallbackCost 16 1024 = 3920000 := by
  decide +kernel

/-! ## The chosen configurations are exact, and the schemes' theorems apply

`10`-bit slices on the A100 and H100 fp16 variants and the H100 tf32 `mma` variant; the other
choices (`11`-bit slices on V100, A100 tf32 and the H100 tf32 `wmma` variant, `8`-bit on bf16) are
the instances of `OzakiTC.Models` and `OzakiTC.LongDot`. -/

theorem a100F16_exactOn10 : (tcMultiplier ampereF16F32).ExactOn 10 (2 ^ 24) :=
  tcMultiplier_exactOn ⟨by decide, by decide, eAlignMin_ok _ _ (by decide), by decide⟩
    ⟨by decide, by decide, by decide, by decide⟩ (by decide)

theorem h100F16_exactOn10 : (tcMultiplier hopperF16F32).ExactOn 10 (2 ^ 24) :=
  tcMultiplier_exactOn ⟨by decide, by decide, eAlignMin_ok _ _ (by decide), by decide⟩
    ⟨by decide, by decide, by decide, by decide⟩ (by decide)

theorem h100TF32Mma_exactOn10 : (tcMultiplier hopperTF32MmaF32).ExactOn 10 (2 ^ 24) :=
  tcMultiplier_exactOn ⟨by decide, by decide, eAlignMin_ok _ _ (by decide), by decide⟩
    ⟨by decide, by decide, by decide, by decide⟩ (by decide)

/-- Split-K with `10`-bit slices on H100 fp16 (chunks of sixteen, one full block FMA each) is exact
for every length. -/
theorem h100F16_splitK10_exactOn (B : ℕ) : (tcSplitK hopperF16F32 10).ExactOn 10 B :=
  tcSplitK_exactOn h100F16_exactOn10 (by decide) B

/-- **Correctly rounded FP64 on H100 fp16 with the cheapest configuration**: `10`-bit slices, the
exact fallback at up to `191` slices (`191 · 11 > 2098`). -/
theorem h100F16_fp64CR10 (ss : List ℕ) {x y : List ℚ} (hx : ∀ a ∈ x, Binary64Value a)
    (hy : ∀ a ∈ y, Binary64Value a) (hlen : x.length = y.length) :
    tcOzaki1CRD hopperF16F32 10 ss 191 x y = rne64 (dot x y) :=
  tcOzaki1CRD_eq h100F16_exactOn10 (by decide) ss (by decide) hx hy hlen

theorem a100F16_fp64CR10 (ss : List ℕ) {x y : List ℚ} (hx : ∀ a ∈ x, Binary64Value a)
    (hy : ∀ a ∈ y, Binary64Value a) (hlen : x.length = y.length) :
    tcOzaki1CRD ampereF16F32 10 ss 191 x y = rne64 (dot x y) :=
  tcOzaki1CRD_eq a100F16_exactOn10 (by decide) ss (by decide) hx hy hlen

theorem h100TF32Mma_fp64CR10 (ss : List ℕ) {x y : List ℚ} (hx : ∀ a ∈ x, Binary64Value a)
    (hy : ∀ a ∈ y, Binary64Value a) (hlen : x.length = y.length) :
    tcOzaki1CRD hopperTF32MmaF32 10 ss 191 x y = rne64 (dot x y) :=
  tcOzaki1CRD_eq h100TF32Mma_exactOn10 (by decide) ss (by decide) hx hy hlen

/-- **Correctly rounded binary32 on H100 fp16 with `10`-bit slices**: the exact fallback at up to
`26` slices (`26 · 11 > 277`). -/
theorem h100F16_fp32CR10 (ss : List ℕ) {x y : List ℚ} (hx : ∀ a ∈ x, Binary32Value a)
    (hy : ∀ a ∈ y, Binary32Value a) (hlen : x.length = y.length) :
    tcOzaki1CRL hopperF16F32 10 ss 26 x y = rne32Q (dot x y) :=
  tcOzaki1CRL_eq h100F16_exactOn10 (by decide) ss (by decide) hx hy hlen

/-- **FP64 emulation error on H100 fp16 with `10`-bit slices** for every `k`, and with six slices
(`slicesFor 10 53 = 6`) the slicing term is at most `2^-53 k max|x| max|y|`. -/
theorem h100F16_slices10 : slicesFor 10 53 = 6 ∧ (6 + 1) * 2 ^ (53 + 2) ≤ 2 ^ (6 * (10 + 1)) ∧
    slicesFor 11 53 = 5 ∧ slicesFor 10 24 = 3 ∧ slicesFor 11 24 = 3 ∧ slicesFor 8 53 = 7 ∧
    slicesFor 8 24 = 4 := by
  decide +kernel

end Ozaki.TC
