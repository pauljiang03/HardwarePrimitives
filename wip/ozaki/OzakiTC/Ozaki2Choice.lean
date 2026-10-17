import OzakiTC.SplitChoice
import Ozaki.ModuliRule

/-! # Choosing the configuration of Ozaki-II per Tensor Core variant, and Ozaki-I against Ozaki-II

Ozaki-II runs one product on the matrix multiplier per modulus. With `b`-bit residues (moduli at
most `2^(b+1)`) the configurations of the matrix multiplier are those of Ozaki-I
(`OzakiTC.SplitChoice`): split-K with chunks of `chunkLen b`, or two passes over full block FMAs,
every one exact for every length (`candidates_exact`). For a target of `t` bits the moduli rule
`moduliFor b t k` takes `P = t + 2` and the fewest greedy coprime moduli at most `2^(b+1)` whose
product exceeds `2 k 2^(2P)` (`Ozaki.moduliFor_spec`); then Ozaki-II's truncation term is at most
`2^-t · k · max|x| · max|y|`, the target of Ozaki-I's slice rule. The cost of a configuration is
`moduliFor b t k · blocks`, in Tensor Core blocks, against Ozaki-I's `s(s+1)/2 · blocks`.

**The cost counts model blocks only.** It leaves out the work off the matrix multiplier, which
differs between the schemes: Ozaki-II computes residues and a Chinese-remainder reconstruction with
integers of `2P + log₂ k + 1` bits; Ozaki-I splits and adds exact slice products. It also leaves out
the extra moduli correct rounding may need, since Ozaki-II carries no margin (see
`OzakiTC.Correct`).

## Results (inner dimension `k = 1024`)

| variant | FP64: Ozaki-II best | moduli | blocks | Ozaki-I best blocks | binary32: Ozaki-II blocks | Ozaki-I blocks |
| --- | --- | --- | --- | --- | --- | --- |
| V100 fp16 | `b = 11`, split-K | 11 | 2816 | 3840 | 1536 | 1536 |
| A100 fp16 | `b = 10`, split-K | 12 | 1536 | 2688 | 768 | 768 |
| A100 bf16 | `b = 8`, split-K | 14 | 1792 | 3584 | 1024 | 1280 |
| A100 tf32 | `b = 11`, split-K | 11 | 2816 | 3840 | 1536 | 1536 |
| H100 fp16 | `b = 10`, split-K | 12 | 768 | 1344 | 384 | 384 |
| H100 bf16 | `b = 8`, split-K | 14 | 896 | 1792 | 512 | 640 |
| H100 tf32 (wmma) | `b = 11`, split-K | 11 | 2816 | 3840 | 1536 | 1536 |
| H100 tf32 (mma) | `b = 10`, split-K | 12 | 1536 | 2688 | 768 | 768 |

For FP64, Ozaki-II needs `11` to `14` residue products where Ozaki-I needs `15` to `28` slice
products, so it costs `1.4` to `2` times fewer blocks on every variant. For binary32 the counts are
close (`6` moduli against `6` slice products for `10`- and `11`-bit residues), and the two tie
except on bf16, where Ozaki-II's `8` moduli beat Ozaki-I's `10` products. As for Ozaki-I, `10`-bit
residues filling a whole block FMA win wherever a block FMA holds more than four products, and two
passes never win. -/

open TensorCore

namespace Ozaki.TC

/-- **The cost of Ozaki-II for `t` bits**: `moduliFor b t k` residue products, each `blocks`. -/
def SliceRun.cost2 (K t k : ℕ) (r : SliceRun) : ℕ := moduliFor r.width t k * r.blocks K k

/-- A configuration is feasible for Ozaki-II when some moduli meet the target (`moduliFor > 0`):
narrow residues have too few coprime moduli below `2^(b+1)`. -/
def SliceRun.feasible2 (t k : ℕ) (r : SliceRun) : Bool := 0 < moduliFor r.width t k

/-- The cheapest feasible candidate for Ozaki-II; the first in `candidates` order on a tie. -/
def best2 (p : Model) (bmax t k : ℕ) : Option SliceRun :=
  ((candidates p bmax).filter (SliceRun.feasible2 t k)).foldl (fun acc r => match acc with
    | none => some r
    | some a => if r.cost2 p.nfma t k < a.cost2 p.nfma t k then some r else some a) none

/-- **Every candidate is exact for Ozaki-II**: its matrix multiplier is exact on vectors of every
length, its moduli are at most `2^(b+1)`, and they meet the reconstruction condition for every
length up to `k`. -/
theorem ozaki2Candidates_ok {p : Model} {bmax : ℕ}
    (hfloor : ∀ f ∈ p.eAlignMin, f ≤ p.alignMantissaBits) (hwide : 23 ≤ p.alignMantissaBits)
    (hemin : 1 - p.input.bias ≤ 1) (hh : HoldsInts p bmax) (hK : 0 < p.nfma)
    (hout : 23 ≤ p.outputMantissaBits) {t k : ℕ} :
    ∀ r ∈ candidates p bmax, (∀ B, (r.multiplier p).ExactOn r.width B) ∧
      (∀ m ∈ (moduliBasis r.width (moduliFor r.width t k)).moduli, m ≤ 2 ^ (r.width + 1)) ∧
      (0 < moduliFor r.width t k → ∀ L ≤ k,
        2 * L * (2 ^ (t + 2) * 2 ^ (t + 2)) < (moduliBasis r.width (moduliFor r.width t k)).modulus) :=
  fun r hr => ⟨candidates_exact hfloor hwide hemin hh hK hout r hr, moduliBasis_le _ _,
    fun hn _ hL => moduliFor_spec hn hL⟩

/-- The moduli counts and the validity of the bases at `k = 1024`, for the widths compared here. -/
theorem moduliFor_table :
    moduliFor 8 53 1024 = 14 ∧ moduliFor 10 53 1024 = 12 ∧ moduliFor 11 53 1024 = 11 ∧
    moduliFor 8 24 1024 = 8 ∧ moduliFor 10 24 1024 = 6 ∧ moduliFor 11 24 1024 = 6 := by
  decide +kernel

theorem moduliBasis_valid :
    (moduliBasis 8 14).Valid ∧ (moduliBasis 10 12).Valid ∧ (moduliBasis 11 11).Valid ∧
    (moduliBasis 8 8).Valid ∧ (moduliBasis 10 6).Valid ∧ (moduliBasis 11 6).Valid := by
  decide +kernel

/-! ## The best configuration per variant (`k = 1024`) -/

theorem v100F16_best2 :
    best2 v100F16F32 11 53 1024 = some (.splitK 11) ∧ (SliceRun.splitK 11).cost2 4 53 1024 = 2816 ∧
      (SliceRun.splitK 11).cost 4 53 1024 = 3840 ∧
    best2 v100F16F32 11 24 1024 = some (.splitK 11) ∧ (SliceRun.splitK 11).cost2 4 24 1024 = 1536 := by
  decide +kernel

theorem a100F16_best2 :
    best2 ampereF16F32 11 53 1024 = some (.splitK 10) ∧ (SliceRun.splitK 10).cost2 8 53 1024 = 1536 ∧
      (SliceRun.splitK 10).cost 8 53 1024 = 2688 ∧ (SliceRun.twoPass 11).cost2 8 53 1024 = 2816 ∧
    best2 ampereF16F32 11 24 1024 = some (.splitK 10) ∧ (SliceRun.splitK 10).cost2 8 24 1024 = 768 := by
  decide +kernel

theorem a100BF16_best2 :
    best2 a100BF16F32 8 53 1024 = some (.splitK 8) ∧ (SliceRun.splitK 8).cost2 8 53 1024 = 1792 ∧
      (SliceRun.splitK 8).cost 8 53 1024 = 3584 ∧
    best2 a100BF16F32 8 24 1024 = some (.splitK 8) ∧ (SliceRun.splitK 8).cost2 8 24 1024 = 1024 := by
  decide +kernel

theorem a100TF32_best2 :
    best2 a100TF32F32 11 53 1024 = some (.splitK 11) ∧ (SliceRun.splitK 11).cost2 4 53 1024 = 2816 ∧
    best2 a100TF32F32 11 24 1024 = some (.splitK 11) ∧ (SliceRun.splitK 11).cost2 4 24 1024 = 1536 := by
  decide +kernel

/-- **H100 fp16**: Ozaki-II with `12` moduli at most `2048` (`10`-bit residues in full block FMAs of
sixteen) costs `768` blocks for FP64, against `1344` for Ozaki-I's best and `1408` for `11`-bit
residues with two passes. -/
theorem h100F16_best2 :
    best2 hopperF16F32 11 53 1024 = some (.splitK 10) ∧ (SliceRun.splitK 10).cost2 16 53 1024 = 768 ∧
      (SliceRun.splitK 10).cost 16 53 1024 = 1344 ∧ (SliceRun.twoPass 11).cost2 16 53 1024 = 1408 ∧
    best2 hopperF16F32 11 24 1024 = some (.splitK 10) ∧ (SliceRun.splitK 10).cost2 16 24 1024 = 384 ∧
      (SliceRun.splitK 10).cost 16 24 1024 = 384 := by
  decide +kernel

theorem h100BF16_best2 :
    best2 hopperBF16F32 8 53 1024 = some (.splitK 8) ∧ (SliceRun.splitK 8).cost2 16 53 1024 = 896 ∧
    best2 hopperBF16F32 8 24 1024 = some (.splitK 8) ∧ (SliceRun.splitK 8).cost2 16 24 1024 = 512 := by
  decide +kernel

theorem h100TF32Wmma_best2 :
    best2 hopperTF32WmmaF32 11 53 1024 = some (.splitK 11) ∧
      (SliceRun.splitK 11).cost2 4 53 1024 = 2816 ∧
    best2 hopperTF32WmmaF32 11 24 1024 = some (.splitK 11) ∧
      (SliceRun.splitK 11).cost2 4 24 1024 = 1536 := by
  decide +kernel

theorem h100TF32Mma_best2 :
    best2 hopperTF32MmaF32 11 53 1024 = some (.splitK 10) ∧
      (SliceRun.splitK 10).cost2 8 53 1024 = 1536 ∧
    best2 hopperTF32MmaF32 11 24 1024 = some (.splitK 10) ∧
      (SliceRun.splitK 10).cost2 8 24 1024 = 768 := by
  decide +kernel

/-! ## The chosen configurations, correctly rounded

For inner dimension up to `1024` the chosen moduli meet the reconstruction condition, so correctly
rounded FP64 Ozaki-II (`tcOzaki2CRD`) with them is the round to nearest of `x · y`. -/

theorem moduliFor_cond {b t n : ℕ} (h : moduliFor b t 1024 = n) (hn : 0 < n) {L : ℕ}
    (hL : L ≤ 1024) : 2 * L * (2 ^ (t + 2) * 2 ^ (t + 2)) < (moduliBasis b n).modulus := by
  subst h; exact moduliFor_spec hn hL

/-- **Correctly rounded FP64 on H100 fp16 by Ozaki-II with the cheapest configuration**: `12` moduli
at most `2048`, `P = 55`, `10`-bit residues, inner dimension up to `1024`. -/
theorem h100F16_fp64CR2 {x y : List ℚ} (hx : ∀ a ∈ x, Binary64Value a)
    (hy : ∀ a ∈ y, Binary64Value a) (hlen : x.length = y.length) (hk : x.length ≤ 1024) :
    tcOzaki2CRD hopperF16F32 [(moduliBasis 10 12, 55)] 10 191 x y = rne64 (dot x y) := by
  refine tcOzaki2CRD_eq h100F16_exactOn10 (by decide) (by decide) ?_ hx hy hlen
  intro c hc
  rw [List.mem_singleton.mp hc]
  exact ⟨moduliBasis_valid.2.1, moduliBasis_le 10 12,
    moduliFor_cond (b := 10) (t := 53) moduliFor_table.2.1 (by decide) hk⟩

theorem a100F16_fp64CR2 {x y : List ℚ} (hx : ∀ a ∈ x, Binary64Value a)
    (hy : ∀ a ∈ y, Binary64Value a) (hlen : x.length = y.length) (hk : x.length ≤ 1024) :
    tcOzaki2CRD ampereF16F32 [(moduliBasis 10 12, 55)] 10 191 x y = rne64 (dot x y) := by
  refine tcOzaki2CRD_eq a100F16_exactOn10 (by decide) (by decide) ?_ hx hy hlen
  intro c hc
  rw [List.mem_singleton.mp hc]
  exact ⟨moduliBasis_valid.2.1, moduliBasis_le 10 12,
    moduliFor_cond (b := 10) (t := 53) moduliFor_table.2.1 (by decide) hk⟩

/-- **Correctly rounded FP64 on V100 fp16 by Ozaki-II**: `11` moduli at most `4096`. -/
theorem v100F16_fp64CR2 {x y : List ℚ} (hx : ∀ a ∈ x, Binary64Value a)
    (hy : ∀ a ∈ y, Binary64Value a) (hlen : x.length = y.length) (hk : x.length ≤ 1024) :
    tcOzaki2CRD v100F16F32 [(moduliBasis 11 11, 55)] 11 175 x y = rne64 (dot x y) := by
  refine tcOzaki2CRD_eq v100_exactOn (by decide) (by decide) ?_ hx hy hlen
  intro c hc
  rw [List.mem_singleton.mp hc]
  exact ⟨moduliBasis_valid.2.2.1, moduliBasis_le 11 11,
    moduliFor_cond (b := 11) (t := 53) moduliFor_table.2.2.1 (by decide) hk⟩

/-- **Correctly rounded FP64 on A100 bf16 by Ozaki-II**: `14` moduli at most `512`. -/
theorem a100BF16_fp64CR2 {x y : List ℚ} (hx : ∀ a ∈ x, Binary64Value a)
    (hy : ∀ a ∈ y, Binary64Value a) (hlen : x.length = y.length) (hk : x.length ≤ 1024) :
    tcOzaki2CRD a100BF16F32 [(moduliBasis 8 14, 55)] 8 234 x y = rne64 (dot x y) := by
  refine tcOzaki2CRD_eq a100BF16_exactOn (by decide) (by decide) ?_ hx hy hlen
  intro c hc
  rw [List.mem_singleton.mp hc]
  exact ⟨moduliBasis_valid.1, moduliBasis_le 8 14,
    moduliFor_cond (b := 8) (t := 53) moduliFor_table.1 (by decide) hk⟩

end Ozaki.TC
