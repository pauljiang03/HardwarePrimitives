import OzakiTC.Ozaki2Choice
import OzakiTC.CRRules

/-! # Ozaki-I against Ozaki-II with the correct-rounding margin, per Tensor Core path

`OzakiTC.SplitChoice` and `OzakiTC.Ozaki2Choice` chose configurations for an error of
`2^-t · k · max|x| · max|y|`. Correct rounding needs the bound small against the result's spacing
whatever `k`, so the rules of `Ozaki.SliceRuleCR` add `⌈log₂ k⌉` bits: at `k = 1024`, `t = 63` for
FP64 and `34` for binary32 (`clog2 1024 = 10`). The cost functions are the same (`SliceRun.cost`,
`SliceRun.cost2` at the larger `t`), and so is the candidate set, every candidate exact for every
length. With the margin, Ozaki-I needs `6` slices of `11` bits (`21` products) for FP64 and Ozaki-II
`12` moduli; the two-pass engine still never wins.

## Results (inner dimension `k = 1024`, Tensor Core blocks)

| path | Ozaki-I FP64 | Ozaki-II FP64 | Ozaki-I binary32 | Ozaki-II binary32 |
| --- | --- | --- | --- | --- |
| V100 fp16 | `b = 11`, 5376 | `b = 11`, 3072 | 2560 | 1792 |
| A100 fp16 | `b = 10`, 3584 | `b = 10`, 1664 | 1280 | 1024 |
| A100 bf16 | `b = 8`, 4608 | `b = 8`, 2048 | 1920 | 1280 |
| A100 tf32 | `b = 11`, 5376 | `b = 11`, 3072 | 2560 | 1792 |
| H100 fp16 | `b = 10`, 1792 | `b = 10`, 832 | 640 | 512 |
| H100 bf16 | `b = 8`, 2304 | `b = 8`, 1024 | 960 | 640 |
| H100 tf32 (wmma) | `b = 11`, 5376 | `b = 11`, 3072 | 2560 | 1792 |
| H100 tf32 (mma) | `b = 10`, 3584 | `b = 10`, 1664 | 1280 | 1024 |

With the margin, Ozaki-II costs `1.75` to `2.25` times fewer blocks than Ozaki-I for FP64, and
`1.25` to `1.5` times fewer for binary32, on every path; without it the two tied for binary32. The
margin costs Ozaki-I more than Ozaki-II: one more slice (`15 → 21` products for FP64) against one
more modulus (`11 → 12`). As before, the counts leave out the work off the engine, notably
Ozaki-II's reconstruction with integers of about `2P + log₂ k` bits, here `P = t + 12`.

Every basis the moduli rule produces is valid (`Ozaki.moduliBasis_valid_all`), so the chosen
configurations need no kernel check of their bases (`h100F16_fp64CR2_margin`). -/

open TensorCore

namespace Ozaki.TC

/-- The moduli counts with the margin at `k = 1024`. -/
theorem moduliForCR_table :
    moduliForCR 8 53 1024 = 16 ∧ moduliForCR 10 53 1024 = 13 ∧ moduliForCR 11 53 1024 = 12 ∧
    moduliForCR 8 24 1024 = 10 ∧ moduliForCR 10 24 1024 = 8 ∧ moduliForCR 11 24 1024 = 7 ∧
    clog2 1024 = 10 := by
  decide +kernel

theorem v100F16_bestCR :
    best v100F16F32 11 63 1024 = some (.splitK 11) ∧ (SliceRun.splitK 11).cost 4 63 1024 = 5376 ∧
    best2 v100F16F32 11 63 1024 = some (.splitK 11) ∧ (SliceRun.splitK 11).cost2 4 63 1024 = 3072 ∧
    best v100F16F32 11 34 1024 = some (.splitK 11) ∧ (SliceRun.splitK 11).cost 4 34 1024 = 2560 ∧
    best2 v100F16F32 11 34 1024 = some (.splitK 11) ∧ (SliceRun.splitK 11).cost2 4 34 1024 = 1792 := by
  decide +kernel

theorem a100F16_bestCR :
    best ampereF16F32 11 63 1024 = some (.splitK 10) ∧ (SliceRun.splitK 10).cost 8 63 1024 = 3584 ∧
    best2 ampereF16F32 11 63 1024 = some (.splitK 10) ∧ (SliceRun.splitK 10).cost2 8 63 1024 = 1664 ∧
    best ampereF16F32 11 34 1024 = some (.splitK 10) ∧ (SliceRun.splitK 10).cost 8 34 1024 = 1280 ∧
    best2 ampereF16F32 11 34 1024 = some (.splitK 10) ∧ (SliceRun.splitK 10).cost2 8 34 1024 = 1024 := by
  decide +kernel

theorem a100BF16_bestCR :
    best a100BF16F32 8 63 1024 = some (.splitK 8) ∧ (SliceRun.splitK 8).cost 8 63 1024 = 4608 ∧
    best2 a100BF16F32 8 63 1024 = some (.splitK 8) ∧ (SliceRun.splitK 8).cost2 8 63 1024 = 2048 ∧
    best a100BF16F32 8 34 1024 = some (.splitK 8) ∧ (SliceRun.splitK 8).cost 8 34 1024 = 1920 ∧
    best2 a100BF16F32 8 34 1024 = some (.splitK 8) ∧ (SliceRun.splitK 8).cost2 8 34 1024 = 1280 := by
  decide +kernel

theorem a100TF32_bestCR :
    best a100TF32F32 11 63 1024 = some (.splitK 11) ∧ (SliceRun.splitK 11).cost 4 63 1024 = 5376 ∧
    best2 a100TF32F32 11 63 1024 = some (.splitK 11) ∧ (SliceRun.splitK 11).cost2 4 63 1024 = 3072 := by
  decide +kernel

/-- **H100 fp16 with the margin**: Ozaki-II with `13` moduli at most `2048` costs `832` blocks for
FP64 against `1792` for Ozaki-I; for binary32 `512` against `640`. -/
theorem h100F16_bestCR :
    best hopperF16F32 11 63 1024 = some (.splitK 10) ∧ (SliceRun.splitK 10).cost 16 63 1024 = 1792 ∧
    best2 hopperF16F32 11 63 1024 = some (.splitK 10) ∧ (SliceRun.splitK 10).cost2 16 63 1024 = 832 ∧
    best hopperF16F32 11 34 1024 = some (.splitK 10) ∧ (SliceRun.splitK 10).cost 16 34 1024 = 640 ∧
    best2 hopperF16F32 11 34 1024 = some (.splitK 10) ∧ (SliceRun.splitK 10).cost2 16 34 1024 = 512 := by
  decide +kernel

theorem h100BF16_bestCR :
    best hopperBF16F32 8 63 1024 = some (.splitK 8) ∧ (SliceRun.splitK 8).cost 16 63 1024 = 2304 ∧
    best2 hopperBF16F32 8 63 1024 = some (.splitK 8) ∧ (SliceRun.splitK 8).cost2 16 63 1024 = 1024 ∧
    best hopperBF16F32 8 34 1024 = some (.splitK 8) ∧ (SliceRun.splitK 8).cost 16 34 1024 = 960 ∧
    best2 hopperBF16F32 8 34 1024 = some (.splitK 8) ∧ (SliceRun.splitK 8).cost2 16 34 1024 = 640 := by
  decide +kernel

theorem h100TF32Wmma_bestCR :
    best hopperTF32WmmaF32 11 63 1024 = some (.splitK 11) ∧
      (SliceRun.splitK 11).cost 4 63 1024 = 5376 ∧
    best2 hopperTF32WmmaF32 11 63 1024 = some (.splitK 11) ∧
      (SliceRun.splitK 11).cost2 4 63 1024 = 3072 := by
  decide +kernel

theorem h100TF32Mma_bestCR :
    best hopperTF32MmaF32 11 63 1024 = some (.splitK 10) ∧
      (SliceRun.splitK 10).cost 8 63 1024 = 3584 ∧
    best2 hopperTF32MmaF32 11 63 1024 = some (.splitK 10) ∧
      (SliceRun.splitK 10).cost2 8 63 1024 = 1664 := by
  decide +kernel

/-- **Correctly rounded FP64 on H100 fp16 by Ozaki-II with the margin**: `13` moduli at most `2048`,
`P = 65`, inner dimension up to `1024`; the basis is valid by `moduliBasis_valid_all`, with no
kernel check. -/
theorem h100F16_fp64CR2_margin {x y : List ℚ} (hx : ∀ a ∈ x, Binary64Value a)
    (hy : ∀ a ∈ y, Binary64Value a) (hlen : x.length = y.length) (hk : x.length ≤ 1024) :
    tcOzaki2CRD hopperF16F32 [(moduliBasis 10 13, 65)] 10 191 x y = rne64 (dot x y) := by
  refine tcOzaki2CRD_eq h100F16_exactOn10 (by decide) (by decide) ?_ hx hy hlen
  intro c hc
  rw [List.mem_singleton.mp hc]
  refine ⟨moduliBasis_valid_all 10 13, moduliBasis_le 10 13, ?_⟩
  have h := moduliForCR_spec (b := 10) (t := 53) (k := 1024) (by rw [moduliForCR_table.2.1]; decide) hk
  rw [moduliForCR_table.2.1, moduliForCR_table.2.2.2.2.2.2] at h
  exact h

end Ozaki.TC
