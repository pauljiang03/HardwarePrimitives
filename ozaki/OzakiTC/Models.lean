import OzakiTC.MatrixMultiplier

/-! # The eight GPU variants

Exact matrix multipliers on every Tensor Core variant of `TensorCore`. The slice width is set by
what the operand format holds: `b = 11` for fp16 and tf32 (`2^11 = 2048` and every smaller integer
are exact), `b = 8` for bf16. Every variant has `F ≥ 23` and `2b ≤ F`.

| variant | `K` | `F` | `b` |
| --- | --- | --- | --- |
| V100 fp16 | 4 | 23 | 11 |
| A100 fp16 | 8 | 24 | 11 |
| A100 bf16 | 8 | 24 | 8 |
| A100 tf32 | 4 | 24 | 11 |
| H100 fp16 | 16 | 25 | 11 |
| H100 bf16 | 16 | 25 | 8 |
| H100 tf32 (wmma) | 4 | 25 | 11 |
| H100 tf32 (mma) | 8 | 25 | 11 |

The exactness bound `Σ|aᵢbᵢ| ≤ 2^24` is the same on every variant: it is set by the binary32 output.
For `11`-bit slices it allows inner dimension `k ≤ 4`, a single V100 block; the A100 and H100 fp16
variants take block FMAs of 8 and 16 products, whose products can exceed it (`OzakiTC.Limits`). -/

open TensorCore

namespace Ozaki.TC

theorem eAlignMin_ok (f : ℤ) (F : ℤ) (h : f ≤ F) : ∀ g ∈ some f, g ≤ F := by
  intro g hg; cases hg; exact h

theorem v100_exactOn : (tcMultiplier v100F16F32).ExactOn 11 (2 ^ 24) :=
  tcMultiplier_exactOn ⟨by decide, by decide, (fun _ hf => by cases hf), by decide⟩
    ⟨by decide, by decide, by decide, by decide⟩ (by decide)

theorem a100F16_exactOn : (tcMultiplier ampereF16F32).ExactOn 11 (2 ^ 24) :=
  tcMultiplier_exactOn ⟨by decide, by decide, eAlignMin_ok _ _ (by decide), by decide⟩
    ⟨by decide, by decide, by decide, by decide⟩ (by decide)

theorem a100BF16_exactOn : (tcMultiplier a100BF16F32).ExactOn 8 (2 ^ 24) :=
  tcMultiplier_exactOn ⟨by decide, by decide, eAlignMin_ok _ _ (by decide), by decide⟩
    ⟨by decide, by decide, by decide, by decide⟩ (by decide)

theorem a100TF32_exactOn : (tcMultiplier a100TF32F32).ExactOn 11 (2 ^ 24) :=
  tcMultiplier_exactOn ⟨by decide, by decide, eAlignMin_ok _ _ (by decide), by decide⟩
    ⟨by decide, by decide, by decide, by decide⟩ (by decide)

theorem h100F16_exactOn : (tcMultiplier hopperF16F32).ExactOn 11 (2 ^ 24) :=
  tcMultiplier_exactOn ⟨by decide, by decide, eAlignMin_ok _ _ (by decide), by decide⟩
    ⟨by decide, by decide, by decide, by decide⟩ (by decide)

theorem h100BF16_exactOn : (tcMultiplier hopperBF16F32).ExactOn 8 (2 ^ 24) :=
  tcMultiplier_exactOn ⟨by decide, by decide, eAlignMin_ok _ _ (by decide), by decide⟩
    ⟨by decide, by decide, by decide, by decide⟩ (by decide)

theorem h100TF32Wmma_exactOn : (tcMultiplier hopperTF32WmmaF32).ExactOn 11 (2 ^ 24) :=
  tcMultiplier_exactOn ⟨by decide, by decide, eAlignMin_ok _ _ (by decide), by decide⟩
    ⟨by decide, by decide, by decide, by decide⟩ (by decide)

theorem h100TF32Mma_exactOn : (tcMultiplier hopperTF32MmaF32).ExactOn 11 (2 ^ 24) :=
  tcMultiplier_exactOn ⟨by decide, by decide, eAlignMin_ok _ _ (by decide), by decide⟩
    ⟨by decide, by decide, by decide, by decide⟩ (by decide)

end Ozaki.TC
