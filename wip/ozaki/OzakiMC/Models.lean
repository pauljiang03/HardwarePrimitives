import OzakiMC.MatrixMultiplier

/-! # The matrix-core variants

Exact matrix multipliers on the variants of `MatrixCore` whose operand formats hold the slices. The
slice width is bounded by what the format holds: `b ≤ 11` for fp16 and XF32, `b ≤ 8` for bf16, and
`b ≤ 24` for the binary32 SFMA. The exactness bound `Σ|aᵢbᵢ| ≤ 2^24` is the same on every variant:
it is set by the binary32 output.

| variant | `N_FMA` | configuration | `b` |
| --- | --- | --- | --- |
| SFMA (CDNA 1, 2, 3) fp32 | 1 | `correct_rounding` | ≤ 24 |
| CDNA 1 fp16 | 4 | `correct_rounding` | ≤ 11 |
| CDNA 1 bf16 | 2 | `correct_rounding` | ≤ 8 |
| CDNA 2 fp16 | 4 | `pair_wise_sum` | ≤ 11 |
| CDNA 2 bf16 | 2 | `pair_wise_sum` | ≤ 8 |
| CDNA 2 bf16 `_1k` | 4 | `pair_wise_sum` | ≤ 8 |
| CDNA 3 fp16 | 8 | `global_alignment` | ≤ 11 |
| CDNA 3 bf16 | 8 | `global_alignment` | ≤ 8 |
| CDNA 3 XF32 | 4 | `global_alignment` | ≤ 11 |

The fp8 variants of CDNA 3 (`odd_even_grouping`) are not covered. -/

open MatrixCore

namespace Ozaki.MC

/-- A model whose matrix core is exact on `b`-bit slices: an exact configuration, operand
formats with small subnormals that hold every `b`-bit integer, and a nonempty block. -/
structure ExactMultiplier (P : Model) (b : ℕ) : Prop where
  config : ExactConfig P
  subA : smallSubnormals P.a
  subB : smallSubnormals P.b
  nfma : 0 < P.nfma
  encA : EncodesInts P.a b
  encB : EncodesInts P.b b

theorem ExactMultiplier.exactOn {P : Model} {b : ℕ} (h : ExactMultiplier P b) :
    (mcMultiplier P).ExactOn b (2 ^ 24) :=
  mcMultiplier_exactOn h.config h.subA h.subB h.nfma h.encA h.encB

theorem EncodesInts.mono {i : InputFormat} {b b' : ℕ} (h : EncodesInts i b) (hb : b' ≤ b) :
    EncodesInts i b' := fun z hz => h z (Nat.le_trans hz (Nat.pow_le_pow_right (by decide) hb))

theorem binary16_encodesInts {b : ℕ} (hb : b ≤ 11) : EncodesInts (.packed fp16) b :=
  packed_encodesInts fp16 (by decide) (by decide) (by decide) hb

theorem bfloat16_encodesInts {b : ℕ} (hb : b ≤ 8) : EncodesInts (.packed bf16) b :=
  packed_encodesInts bf16 (by decide) (by decide) (by decide) hb

theorem binary32_encodesInts {b : ℕ} (hb : b ≤ 24) : EncodesInts (.packed fp32) b :=
  packed_encodesInts fp32 (by decide) (by decide) (by decide) hb

theorem xf32_encodesInts_le {b : ℕ} (hb : b ≤ 11) : EncodesInts .xf32 b :=
  xf32_encodesInts.mono hb

theorem binary16_small : smallSubnormals (.packed fp16) := by
  show fp16.emin ≤ 0; decide
theorem bfloat16_small : smallSubnormals (.packed bf16) := by
  show bf16.emin ≤ 0; decide
theorem binary32_small : smallSubnormals (.packed fp32) := by
  show fp32.emin ≤ 0; decide

theorem cdna3_config (P : Model) (hacc : P.accumulation = .globalAlignment) (hn : P.padding = 1)
    (hl : P.late = {}) (hc : P.cZeroExp = some (-126)) : ExactConfig P :=
  Or.inr (Or.inr ⟨hacc, by omega, hl, hc⟩)

theorem sfmaF32_exactMultiplier {b : ℕ} (hb : b ≤ 24) : ExactMultiplier sfmaF32 b :=
  ⟨Or.inl rfl, binary32_small, binary32_small, by decide, binary32_encodesInts hb,
    binary32_encodesInts hb⟩

theorem cdna1F16_exactMultiplier {b : ℕ} (hb : b ≤ 11) : ExactMultiplier cdna1F16 b :=
  ⟨Or.inl rfl, binary16_small, binary16_small, by decide, binary16_encodesInts hb,
    binary16_encodesInts hb⟩

theorem cdna1BF16_exactMultiplier {b : ℕ} (hb : b ≤ 8) : ExactMultiplier cdna1BF16 b :=
  ⟨Or.inl rfl, bfloat16_small, bfloat16_small, by decide, bfloat16_encodesInts hb,
    bfloat16_encodesInts hb⟩

theorem cdna2F16_exactMultiplier {b : ℕ} (hb : b ≤ 11) : ExactMultiplier cdna2F16 b :=
  ⟨Or.inr (Or.inl rfl), binary16_small, binary16_small, by decide, binary16_encodesInts hb,
    binary16_encodesInts hb⟩

theorem cdna2BF16_exactMultiplier {b : ℕ} (hb : b ≤ 8) : ExactMultiplier cdna2BF16 b :=
  ⟨Or.inr (Or.inl rfl), bfloat16_small, bfloat16_small, by decide, bfloat16_encodesInts hb,
    bfloat16_encodesInts hb⟩

theorem cdna2BF16_1k_exactMultiplier {b : ℕ} (hb : b ≤ 8) : ExactMultiplier cdna2BF16_1k b :=
  ⟨Or.inr (Or.inl rfl), bfloat16_small, bfloat16_small, by decide, bfloat16_encodesInts hb,
    bfloat16_encodesInts hb⟩

theorem cdna3F16_exactMultiplier {b : ℕ} (hb : b ≤ 11) : ExactMultiplier cdna3F16 b :=
  ⟨cdna3_config _ rfl rfl rfl rfl, binary16_small, binary16_small, by decide,
    binary16_encodesInts hb, binary16_encodesInts hb⟩

theorem cdna3BF16_exactMultiplier {b : ℕ} (hb : b ≤ 8) : ExactMultiplier cdna3BF16 b :=
  ⟨cdna3_config _ rfl rfl rfl rfl, bfloat16_small, bfloat16_small, by decide,
    bfloat16_encodesInts hb, bfloat16_encodesInts hb⟩

theorem cdna3XF32_exactMultiplier {b : ℕ} (hb : b ≤ 11) : ExactMultiplier cdna3XF32 b :=
  ⟨cdna3_config _ rfl rfl rfl rfl, trivial, trivial, by decide, xf32_encodesInts_le hb,
    xf32_encodesInts_le hb⟩

end Ozaki.MC
