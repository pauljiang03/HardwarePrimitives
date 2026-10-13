import TensorCore.TC.MonotonicityRange
import TensorCoreTests.TC.Cases

/-! TC-EFT Theorems III.4 and III.5 on the three source FP16 variants, the Table III witnesses, and the witness ranges. -/

namespace TensorCore

def halfDecoded (e : ℤ) : Decoded := ⟨1024, e, 10⟩

/-- V100 family: any `K < 2^24` products `2^-12 · 2^-12`. -/
theorem nonmonotone_v100_family (K : ℕ) (hK : K < 2 ^ 24) :
    ∃ t t' : BlockTrace,
      evalBlock (⟨List.replicate K (0x0c00, 0x0c00), 0x3f800000⟩ :
        BlockInput (fp16Fp32Model K 0 none)) = .ok t ∧
      evalBlock (⟨List.replicate K (0x0c00, 0x0c00), 0x3f7fffff⟩ :
        BlockInput (fp16Fp32Model K 0 none)) = .ok t' ∧
      t.output.value = 1 ∧ (1 < t'.output.value ↔ 3 * 2 ^ 0 ≤ K) :=
  nonmonotone_encoded K 0 none (by simp) _ _ (halfDecoded (-12)) (halfDecoded (-12))
    (by show (classify fp16 0x0c00).finite = some _; decide +kernel)
    (by show (classify fp16 0x0c00).finite = some _; decide +kernel)
    (by decide +kernel) (by decide +kernel) hK

/-- Ampere family: one extra alignment bit, minimum alignment exponent `−132`, products `2^-12 · 2^-13`. -/
theorem nonmonotone_ampere_family (K : ℕ) (hK : K < 2 ^ 25) :
    ∃ t t' : BlockTrace,
      evalBlock (⟨List.replicate K (0x0c00, 0x0800), 0x3f800000⟩ :
        BlockInput (fp16Fp32Model K 1 (some (-132)))) = .ok t ∧
      evalBlock (⟨List.replicate K (0x0c00, 0x0800), 0x3f7fffff⟩ :
        BlockInput (fp16Fp32Model K 1 (some (-132)))) = .ok t' ∧
      t.output.value = 1 ∧ (1 < t'.output.value ↔ 3 * 2 ^ 1 ≤ K) :=
  nonmonotone_encoded K 1 (some (-132)) (by simp) _ _ (halfDecoded (-12)) (halfDecoded (-13))
    (by show (classify fp16 0x0c00).finite = some _; decide +kernel)
    (by show (classify fp16 0x0800).finite = some _; decide +kernel)
    (by decide +kernel) (by decide +kernel) hK

/-- Hopper family: two extra alignment bits, minimum alignment exponent `−133`, products `2^-12 · 2^-14`. -/
theorem nonmonotone_hopper_family (K : ℕ) (hK : K < 2 ^ 26) :
    ∃ t t' : BlockTrace,
      evalBlock (⟨List.replicate K (0x0c00, 0x0400), 0x3f800000⟩ :
        BlockInput (fp16Fp32Model K 2 (some (-133)))) = .ok t ∧
      evalBlock (⟨List.replicate K (0x0c00, 0x0400), 0x3f7fffff⟩ :
        BlockInput (fp16Fp32Model K 2 (some (-133)))) = .ok t' ∧
      t.output.value = 1 ∧ (1 < t'.output.value ↔ 3 * 2 ^ 2 ≤ K) :=
  nonmonotone_encoded K 2 (some (-133)) (by simp) _ _ (halfDecoded (-12)) (halfDecoded (-14))
    (by show (classify fp16 0x0c00).finite = some _; decide +kernel)
    (by show (classify fp16 0x0400).finite = some _; decide +kernel)
    (by decide +kernel) (by decide +kernel) hK


theorem nonmonotone_range_v100_family (K j : ℕ) (hK : K < 2 ^ 24) (hj1 : 1 ≤ j)
    (hj2 : j ≤ 2 ^ 23) :
    ∃ t : BlockTrace,
      evalBlock (⟨List.replicate K (0x0c00, 0x0c00), BitVec.ofNat 32 (0x3f800000 - j)⟩ :
        BlockInput (fp16Fp32Model K 0 none)) = .ok t ∧
      (1 < t.output.value ↔ j ≤ min (2 ^ 23) (K / 2 ^ 0 - 2)) ∧
      (j * 2 ^ 0 ≤ K →
        t.output.value = 1 + (((K - j * 2 ^ 0) / 2 ^ (0 + 1) : ℕ) : ℚ) * pow2 (-23)) ∧
      t.output.value ≤ 1 + (((K - 2 ^ 0) / 2 ^ (0 + 1) : ℕ) : ℚ) * pow2 (-23) :=
  nonmonotone_range_encoded K 0 j none (by simp) _ _ (halfDecoded (-12)) (halfDecoded (-12))
    (by show (classify fp16 0x0c00).finite = some _; decide +kernel)
    (by show (classify fp16 0x0c00).finite = some _; decide +kernel)
    (by decide +kernel) (by decide +kernel) hK hj1 hj2

/-- Ampere family, Theorem III.5: witnesses for `1 ≤ j ≤ min(2^23, ⌊K/2⌋ − 2)`. -/
theorem nonmonotone_range_ampere_family (K j : ℕ) (hK : K < 2 ^ 25) (hj1 : 1 ≤ j)
    (hj2 : j ≤ 2 ^ 23) :
    ∃ t : BlockTrace,
      evalBlock (⟨List.replicate K (0x0c00, 0x0800), BitVec.ofNat 32 (0x3f800000 - j)⟩ :
        BlockInput (fp16Fp32Model K 1 (some (-132)))) = .ok t ∧
      (1 < t.output.value ↔ j ≤ min (2 ^ 23) (K / 2 ^ 1 - 2)) ∧
      (j * 2 ^ 1 ≤ K →
        t.output.value = 1 + (((K - j * 2 ^ 1) / 2 ^ (1 + 1) : ℕ) : ℚ) * pow2 (-23)) ∧
      t.output.value ≤ 1 + (((K - 2 ^ 1) / 2 ^ (1 + 1) : ℕ) : ℚ) * pow2 (-23) :=
  nonmonotone_range_encoded K 1 j (some (-132)) (by simp) _ _ (halfDecoded (-12))
    (halfDecoded (-13))
    (by show (classify fp16 0x0c00).finite = some _; decide +kernel)
    (by show (classify fp16 0x0800).finite = some _; decide +kernel)
    (by decide +kernel) (by decide +kernel) hK hj1 hj2

/-- Hopper family, Theorem III.5: witnesses for `1 ≤ j ≤ min(2^23, ⌊K/4⌋ − 2)`. -/
theorem nonmonotone_range_hopper_family (K j : ℕ) (hK : K < 2 ^ 26) (hj1 : 1 ≤ j)
    (hj2 : j ≤ 2 ^ 23) :
    ∃ t : BlockTrace,
      evalBlock (⟨List.replicate K (0x0c00, 0x0400), BitVec.ofNat 32 (0x3f800000 - j)⟩ :
        BlockInput (fp16Fp32Model K 2 (some (-133)))) = .ok t ∧
      (1 < t.output.value ↔ j ≤ min (2 ^ 23) (K / 2 ^ 2 - 2)) ∧
      (j * 2 ^ 2 ≤ K →
        t.output.value = 1 + (((K - j * 2 ^ 2) / 2 ^ (2 + 1) : ℕ) : ℚ) * pow2 (-23)) ∧
      t.output.value ≤ 1 + (((K - 2 ^ 2) / 2 ^ (2 + 1) : ℕ) : ℚ) * pow2 (-23) :=
  nonmonotone_range_encoded K 2 j (some (-133)) (by simp) _ _ (halfDecoded (-12))
    (halfDecoded (-14))
    (by show (classify fp16 0x0c00).finite = some _; decide +kernel)
    (by show (classify fp16 0x0400).finite = some _; decide +kernel)
    (by decide +kernel) (by decide +kernel) hK hj1 hj2

namespace Regression

set_option maxRecDepth 16384
set_option maxHeartbeats 4000000

/-- TC-EFT Table III: the source FMA sizes `K = 4, 8, 16` all exceed `3·2^p`, and decreasing the accumulator from `3f800000` to `3f7fffff` raises the output to `3f800001`. -/
theorem nonmonotone_ampere_hopper_witnesses :
    outputBits (⟨List.replicate 8 (0x0c00, 0x0800), 0x3f800000⟩ : BlockInput ampereF16F32) =
      .ok 0x3f800000 ∧
    outputBits (⟨List.replicate 8 (0x0c00, 0x0800), 0x3f7fffff⟩ : BlockInput ampereF16F32) =
      .ok 0x3f800001 ∧
    outputBits (⟨List.replicate 16 (0x0c00, 0x0400), 0x3f800000⟩ : BlockInput hopperF16F32) =
      .ok 0x3f800000 ∧
    outputBits (⟨List.replicate 16 (0x0c00, 0x0400), 0x3f7fffff⟩ : BlockInput hopperF16F32) =
      .ok 0x3f800001 := by decide +kernel

/-- Below the threshold the perturbation is monotone: two V100 products (`K = 2 < 3`) leave the output at `1`, and eleven Hopper products (`K = 11 < 12`) do too. -/
theorem below_threshold_monotone :
    outputBits (⟨List.replicate 2 (0x0c00, 0x0c00), 0x3f7fffff⟩ :
      BlockInput (fp16Fp32Model 2 0 none)) = .ok 0x3f800000 ∧
    outputBits (⟨List.replicate 11 (0x0c00, 0x0400), 0x3f7fffff⟩ :
      BlockInput (fp16Fp32Model 11 2 (some (-133)))) = .ok 0x3f800000 := by decide +kernel

/-- Theorem III.5 witness ranges on the source FMA sizes: `J = min(2^23, ⌊K/2^p⌋ − 2) = 2` for V100 (`K = 4`), Ampere (`K = 8`), and Hopper (`K = 16`). -/
theorem range_witnesses :
    outputBits (⟨List.replicate 4 (0x0c00, 0x0c00), 0x3f7ffffe⟩ : BlockInput v100F16F32) =
      .ok 0x3f800001 ∧
    outputBits (⟨List.replicate 4 (0x0c00, 0x0c00), 0x3f7ffffd⟩ : BlockInput v100F16F32) =
      .ok 0x3f800000 ∧
    outputBits (⟨List.replicate 8 (0x0c00, 0x0800), 0x3f7ffffe⟩ : BlockInput ampereF16F32) =
      .ok 0x3f800001 ∧
    outputBits (⟨List.replicate 8 (0x0c00, 0x0800), 0x3f7ffffd⟩ : BlockInput ampereF16F32) =
      .ok 0x3f800000 ∧
    outputBits (⟨List.replicate 16 (0x0c00, 0x0400), 0x3f7ffffe⟩ : BlockInput hopperF16F32) =
      .ok 0x3f800001 ∧
    outputBits (⟨List.replicate 16 (0x0c00, 0x0400), 0x3f7ffffd⟩ : BlockInput hopperF16F32) =
      .ok 0x3f800000 := by decide +kernel

/-- The TC-EFT paper's `K = 5`, `p = 0` example: the largest output increase `2·2^-23` occurs at `j = 1`, the largest input decrease `3·2^-24` at `J = 3`, and `j = 4` is monotone. -/
theorem range_extrema_k5 :
    outputBits (⟨List.replicate 5 (0x0c00, 0x0c00), 0x3f7fffff⟩ :
      BlockInput (fp16Fp32Model 5 0 none)) = .ok 0x3f800002 ∧
    outputBits (⟨List.replicate 5 (0x0c00, 0x0c00), 0x3f7ffffd⟩ :
      BlockInput (fp16Fp32Model 5 0 none)) = .ok 0x3f800001 ∧
    outputBits (⟨List.replicate 5 (0x0c00, 0x0c00), 0x3f7ffffc⟩ :
      BlockInput (fp16Fp32Model 5 0 none)) = .ok 0x3f800000 := by decide +kernel

end Regression

end TensorCore
