import TensorCore.TC.FinalRounding
import TensorCoreTests.TC.Cases

namespace TensorCore.Regression

set_option maxRecDepth 16384
set_option maxHeartbeats 4000000

/-- Midpoints round to even in every format; truncation keeps the lower neighbor. -/
theorem binary_rounding_ties :
    (roundBinary fp16 .nearestEven (1 + 1 / 2048)).map BitVec.toNat = some 0x3c00 ∧
    (roundBinary fp16 .nearestEven (1 + 3 / 2048)).map BitVec.toNat = some 0x3c02 ∧
    (roundBinary fp16 .truncate (1 + 3 / 2048)).map BitVec.toNat = some 0x3c01 ∧
    (roundBinary bf16 .nearestEven (1 + 1 / 256)).map BitVec.toNat = some 0x3f80 ∧
    (roundBinary bf16 .nearestEven (1 + 3 / 256)).map BitVec.toNat = some 0x3f82 ∧
    (roundBinary tf19 .nearestEven (1 + 1 / 2048)).map BitVec.toNat = some 0x1fc00 ∧
    (roundBinary tf19 .truncate (-(1 + 3 / 2048))).map BitVec.toNat = some 0x5fc01 ∧
    (roundBinary fp64 .nearestEven (1 / 3)).map BitVec.toNat = some 0x3fd5555555555555 := by
  decide +kernel

theorem binary_rounding_boundaries :
    roundBinary fp16 .nearestEven 65520 = none ∧
    (roundBinary fp16 .nearestEven 65504).map BitVec.toNat = some 0x7bff ∧
    fp16.maxFinite = 65504 ∧
    (roundBinary fp16 .nearestEven (1 / 33554432)).map BitVec.toNat = some 0 ∧
    (roundBinary fp16 .truncate (1 / 33554432)).map BitVec.toNat = some 0 := by
  decide +kernel

theorem formats_wellFormed : fp16.WellFormed ∧ bf16.WellFormed ∧ tf19.WellFormed ∧ fp64.WellFormed := by
  decide

/-- Nearest-even and truncation correctness on the four formats of the source variants. -/
theorem fp16_rounding_correct (x : ℚ) (hr : absQ x ≤ fp16.maxFinite) :
    (∃ b, roundBinary fp16 .nearestEven x = some b ∧ NearestEven fp16 x b) ∧
    (∃ b, roundBinary fp16 .truncate x = some b ∧ Truncated fp16 x b) :=
  ⟨roundBinary_nearestEven_correct fp16 (by decide) x hr,
    roundBinary_truncate_correct fp16 (by decide) x hr⟩

theorem bf16_rounding_correct (x : ℚ) (hr : absQ x ≤ bf16.maxFinite) :
    (∃ b, roundBinary bf16 .nearestEven x = some b ∧ NearestEven bf16 x b) ∧
    (∃ b, roundBinary bf16 .truncate x = some b ∧ Truncated bf16 x b) :=
  ⟨roundBinary_nearestEven_correct bf16 (by decide) x hr,
    roundBinary_truncate_correct bf16 (by decide) x hr⟩

theorem tf19_rounding_correct (x : ℚ) (hr : absQ x ≤ tf19.maxFinite) :
    (∃ b, roundBinary tf19 .nearestEven x = some b ∧ NearestEven tf19 x b) ∧
    (∃ b, roundBinary tf19 .truncate x = some b ∧ Truncated tf19 x b) :=
  ⟨roundBinary_nearestEven_correct tf19 (by decide) x hr,
    roundBinary_truncate_correct tf19 (by decide) x hr⟩

theorem fp64_rounding_correct (x : ℚ) (hr : absQ x ≤ fp64.maxFinite) :
    (∃ b, roundBinary fp64 .nearestEven x = some b ∧ NearestEven fp64 x b) ∧
    (∃ b, roundBinary fp64 .truncate x = some b ∧ Truncated fp64 x b) :=
  ⟨roundBinary_nearestEven_correct fp64 (by decide) x hr,
    roundBinary_truncate_correct fp64 (by decide) x hr⟩

/-- Specializing generic binary rounding correctness to FP32 yields the FP32 rounding contract. -/
theorem fp32_generic_agrees (x : ℚ) (hr : absQ x ≤ maxFinite32) :
    ∃ b, round32 .nearestEven x = some b ∧ NearestEven32 x b := by
  have h := roundBinary_nearestEven_correct fp32 (by decide) x hr
  obtain ⟨b, hb, hc⟩ := h
  refine ⟨b, ?_, hc⟩
  rw [← roundBinary_fp32 .nearestEven]
  exact hb

end TensorCore.Regression
