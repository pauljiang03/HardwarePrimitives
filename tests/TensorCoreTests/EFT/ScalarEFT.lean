import TensorCore.EFT.Scalar
import TensorCore.EFT.ExtractionGrid
import TensorCore.EFT.Encoded
import TensorCoreTests.EFT.EFT

/-! Kernel regressions for generic scalar consolidation: subnormals, precision and range boundaries, the bit-span condition, and the FP64-to-FP32 double-rounding trap. -/

namespace TensorCore.Regression

set_option maxRecDepth 16384
set_option maxHeartbeats 4000000

theorem scalar64_subnormal_sum :
    naiveSumBinary fp64 [pow2 (-1074), -pow2 (-1074), 2 * pow2 (-1074)] =
      some (2 * pow2 (-1074)) ∧
    naiveSumBinary fp64 [] = some 0 := by decide +kernel

/-- The 53-bit format preserves a residual that 24-bit additions lose under cancellation. -/
theorem scalar64_preserves_low_component :
    naiveSumBinary fp64 [1, pow2 (-51), -1] = some (pow2 (-51)) ∧
    naiveSum32 [1, pow2 (-51), -1] = some 0 := by decide +kernel

/-- Coarser than emax−52 is allowed when the actual coefficient fits the finite range. -/
theorem scalar64_coarse_grid : naiveSumBinary fp64 [pow2 1023] = some (pow2 1023) := by
  have h := naiveSum64_exact 1023 (by decide) [1] (by decide)
    (by decide +kernel)
  simpa [magnitudeSum, sumZ] using h

/-- Final cancellation does not justify overflowing an earlier prefix. -/
theorem scalar64_prefix_overflow :
    naiveSumBinary fp64 [fp64.maxFinite, fp64.maxFinite, -fp64.maxFinite] = none := by
  decide +kernel

theorem scalar64_finite_boundary :
    binaryAdd fp64 fp64.maxFinite 0 = some fp64.maxFinite ∧
    binaryAdd fp64 fp64.maxFinite (pow2 971) = none := by decide +kernel

/-- The coefficient bound can fail even though the signed final sum fits. -/
theorem scalar_coefficient_boundary :
    magnitudeSum [2 ^ 52 - 1, 2 ^ 52] < 2 ^ 53 ∧
    ¬ magnitudeSum [2 ^ 52, -(2 ^ 52)] < 2 ^ 53 ∧
    ceilLog2 0 = 0 ∧ ceilLog2 1 = 0 ∧ ceilLog2 8 = 3 ∧ ceilLog2 9 = 4 := by
  decide +kernel

/-- Exercise the TC-EFT paper's bit-span theorem at equality, with a signed list. -/
theorem scalar_bitSpan_bound : magnitudeSum [7, -7, 7, -7] < 2 ^ 5 := by
  apply bitSpan_coefficient_bound [7, -7, 7, -7] 2 0 5
  · intro z hz
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
    rcases hz with h | h | h | h <;> subst z <;> decide +kernel
  · decide +kernel

/-- D = 1 and S = 1 + 2^-24 + 2^-53. -/
def scalar64DoubleRound : V100Input :=
  ⟨[(0x3c00, 0x3c00), (0x0001, 0x3c00), (0, 0), (0, 0)], 0x25000000⟩

theorem scalar64_corrects_midpoint :
    ((evalBlock scalar64DoubleRound).map fun t =>
      (t.output.bits.toNat, t.scalarPredicate, t.scalarPredicateIn fp64,
        t.scalarCorrectedIn fp64 |>.map BitVec.toNat)) =
      .ok (0x3f800000, false, true, some 0x3f800001) := by decide +kernel

theorem scalar64_double_rounding_incorrect :
    (round32 .nearestEven (1 + pow2 (-24) + pow2 (-53))).map BitVec.toNat = some 0x3f800001 ∧
    (((roundBinary fp64 .nearestEven (1 + pow2 (-24) + pow2 (-53))).bind (binaryValue fp64)).bind
      (round32 .nearestEven)).map BitVec.toNat = some 0x3f800000 := by decide +kernel

/-- More precision still does not authorize unsafe summation on the subnormal witness. -/
theorem scalar64_subnormal_guard_rejects :
    ((evalBlock subnormalAccumulator).map fun t =>
      (t.scalarPredicateIn fp64, t.scalarCorrectedIn fp64)) = .ok (false, none) := by
  decide +kernel

theorem scalar_generic_invalid_format_rejects :
    ((evalBlock r3).map fun t => t.scalarCorrectedIn ⟨0, 8, 127⟩) = .ok none := by
  decide +kernel

def inputGridBlock : BlockInput v100F16F32 := ⟨List.replicate 4 (0x0c00, 0x0c00), 0x3f800000⟩

/-- Four products `2^-24` with `C = 1` and `D = 1 + 2^-22`. -/
def inputGridTrace : BlockTrace :=
  match prepareEncodedEFT inputGridBlock 0x3f800002 with
  | .ok t => t
  | .error _ => ⟨⟨v100F16F32, [], ⟨0, 0, 0⟩⟩, ⟨0, ⟨0, 0, 0⟩, by decide +kernel⟩⟩

theorem onGrid_of_den {x q : ℚ} (hq : q ≠ 0) (h : (x / q).den = 1) : ∃ z : ℤ, x = (z : ℚ) * q :=
  have hn : ((x / q).num : ℚ) = x / q := Rat.ext rfl h.symm
  ⟨(x / q).num, by rw [hn, Rat.div_mul_cancel hq]⟩

/-- The FP32 input-grid hypotheses hold together on a concrete block. -/
theorem inputGrid_fp32_witness :
    let t := inputGridTrace
    let g := t.defaultExtraction
    (-149 : ℤ) ≤ -24 ∧ (-24 : ℤ) ≤ 104 ∧ (-24 : ℤ) ≤ g.exponent ∧
    (∀ x ∈ t.block.terms, ∃ z : ℤ, x.value = (z : ℚ) * pow2 (-24)) ∧
    t.block.terms.length * (2 ^ (g.exponent - (-24)).toNat - 1) < 2 ^ 24 ∧
    representableBinary fp32 g.overlap = true ∧ representableBinary fp32 g.retainedSum = true ∧
    absQ t.block.exactDot ≤ maxFinite32 := by
  have hgrid : (inputGridTrace.block.terms.all fun x => (x.value / pow2 (-24)).den == 1) = true := by
    decide +kernel
  refine ⟨by decide, by decide, by decide +kernel, ?_, by decide +kernel, by decide +kernel,
    by decide +kernel, by decide +kernel⟩
  intro x hx
  exact onGrid_of_den (Rat.ne_of_gt (pow2_pos _))
    (by simpa using List.all_eq_true.mp hgrid x hx)

/-- On that block the theorem yields the scalar predicate. -/
example : inputGridTrace.defaultExtraction.scalarPredicate fp32 (-24) = true := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := inputGrid_fp32_witness
  exact ExtractionGrid.inputGrid_scalarPredicate_fp32 _ _ h1 h2 h3 h4 h5 h6 h7 h8

end TensorCore.Regression
