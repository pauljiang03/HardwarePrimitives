import TensorCore.TC.StageResiduals

namespace TensorCore.Regression

abbrev V100Input := BlockInput v100F16F32

def r1a : V100Input := ⟨[(0x3e00, 0x3e00), (0x1000, 0x0c00),
  (0x1000, 0x0c00), (0, 0)], 0⟩
def r1b : V100Input := ⟨[(0x3c00, 0x4080), (0x1000, 0x0c00),
  (0x1000, 0x0c00), (0, 0)], 0⟩
def r2 : V100Input := ⟨[(0x3e00, 0x3e00), (0x3c01, 0x3001),
  (0x3c01, 0x3001), (0x3c00, 0x3000)], 0x3e000000⟩
def r3 : V100Input := ⟨List.replicate 4 (0x3e00, 0x3d00), 0x3f7fffff⟩

/-- A projection of the evaluator's trace; `c` is term zero. -/
structure Snapshot where
  bits : ℕ
  alignExp : Option ℤ
  qExponent : ℤ
  exponents : List ℤ
  alignedBits : List ℤ
  ideal : ℚ
  accumulator : ℚ
  alignmentResiduals : List ℚ
  outputResidual : ℚ
  residual : ℚ
  correctedBits : Option ℕ
  deriving Repr, DecidableEq

def snapshot {p : Model} (x : BlockInput p) : Except ModelError Snapshot := do
  let t ← evalBlock x
  return ⟨t.output.bits.toNat, t.block.alignExp, t.block.alignGridExponent,
    t.block.products.map (fun (a, b) => (denormalizedMul a b).exponent),
    t.block.alignedBits, t.block.exactDot, t.block.accumulator,
    t.block.alignmentResiduals, t.outputResidual, t.residual,
    t.corrected.map BitVec.toNat⟩

def outputBits {p : Model} (x : BlockInput p) : Except ModelError ℕ :=
  (evalBlock x).map fun t => t.output.bits.toNat

set_option maxRecDepth 16384
set_option maxHeartbeats 2000000

theorem r1_equal_ideal : exactDot r1a = exactDot r1b := by decide +kernel
theorem r1_equal_product_values :
    ((prepare r1a).map fun b => b.products.map fun (a, b) => a.value * b.value) =
    ((prepare r1b).map fun b => b.products.map fun (a, b) => a.value * b.value) := by decide +kernel
theorem r1_first_output : outputBits r1a = .ok 0x40100001 := by decide +kernel
theorem r1_second_output : outputBits r1b = .ok 0x40100000 := by decide +kernel
theorem r1_factorization_changes_output : outputBits r1a ≠ outputBits r1b := by decide +kernel

theorem r1a_trace : snapshot r1a = .ok
    ⟨0x40100001, some 0, -23, [0, -23, -23, 0], [0, 18874368, 1, 1, 0],
      9437185 / 4194304, 9437185 / 4194304, [0, 0, 0, 0, 0], 0, 0,
      some 0x40100001⟩ := by decide +kernel

theorem r1b_trace : snapshot r1b = .ok
    ⟨0x40100000, some 1, -22, [1, -23, -23, 0], [0, 9437184, 0, 0, 0],
      9437185 / 4194304, 9 / 4, [0, 0, 1 / 8388608, 1 / 8388608, 0],
      0, 1 / 4194304, some 0x40100001⟩ := by decide +kernel

theorem r2_trace : snapshot r2 = .ok
    ⟨0x40300801, some 0, -23, [0, -3, -3, -3],
      [1048576, 18874368, 1050625, 1050625, 1048576],
      11536385 / 4194304, 11536385 / 4194304, [0, 0, 0, 0, 0], 0, 0,
      some 0x40300801⟩ := by decide +kernel

theorem r2_correction_unchanged :
    ((evalV100 r2).map fun t => (t.residual, t.corrected)) =
      .ok (0, some 0x40300801) := by decide +kernel

theorem r3_trace : snapshot r3 = .ok
    ⟨0x4107ffff, some 0, -23, [0, 0, 0, 0],
      [8388607, 15728640, 15728640, 15728640, 15728640],
      142606335 / 16777216, 71303167 / 8388608,
      [1 / 16777216, 0, 0, 0, 0], 7 / 8388608, 15 / 16777216,
      some 0x41080000⟩ := by decide +kernel

theorem r4_binade_asymmetry :
    round32 .nearestEven (1 - 3 * pow2 (-25)) = some 0x3f7ffffe := by decide +kernel

theorem r4_cancellation :
    round32 .nearestEven (1 - (1 - pow2 (-24))) = some 0x33800000 := by decide +kernel

theorem r4_signed_truncation :
    truncGrid (1 - 1 / 2) 0 = 0 ∧
    1 + truncGrid (-1 / 2) 0 = 1 := by decide +kernel

theorem r4_even_tie :
    round32 .nearestEven (1 + pow2 (-24)) = some 0x3f800000 := by decide +kernel
theorem r4_odd_tie :
    round32 .nearestEven (1 + 3 * pow2 (-24)) = some 0x3f800002 := by decide +kernel
theorem r4_binade_carry :
    round32 .nearestEven (2 - pow2 (-24)) = some 0x40000000 := by decide +kernel
theorem r4_subnormal_boundary :
    round32 .nearestEven (pow2 (-126) - pow2 (-150)) = some 0x00800000 := by decide +kernel
theorem r4_zero_tie :
    round32 .nearestEven (pow2 (-150)) = some 0 := by decide +kernel
theorem r4_negative_zero :
    round32 .nearestEven (-pow2 (-150)) = some 0x80000000 := by decide +kernel

theorem zero_block :
    outputBits (⟨List.replicate 4 (0, 0), 0x80000000⟩ : V100Input) = .ok 0 := by decide +kernel
theorem subnormal_multiplicand :
    outputBits (⟨[(1, 0x3c00), (0, 0), (0, 0), (0, 0)], 0⟩ : V100Input) =
      .ok 0x33800000 := by decide +kernel
theorem subnormal_accumulator :
    outputBits (⟨List.replicate 4 (0, 0), 1⟩ : V100Input) = .ok 1 := by decide +kernel
theorem nonfinite_rejected :
    outputBits (⟨List.replicate 4 (0x7c00, 0), 0⟩ : V100Input) =
      .error .nonfiniteInput := by decide +kernel
/-- The accepted domain remains the explicitly specified finite range. -/
theorem out_of_range_rejected :
    round32 .truncate (maxFinite32 + 1) = none ∧
    round32 .truncate (pow2 128) = none ∧
    round32 .nearestEven (maxFinite32 + pow2 102) = none ∧
    round32 .nearestEven (maxFinite32 + pow2 103) = none ∧
    round32 .nearestEven (-(maxFinite32 + pow2 103)) = none := by decide +kernel

theorem wrong_shape_rejected :
    outputBits (⟨[], 0⟩ : V100Input) = .error .wrongProductCount := by decide +kernel

/-- TC-EFT III.4: one concrete V100 witness. -/
theorem v100_nonmonotonicity_witness :
    outputBits (⟨List.replicate 4 (0x0c00, 0x0c00), 0x3f800000⟩ : V100Input) = .ok 0x3f800000 ∧
    outputBits (⟨List.replicate 4 (0x0c00, 0x0c00), 0x3f7fffff⟩ : V100Input) = .ok 0x3f800001 := by
  decide +kernel

end TensorCore.Regression
