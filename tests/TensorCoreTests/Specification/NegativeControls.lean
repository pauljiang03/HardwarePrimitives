import TensorCore.TC.Specification.Composition
import TensorCoreTests.TC.Cases

/-! Deliberately incorrect evaluators and encoded witnesses separating them from the independent Accurate Models specification. -/

namespace TensorCore.IndependentSpec.Controls

set_option maxRecDepth 16384
set_option maxHeartbeats 4000000

def normalized (t : Term) : Term :=
  if magnitude t.value ≥ (2 : ℚ) ^ (t.exponent + 1) then
    ⟨t.value, t.exponent + 1⟩ else t

def normalizedBits (p : Parameters) (x : Input p) : Option F32 := do
  let ts ← terms p x
  round32 .truncate (accumulated p (ts.map normalized))

def noEAlignMinBits (p : Parameters) (x : Input p) : Option F32 := do
  let ts ← terms p x
  round32 .truncate (accumulated { p with eAlignMin := none } ts)

/-- Incorrectly replace common-grid alignment by IEEE-style RTZ of each term. -/
def ieeeAlignmentBits (p : Parameters) (x : Input p) : Option F32 := do
  let ts ← terms p x
  let rounded ← ts.mapM fun t => do
    let b ← round32 .truncate t.value
    TensorCore.value32 b
  round32 .truncate (rounded.foldr (· + ·) 0)

theorem premature_normalization_detected :
    normalizedBits (parametersOf v100F16F32) (inputOf Regression.r1a) = some 0x40100000 ∧
    bits (parametersOf v100F16F32) (inputOf Regression.r1a) = some 0x40100001 := by
  constructor
  · decide +kernel
  · rw [← evalBlock_eq_spec]
    decide +kernel

theorem ieee_alignment_detected :
    ieeeAlignmentBits (parametersOf v100F16F32) (inputOf Regression.r1b) = some 0x40100001 ∧
    bits (parametersOf v100F16F32) (inputOf Regression.r1b) = some 0x40100000 := by
  constructor
  · decide +kernel
  · rw [← evalBlock_eq_spec]
    decide +kernel

/-- A100: p1 = sum_{j=150..155} 2^-j, p2 = 2^-156, p3 = p4 = 2^-157. -/
def ampereEAlignMinInput : BlockInput a100BF16F32 :=
  ⟨[(0x1a7c, 0x1a00), (0x1880, 0x1880), (0x1880, 0x1800), (0x1880, 0x1800)] ++
    List.replicate 4 (0, 0), 0⟩

/-- Hopper's finer grid needs a separate witness at its own floor. -/
def hopperEAlignMinInput : BlockInput hopperBF16F32 :=
  ⟨[(0x1a7f, 0x1a00), (0x1800, 0x1800), (0x1800, 0x1780), (0x1800, 0x1780)] ++
    List.replicate 12 (0, 0), 0⟩

theorem ampere_eAlignMin_removal_detected :
    noEAlignMinBits (parametersOf a100BF16F32) (inputOf ampereEAlignMinInput) = some 1 ∧
    bits (parametersOf a100BF16F32) (inputOf ampereEAlignMinInput) = some 0 := by
  constructor
  · decide +kernel
  · rw [← evalBlock_eq_spec]
    decide +kernel

theorem hopper_eAlignMin_removal_detected :
    noEAlignMinBits (parametersOf hopperBF16F32) (inputOf hopperEAlignMinInput) = some 1 ∧
    bits (parametersOf hopperBF16F32) (inputOf hopperEAlignMinInput) = some 0 := by
  constructor
  · decide +kernel
  · rw [← evalBlock_eq_spec]
    decide +kernel

def cancelGroup : List (F16 × F16) := (0xbc00, 0x3c00) :: List.replicate 7 (0, 0)
def tinyGroup : List (F16 × F16) := (1, 0x3c00) :: List.replicate 7 (0, 0)

theorem group_reversal_detected :
    lastBits (parametersOf ampereF16F32) 0x3f800000 [cancelGroup, tinyGroup] = some 0x33800000 ∧
    lastBits (parametersOf ampereF16F32) 0x3f800000 [tinyGroup, cancelGroup] = some 0 := by
  constructor
  · exact (schedule_last_eq_spec ampereF16F32 0x3f800000 [cancelGroup, tinyGroup]).symm.trans
      (by decide +kernel)
  · exact (schedule_last_eq_spec ampereF16F32 0x3f800000 [tinyGroup, cancelGroup]).symm.trans
      (by decide +kernel)

/-- Value equality alone cannot distinguish these two encodings; the sign clause can. -/
theorem signed_zero_is_required :
    Rounds (-(2 : ℚ) ^ (-150 : ℤ)) 0x80000000 ∧
    ¬ Rounds (-(2 : ℚ) ^ (-150 : ℤ)) 0 := by
  constructor
  · apply round32_rounds
    decide +kernel
  · intro h
    have hs := h.1
    have hx : (-(2 : ℚ) ^ (-150 : ℤ)) < 0 := by decide +kernel
    simp [hx] at hs

theorem all_zero_and_nonfinite_boundaries :
    bits (parametersOf v100F16F32)
      (inputOf (⟨List.replicate 4 (0x8000, 0), 0x80000000⟩ : BlockInput v100F16F32)) = some 0 ∧
    bits (parametersOf v100F16F32)
      (inputOf (⟨List.replicate 4 (0x7c00, 0), 0⟩ : BlockInput v100F16F32)) = none := by
  constructor <;> rw [← evalBlock_eq_spec] <;> decide +kernel

end TensorCore.IndependentSpec.Controls
