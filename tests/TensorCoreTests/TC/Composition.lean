import TensorCore.TC.Correction
import TensorCoreTests.TC.Cases

namespace TensorCore.Regression

/-- The second block cancels 17/2, exposing the first block's lost residual. -/
def cancelEightAndHalf : List (v100F16F32.Word × v100F16F32.Word) :=
  [(0xc000, 0x4400), (0xb800, 0x3c00), (0, 0), (0, 0)]

def twoBlockSummary : Except ModelError (List ℕ × ℚ × ℚ) := do
  let ts ← runV100 r3.c [r3.products, cancelEightAndHalf]
  let last := ts.getLast?.map (fun t => t.output.value)
  return (ts.map (fun t => t.output.bits.toNat),
    sumQ (ts.map BlockTrace.residual), last.getD 0 + sumQ (ts.map BlockTrace.residual))

set_option maxRecDepth 16384
set_option maxHeartbeats 2000000

theorem two_block_cancellation :
    twoBlockSummary = .ok ([0x4107ffff, 0xb5800000],
      15 / 16777216, -1 / 16777216) := by decide +kernel

def twoBlockCorrection : Except ModelError (Option F32) := do
  let ts ← runV100 r3.c [r3.products, cancelEightAndHalf]
  let some initial := finite32 r3.c | .error .nonfiniteInput
  return correctedSchedule initial ts

theorem two_block_corrected : twoBlockCorrection = .ok (some 0xb3800000) := by
  decide +kernel

/-- Midpoint distances behind the handoff correction. -/
theorem r4_midpoint_distances :
    absQ ((1 - 3 * pow2 (-25)) - (1 - pow2 (-23))) = pow2 (-25) ∧
    absQ ((1 - 3 * pow2 (-25)) - (1 - pow2 (-24))) = pow2 (-25) := by decide +kernel

end TensorCore.Regression
