import TensorCore.TC.Composition
import TensorCore.Numerics.CorrectRounding

/-! Correctly rounded results recovered from traces. -/

namespace TensorCore

/-- Exact residual recovery followed by mathematically nearest-even rounding to FP32. -/
theorem corrected_correct (t : BlockTrace) (hr : absQ t.block.exactDot ≤ maxFinite32) :
    ∃ b, t.corrected = some b ∧ NearestEven32 t.block.exactDot b := by
  rw [corrected_eq_round_exactDot]
  exact round32_nearestEven_correct _ hr

/-- Correct rounding of the independently defined ideal encoded-input sum. -/
theorem evalBlock_corrected_correct {p : Model} {x : BlockInput p} {t : BlockTrace}
    {z : ℚ} (h : evalBlock x = .ok t) (hz : exactDot x = some z)
    (hr : absQ z ≤ maxFinite32) :
    ∃ b, t.corrected = some b ∧ NearestEven32 z b := by
  simp only [exactDot, evalBlock_prepared h, Option.map_some] at hz
  have he := Option.some.inj hz
  rw [← he] at hr ⊢
  exact corrected_correct t hr

def recoveredSchedule (initial : Finite32) (ts : List BlockTrace) : ℚ :=
  (lastOutput initial ts).value + sumQ (ts.map BlockTrace.residual)

def correctedSchedule (initial : Finite32) (ts : List BlockTrace) : Option F32 :=
  round32 .nearestEven (recoveredSchedule initial ts)

/-- The exact ledger is consolidated before the single final rounding. -/
theorem correctedSchedule_correct (initial : Finite32) (ts : List BlockTrace)
    (chain : EncodedChain initial ts)
    (hr : absQ (initial.value + sumQ (ts.map fun t => t.block.exactProducts)) ≤ maxFinite32) :
    ∃ b, correctedSchedule initial ts = some b ∧
      NearestEven32 (initial.value + sumQ (ts.map fun t => t.block.exactProducts)) b := by
  unfold correctedSchedule recoveredSchedule
  rw [← encoded_trace_ledger initial ts chain]
  exact round32_nearestEven_correct _ hr

/-- Every successful executable schedule has a correctly rounded correction when its exact ideal sum is in the specified finite range. -/
theorem runBlocks_corrected_correct (p : Model) (initial : Finite32)
    (ps : List (List (p.Word × p.Word))) (ts : List BlockTrace)
    (h : runBlocks p initial.bits ps = .ok ts)
    (hr : absQ (initial.value + sumQ (ts.map fun t => t.block.exactProducts)) ≤ maxFinite32) :
    ∃ b, correctedSchedule initial ts = some b ∧
      NearestEven32 (initial.value + sumQ (ts.map fun t => t.block.exactProducts)) b :=
  correctedSchedule_correct initial ts (runBlocks_chain p initial ps ts h) hr

end TensorCore
