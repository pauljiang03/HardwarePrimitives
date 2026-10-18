import TensorCore.EFT.Extraction
import TensorCoreTests.EFT.MachineSplit
import TensorCoreTests.TC.Cases

namespace TensorCore.Regression

structure EftSnapshot where
  extractionExponent : ℤ
  lowParts : List ℚ
  overlap : ℚ
  scalarPredicate : Bool
  scalarBits : Option ℕ
  scalarTcEftBits : Option ℕ
  deriving Repr, DecidableEq

def eftSnapshot {p : Model} (x : BlockInput p) : Except ModelError EftSnapshot := do
  let t ← evalBlock x
  return ⟨t.extractionExponent, t.lowParts, t.overlap, t.scalarPredicate,
    t.scalarCorrectedUnchecked.map BitVec.toNat, t.scalarTcEft.map BitVec.toNat⟩

set_option maxRecDepth 16384
set_option maxHeartbeats 4000000

/-- R2: nonzero coarse overlap with zero total residual (TC-EFT IV-A). -/
theorem r2_eft : eftSnapshot r2 = .ok
    ⟨-22, [0, 0, 1 / 8388608, 1 / 8388608, 0], 1 / 4194304, true,
      some 0x40300801, some 0x40300801⟩ := by decide +kernel

/-- R3: the scalar branch corrects `4107ffff` to `41080000`. -/
theorem r3_eft : eftSnapshot r3 = .ok
    ⟨-20, [15 / 16777216, 0, 0, 0, 0], 0, true, some 0x41080000, some 0x41080000⟩ := by
  decide +kernel

/-- The TC-EFT §V-D cancellation example. -/
def cancellationExample : V100Input :=
  ⟨[(0xd83d, 0x5a03), (0x5061, 0x5722), (0x444c, 0x49d5), (0x5810, 0x5976)], 0x4416cfe5⟩

theorem cancellation_eft :
    outputBits cancellationExample = .ok 0x449fbe50 ∧
    eftSnapshot cancellationExample = .ok
      ⟨-9, [5 / 16384, 0, 0, 15 / 8192, 0], 0, true, some 0x449fbe62, some 0x449fbe62⟩ := by
  decide +kernel

/-- Low parts that exceed the 24-bit coefficient bound on the common grid. -/
def supportOverflow : V100Input :=
  ⟨[(0x5bff, 0x37ff), (0x5bff, 0x37ff), (0x5bff, 0x37ff), (1, 1)], 0x4e800000⟩

theorem predicate_rejected :
    outputBits supportOverflow = .ok 0x4e800000 ∧
    ((eftSnapshot supportOverflow).map fun s => (s.scalarPredicate, s.scalarTcEftBits)) =
      .ok (false, none) ∧
    ((snapshot supportOverflow).map fun s => s.correctedBits) = .ok (some 0x4e800003) := by
  decide +kernel

def subnormalAccumulator : V100Input :=
  ⟨[(0x3c00, 0x3c00), (0x0001, 0x3c00), (0, 0), (0, 0)], 0x00000001⟩

theorem subnormal_accumulator_rejected :
    outputBits subnormalAccumulator = .ok 0x3f800000 ∧
    ((eftSnapshot subnormalAccumulator).map fun s =>
      (s.extractionExponent, s.scalarPredicate, s.scalarBits, s.scalarTcEftBits)) =
      .ok (-23, false, some 0x3f800000, none) ∧
    ((snapshot subnormalAccumulator).map fun s => s.correctedBits) = .ok (some 0x3f800001) := by
  decide +kernel

/-- Both public names enforce the guard on the subnormal counterexample. -/
theorem scalar_public_subnormal_rejected :
    ((evalBlock subnormalAccumulator).map fun t =>
      (t.scalarCorrected, t.scalarTcEft)) = .ok (none, none) := by decide +kernel

/-- A correction that changes the output remains available through the safe helper. -/
theorem scalar_public_r3 :
    ((evalBlock r3).map fun t => t.scalarCorrected.map BitVec.toNat) =
      .ok (some 0x41080000) := by decide +kernel

/-- Seed 20260906, V100 sample 250: the unchecked branch breaks a correctly rounded output. -/
def broadFiniteCounterexample : V100Input :=
  ⟨[(0x210f, 0x4553), (0x5a5b, 0x9753), (0x9a0b, 0xd06e), (0xd68c, 0x1eb6)],
    0x238ac5ec⟩

theorem broad_finite_unchecked_incorrect :
    ((evalBlock broadFiniteCounterexample).map fun t =>
      (t.output.bits.toNat, t.scalarCorrectedUnchecked.map BitVec.toNat,
        t.corrected.map BitVec.toNat, t.scalarCorrected)) =
      .ok (3211041529, some 3211041530, some 3211041529, none) := by decide +kernel

end TensorCore.Regression
