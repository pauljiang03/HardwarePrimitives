import TensorCore

/-! FP8 `mma.sync`: the correction on the interleaving experiment and on late `c`. -/

namespace TensorCoreTests.MmaSyncFP8

open TensorCore

/-- With the extra product in the second group, `mma.sync` returns `1`; the 576-bit TC-EFT of B200's
E5M2 block returns `1 + 2^-23`, the correctly rounded `1 + 2^-23`, from that output. -/
example : ∀ k, k < 32 → 2 ≤ k → 2 ≤ k % 4 →
    mmaSyncFP8 e5m2ToF16 0 (interleaveInput k) = some 0x3f800000 ∧
    EFMachine.tcEft .blackwellE5M2 ⟨interleaveInput k, 0⟩ 0x3f800000 = .ok (.scalar 0x3f800001) := by
  decide +kernel

/-- `c = 1` and three products `2^-24`: `mma.sync` is already correctly rounded here. -/
example : mmaSyncFP8 e5m2ToF16 0x3f800000 lateInput = some 0x3f800002 ∧
    EFMachine.tcEft .blackwellE5M2 ⟨lateInput, 0x3f800000⟩ 0x3f800002 = .ok (.scalar 0x3f800002) := by
  decide +kernel

/-- The datapath on the same inputs. -/
example : Datapath.mmaSyncFP8 e5m2ToF16 0 (interleaveInput 2) = some 0x3f800000 ∧
    Datapath.mmaSyncFP8 e5m2ToF16 0x3f800000 lateInput = some 0x3f800002 := by
  decide +kernel

end TensorCoreTests.MmaSyncFP8
