import TensorCore.Kernels.EFT.Native

namespace TensorCore.Regression.NativeEFT

open EFMachine

set_option exponentiation.threshold 1024

theorem signed_zeros : add32WithLean 0x80000000 0x80000000 = some 0 := by decide +kernel

theorem zero_then_negative : add32WithLean 0 0xbf800000 = some 0xbf800000 := by decide +kernel

theorem cancellation : add32WithLean 0x3f800000 0xbf800000 = some 0 := by decide +kernel

theorem subnormal_boundary : add32WithLean 0x007fffff 1 = some 0x00800000 := by decide +kernel

theorem tie_even : add32WithLean 0x3f800000 0x33800000 = some 0x3f800000 := by decide +kernel

theorem tie_odd : add32WithLean 0x3f800001 0x33800000 = some 0x3f800002 := by decide +kernel

/-- Each addition rounds separately. -/
theorem every_step_rounds :
    naiveSum32WithLeanFrom 0 [0x3f800000, 0x33800000, 0x33800000] = some 0x3f800000 := by
  decide +kernel

theorem order_loses_one :
    naiveSum32WithLeanFrom 0 [0x4b800000, 0x3f800000, 0xcb800000] = some 0 := by decide +kernel

theorem order_keeps_one :
    naiveSum32WithLeanFrom 0 [0x4b800000, 0xcb800000, 0x3f800000] = some 0x3f800000 := by
  decide +kernel

theorem exact_residual_sum :
    naiveSum32WithLeanFrom 0 [0x3f800000, 0xbf000000, 0x3e800000] = some 0x3f400000 := by
  decide +kernel

/-- An exact sum just above the largest finite value is rejected. -/
theorem exact_range_rejection : add32WithLean 0x7f7fffff 0x3f800000 = none := by decide +kernel

theorem intermediate_range_rejection :
    naiveSum32WithLeanFrom 0 [0x7f7fffff, 0x7f7fffff, 0xff7fffff] = none := by decide +kernel

theorem nonfinite_rejection : add32WithLean 0 0x7f800000 = none := by decide +kernel

theorem nan_rejection : add32WithLean 0x7fc00007 0 = none := by decide +kernel

theorem single_v100_corrected :
    tcEftWithLean .v100F16
      ⟨[(0x3e00, 0x3d00), (0x3e00, 0x3d00), (0x3e00, 0x3d00), (0x3e00, 0x3d00)],
        0x3f7fffff⟩ 0x4107ffff = .ok (.scalar 0x41080000) := by decide +kernel

end TensorCore.Regression.NativeEFT
