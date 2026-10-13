import TensorCore.TC.Canonical
import TensorCore.TC.Composition

namespace TensorCore.Regression

set_option maxRecDepth 16384
set_option maxHeartbeats 4000000

theorem zero_product_canonical :
    invocationBits (p := fp16Fp32Invocation 0 0 none) ⟨[], 0x3f800000⟩ = some 0x3f800000 ∧
    invocationBits (p := fp16Fp32Invocation 0 2 (some (-133))) ⟨[], 1⟩ = some 1 ∧
    evalInvocation (p := fp16Fp32Invocation 0 0 none) ⟨[], 0x7fc00000⟩ =
      .error .nonfiniteOrInvalidEncoding ∧
    evalInvocation (p := fp16Fp32Invocation 0 0 none) ⟨[(0, 0)], 0⟩ =
      .error .wrongProductCount := by decide +kernel

theorem fused_requires_one_product :
    ¬ ({v100Invocation with nfma := 0, accumulation := .fused} : InvocationSpec).Valid ∧
    ¬ ({v100Invocation with nfma := 2, accumulation := .fused} : InvocationSpec).Valid := by
  decide +kernel

theorem finite_range_rounding_policy :
    round32 .truncate (maxFinite32 + 1) = none ∧
    round32 .nearestEven (maxFinite32 + 1) = none ∧
    round32Core .truncate (maxFinite32 + 1) = some 0x7f7fffff := by decide +kernel

end TensorCore.Regression
