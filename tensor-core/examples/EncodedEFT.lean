import TensorCore.EFT.Encoded
import TensorCore.TC.EncodedMonotonicity

open TensorCore

-- `D` is a supplied FP32 result, not a rerun of the Tensor Core invocation.
example : tcEftEncoded (⟨List.replicate 4 (0x3e00, 0x3d00), 0x3f7fffff⟩ :
    BlockInput v100F16F32) 0x4107ffff = .ok (.consolidated (.scalar 0x41080000)) := by
  decide +kernel

example {p : Model} {x : BlockInput p} {D b : F32} {r : EncodedEFTResult}
    (h : tcEftEncoded x D = .ok r) (hb : r.bits = some b) :
    ∃ z, exactDot x = some z ∧ NearestEven32 z b := tcEftEncoded_correct h hb

example {p : Model} {ps : List (p.Word × p.Word)} {decoded : List (Decoded × Decoded)}
    (hp : prepareProducts p ps = some decoded) (hm : MonotoneInAccumulator p decoded) :
    MonotoneInEncodedAccumulator p ps := monotoneInAccumulator_encoded hp hm
