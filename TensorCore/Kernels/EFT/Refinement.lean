import TensorCore.Kernels.EFT.Cost
import TensorCore.EFT.Encoded

/-! The 576-bit TC-EFT returns the same bits as the reference version. -/

namespace TensorCore.EFMachine

/-- Bit refinement of the encoded-interface reference algorithm on every accepted finite input. -/
theorem tcEft_agrees {variant : Variant} {x : BlockInput variant.model} {D : F32} {t : BlockTrace}
    (ht : prepareEncodedEFT x D = .ok t) :
    (tcEft variant x D).map Result.bits = .ok t.tcEft.bits := by
  obtain ⟨hlen, hx, hD⟩ := prepareEncodedEFT_spec ht
  have hs : TensorCore.exactDot x = some t.block.exactDot := by simp [TensorCore.exactDot, hx]
  have hd : TensorCore.value32 D = some t.output.value := by
    unfold finite32 at hD
    split at hD
    · contradiction
    · rename_i d hd
      have hv := congrArg Finite32.value (Option.some.inj hD)
      simpa [TensorCore.value32, hd, Finite32.value] using congrArg some hv
  obtain ⟨r, hr, hb⟩ := tcEft_correct hlen hs hd
  rw [hr, Except.map, hb, tcEft_bits_eq_round]

/-- Agreement when `D` is the model's own output word. -/
theorem tcEft_of_evalBlock {variant : Variant} {x : BlockInput variant.model} {t : BlockTrace}
    (ht : evalBlock x = .ok t) :
    (tcEft variant x t.output.bits).map Result.bits = .ok t.tcEft.bits :=
  tcEft_agrees (prepareEncodedEFT_of_evalBlock ht)

end TensorCore.EFMachine
