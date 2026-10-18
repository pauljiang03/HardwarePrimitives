import TensorCore.Kernels.EFT.Extraction

/-! Values of bounded FP32 conversions and additions. -/

namespace TensorCore.EFMachine

set_option exponentiation.threshold 1024

theorem Word.sameValue_value {x y : Word} (h : x.sameValue y = true) : x.value = y.value := by
  simp only [Word.sameValue, Bool.and_eq_true, beq_iff_eq, Bool.or_eq_true] at h
  obtain ⟨hm, hs⟩ := h
  rcases hs with hz | hs
  · have hy : y.magnitude = 0 := hm.symm.trans hz
    simp [Word.value, Word.coefficient, hz, hy, Rat.zero_mul]
  · simp [Word.value, Word.coefficient, hm, hs]

theorem Word.exact32_value {x : Word} {b : F32} (h : x.exact32 = some b) :
    TensorCore.value32 b = some x.value := by
  unfold Word.exact32 at h
  cases hb : x.round32 with
  | none => simp [hb] at h
  | some r =>
    cases hd : decode32Word r with
    | none => simp [hb, hd] at h
    | some y =>
      simp [hb, hd] at h
      obtain ⟨he, rfl⟩ := h
      rw [← decode32Word_value, hd, Option.map_some, Word.sameValue_value he]

/-- The executable scalar primitive is exactly one finite-range nearest-even FP32 addition. -/
theorem add32_eq (a b : F32) :
    add32 a b = (do
      let x ← TensorCore.value32 a
      let y ← TensorCore.value32 b
      TensorCore.round32 .nearestEven (x + y)) := by
  rw [← decode32Word_value, ← decode32Word_value]
  cases ha : decode32Word a with
  | none => simp [add32, ha]
  | some x =>
    cases hb : decode32Word b with
    | none => simp [add32, ha, hb]
    | some y =>
      have hx := decode32Word_magnitude ha
      have hy := decode32Word_magnitude hb
      obtain ⟨z, hz⟩ := x.add_exists y (by omega)
      simp [add32, ha, hb, hz, Word.round32_eq, Word.add_value hz]

end TensorCore.EFMachine
