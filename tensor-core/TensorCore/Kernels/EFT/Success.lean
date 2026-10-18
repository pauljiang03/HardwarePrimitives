import TensorCore.Kernels.EFT.Refinement
import TensorCore.Numerics.Sum

/-! An input-only success family for the 576-bit TC-EFT. -/

namespace TensorCore.EFMachine

private theorem unit_product (a b : ℚ) (ha : absQ a ≤ 1) (hb : absQ b ≤ 1) :
    absQ (a * b) ≤ 1 := by
  have ha' := (absQ_le_iff _ _).mp ha
  have hb' := (absQ_le_iff _ _).mp hb
  apply (absQ_le_iff _ _).mpr
  by_cases ha0 : 0 ≤ a <;> by_cases hb0 : 0 ≤ b
  · have h1 := Rat.mul_le_mul_of_nonneg_left hb'.2 ha0
    have h2 := Rat.mul_nonneg ha0 hb0
    grind
  · have h1 := Rat.mul_le_mul_of_nonneg_left hb'.1 ha0
    have h2 := Rat.mul_le_mul_of_nonneg_left (show b ≤ 0 by grind) ha0
    grind
  · have h1 := Rat.mul_le_mul_of_nonneg_right ha'.1 hb0
    have h2 := Rat.mul_le_mul_of_nonneg_right (show a ≤ 0 by grind) hb0
    grind
  · have hn1 : 0 ≤ -a := by grind
    have hn2 : 0 ≤ -b := by grind
    have h1 := Rat.mul_le_mul_of_nonneg_left (show -b ≤ 1 by grind) hn1
    have h2 := Rat.mul_nonneg hn1 hn2
    grind

/-- Success with no bound on the exact result: all inputs and `c` have magnitude at most one. -/
theorem tcEft_unitInputs_success {variant : Variant} {x : BlockInput variant.model} {D : F32}
    {b : PreparedBlock} {d : ℚ}
    (shape : x.products.length = variant.model.nfma)
    (inputs : TensorCore.prepare x = some b)
    (hc : absQ b.c.value ≤ 1)
    (hp : ∀ ab ∈ b.products, absQ ab.1.value ≤ 1 ∧ absQ ab.2.value ≤ 1)
    (hD : TensorCore.value32 D = some d) :
    absQ b.exactDot ≤ 33 ∧
      ∃ r bits, tcEft variant x D = .ok r ∧ r.bits = some bits ∧ NearestEven32 b.exactDot bits := by
  have hlen : b.products.length = variant.model.nfma := by
    unfold TensorCore.prepare at inputs
    cases hd : TensorCore.decode32 x.c <;>
      cases hs : TensorCore.prepareProducts variant.model x.products <;>
      simp only [hd, hs, Option.some.injEq] at inputs
    · contradiction
    · contradiction
    · contradiction
    · subst b
      have h := mapM_bounds (P := fun _ => True) (fun _ _ _ => trivial) hs
      exact h.1.trans shape
  have hp' : ∀ ab ∈ b.products, absQ (ab.1.value * ab.2.value) ≤ 1 := by
    intro ab hab
    exact unit_product _ _ (hp ab hab).1 (hp ab hab).2
  have hs := absQ_sumQ_le (b.products.map fun ab => ab.1.value * ab.2.value)
  have hb := sumQ_map_le b.products (fun ab => absQ (ab.1.value * ab.2.value)) 1 hp'
  simp only [List.map_map, Function.comp_def] at hs
  have ha := absQ_add_le b.c.value b.exactProducts
  have hn : (b.products.length : ℚ) ≤ 32 :=
    Rat.natCast_le_natCast.mpr (by rw [hlen]; exact variant_count variant)
  have hbound : absQ b.exactDot ≤ 33 := by
    dsimp only [PreparedBlock.exactProducts] at ha
    dsimp only [PreparedBlock.exactDot, PreparedBlock.exactProducts]
    grind
  refine ⟨hbound, tcEft_success shape ?_ hD ?_⟩
  · simp [TensorCore.exactDot, inputs]
  · have hmax : (33 : ℚ) ≤ maxFinite32 := by decide +kernel
    exact Rat.le_trans hbound hmax

end TensorCore.EFMachine
