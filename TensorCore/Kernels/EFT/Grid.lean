import TensorCore.Kernels.EFT.Preparation

/-! The bounded extraction grid. -/

namespace TensorCore.EFMachine

set_option exponentiation.threshold 1024

/-- Specification of the maximum exponent: zero terms are ignored, before any shift or normalization. -/
def maxBiasedExp (ts : List Term) (initial : ℕ) : ℕ :=
  ts.foldl (fun e t => if t.word.magnitude = 0 then e else max e t.biasedExp.toNat) initial

theorem maxBiasedExp_eq (ts : List Term) (e : Grid) :
    (ts.foldl (fun e t => if t.word.magnitude == 0 then e
      else if e ≤ t.biasedExp then t.biasedExp else e) e).toNat = maxBiasedExp ts e.toNat := by
  induction ts generalizing e with
  | nil => rfl
  | cons t ts ih =>
    simp only [List.foldl_cons, maxBiasedExp]
    rw [ih]
    by_cases hz : t.word.magnitude = 0
    · simp [hz, maxBiasedExp]
    · simp only [beq_iff_eq, hz, if_false]
      split
      · rename_i h; rw [Nat.max_eq_right h]; rfl
      · rename_i h
        have h' : t.biasedExp.toNat ≤ e.toNat := by change ¬ e.toNat ≤ t.biasedExp.toNat at h; omega
        rw [Nat.max_eq_left h']; rfl

theorem outputGrid_spec (D : F32) :
    (outputGrid D).toNat = (D.toNat / 8388608 % 256) +
      (if D.toNat / 8388608 % 256 = 0 then 123 else 122) ∧
    ((outputGrid D).toNat : ℤ) - 272 = outputUlpExponent D ∧
    123 ≤ (outputGrid D).toNat := by
  have he := fp32_exponent_toNat D
  have hb : D.toNat / 8388608 % 256 < 256 := Nat.mod_lt _ (by decide)
  unfold outputGrid
  by_cases hz : D.toNat / 8388608 % 256 = 0
  · have hz' : (((D >>> 23).setWidth 8).zeroExtend 10 : Grid) = 0 := by
      apply BitVec.eq_of_toNat_eq; simpa [hz] using he
    simp [hz', outputUlpExponent, hz, emin32, Int.max_def]
  · have hz' : (((D >>> 23).setWidth 8).zeroExtend 10 : Grid) ≠ 0 := by
      intro h; have hh := congrArg BitVec.toNat h; rw [he] at hh; exact hz hh
    simp only [beq_iff_eq, hz', if_false, BitVec.toNat_add, he]
    have hm : (D.toNat / 8388608 % 256 + 122) % 1024 = D.toNat / 8388608 % 256 + 122 :=
      Nat.mod_eq_of_lt (by omega)
    simp only [show (122 : Grid).toNat = 122 from rfl, Nat.reducePow, hm, hz, if_false]
    unfold outputUlpExponent
    simp only [Nat.reducePow, emin32]
    rw [Int.max_eq_left (by omega)]
    exact ⟨trivial, by omega, by omega⟩

/-- Exact qE=max(qA,qD), with qA obtained from exponents, not product magnitude. -/
theorem selectedGrid_spec (variant : Variant) (ts : List Term) (D : F32) :
    ((selectedGrid variant ts D).toNat : ℤ) - 272 =
      max ((maxBiasedExp ts variant.eAlignMin.toNat : ℤ) - 512 - variant.model.alignFracBits)
        (outputUlpExponent D) := by
  have ho : (variant.alignmentBits + 240).toNat = variant.model.alignFracBits.toNat + 240 := by
    cases variant <;> decide
  have hal : (variant.model.alignFracBits.toNat : ℤ) = variant.model.alignFracBits := by
    cases variant <;> decide
  have hd := outputGrid_spec D
  unfold selectedGrid
  generalize he : ts.foldl _ variant.eAlignMin = e
  have hem := maxBiasedExp_eq ts variant.eAlignMin
  rw [he] at hem
  dsimp only
  by_cases hsmall : e < variant.alignmentBits + 240
  · rw [if_pos hsmall, if_pos (show (0 : Grid) ≤ outputGrid D from by exact Nat.zero_le _)]
    rw [hd.2.1, Int.max_eq_right]
    change e.toNat < (variant.alignmentBits + 240).toNat at hsmall
    rw [ho, hem] at hsmall
    omega
  · have hle : variant.alignmentBits + 240 ≤ e := by
      change ¬ e.toNat < _ at hsmall; change _ ≤ e.toNat; omega
    have hsub : (e - (variant.alignmentBits + 240)).toNat =
        maxBiasedExp ts variant.eAlignMin.toNat - (variant.model.alignFracBits.toNat + 240) := by
      rw [BitVec.toNat_sub_of_le hle, hem, ho]
    rw [if_neg hsmall]
    split
    · rename_i h
      change (e - (variant.alignmentBits + 240)).toNat ≤ (outputGrid D).toNat at h
      rw [hsub] at h
      rw [hd.2.1, Int.max_eq_right]
      change (variant.alignmentBits + 240).toNat ≤ e.toNat at hle
      rw [ho, hem] at hle
      omega
    · rename_i h
      change ¬ (e - (variant.alignmentBits + 240)).toNat ≤ (outputGrid D).toNat at h
      rw [hsub] at h
      rw [hsub, Int.max_eq_left]
      · omega
      · omega

end TensorCore.EFMachine
