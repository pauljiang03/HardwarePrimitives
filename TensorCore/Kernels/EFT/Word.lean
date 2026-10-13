import TensorCore.Kernels.EFT.WordDefs
import TensorCore.EFT.Extraction

/-! Values of bounded signed words and their sums. -/

namespace TensorCore.EFMachine

set_option exponentiation.threshold 1024

theorem Word.neg_coefficient (x : Word) : x.neg.coefficient = -x.coefficient := by
  cases hn : x.negative <;> simp [Word.neg, Word.coefficient, hn]

theorem Word.neg_value (x : Word) : x.neg.value = -x.value := by
  simp [Word.value, Word.neg_coefficient, Rat.neg_mul]

theorem magnitude_add_no_wrap (a b : Magnitude) :
    ¬ a + b < a ↔ a.toNat + b.toNat < 2 ^ 576 := by
  have ha := a.isLt
  have hb := b.isLt
  simp only [BitVec.lt_def, BitVec.toNat_add]
  omega

theorem Word.add_coefficient {x y z : Word} (h : x.add y = some z) :
    z.coefficient = x.coefficient + y.coefficient := by
  unfold Word.add at h
  dsimp only at h
  split at h
  · rename_i hs
    have hs' : x.negative = y.negative := by simpa using hs
    split at h
    · contradiction
    · rename_i hn
      cases Option.some.inj h
      have hw := magnitude_add_no_wrap x.magnitude y.magnitude |>.mp hn
      simp only [Word.coefficient, BitVec.toNat_add, Nat.mod_eq_of_lt hw, hs']
      cases y.negative <;> simp <;> omega
  · rename_i hs
    have hs' : x.negative ≠ y.negative := by simpa using hs
    split at h
    · rename_i hm
      cases Option.some.inj h
      have hm' : y.magnitude.toNat ≤ x.magnitude.toNat := hm
      rw [Word.coefficient, BitVec.toNat_sub_of_le hm, Int.ofNat_sub hm']
      cases hx : x.negative <;> cases hy : y.negative <;>
        simp_all [Word.coefficient] <;> omega
    · rename_i hm
      cases Option.some.inj h
      have hm' : x.magnitude ≤ y.magnitude := by
        simp only [BitVec.le_def] at *; omega
      rw [Word.coefficient, BitVec.toNat_sub_of_le hm', Int.ofNat_sub hm']
      cases hx : x.negative <;> cases hy : y.negative <;>
        simp_all [Word.coefficient] <;> omega

theorem Word.add_value {x y z : Word} (h : x.add y = some z) :
    z.value = x.value + y.value := by
  simp only [Word.value, Word.add_coefficient h, Rat.intCast_add, Rat.add_mul]

theorem Word.sub_value {x y z : Word} (h : x.sub y = some z) :
    z.value = x.value - y.value := by
  have ha := Word.add_value h
  rw [Word.neg_value] at ha
  simpa [Rat.sub_eq_add_neg] using ha

/-- A sufficient input-derived magnitude budget guarantees an accepted addition. -/
theorem Word.add_exists (x y : Word)
    (h : x.magnitude.toNat + y.magnitude.toNat < 2 ^ 576) :
    ∃ z, x.add y = some z := by
  unfold Word.add
  split
  · rw [if_neg ((magnitude_add_no_wrap _ _).mpr h)]
    exact ⟨_, rfl⟩
  · split <;> exact ⟨_, rfl⟩

theorem Word.add_magnitude {x y z : Word} (h : x.add y = some z) :
    z.magnitude.toNat ≤ x.magnitude.toNat + y.magnitude.toNat := by
  unfold Word.add at h
  dsimp only at h
  split at h
  · split at h
    · contradiction
    · cases Option.some.inj h
      simp only [BitVec.toNat_add]
      exact Nat.mod_le _ _
  · split at h
    · rename_i hm
      cases Option.some.inj h
      rw [BitVec.toNat_sub_of_le hm]
      omega
    · rename_i hm
      cases Option.some.inj h
      have hm' : x.magnitude ≤ y.magnitude := by
        simp only [BitVec.le_def] at *; omega
      rw [BitVec.toNat_sub_of_le hm']
      omega

theorem sumWords_value {xs : List Word} {z : Word} (h : sumWords xs = some z) :
    z.value = sumQ (xs.map Word.value) := by
  induction xs generalizing z with
  | nil => cases Option.some.inj h; simp [Word.value, Word.coefficient, Word.zero, sumQ]
  | cons x xs ih =>
    cases hs : sumWords xs with
    | none => simp [sumWords, hs] at h
    | some y =>
      simp only [sumWords, hs] at h
      rw [Word.add_value h, ih hs]
      rfl

def wordMagnitudeSum (xs : List Word) : ℕ := (xs.map fun x => x.magnitude.toNat).sum

/-- Every suffix sum fits under the original inputs' absolute budget. -/
theorem sumWords_exists (xs : List Word) (h : wordMagnitudeSum xs < 2 ^ 576) :
    ∃ z, sumWords xs = some z ∧ z.magnitude.toNat ≤ wordMagnitudeSum xs := by
  induction xs with
  | nil => exact ⟨Word.zero, rfl, by simp [wordMagnitudeSum, Word.zero]⟩
  | cons x xs ih =>
    have hb : wordMagnitudeSum (x :: xs) = x.magnitude.toNat + wordMagnitudeSum xs := by
      simp [wordMagnitudeSum]
    obtain ⟨y, hy, hmy⟩ := ih (by omega)
    obtain ⟨z, hz⟩ := Word.add_exists x y (by omega)
    refine ⟨z, by simp [sumWords, hy, hz], ?_⟩
    have hm := Word.add_magnitude hz
    omega

theorem Word.split_coarse (x : Word) (g : Grid) :
    (x.split g).coarse.magnitude.toNat = x.magnitude.toNat / 2 ^ g.toNat * 2 ^ g.toNat := by
  have hm := x.magnitude.isLt
  have hle := Nat.div_mul_le_self x.magnitude.toNat (2 ^ g.toNat)
  unfold Word.split
  split
  · rename_i hg
    have hg' : 576 ≤ g.toNat := by simpa [BitVec.le_def] using hg
    have hp : 2 ^ 576 ≤ 2 ^ g.toNat := Nat.pow_le_pow_right (by decide) hg'
    have hz : x.magnitude.toNat / 2 ^ g.toNat = 0 := Nat.div_eq_of_lt (by omega)
    simp [hz]
  · change (((x.magnitude >>> g.toNat) <<< g.toNat) : Magnitude).toNat = _
    rw [BitVec.toNat_shiftLeft, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow,
      Nat.shiftLeft_eq, Nat.mod_eq_of_lt (by omega)]

theorem Word.split_low (x : Word) (g : Grid) :
    (x.split g).low.magnitude.toNat = x.magnitude.toNat % 2 ^ g.toNat := by
  have hc := x.split_coarse g
  have hle := Nat.div_mul_le_self x.magnitude.toNat (2 ^ g.toNat)
  have hmod := Nat.mod_add_div x.magnitude.toNat (2 ^ g.toNat)
  rw [Nat.mul_comm] at hmod
  by_cases hg : g ≥ 576
  · simp only [Word.split, if_pos hg] at hc ⊢
    have hz : x.magnitude.toNat / 2 ^ g.toNat * 2 ^ g.toNat = 0 := by simpa using hc.symm
    omega
  · simp only [Word.split, if_neg hg] at hc ⊢
    rw [BitVec.toNat_sub_of_le (by rw [BitVec.le_def, hc]; exact hle), hc]
    omega

theorem Word.split_sign (x : Word) (g : Grid) :
    (x.split g).coarse.negative = x.negative ∧ (x.split g).low.negative = x.negative := by
  unfold Word.split; split <;> exact ⟨rfl, rfl⟩

theorem Word.split_reconstruct (x : Word) (g : Grid) :
    (x.split g).coarse.value + (x.split g).low.value = x.value := by
  have hc := x.split_coarse g
  have hl := x.split_low g
  have hm := Nat.mod_add_div x.magnitude.toNat (2 ^ g.toNat)
  rw [Nat.mul_comm] at hm
  have hn : (x.split g).coarse.magnitude.toNat + (x.split g).low.magnitude.toNat =
      x.magnitude.toNat := by omega
  have hi := congrArg (fun n : ℕ => (n : ℤ)) hn
  simp only [Int.natCast_add] at hi
  have hs := x.split_sign g
  have he : (x.split g).coarse.coefficient + (x.split g).low.coefficient = x.coefficient := by
    simp only [Word.coefficient, hs.1, hs.2]
    cases x.negative <;> simp_all <;> omega
  simp only [Word.value, ← Rat.add_mul, ← Rat.intCast_add, he]

theorem Word.split_magnitude (x : Word) (g : Grid) :
    (x.split g).coarse.magnitude.toNat ≤ x.magnitude.toNat ∧
    (x.split g).low.magnitude.toNat ≤ x.magnitude.toNat := by
  rw [x.split_coarse, x.split_low]
  exact ⟨Nat.div_mul_le_self _ _, Nat.mod_le _ _⟩

end TensorCore.EFMachine
