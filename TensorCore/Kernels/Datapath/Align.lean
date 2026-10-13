import TensorCore.Kernels.Datapath.Defs
import TensorCore.Kernels.EFT.Dyadic
import TensorCore.TC.AlignmentExponent

/-! Bitvector alignment and accumulation are exact truncation and summation. -/

namespace TensorCore.Datapath

open EFMachine

set_option exponentiation.threshold 1024

/-- The product or c this term denotes. -/
def Term.denormalized (t : Term) : DenormalizedProduct :=
  ⟨if t.negative then -(t.significand.toNat : ℤ) else t.significand.toNat,
    (t.biasedExp.toNat : ℤ) - 256, t.mantissaBits.toNat⟩

/-- A significand below 4 with at most 23 bits after the binary point. -/
def Term.Valid (t : Term) : Prop :=
  t.significand.toNat < 2 ^ (t.mantissaBits.toNat + 2) ∧ t.mantissaBits.toNat ≤ 23

theorem Term.aligned_toNat (variant : Variant) (e : Exp) (t : Term) (ht : t.Valid)
    (hF : 23 ≤ (alignBits variant).toNat) :
    (t.aligned variant e).toNat = t.significand.toNat * 2 ^ ((alignBits variant).toNat - t.mantissaBits.toNat) /
      2 ^ (e - t.biasedExp).toNat := by
  obtain ⟨ht1, ht2⟩ := ht
  have hsub : ((alignBits variant) - t.mantissaBits).toNat =
      (alignBits variant).toNat - t.mantissaBits.toNat := by
    rw [BitVec.toNat_sub_of_le (by rw [BitVec.le_def]; omega)]
  have hz : (t.significand.zeroExtend (termWidth variant)).toNat = t.significand.toNat := by
    rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt]
    exact Nat.lt_of_lt_of_le ht1 (Nat.pow_le_pow_right (by decide) (by unfold termWidth; omega))
  have hfit : t.significand.toNat * 2 ^ ((alignBits variant).toNat - t.mantissaBits.toNat) <
      2 ^ termWidth variant := by
    have h := Nat.mul_lt_mul_of_pos_right ht1
      (Nat.two_pow_pos ((alignBits variant).toNat - t.mantissaBits.toNat))
    rw [← Nat.pow_add] at h
    exact Nat.lt_of_lt_of_le h (Nat.pow_le_pow_right (by decide) (by unfold termWidth; omega))
  unfold Term.aligned
  rw [BitVec.ushiftRight_eq', BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow,
    BitVec.shiftLeft_eq', BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, hsub, hz, Nat.mod_eq_of_lt hfit]

theorem truncBits_zero (e : ℤ) : truncBits 0 e = 0 := by
  unfold truncBits
  rw [if_neg (by grind), Rat.div_def, Rat.zero_mul]
  simpa using Rat.floor_intCast 0

/-- An aligned term is the model's truncation on the grid `2 ^ (e - 256 - F)`. -/
theorem Term.truncBits_eq (variant : Variant) (e : Exp) (t : Term) (ht : t.Valid)
    (hF : 23 ≤ (alignBits variant).toNat)
    (he : t.significand ≠ 0 → t.biasedExp.toNat ≤ e.toNat) :
    truncBits t.denormalized.value ((e.toNat : ℤ) - 256 - (alignBits variant).toNat) =
      if t.negative then -((t.aligned variant e).toNat : ℤ) else ((t.aligned variant e).toNat : ℤ) := by
  rw [t.aligned_toNat variant e ht hF]
  by_cases hz : t.significand = 0
  · have h0 : t.significand.toNat = 0 := by rw [hz]; rfl
    have hv : t.denormalized.value = 0 := by
      simp [Term.denormalized, DenormalizedProduct.value, h0]
    rw [hv, truncBits_zero, h0]
    cases t.negative <;> simp
  · have hle := he hz
    have hd : (e - t.biasedExp).toNat = e.toNat - t.biasedExp.toNat := by
      rw [BitVec.toNat_sub_of_le (by rw [BitVec.le_def]; exact hle)]
    rw [hd]
    have hn : 0 < t.significand.toNat := by
      have : t.significand.toNat ≠ 0 := fun h => hz (BitVec.eq_of_toNat_eq h)
      omega
    -- |value| / 2^g is the shifted significand over 2^(e - exponent)
    have hq : (t.significand.toNat : ℚ) * pow2 (((t.biasedExp.toNat : ℤ) - 256) - t.mantissaBits.toNat) /
        pow2 ((e.toNat : ℤ) - 256 - (alignBits variant).toNat) =
        ((t.significand.toNat * 2 ^ ((alignBits variant).toNat - t.mantissaBits.toNat) : ℕ) : ℚ) /
          ((2 ^ (e.toNat - t.biasedExp.toNat) : ℕ) : ℚ) := by
      have h1 : (t.significand.toNat : ℚ) *
          pow2 (((t.biasedExp.toNat : ℤ) - 256) - t.mantissaBits.toNat) =
          ((t.significand.toNat * 2 ^ ((alignBits variant).toNat - t.mantissaBits.toNat) : ℕ) : ℚ) *
            pow2 ((t.biasedExp.toNat : ℤ) - 256 - (alignBits variant).toNat) := by
        rw [Rat.natCast_mul, Rat.mul_assoc, ← pow2_natCast, ← pow2_add]
        congr 2
        have := ht.2
        omega
      rw [h1, show (e.toNat : ℤ) - 256 - (alignBits variant).toNat =
          ((t.biasedExp.toNat : ℤ) - 256 - (alignBits variant).toNat) +
            ((e.toNat - t.biasedExp.toNat : ℕ) : ℤ) by omega]
      exact dyadic_div _ _ _
    have hpos : 0 ≤ (t.significand.toNat : ℚ) *
        pow2 (((t.biasedExp.toNat : ℤ) - 256) - t.mantissaBits.toNat) :=
      Rat.mul_nonneg (Rat.natCast_nonneg) (Rat.le_of_lt (pow2_pos _))
    cases hs : t.negative
    · simp only [Term.denormalized, DenormalizedProduct.value, hs, Bool.false_eq_true, if_false,
        Rat.intCast_natCast]
      unfold truncBits
      rw [if_neg (by grind), hq, floor_nat_div _ _ (Nat.two_pow_pos _)]
    · simp only [Term.denormalized, DenormalizedProduct.value, hs, if_true, Rat.intCast_neg,
        Rat.intCast_natCast, Rat.neg_mul]
      unfold truncBits
      have hpos' : 0 < (t.significand.toNat : ℚ) *
          pow2 (((t.biasedExp.toNat : ℤ) - 256) - t.mantissaBits.toNat) :=
        Rat.mul_pos (Rat.natCast_pos.mpr hn) (pow2_pos _)
      rw [if_pos (by grind), Rat.neg_neg, hq, floor_nat_div _ _ (Nat.two_pow_pos _)]

theorem Term.signedAligned_eq (variant : Variant) (e : Exp) (t : Term) :
    t.signedAligned variant e = BitVec.ofInt (accWidth variant)
      (if t.negative then -((t.aligned variant e).toNat : ℤ) else ((t.aligned variant e).toNat : ℤ)) := by
  have hz : ((t.aligned variant e).zeroExtend (accWidth variant)) =
      BitVec.ofInt (accWidth variant) ((t.aligned variant e).toNat : ℤ) := by
    rw [BitVec.ofInt_natCast]
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
  unfold Term.signedAligned
  cases t.negative
  · simp only [Bool.false_eq_true, if_false]
    exact hz
  · simp only [if_true, BitVec.ofInt_neg, hz]

theorem accumulate_eq (variant : Variant) (e : Exp) (ts : List Term) (s : BitVec (accWidth variant)) :
    ts.foldl (fun s t => s + t.signedAligned variant e) s =
      machineAccumulate (accWidth variant) s (ts.map fun t =>
        if t.negative then -((t.aligned variant e).toNat : ℤ) else ((t.aligned variant e).toNat : ℤ)) := by
  induction ts generalizing s with
  | nil => rfl
  | cons t ts ih =>
    simp only [List.foldl_cons, List.map_cons, machineAccumulate]
    rw [ih, t.signedAligned_eq]

/-- The two's complement accumulator holds the exact sum of the aligned terms. -/
theorem accumulate_toInt (variant : Variant) (e : Exp) (ts : List Term)
    (hlen : ts.length = variant.model.nfma + 1) :
    (accumulate variant e ts).toInt = sumZ (ts.map fun t =>
      if t.negative then -((t.aligned variant e).toNat : ℤ) else ((t.aligned variant e).toNat : ℤ)) := by
  unfold accumulate
  rw [accumulate_eq]
  apply machineAccumulate_of_coefficient_bound _ (termWidth variant) (carryBits variant)
  · intro z hz
    obtain ⟨t, _, rfl⟩ := List.mem_map.mp hz
    have := (t.aligned variant e).isLt
    cases t.negative <;> simp <;> omega
  · rw [List.length_map, hlen]
    exact Nat.lt_log2_self

/-- Specification of the alignment exponent fold. -/
theorem alignFold_spec (ts : List Term) (init : Exp) :
    let r := ts.foldl (fun e t => if t.significand == 0 then e
      else if e ≤ t.biasedExp then t.biasedExp else e) init
    init.toNat ≤ r.toNat ∧ (∀ t ∈ ts, t.significand ≠ 0 → t.biasedExp.toNat ≤ r.toNat) ∧
      (r = init ∨ ∃ t ∈ ts, t.significand ≠ 0 ∧ r = t.biasedExp) := by
  induction ts generalizing init with
  | nil => exact ⟨Nat.le_refl _, by simp, Or.inl rfl⟩
  | cons t ts ih =>
    simp only [List.foldl_cons]
    by_cases hz : t.significand = 0
    · simp only [hz, beq_self_eq_true, if_true]
      obtain ⟨h1, h2, h3⟩ := ih init
      refine ⟨h1, ?_, ?_⟩
      · intro u hu hnz
        rcases List.mem_cons.mp hu with rfl | hu
        · exact absurd hz hnz
        · exact h2 u hu hnz
      · rcases h3 with h | ⟨u, hu, hnz, h⟩
        · exact Or.inl h
        · exact Or.inr ⟨u, List.mem_cons_of_mem _ hu, hnz, h⟩
    · have hb : (t.significand == 0) = false := by simpa using hz
      simp only [hb, Bool.false_eq_true, if_false]
      generalize hn : (if init ≤ t.biasedExp then t.biasedExp else init) = next
      have hnext : init.toNat ≤ next.toNat ∧ t.biasedExp.toNat ≤ next.toNat ∧
          (next = init ∨ next = t.biasedExp) := by
        rw [← hn]
        split
        · rename_i h; rw [BitVec.le_def] at h; exact ⟨h, Nat.le_refl _, Or.inr rfl⟩
        · rename_i h; rw [BitVec.le_def] at h; exact ⟨Nat.le_refl _, by omega, Or.inl rfl⟩
      obtain ⟨h1, h2, h3⟩ := ih next
      refine ⟨by omega, ?_, ?_⟩
      · intro u hu hnz
        rcases List.mem_cons.mp hu with rfl | hu
        · omega
        · exact h2 u hu hnz
      · rcases h3 with h | ⟨u, hu, hnz, h⟩
        · rcases hnext.2.2 with h' | h'
          · exact Or.inl (h.trans h')
          · exact Or.inr ⟨t, List.mem_cons_self, hz, h.trans h'⟩
        · exact Or.inr ⟨u, List.mem_cons_of_mem _ hu, hnz, h⟩

end TensorCore.Datapath
