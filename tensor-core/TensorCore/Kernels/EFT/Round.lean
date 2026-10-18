import TensorCore.Kernels.EFT.Dyadic
import TensorCore.Kernels.EFT.BitScan

/-! Correctness of bounded rounding to FP32. -/

namespace TensorCore.EFMachine

set_option exponentiation.threshold 1024
set_option maxRecDepth 4096

def magnitudeValue (m : Magnitude) : ℚ := (m.toNat : ℚ) * pow2 (-272)

theorem pow2_common (n : ℕ) :
    pow2 ((n : ℤ) - 272) = ((2 ^ n : ℕ) : ℚ) * pow2 (-272) := by
  rw [Int.sub_eq_add_neg, pow2_add, pow2_natCast]

theorem magnitudeExponent_word (m : Magnitude) (hm : m ≠ 0) :
    magnitudeExponent (magnitudeValue m) = ((575 - m.clz.toNat : ℕ) : ℤ) - 272 := by
  have hc : m.clz.toNat < 576 := by
    simpa [BitVec.lt_def] using (BitVec.clz_lt_iff_ne_zero.mpr hm)
  have hl := BitVec.two_pow_sub_clz_le_toNat_of_ne_zero (x := m) (by decide) hm
  have hu := BitVec.toNat_lt_two_pow_sub_clz (x := m)
  apply magnitudeExponent_eq_of_bounds
  · rw [pow2_common]
    exact Rat.mul_le_mul_of_nonneg_right (Rat.natCast_le_natCast.mpr hl)
      (Rat.le_of_lt (pow2_pos _))
  · have he : (((575 - m.clz.toNat : ℕ) : ℤ) - 272) + 1 =
        ((576 - m.clz.toNat : ℕ) : ℤ) - 272 := by omega
    rw [he, pow2_common]
    exact Rat.mul_lt_mul_of_pos_right (Rat.natCast_lt_natCast.mpr hu) (pow2_pos _)

theorem roundingGrid_toNat (m : Magnitude) :
    (roundingGrid m).toNat = max 123 (576 - m.clz.toNat - 24) := by
  have hc : m.clz ≤ (576 : Magnitude) := BitVec.clz_le
  have hl : ((576 : Magnitude) - m.clz).toNat = 576 - m.clz.toNat := by
    rw [BitVec.toNat_sub_of_le hc]; rfl
  unfold roundingGrid
  rw [leadingZeros_eq]
  dsimp only
  split
  · rename_i hs
    have hs' : 576 - m.clz.toNat ≤ 147 := by
      change ((576 : Magnitude) - m.clz).toNat ≤ 147 at hs
      rwa [hl] at hs
    change 123 = _
    omega
  · rename_i hs
    have hs' : 147 < 576 - m.clz.toNat := by
      simp only [BitVec.le_def, hl] at hs
      change ¬576 - m.clz.toNat ≤ 147 at hs
      omega
    rw [BitVec.toNat_sub_of_le (by change 24 ≤ ((576 : Magnitude) - m.clz).toNat; rw [hl]; omega)]
    rw [hl]
    change 576 - m.clz.toNat - 24 = _
    omega

theorem roundingGrid_bounds (m : Magnitude) :
    123 ≤ (roundingGrid m).toNat ∧ (roundingGrid m).toNat ≤ 552 := by
  rw [roundingGrid_toNat]; omega

theorem roundingGrid_normExp (m : Magnitude) (hm : m ≠ 0) :
    normExp (magnitudeValue m) = ((roundingGrid m).toNat : ℤ) - 249 := by
  have hc : m.clz.toNat < 576 := by
    simpa [BitVec.lt_def] using (BitVec.clz_lt_iff_ne_zero.mpr hm)
  rw [roundingGrid_toNat]
  unfold normExp emin32
  rw [magnitudeExponent_word m hm]
  omega

theorem roundingGrid_div (m : Magnitude) (hm : m ≠ 0) :
    magnitudeValue m / pow2 (normExp (magnitudeValue m) - 23) =
      (m.toNat : ℚ) / (2 ^ (roundingGrid m).toNat : ℕ) := by
  rw [roundingGrid_normExp m hm]
  have he : ((roundingGrid m).toNat : ℤ) - 249 - 23 =
      -272 + (roundingGrid m).toNat := by omega
  rw [he]
  exact dyadic_div _ _ _

theorem roundingGrid_quotient_bound (m : Magnitude) :
    m.toNat / 2 ^ (roundingGrid m).toNat < 2 ^ 24 := by
  have hu := BitVec.toNat_lt_two_pow_sub_clz (x := m)
  have hg := roundingGrid_toNat m
  have he : 576 - m.clz.toNat ≤ (roundingGrid m).toNat + 24 := by omega
  have hp := Nat.pow_le_pow_right (n := 2) (by decide) he
  have hh : m.toNat < 2 ^ 24 * 2 ^ (roundingGrid m).toNat := by
    rw [← Nat.pow_add, Nat.add_comm 24]
    omega
  exact (Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _)).mpr hh

theorem roundingCoefficient_spec (m g : Magnitude)
    (hg : 1 ≤ g.toNat) (hg' : g.toNat < 576)
    (hk : m.toNat / 2 ^ g.toNat < 2 ^ 24) :
    ((roundingCoefficient m g).toNat : ℤ) =
      rneInt ((m.toNat : ℚ) / (2 ^ g.toNat : ℕ)) := by
  let k := m >>> g
  let r := m - (k <<< g)
  let half := (1 : Magnitude) <<< (g - 1)
  have hk' : k.toNat = m.toNat / 2 ^ g.toNat := by
    change (m >>> g.toNat).toNat = _
    rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
  have hcoarse : (k <<< g).toNat = m.toNat / 2 ^ g.toNat * 2 ^ g.toNat := by
    change (k <<< g.toNat).toNat = _
    rw [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, hk',
      Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.div_mul_le_self _ _) m.isLt)]
  have hr : r.toNat = m.toNat % 2 ^ g.toNat := by
    have hb : k <<< g ≤ m := by
      change (k <<< g).toNat ≤ m.toNat
      rw [hcoarse]; exact Nat.div_mul_le_self _ _
    dsimp only [r]
    rw [BitVec.toNat_sub_of_le hb, hcoarse]
    have hh := Nat.mod_add_div m.toNat (2 ^ g.toNat)
    rw [Nat.mul_comm] at hh
    omega
  have hgap : (g - 1).toNat = g.toNat - 1 := by
    rw [BitVec.toNat_sub_of_le (by exact hg)]; rfl
  have hhalf : half.toNat = 2 ^ (g.toNat - 1) := by
    change ((1 : Magnitude) <<< (g - 1).toNat).toNat = _
    rw [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, hgap]
    change (1 * 2 ^ (g.toNat - 1)) % 2 ^ 576 = _
    rw [Nat.one_mul, Nat.mod_eq_of_lt (Nat.pow_lt_pow_right (by decide) (by omega))]
  have htwo : 2 ^ g.toNat = 2 * half.toNat := by
    calc
      2 ^ g.toNat = 2 ^ ((g.toNat - 1) + 1) := by congr 1; omega
      _ = 2 * 2 ^ (g.toNat - 1) := by rw [Nat.pow_succ, Nat.mul_comm]
      _ = 2 * half.toNat := by rw [hhalf]
  have hparity : (k &&& 1).toNat = k.toNat % 2 := by
    rw [BitVec.toNat_and]
    change k.toNat &&& 1 = _
    exact Nat.and_one_is_mod _
  have hcond : (r > half || (r == half && (k &&& 1) == 1)) = true ↔
      2 ^ g.toNat < 2 * (m.toNat % 2 ^ g.toNat) ∨
        (2 * (m.toNat % 2 ^ g.toNat) = 2 ^ g.toNat ∧ m.toNat / 2 ^ g.toNat % 2 = 1) := by
    simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, BitVec.lt_def,
      BitVec.toNat_eq, hr, hparity, hk', decide_eq_true_eq]
    change half.toNat < m.toNat % 2 ^ g.toNat ∨
      (m.toNat % 2 ^ g.toNat = half.toNat ∧ m.toNat / 2 ^ g.toNat % 2 = 1) ↔ _
    omega
  rw [rneInt_nat_div _ _ (Nat.two_pow_pos _)]
  change ((if r > half || (r == half && (k &&& 1) == 1) then k + 1 else k).toNat : ℤ) = _
  split
  · rename_i hc
    rw [if_pos (hcond.mp hc), BitVec.toNat_add]
    have hkn : k.toNat + 1 < 2 ^ 576 := by rw [hk'] at *; omega
    change (((k.toNat + 1) % 2 ^ 576 : ℕ) : ℤ) = _
    rw [Nat.mod_eq_of_lt hkn, hk']
  · rename_i hc
    rw [if_neg (by intro h; exact hc (hcond.mpr h)), hk']

theorem roundingCoefficient_roundedSignificand (m : Magnitude) (hm : m ≠ 0) :
    ((roundingCoefficient m (roundingGrid m)).toNat : ℤ) =
      roundedSignificand .nearestEven (magnitudeValue m) := by
  have hg := roundingGrid_bounds m
  rw [roundingCoefficient_spec _ _ (by omega) (by omega) (roundingGrid_quotient_bound m)]
  unfold roundedSignificand roundSignificand
  rw [roundingGrid_div m hm]

theorem encodeAtGrid_spec (negative : Bool) (g k : Magnitude)
    (hg : 123 ≤ g.toNat) (hg' : g.toNat ≤ 553) (hk : k.toNat < 16777216) :
    encodeAtGrid negative g k = encode32 negative ((g.toNat : ℤ) - 249) k.toNat := by
  have hgs : (g - 122).toNat = g.toNat - 122 := by
    rw [BitVec.toNat_sub_of_le (by change 122 ≤ g.toNat; omega)]; rfl
  have hexp : (((g.toNat : ℤ) - 249) + 127).toNat = g.toNat - 122 := by omega
  unfold encodeAtGrid encode32
  have hsmall : k < (8388608 : Magnitude) ↔ (k.toNat : ℤ) < 2 ^ 23 := by
    change k.toNat < 8388608 ↔ (k.toNat : ℤ) < 8388608
    omega
  split
  · rename_i hs
    rw [if_pos (hsmall.mp hs)]
    apply BitVec.eq_of_toNat_eq
    cases negative <;> simp [BitVec.toNat_add, BitVec.toNat_setWidth, Nat.add_mod]
  · rename_i hs
    simp only [if_neg (mt hsmall.mpr hs), hexp]
    have hklo : 8388608 ≤ k.toNat := by change ¬ k.toNat < 8388608 at hs; omega
    have hks : (k - 8388608).toNat = k.toNat - 8388608 := by
      rw [BitVec.toNat_sub_of_le hklo]; rfl
    have hshift : ((g - 122) <<< 23).toNat = (g.toNat - 122) * 8388608 := by
      rw [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, hgs]
      change ((g.toNat - 122) * 8388608) % 2 ^ 576 = _
      exact Nat.mod_eq_of_lt (by omega)
    have hp : (((g - 122) <<< 23) + (k - 8388608)).toNat =
        (g.toNat - 122) * 8388608 + (k.toNat - 8388608) := by
      rw [BitVec.toNat_add, hshift, hks, Nat.mod_eq_of_lt (by omega)]
    have hki : ((k.toNat : ℤ) - 2 ^ 23).toNat = k.toNat - 8388608 := by omega
    rw [hki]
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_add, BitVec.toNat_setWidth, hp, BitVec.toNat_ofNat]
    cases negative <;> simp [Nat.add_mod]

theorem encodeRounded_spec (negative : Bool) (g k : Magnitude)
    (hg : 123 ≤ g.toNat) (hg' : g.toNat ≤ 552) (hk : k.toNat ≤ 16777216) :
    encodeRounded negative g k =
      encode32 negative (carry ((g.toNat : ℤ) - 249) k.toNat).1
        (carry ((g.toNat : ℤ) - 249) k.toNat).2 := by
  unfold encodeRounded
  dsimp only
  split
  · rename_i hc
    dsimp only
    have hc' : k.toNat = 16777216 := by
      have hh := congrArg BitVec.toNat (beq_iff_eq.mp hc)
      exact hh
    have hgn : (g + 1).toNat = g.toNat + 1 := by
      rw [BitVec.toNat_add]
      change (g.toNat + 1) % 2 ^ 576 = _
      exact Nat.mod_eq_of_lt (by omega)
    have hkn : (k >>> 1).toNat = 8388608 := by
      rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, hc']
    rw [encodeAtGrid_spec _ _ _ (by omega) (by omega) (by omega), hgn, hkn]
    simp only [carry, hc', show ((16777216 : ℕ) : ℤ) = 2 ^ 24 by decide, if_true]
    congr 1 <;> omega
  · rename_i hc
    dsimp only
    have hc' : k.toNat ≠ 16777216 := by
      intro h
      apply hc
      exact beq_iff_eq.mpr (BitVec.eq_of_toNat_eq h)
    rw [encodeAtGrid_spec _ _ _ hg (by omega) (by omega)]
    have hn : (k.toNat : ℤ) ≠ 2 ^ 24 := by omega
    simp only [carry, if_neg hn]

theorem Word.abs_value (x : Word) : absQ x.value = magnitudeValue x.magnitude := by
  have hp : (0 : ℚ) ≤ magnitudeValue x.magnitude :=
    Rat.mul_nonneg Rat.natCast_nonneg (Rat.le_of_lt (pow2_pos _))
  cases hn : x.negative
  · simpa [Word.value, Word.coefficient, hn, magnitudeValue, Rat.intCast_natCast] using absQ_of_nonneg hp
  · simpa [Word.value, Word.coefficient, hn, magnitudeValue, Rat.intCast_natCast, Rat.neg_mul, absQ_neg] using
      absQ_of_nonneg hp

theorem Word.value_zero_iff (x : Word) : x.value = 0 ↔ x.magnitude = 0 := by
  have hp := pow2_pos (-272)
  have hm := x.magnitude.isLt
  have he : (magnitudeValue x.magnitude = 0) ↔ x.magnitude = 0 := by
    unfold magnitudeValue
    rw [Rat.mul_eq_zero]
    simp only [Rat.ne_of_gt hp, or_false, BitVec.toNat_eq]
    change (x.magnitude.toNat : ℚ) = ((0 : ℕ) : ℚ) ↔ x.magnitude.toNat = 0
    exact Rat.natCast_inj
  have ha := x.abs_value
  have hz : absQ x.value = 0 ↔ x.value = 0 := by unfold absQ; split <;> grind
  rw [← hz, ha, he]

theorem Word.sign_value (x : Word) (hx : x.magnitude ≠ 0) :
    decide (x.value < 0) = x.negative := by
  have hm : 0 < x.magnitude.toNat := by
    have hn : x.magnitude.toNat ≠ 0 := by intro h; exact hx (BitVec.eq_of_toNat_eq h)
    omega
  have hp : (0 : ℚ) < magnitudeValue x.magnitude :=
    Rat.mul_pos (Rat.natCast_pos.mpr hm) (pow2_pos _)
  cases hn : x.negative <;>
    simp only [Word.value, Word.coefficient, hn, Bool.false_eq_true, if_false, if_true,
      Rat.intCast_natCast, Rat.intCast_neg, Rat.neg_mul] <;>
    change decide _ = _ <;> unfold magnitudeValue at hp <;> simp_all <;> grind

theorem maxMagnitude32_value : magnitudeValue maxMagnitude32 = maxFinite32 := by decide +kernel

theorem Word.range_iff (x : Word) :
    absQ x.value ≤ maxFinite32 ↔ x.magnitude ≤ maxMagnitude32 := by
  rw [x.abs_value, ← maxMagnitude32_value]
  unfold magnitudeValue
  have hp := pow2_pos (-272)
  constructor
  · intro h
    have hn : (x.magnitude.toNat : ℚ) ≤ (maxMagnitude32.toNat : ℚ) := by
      have hh := Rat.mul_lt_mul_right (a := (maxMagnitude32.toNat : ℚ))
        (b := (x.magnitude.toNat : ℚ)) hp
      grind
    exact Rat.natCast_le_natCast.mp hn
  · intro h
    exact Rat.mul_le_mul_of_nonneg_right (Rat.natCast_le_natCast.mpr h) (Rat.le_of_lt hp)

/-- Bounded rounding to FP32 equals exact nearest-even rounding, bit for bit. -/
theorem Word.round32_eq (x : Word) :
    x.round32 = TensorCore.round32 .nearestEven x.value := by
  by_cases hr : x.magnitude ≤ maxMagnitude32
  · have hr' := x.range_iff.mpr hr
    have hnr : ¬ x.magnitude > maxMagnitude32 := by
      change ¬ maxMagnitude32.toNat < x.magnitude.toNat
      exact Nat.not_lt.mpr hr
    have hnr' : ¬ absQ x.value > maxFinite32 := by grind
    by_cases hz : x.magnitude = 0
    · have hz' := x.value_zero_iff.mpr hz
      simp only [Word.round32, hz, beq_self_eq_true, if_true, hz']
      exact (show TensorCore.round32 .nearestEven 0 = some 0 by decide +kernel).symm
    · have hz' : x.value ≠ 0 := by intro h; exact hz (x.value_zero_iff.mp h)
      have hp : 0 < magnitudeValue x.magnitude := by
        rw [← x.abs_value]
        exact absQ_pos_of_ne_zero _ hz'
      have hmr : magnitudeValue x.magnitude ≤ maxFinite32 := by rwa [x.abs_value] at hr'
      have hnmr : ¬ magnitudeValue x.magnitude > maxFinite32 := by grind
      obtain ⟨he0, he1, _, _⟩ := normExp_bounds _ hp hmr
      obtain ⟨hk0, hk1, hsub, htop⟩ := roundedSignificand_bounds .nearestEven _ hp hmr
      have hs := carry_spec _ _ he0 he1 hk0 hk1 hsub htop
      have hcarry : ¬ (carry (normExp (magnitudeValue x.magnitude))
          (roundedSignificand .nearestEven (magnitudeValue x.magnitude))).1 > 127 := by
        exact Int.not_lt.mpr hs.2.1
      have hg := roundingGrid_bounds x.magnitude
      have hk := roundingCoefficient_roundedSignificand x.magnitude hz
      have hsign := x.sign_value hz
      simp only [Word.round32, if_neg hnr, beq_iff_eq, if_neg hz]
      rw [encodeRounded_spec _ _ _ hg.1 hg.2 (by omega), hk,
        ← roundingGrid_normExp x.magnitude hz]
      simp only [TensorCore.round32, round32Core, if_neg hz', x.abs_value,
        hsign, if_neg hcarry, if_neg hnmr]
  · have hr' : absQ x.value > maxFinite32 := by
      have h := x.range_iff
      grind
    have hm : x.magnitude > maxMagnitude32 := by
      change maxMagnitude32.toNat < x.magnitude.toNat
      change ¬ x.magnitude.toNat ≤ maxMagnitude32.toNat at hr
      omega
    simp only [Word.round32, if_pos hm, TensorCore.round32, if_pos hr']

theorem Word.round32_correct {x : Word} {b : F32} (h : x.round32 = some b) :
    NearestEven32 x.value b := by
  rw [x.round32_eq] at h
  exact finalRound_correct _ _ (TensorCore.round32_range h) h

theorem Word.round32_isSome_iff (x : Word) :
    x.round32.isSome = true ↔ absQ x.value ≤ maxFinite32 := by
  rw [x.round32_eq]
  constructor
  · cases hh : TensorCore.round32 .nearestEven x.value with
    | none => simp
    | some b => intro _; exact TensorCore.round32_range hh
  · intro h
    obtain ⟨b, hb, _⟩ := round32_nearestEven_correct x.value h
    rw [hb]; rfl

end TensorCore.EFMachine
