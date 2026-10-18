import TensorCore.Kernels.Datapath.Defs
import TensorCore.Kernels.EFT.Dyadic

/-! Bitvector normalization is FP32 truncation of the accumulator. -/

namespace TensorCore.Datapath

open EFMachine

set_option exponentiation.threshold 1024

theorem pow2_shift (g : ℤ) (a : ℕ) : ((2 ^ a : ℕ) : ℚ) * pow2 g = pow2 (g + a) := by
  rw [pow2_add, pow2_natCast, Rat.mul_comm]

theorem gt_mul_iff (n D M : ℕ) (hD : 0 < D) (hq : n / D ≤ M) :
    M * D < n ↔ n / D = M ∧ n % D ≠ 0 := by
  have h1 := Nat.div_add_mod n D
  have h2 := Nat.mod_lt n hD
  by_cases he : n / D = M
  · rw [he] at h1
    rw [Nat.mul_comm M D]
    constructor
    · intro h; exact ⟨he, by omega⟩
    · intro h; omega
  · have hlt : n / D + 1 ≤ M := by omega
    have hm := Nat.mul_le_mul_left D hlt
    rw [Nat.mul_add, Nat.mul_one] at hm
    rw [Nat.mul_comm M D]
    constructor
    · intro h; omega
    · intro h; exact absurd h.1 he

theorem dyadic_range (n P : ℕ) (g E r : ℤ) (k : ℕ)
    (hlo : 2 ^ P ≤ n) (hhi : n < 2 ^ (P + 1))
    (hE : E = max ((P : ℤ) + g) (-126)) (hr : r = E - 23 - g)
    (hk : k = if r ≤ 0 then n * 2 ^ (-r).toNat else n / 2 ^ r.toNat) (hk24 : k < 2 ^ 24) :
    maxFinite32 < (n : ℚ) * pow2 g ↔
      128 ≤ E ∨ (E = 127 ∧ 0 < r ∧ k = 2 ^ 24 - 1 ∧ n % 2 ^ r.toNat ≠ 0) := by
  have hpg := pow2_pos g
  have hlo' : pow2 ((P : ℤ) + g) ≤ (n : ℚ) * pow2 g := by
    rw [show (P : ℤ) + g = g + (P : ℕ) by omega, ← pow2_shift]
    exact Rat.mul_le_mul_of_nonneg_right (Rat.natCast_le_natCast.mpr hlo) (Rat.le_of_lt hpg)
  have hhi' : (n : ℚ) * pow2 g < pow2 ((P : ℤ) + 1 + g) := by
    rw [show (P : ℤ) + 1 + g = g + ((P + 1 : ℕ) : ℤ) by omega, ← pow2_shift]
    exact Rat.mul_lt_mul_of_pos_right (Rat.natCast_lt_natCast.mpr hhi) hpg
  by_cases h128 : 128 ≤ E
  · have hP : 128 ≤ (P : ℤ) + g := by omega
    have := pow2_le_of_le hP
    have := maxFinite32_lt_pow128
    constructor
    · intro; exact Or.inl h128
    · intro; grind
  · by_cases h127 : E = 127
    · have hP : (P : ℤ) + g = 127 := by omega
      by_cases hr0 : r ≤ 0
      · have hk' : k = n * 2 ^ (-r).toNat := by rw [hk, if_pos hr0]
        have hval : (n : ℚ) * pow2 g = ((k : ℕ) : ℚ) * pow2 104 := by
          rw [hk', Rat.natCast_mul, Rat.mul_assoc, pow2_shift]
          congr 2
          omega
        have hle : ((k : ℕ) : ℚ) ≤ ((2 ^ 24 - 1 : ℕ) : ℚ) := Rat.natCast_le_natCast.mpr (by omega)
        have := Rat.mul_le_mul_of_nonneg_right hle (Rat.le_of_lt (pow2_pos 104))
        unfold maxFinite32
        constructor
        · intro h; grind
        · intro h; omega
      · have hk' : k = n / 2 ^ r.toNat := by rw [hk, if_neg hr0]
        have hmax : maxFinite32 = (((2 ^ 24 - 1) * 2 ^ r.toNat : ℕ) : ℚ) * pow2 g := by
          unfold maxFinite32
          rw [Rat.natCast_mul, Rat.mul_assoc, pow2_shift]
          congr 2
          omega
        rw [hmax]
        have hiff : (((2 ^ 24 - 1) * 2 ^ r.toNat : ℕ) : ℚ) * pow2 g < (n : ℚ) * pow2 g ↔
            (2 ^ 24 - 1) * 2 ^ r.toNat < n := by
          constructor
          · intro h
            exact Rat.natCast_lt_natCast.mp ((Rat.mul_lt_mul_right hpg).mp h)
          · intro h
            exact Rat.mul_lt_mul_of_pos_right (Rat.natCast_lt_natCast.mpr h) hpg
        rw [hiff, gt_mul_iff _ _ _ (Nat.two_pow_pos _) (by omega), ← hk']
        constructor
        · rintro ⟨h1, h2⟩; exact Or.inr ⟨h127, by omega, h1, h2⟩
        · rintro (h | ⟨_, _, h1, h2⟩)
          · omega
          · exact ⟨h1, h2⟩
    · have hle : (P : ℤ) + 1 + g ≤ 127 := by omega
      have h127' : pow2 127 ≤ maxFinite32 := by decide +kernel
      have := pow2_le_of_le hle
      constructor
      · intro h; grind
      · intro h; omega

/-- FP32 truncation of `±n · 2^g` with `2^P ≤ n < 2^(P+1)`, in shifts of `n`. -/
theorem round32_truncate_dyadic (neg : Bool) (n P : ℕ) (g E r : ℤ) (k : ℕ)
    (hlo : 2 ^ P ≤ n) (hhi : n < 2 ^ (P + 1))
    (hE : E = max ((P : ℤ) + g) (-126)) (hr : r = E - 23 - g)
    (hk : k = if r ≤ 0 then n * 2 ^ (-r).toNat else n / 2 ^ r.toNat) :
    round32 .truncate ((if neg then -(n : ℚ) else n) * pow2 g) =
      if 128 ≤ E ∨ (E = 127 ∧ 0 < r ∧ k = 2 ^ 24 - 1 ∧ n % 2 ^ r.toNat ≠ 0) then none
      else some (encode32 neg E k) := by
  have hpg := pow2_pos g
  have hn0 : 0 < n := Nat.lt_of_lt_of_le (Nat.two_pow_pos P) hlo
  have hm : 0 < (n : ℚ) * pow2 g := Rat.mul_pos (Rat.natCast_pos.mpr hn0) hpg
  have hk24 : k < 2 ^ 24 := by
    rw [hk]
    split
    · rename_i hr0
      have hp : 2 ^ (P + 1) * 2 ^ (-r).toNat ≤ 2 ^ 24 := by
        rw [← Nat.pow_add]; exact Nat.pow_le_pow_right (by decide) (by omega)
      have := Nat.mul_lt_mul_of_pos_right hhi (Nat.two_pow_pos (-r).toNat)
      omega
    · rename_i hr0
      apply (Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _)).mpr
      rw [← Nat.pow_add]
      exact Nat.lt_of_lt_of_le hhi (Nat.pow_le_pow_right (by decide) (by omega))
  have habs : absQ ((if neg then -(n : ℚ) else n) * pow2 g) = (n : ℚ) * pow2 g := by
    cases neg
    · exact absQ_of_nonneg (Rat.le_of_lt hm)
    · simp only [if_true, Rat.neg_mul, absQ_neg]; exact absQ_of_nonneg (Rat.le_of_lt hm)
  have hx0 : (if neg then -(n : ℚ) else n) * pow2 g ≠ 0 := by
    cases neg <;> simp only [Bool.false_eq_true, if_false, if_true, Rat.neg_mul] <;> grind
  have hsign : decide ((if neg then -(n : ℚ) else n) * pow2 g < 0) = neg := by
    cases neg <;> simp only [Bool.false_eq_true, if_false, if_true, Rat.neg_mul] <;>
      simp only [decide_eq_true_eq, decide_eq_false_iff_not] <;> grind
  have hmag : magnitudeExponent ((n : ℚ) * pow2 g) = (P : ℤ) + g := by
    apply magnitudeExponent_eq_of_bounds
    · rw [show (P : ℤ) + g = g + (P : ℕ) by omega, ← pow2_shift]
      exact Rat.mul_le_mul_of_nonneg_right (Rat.natCast_le_natCast.mpr hlo) (Rat.le_of_lt hpg)
    · rw [show (P : ℤ) + g + 1 = g + ((P + 1 : ℕ) : ℤ) by omega, ← pow2_shift]
      exact Rat.mul_lt_mul_of_pos_right (Rat.natCast_lt_natCast.mpr hhi) hpg
  have hnorm : normExp ((n : ℚ) * pow2 g) = E := by
    unfold normExp emin32; rw [hmag, hE]
  have hround : roundedSignificand .truncate ((n : ℚ) * pow2 g) = k := by
    unfold roundedSignificand
    rw [hnorm]
    change ((n : ℚ) * pow2 g / pow2 (E - 23)).floor = _
    by_cases hr0 : r ≤ 0
    · rw [hk, if_pos hr0]
      have hq : (n : ℚ) * pow2 g / pow2 (E - 23) = (((n * 2 ^ (-r).toNat : ℕ) : ℤ) : ℚ) := by
        have hs : pow2 g = ((2 ^ (-r).toNat : ℕ) : ℚ) * pow2 (E - 23) := by
          rw [pow2_shift]; congr 1; omega
        have hne := Rat.ne_of_gt (pow2_pos (E - 23))
        rw [hs, Rat.intCast_natCast, Rat.natCast_mul, Rat.div_def]
        have hc := Rat.mul_inv_cancel (pow2 (E - 23)) hne
        grind
      rw [hq, Rat.floor_intCast]
    · rw [hk, if_neg hr0]
      have hq : (n : ℚ) * pow2 g / pow2 (E - 23) = (n : ℚ) / ((2 ^ r.toNat : ℕ) : ℚ) := by
        rw [show E - 23 = g + (r.toNat : ℕ) by omega]
        exact dyadic_div n g r.toNat
      rw [hq, floor_nat_div _ _ (Nat.two_pow_pos _)]
  have hcarry : carry E (k : ℤ) = (E, (k : ℤ)) := by
    unfold carry; rw [if_neg (by omega)]
  have hrange := dyadic_range n P g E r k hlo hhi hE hr hk hk24
  unfold round32 round32Core
  rw [habs]
  simp only [if_neg hx0, hnorm, hround, hcarry, hsign]
  by_cases hc : 128 ≤ E ∨ (E = 127 ∧ 0 < r ∧ k = 2 ^ 24 - 1 ∧ n % 2 ^ r.toNat ≠ 0)
  · rw [if_pos hc, if_pos (by rw [GT.gt, hrange]; exact hc)]
  · rw [if_neg hc, if_neg (by rw [GT.gt, hrange]; exact hc), if_neg (by omega)]

theorem toInt_eq_signed (s : BitVec w) :
    s.toInt = if s.msb then -((if s.msb then -s else s).toNat : ℤ)
      else ((if s.msb then -s else s).toNat : ℤ) := by
  rw [BitVec.toInt_eq_msb_cond]
  have hmsb := BitVec.msb_eq_decide s
  have hlt := s.isLt
  have hp := Nat.two_pow_pos (w - 1)
  cases hb : s.msb
  · rfl
  · rw [hb] at hmsb
    have hge : 2 ^ (w - 1) ≤ s.toNat := of_decide_eq_true hmsb.symm
    simp only [if_true, BitVec.toNat_neg]
    rw [Nat.mod_eq_of_lt (by omega)]
    omega

/-- The bitvector normalizer is FP32 truncation of the accumulator's value, bit for bit. -/
theorem normalize_eq {w : ℕ} (s : BitVec w) (e : Exp) (F : BitVec 5) (hw : 24 ≤ w) (hw' : w ≤ 64) :
    normalize s e F = round32 .truncate ((s.toInt : ℚ) * pow2 ((e.toNat : ℤ) - 256 - F.toNat)) := by
  have hsi := toInt_eq_signed s
  unfold normalize
  dsimp only
  generalize hm : (if s.msb = true then -s else s) = m at hsi
  have hsq : (s.toInt : ℚ) = if s.msb then -((m.toNat : ℕ) : ℚ) else ((m.toNat : ℕ) : ℚ) := by
    rw [hsi]; cases s.msb <;> simp [Rat.intCast_natCast]
  by_cases hz : m = 0
  · subst hz
    have h0 : (s.toInt : ℚ) = 0 := by rw [hsq]; simp
    rw [h0, Rat.zero_mul]
    simp only [beq_self_eq_true, if_true]
    decide +kernel
  · rw [if_neg (by simpa using hz)]
    have hmn : m.toNat ≠ 0 := fun h => hz (BitVec.eq_of_toNat_eq h)
    have hclz : m.clz.toNat < w := by
      have h := BitVec.clz_lt_iff_ne_zero.mpr hz
      simp only [BitVec.lt_def] at h
      have hw2 : (w : BitVec w).toNat = w := by
        change (BitVec.ofNat w w).toNat = w
        rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt Nat.lt_two_pow_self]
      rwa [hw2] at h
    have hlo := BitVec.two_pow_sub_clz_le_toNat_of_ne_zero (by omega) hz
    have hhi := BitVec.toNat_lt_two_pow_sub_clz (x := m)
    have he := e.isLt
    have hFl := F.isLt
    change e.toNat < 512 at he
    change F.toNat < 32 at hFl
    have hF9 : (BitVec.setWidth 9 F).toNat = F.toNat := by
      rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by omega)]
    have hleadN : (BitVec.ofNat 9 (w - 1) - BitVec.setWidth 9 m.clz).toNat = w - 1 - m.clz.toNat := by
      rw [BitVec.toNat_sub_of_le]
      · rw [BitVec.toNat_ofNat, BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by omega),
          Nat.mod_eq_of_lt (by omega)]
      · rw [BitVec.le_def, BitVec.toNat_ofNat, BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by omega),
          Nat.mod_eq_of_lt (by omega)]
        omega
    generalize hF' : BitVec.setWidth 9 F = F9 at hF9
    generalize hlead : BitVec.ofNat 9 (w - 1) - BitVec.setWidth 9 m.clz = lead at hleadN
    generalize hP : w - 1 - m.clz.toNat = P at hleadN hlo
    have hhi' : m.toNat < 2 ^ (P + 1) := by rw [show P + 1 = w - m.clz.toNat by omega]; exact hhi
    have hPw : P < w := by omega
    have hnormalP : decide (F9 + 130 - lead ≤ e) = decide (F.toNat + 130 ≤ P + e.toNat) := by
      apply decide_eq_decide.mpr
      rw [BitVec.le_def, BitVec.toNat_sub_of_le (by rw [BitVec.le_def, BitVec.toNat_add, hF9, hleadN]; change _ ≤ (F.toNat + 130) % 512; omega),
        BitVec.toNat_add, hF9, hleadN]
      change (F.toNat + 130) % 512 - P ≤ _ ↔ _
      omega
    have hovP : decide (F9 + 384 - lead ≤ e) = decide (F.toNat + 384 ≤ P + e.toNat) := by
      apply decide_eq_decide.mpr
      rw [BitVec.le_def, BitVec.toNat_sub_of_le (by rw [BitVec.le_def, BitVec.toNat_add, hF9, hleadN]; change _ ≤ (F.toNat + 384) % 512; omega),
        BitVec.toNat_add, hF9, hleadN]
      change (F.toNat + 384) % 512 - P ≤ _ ↔ _
      omega
    have h23P : decide (lead ≤ 23) = decide (P ≤ 23) := by
      apply decide_eq_decide.mpr; rw [BitVec.le_def, hleadN]; rfl
    have h107P : decide (F9 + 107 ≤ e) = decide (F.toNat + 107 ≤ e.toNat) := by
      apply decide_eq_decide.mpr
      rw [BitVec.le_def, BitVec.toNat_add, hF9]
      change (F.toNat + 107) % 512 ≤ _ ↔ _
      omega
    rw [hnormalP, hovP, h23P, h107P]
    generalize hleft : (if decide (F.toNat + 130 ≤ P + e.toNat) = true then decide (P ≤ 23)
      else decide (F.toNat + 107 ≤ e.toNat)) = left
    generalize hbiased : (if decide (F.toNat + 130 ≤ P + e.toNat) = true then e - (F9 + 129 - lead)
      else 1) = biased
    generalize hamount : (if decide (F.toNat + 130 ≤ P + e.toNat) = true then
        (if left = true then 23 - lead else lead - 23)
      else (if left = true then e - (F9 + 107) else F9 + 107 - e)) = amount
    generalize hkb : (if left = true then m <<< amount else m >>> amount) = kb
    have hbN : (biased.toNat : ℤ) = max ((P : ℤ) + ((e.toNat : ℤ) - 256 - F.toNat)) (-126) + 127 := by
      rw [← hbiased]
      by_cases hn : F.toNat + 130 ≤ P + e.toNat
      · simp only [hn, decide_true, if_true]
        have h1 : (F9 + 129 - lead).toNat = F.toNat + 129 - P := by
          rw [BitVec.toNat_sub_of_le (by rw [BitVec.le_def, BitVec.toNat_add, hF9, hleadN]; change _ ≤ (F.toNat + 129) % 512; omega),
            BitVec.toNat_add, hF9, hleadN]
          change (F.toNat + 129) % 512 - P = _
          omega
        rw [BitVec.toNat_sub_of_le (by rw [BitVec.le_def, h1]; omega), h1]
        omega
      · simp only [hn, decide_false, Bool.false_eq_true, if_false]
        change ((1 : ℕ) : ℤ) = _
        omega
    have hleftN : left = decide (((if F.toNat + 130 ≤ P + e.toNat then (P : ℤ) - 23
        else (F.toNat : ℤ) + 107 - e.toNat)) ≤ 0) := by
      rw [← hleft]
      by_cases hn : F.toNat + 130 ≤ P + e.toNat
      · simp only [hn, decide_true, if_true]; apply decide_eq_decide.mpr; omega
      · simp only [hn, decide_false, Bool.false_eq_true, if_false]; apply decide_eq_decide.mpr; omega
    generalize hr : (if F.toNat + 130 ≤ P + e.toNat then (P : ℤ) - 23
      else (F.toNat : ℤ) + 107 - e.toNat) = r at hleftN
    have hamtN : amount.toNat = if r ≤ 0 then (-r).toNat else r.toNat := by
      rw [← hamount, hleftN]
      by_cases hn : F.toNat + 130 ≤ P + e.toNat
      · rw [if_pos hn] at hr
        simp only [hn, decide_true, if_true]
        by_cases hl : r ≤ 0
        · simp only [hl, decide_true, if_true]
          rw [BitVec.toNat_sub_of_le (by rw [BitVec.le_def, hleadN]; change _ ≤ 23; omega), hleadN]
          change 23 - P = _; omega
        · simp only [hl, decide_false, Bool.false_eq_true, if_false]
          rw [BitVec.toNat_sub_of_le (by rw [BitVec.le_def, hleadN]; change 23 ≤ _; omega), hleadN]
          change P - 23 = _; omega
      · rw [if_neg hn] at hr
        simp only [hn, decide_false, Bool.false_eq_true, if_false]
        by_cases hl : r ≤ 0
        · simp only [hl, decide_true, if_true]
          rw [BitVec.toNat_sub_of_le (by rw [BitVec.le_def, BitVec.toNat_add, hF9]; change (F.toNat + 107) % 512 ≤ _; omega),
            BitVec.toNat_add, hF9]
          change _ - (F.toNat + 107) % 512 = _; omega
        · simp only [hl, decide_false, Bool.false_eq_true, if_false]
          rw [BitVec.toNat_sub_of_le (by rw [BitVec.le_def, BitVec.toNat_add, hF9]; change _ ≤ (F.toNat + 107) % 512; omega),
            BitVec.toNat_add, hF9]
          change (F.toNat + 107) % 512 - _ = _; omega
    have hrange : (r ≤ 0 → P + 1 + (-r).toNat ≤ 24) ∧ (0 < r → P + 1 ≤ 24 + r.toNat) := by
      by_cases hn : F.toNat + 130 ≤ P + e.toNat
      · rw [if_pos hn] at hr; omega
      · rw [if_neg hn] at hr; omega
    have hkN : kb.toNat = if r ≤ 0 then m.toNat * 2 ^ (-r).toNat else m.toNat / 2 ^ r.toNat := by
      rw [← hkb, hleftN]
      by_cases hl : r ≤ 0
      · simp only [hl, decide_true, if_true]
        rw [BitVec.shiftLeft_eq', BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, hamtN, if_pos hl]
        apply Nat.mod_eq_of_lt
        have h1 := Nat.mul_lt_mul_of_pos_right hhi' (Nat.two_pow_pos (-r).toNat)
        rw [← Nat.pow_add] at h1
        exact Nat.lt_of_lt_of_le h1 (Nat.pow_le_pow_right (by decide) (by have := hrange.1 hl; omega))
      · simp only [hl, decide_false, Bool.false_eq_true, if_false]
        rw [BitVec.ushiftRight_eq', BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, hamtN, if_neg hl]
    have hk24 : kb.toNat < 2 ^ 24 := by
      rw [hkN]
      split
      · rename_i hl
        have h1 := Nat.mul_lt_mul_of_pos_right hhi' (Nat.two_pow_pos (-r).toNat)
        rw [← Nat.pow_add] at h1
        exact Nat.lt_of_lt_of_le h1 (Nat.pow_le_pow_right (by decide) (hrange.1 hl))
      · rename_i hl
        apply (Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _)).mpr
        rw [← Nat.pow_add]
        exact Nat.lt_of_lt_of_le hhi' (Nat.pow_le_pow_right (by decide) (by have := hrange.2 (by omega); omega))
    have hE := (rfl : max ((P : ℤ) + ((e.toNat : ℤ) - 256 - F.toNat)) (-126) =
      max ((P : ℤ) + ((e.toNat : ℤ) - 256 - F.toNat)) (-126))
    have hrE : r = max ((P : ℤ) + ((e.toNat : ℤ) - 256 - F.toNat)) (-126) - 23 -
        ((e.toNat : ℤ) - 256 - F.toNat) := by
      by_cases hn : F.toNat + 130 ≤ P + e.toNat
      · rw [if_pos hn] at hr; omega
      · rw [if_neg hn] at hr; omega
    rw [hsq, round32_truncate_dyadic s.msb m.toNat P _ _ r kb.toNat hlo hhi' hE hrE hkN]
    generalize hEv : max ((P : ℤ) + ((e.toNat : ℤ) - 256 - F.toNat)) (-126) = E at hbN hrE
    have hw24 : 2 ^ 24 ≤ 2 ^ w := Nat.pow_le_pow_right (by decide) hw
    have hcond : (decide (F.toNat + 384 ≤ P + e.toNat) ||
        (biased == 254 && kb == 16777215 && !(left || kb <<< amount == m))) = true ↔
        (128 ≤ E ∨ (E = 127 ∧ 0 < r ∧ kb.toNat = 2 ^ 24 - 1 ∧ m.toNat % 2 ^ r.toNat ≠ 0)) := by
      have h1 : (F.toNat + 384 ≤ P + e.toNat) ↔ 128 ≤ E := by omega
      have h2 : biased = 254 ↔ E = 127 := by
        rw [BitVec.toNat_eq]; change biased.toNat = 254 ↔ _; omega
      have h3 : kb = 16777215 ↔ kb.toNat = 2 ^ 24 - 1 := by
        have hl : (16777215 : BitVec w).toNat = 16777215 := by
          rw [show (16777215 : BitVec w) = BitVec.ofNat w 16777215 from rfl, BitVec.toNat_ofNat]
          exact Nat.mod_eq_of_lt (by omega)
        rw [BitVec.toNat_eq, hl]
      have h4 : 0 < r → (kb <<< amount = m ↔ m.toNat % 2 ^ r.toNat = 0) := by
        intro hl
        rw [BitVec.toNat_eq, BitVec.shiftLeft_eq', BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, hamtN,
          hkN, if_neg (by omega), if_neg (by omega)]
        generalize r.toNat = d
        rw [Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.div_mul_le_self _ _) m.isLt)]
        have := Nat.mod_add_div' m.toNat (2 ^ d)
        omega
      rw [hleftN]
      simp only [Bool.or_eq_true, Bool.and_eq_true, Bool.not_eq_true', Bool.or_eq_false_iff,
        decide_eq_true_eq, decide_eq_false_iff_not, beq_iff_eq, beq_eq_false_iff_ne, h1, h2, h3]
      by_cases hl : r ≤ 0
      · simp only [hl, not_true_eq_false, false_and, and_false, or_false]
        omega
      · rw [ne_eq, h4 (by omega)]
        simp only [hl, not_false_eq_true, true_and]
        omega
    by_cases hc : 128 ≤ E ∨ (E = 127 ∧ 0 < r ∧ kb.toNat = 2 ^ 24 - 1 ∧ m.toNat % 2 ^ r.toNat ≠ 0)
    · rw [if_pos (hcond.mpr hc), if_pos hc]
    · rw [if_neg (mt hcond.mp hc), if_neg hc]
      apply congrArg some
      have hb : biased.toNat ≤ 254 := by omega
      have hk32 : (BitVec.setWidth 32 kb).toNat = kb.toNat := by
        rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by omega)]
      have hb32 : (BitVec.setWidth 32 biased).toNat = biased.toNat := by
        rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by omega)]
      apply BitVec.eq_of_toNat_eq
      unfold encode32
      by_cases hsmall : kb.toNat < 8388608
      · rw [if_pos (show BitVec.setWidth 32 kb < 8388608 by rw [BitVec.lt_def, hk32]; exact hsmall),
          if_pos (show ((kb.toNat : ℤ) < 2 ^ 23) by omega)]
        cases s.msb <;> simp [BitVec.toNat_add, hk32] <;> omega
      · rw [if_neg (show ¬ BitVec.setWidth 32 kb < 8388608 by rw [BitVec.lt_def, hk32]; exact hsmall),
          if_neg (show ¬ ((kb.toNat : ℤ) < 2 ^ 23) by omega)]
        have hshift : (BitVec.setWidth 32 biased <<< 23).toNat = biased.toNat * 8388608 := by
          rw [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, hb32]
          exact Nat.mod_eq_of_lt (by omega)
        cases s.msb <;> simp [BitVec.toNat_add, hshift] <;> omega

end TensorCore.Datapath
