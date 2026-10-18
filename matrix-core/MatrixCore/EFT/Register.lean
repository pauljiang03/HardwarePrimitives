import MatrixCore.EFT.Core
import MatrixCore.Specification.Stages

/-! # A 576-bit register in units of `2^-298`

`2^-298` is the lowest bit of a product of two FP32 values. FP32 rounding of a register by a
leading-zero count, shifts and comparisons, proven equal to `rne32`; terms as registers; and the
formats whose products fit. -/

namespace MatrixCore

set_option exponentiation.threshold 1024

/-! ## Rounding a natural multiple of `2^-298` -/

/-- `rneInt (n / 2^s)` on naturals: the quotient, plus one above the half or on an odd tie. -/
def rneShift (n s : ℕ) : ℕ :=
  if 2 ^ s < 2 * (n % 2 ^ s) ∨ (2 * (n % 2 ^ s) = 2 ^ s ∧ n / 2 ^ s % 2 = 1) then n / 2 ^ s + 1
  else n / 2 ^ s

/-- `fl{±n · 2^-298}`, from the position of the leading bit of `n`. -/
def round298 (negative : Bool) (n : ℕ) : Option F32 :=
  if n = 0 then some 0
  else
    let top := max n.log2 172
    let k := rneShift n (top - 23)
    let f : ℤ × ℕ := if k = 16777216 then ((top : ℤ) - 297, 8388608) else ((top : ℤ) - 298, k)
    if f.1 > 127 then none else some (encode32 negative f.1 f.2)

theorem natCast_mul_pow2_neg (a s : ℕ) :
    ((2 ^ s * a : ℕ) : ℚ) * pow2 (-(s : ℤ)) = a := by
  rw [Rat.natCast_mul, ← pow2_natCast, Rat.mul_comm (pow2 _), Rat.mul_assoc, ← pow2_add,
    show (s : ℤ) + -(s : ℤ) = 0 by omega, pow2_zero, Rat.mul_one]

theorem natCast_mul_pow2_lt_iff {a b : ℕ} {s : ℤ} :
    (a : ℚ) * pow2 s < (b : ℚ) * pow2 s ↔ a < b := by
  constructor
  · intro h
    rcases Nat.lt_or_ge a b with hab | hab
    · exact hab
    · have := Rat.mul_le_mul_of_nonneg_right (Rat.natCast_le_natCast.mpr hab)
        (Rat.le_of_lt (pow2_pos s))
      exact absurd h (Rat.not_lt.mpr this)
  · intro h
    exact Rat.mul_lt_mul_of_pos_right (Rat.natCast_lt_natCast.mpr h) (pow2_pos s)

theorem natCast_mul_pow2_eq_iff {a b : ℕ} {s : ℤ} :
    (a : ℚ) * pow2 s = (b : ℚ) * pow2 s ↔ a = b := by
  constructor
  · intro h
    rcases Nat.lt_trichotomy a b with hab | hab | hab
    · exact absurd h (Rat.ne_of_lt (natCast_mul_pow2_lt_iff.mpr hab))
    · exact hab
    · exact absurd h (Rat.ne_of_gt (natCast_mul_pow2_lt_iff.mpr hab))
  · rintro rfl; rfl

theorem shiftNat_neg (n s : ℕ) : Spec.shiftNat n (-(s : ℤ)) = n / 2 ^ s := by
  unfold Spec.shiftNat
  split
  · rename_i h
    have : s = 0 := by omega
    subst this; simp
  · congr 2; omega

theorem rneInt_shift (n s : ℕ) : rneInt ((n : ℚ) * pow2 (-(s : ℤ))) = (rneShift n s : ℤ) := by
  have hfl : ((n : ℚ) * pow2 (-(s : ℤ))).floor = ((n / 2 ^ s : ℕ) : ℤ) := by
    rw [Spec.floor_shiftNat, shiftNat_neg]
  have hsplit : (n : ℚ) * pow2 (-(s : ℤ)) =
      ((n / 2 ^ s : ℕ) : ℚ) + ((n % 2 ^ s : ℕ) : ℚ) * pow2 (-(s : ℤ)) := by
    conv => lhs; rw [← Nat.mod_add_div n (2 ^ s)]
    rw [Rat.natCast_add, Rat.add_mul, natCast_mul_pow2_neg, Rat.add_comm]
  have hfrac : (n : ℚ) * pow2 (-(s : ℤ)) - ((((n / 2 ^ s : ℕ) : ℤ)) : ℚ) =
      ((n % 2 ^ s : ℕ) : ℚ) * pow2 (-(s : ℤ)) := by
    rw [hsplit, Rat.intCast_natCast]; grind
  have hone : (1 : ℚ) = ((2 ^ s : ℕ) : ℚ) * pow2 (-(s : ℤ)) := by
    rw [show 2 ^ s = 2 ^ s * 1 by omega, natCast_mul_pow2_neg]; rfl
  have htwo : 2 * (((n % 2 ^ s : ℕ) : ℚ) * pow2 (-(s : ℤ))) =
      ((2 * (n % 2 ^ s) : ℕ) : ℚ) * pow2 (-(s : ℤ)) := by
    rw [Rat.natCast_mul, Rat.mul_assoc]; rfl
  have hgt : 1 < 2 * ((n : ℚ) * pow2 (-(s : ℤ)) - ((((n / 2 ^ s : ℕ) : ℤ)) : ℚ)) ↔
      2 ^ s < 2 * (n % 2 ^ s) := by
    rw [hfrac, htwo, hone]; exact natCast_mul_pow2_lt_iff
  have heq : 2 * ((n : ℚ) * pow2 (-(s : ℤ)) - ((((n / 2 ^ s : ℕ) : ℤ)) : ℚ)) = 1 ↔
      2 * (n % 2 ^ s) = 2 ^ s := by
    rw [hfrac, htwo, hone]; exact natCast_mul_pow2_eq_iff
  have hodd : (((n / 2 ^ s : ℕ) : ℤ)) % 2 = 1 ↔ n / 2 ^ s % 2 = 1 := by omega
  unfold rneInt rneShift
  rw [hfl]
  by_cases h1 : 2 ^ s < 2 * (n % 2 ^ s)
  · rw [if_pos (Or.inl (hgt.mpr h1)), if_pos (Or.inl h1)]; push_cast; rfl
  · by_cases h2 : 2 * (n % 2 ^ s) = 2 ^ s ∧ n / 2 ^ s % 2 = 1
    · rw [if_pos (Or.inr ⟨heq.mpr h2.1, hodd.mpr h2.2⟩), if_pos (Or.inr h2)]; push_cast; rfl
    · rw [if_neg (by rw [hgt, heq, hodd]; exact not_or.mpr ⟨h1, h2⟩), if_neg (not_or.mpr ⟨h1, h2⟩)]

/-- The natural rounding is `fl{±n · 2^-298}`. -/
theorem round298_eq (negative : Bool) (n : ℕ) :
    round298 negative n = rne32 ((if negative then -(n : ℚ) else n) * pow2 (-298)) := by
  unfold round298 rne32
  by_cases hn : n = 0
  · subst hn; simp
  · have hpos : (0 : ℚ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
    have hx : (if negative then -(n : ℚ) else n) * pow2 (-298) ≠ 0 := by
      have hm : (n : ℚ) * pow2 (-298) ≠ 0 := Rat.ne_of_gt (Rat.mul_pos hpos (pow2_pos _))
      cases negative
      · simpa using hm
      · simp only [↓reduceIte, Rat.neg_mul]; grind
    have habs : absQ ((if negative then -(n : ℚ) else n) * pow2 (-298)) = (n : ℚ) * pow2 (-298) := by
      rw [absQ_mul_pos _ _ (pow2_pos _)]
      cases negative
      · simp [absQ_of_nonneg (Rat.le_of_lt hpos)]
      · simp [absQ_neg, absQ_of_nonneg (Rat.le_of_lt hpos)]
    have hsign : decide ((if negative then -(n : ℚ) else n) * pow2 (-298) < 0) = negative := by
      have := pow2_pos (-298)
      cases negative
      · simp only [Bool.false_eq_true, ↓reduceIte, decide_eq_false_iff_not, Rat.not_lt]
        exact Rat.mul_nonneg (Rat.le_of_lt hpos) (Rat.le_of_lt this)
      · simp only [↓reduceIte, decide_eq_true_eq]
        have := Rat.mul_pos hpos this
        rw [Rat.neg_mul]; grind
    have hlog : log2Floor ((n : ℚ) * pow2 (-298)) = (n.log2 : ℤ) - 298 := by
      rw [log2Floor_mul_pow2 hpos, Spec.log2Floor_natCast hn]; omega
    have hnorm : normExp ((n : ℚ) * pow2 (-298)) = ((max n.log2 172 : ℕ) : ℤ) - 298 := by
      unfold normExp; rw [hlog]; omega
    have hdiv : (n : ℚ) * pow2 (-298) / pow2 (((max n.log2 172 : ℕ) : ℤ) - 298 - 23) =
        (n : ℚ) * pow2 (-((max n.log2 172 - 23 : ℕ) : ℤ)) := by
      rw [Rat.div_def, Rat.mul_assoc, ← Rat.div_def, ← pow2_sub]
      congr 2; omega
    simp only [if_neg hx, if_neg hn, habs, hsign]
    unfold rneFields
    simp only [hnorm, hdiv, rneInt_shift]
    by_cases hk : rneShift n (max n.log2 172 - 23) = 16777216
    · have hk' : ((rneShift n (max n.log2 172 - 23) : ℕ) : ℤ) = 16777216 := by rw [hk]; rfl
      simp only [hk, show ((16777216 : ℕ) : ℤ) = 16777216 from rfl, ↓reduceIte,
        show ((max n.log2 172 : ℕ) : ℤ) - 298 + 1 = ((max n.log2 172 : ℕ) : ℤ) - 297 by omega]
    · have hk' : ((rneShift n (max n.log2 172 - 23) : ℕ) : ℤ) ≠ 16777216 := by omega
      simp only [hk, hk', ↓reduceIte, Int.toNat_natCast]

/-! ## The register -/

/-- A 576-bit two's-complement register in units of `2^-298`. -/
abbrev Reg := BitVec 576

/-- `m >>> s`, rounded to nearest even on the bits shifted out. -/
def roundShift (m : Reg) (s : ℕ) : Reg :=
  let k := m >>> s
  let r := m - (k <<< s)
  let half := (1 : Reg) <<< (s - 1)
  if half < r || (r == half && (k &&& 1) == 1) then k + 1 else k

/-- `fl{±m · 2^-298}` by a leading-zero count, shifts and comparisons on the register `m`. -/
def roundReg (negative : Bool) (m : Reg) : Option F32 :=
  if m = 0 then some 0
  else
    let top := max (575 - m.clz.toNat) 172
    let k := roundShift m (top - 23)
    let f : ℤ × ℕ := if k == 16777216 then ((top : ℤ) - 297, 8388608) else ((top : ℤ) - 298, k.toNat)
    if f.1 > 127 then none else some (encode32 negative f.1 f.2)

theorem Reg.toNat_one : (1 : Reg).toNat = 1 := rfl

theorem Reg.toNat_ne_zero {m : Reg} (hm : m ≠ 0) : m.toNat ≠ 0 := fun h =>
  hm (BitVec.eq_of_toNat_eq (by simp [h]))

theorem clz_log2 {m : Reg} (hm : m ≠ 0) : 575 - m.clz.toNat = m.toNat.log2 := by
  have hl := BitVec.two_pow_sub_clz_le_toNat_of_ne_zero (x := m) (by decide) hm
  have hu := BitVec.toNat_lt_two_pow_sub_clz (x := m)
  have hn := Reg.toNat_ne_zero hm
  rw [show 576 - 1 - m.clz.toNat = 575 - m.clz.toNat by omega] at hl
  apply Nat.le_antisymm
  · rcases Nat.lt_or_ge m.toNat.log2 (575 - m.clz.toNat) with h | h
    · exact absurd (Nat.lt_of_lt_of_le ((Nat.log2_lt hn).mp h) hl) (Nat.lt_irrefl _)
    · exact h
  · have := (Nat.log2_lt hn).mpr hu
    omega

theorem roundShift_toNat (m : Reg) (s : ℕ) (hs1 : 1 ≤ s) (hs : s ≤ 552) :
    (roundShift m s).toNat = rneShift m.toNat s := by
  unfold roundShift
  dsimp only
  have hlt := m.isLt
  have hP : 0 < 2 ^ s := Nat.two_pow_pos s
  have hq : (m >>> s).toNat = m.toNat / 2 ^ s := by
    rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
  have hdm := Nat.div_mul_le_self m.toNat (2 ^ s)
  have hql : ((m >>> s) <<< s).toNat = m.toNat / 2 ^ s * 2 ^ s := by
    rw [BitVec.toNat_shiftLeft, hq, Nat.shiftLeft_eq, Nat.mod_eq_of_lt (by omega)]
  have hr : (m - ((m >>> s) <<< s)).toNat = m.toNat % 2 ^ s := by
    rw [BitVec.toNat_sub_of_le (by rw [BitVec.le_def, hql]; exact hdm), hql]
    have := Nat.mod_add_div m.toNat (2 ^ s)
    rw [Nat.mul_comm] at this
    omega
  have hhalf : ((1 : Reg) <<< (s - 1)).toNat = 2 ^ (s - 1) := by
    rw [BitVec.toNat_shiftLeft, Reg.toNat_one, Nat.shiftLeft_eq, Nat.one_mul]
    exact Nat.mod_eq_of_lt (Nat.pow_lt_pow_right (by decide) (by omega))
  have h2 : 2 ^ s = 2 * 2 ^ (s - 1) := by
    rw [← Nat.pow_succ']; congr 1; omega
  have hodd : ((m >>> s) &&& 1).toNat = m.toNat / 2 ^ s % 2 := by
    rw [BitVec.toNat_and, Reg.toNat_one, Nat.and_one_is_mod, hq]
  have hsmall : m.toNat / 2 ^ s + 1 < 2 ^ 576 := by
    have : 2 ^ s ≥ 2 := by
      calc 2 ^ s ≥ 2 ^ 1 := Nat.pow_le_pow_right (by decide) hs1
        _ = 2 := rfl
    have hd : m.toNat / 2 ^ s < 2 ^ 575 := by
      apply Nat.div_lt_of_lt_mul
      calc m.toNat < 2 ^ 576 := hlt
        _ = 2 * 2 ^ 575 := by rw [Nat.pow_succ, Nat.mul_comm]
        _ ≤ 2 ^ s * 2 ^ 575 := Nat.mul_le_mul_right _ this
    have : 2 ^ 575 < 2 ^ 576 := Nat.pow_lt_pow_right (by decide) (by decide)
    omega
  have hcond : ((1 : Reg) <<< (s - 1) < m - ((m >>> s) <<< s) ||
      (m - ((m >>> s) <<< s) == (1 : Reg) <<< (s - 1) && ((m >>> s) &&& 1) == 1)) =
      decide (2 ^ s < 2 * (m.toNat % 2 ^ s) ∨
        (2 * (m.toNat % 2 ^ s) = 2 ^ s ∧ m.toNat / 2 ^ s % 2 = 1)) := by
    have e1 : ((1 : Reg) <<< (s - 1) < m - ((m >>> s) <<< s)) ↔ 2 ^ s < 2 * (m.toNat % 2 ^ s) := by
      rw [BitVec.lt_def, hhalf, hr, h2]; omega
    have e2 : (m - ((m >>> s) <<< s) == (1 : Reg) <<< (s - 1)) = true ↔
        2 * (m.toNat % 2 ^ s) = 2 ^ s := by
      rw [beq_iff_eq, BitVec.toNat_eq, hhalf, hr, h2]; omega
    have e3 : (((m >>> s) &&& 1) == 1) = true ↔ m.toNat / 2 ^ s % 2 = 1 := by
      rw [beq_iff_eq, BitVec.toNat_eq, hodd, Reg.toNat_one]
    rw [Bool.eq_iff_iff, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_iff, decide_eq_true_iff,
      e1, e2, e3]
  rw [hcond]
  unfold rneShift
  by_cases hc : 2 ^ s < 2 * (m.toNat % 2 ^ s) ∨
      (2 * (m.toNat % 2 ^ s) = 2 ^ s ∧ m.toNat / 2 ^ s % 2 = 1)
  · rw [if_pos (decide_eq_true hc), if_pos hc, BitVec.toNat_add, hq, Reg.toNat_one,
      Nat.mod_eq_of_lt hsmall]
  · rw [if_neg (by simpa using hc), if_neg hc, hq]

/-- The register rounding is the natural rounding of the register's value. -/
theorem roundReg_eq (negative : Bool) (m : Reg) : roundReg negative m = round298 negative m.toNat := by
  unfold roundReg round298
  by_cases hm : m = 0
  · subst hm; simp
  · have hn := Reg.toNat_ne_zero hm
    have hlog : m.toNat.log2 < 576 := (Nat.log2_lt hn).mpr m.isLt
    simp only [if_neg hm, if_neg hn, clz_log2 hm]
    have hK := roundShift_toNat m (max m.toNat.log2 172 - 23) (by omega) (by omega)
    generalize roundShift m (max m.toNat.log2 172 - 23) = K at hK ⊢
    have hb : (K == 16777216) = decide (rneShift m.toNat (max m.toNat.log2 172 - 23) = 16777216) := by
      rw [Bool.eq_iff_iff, beq_iff_eq, BitVec.toNat_eq, hK, decide_eq_true_iff]; rfl
    rw [hb, hK]
    simp only [decide_eq_true_eq]

/-! ## Terms in the register -/

/-- A term as a register: `±m · 2^(e − t + 298)`. -/
def Unpacked.toReg (u : Unpacked) : Reg :=
  let r := BitVec.ofNat 576 u.m <<< (u.e - u.t + 298).toNat
  if u.negative then -r else r

/-- The value of a term in units of `2^-298`. -/
def Unpacked.coeff298 (u : Unpacked) : ℤ :=
  if u.negative then -((u.m * 2 ^ (u.e - u.t + 298).toNat : ℕ) : ℤ)
  else ((u.m * 2 ^ (u.e - u.t + 298).toNat : ℕ) : ℤ)

theorem Unpacked.coeff298_value {u : Unpacked} (h : -298 ≤ u.e - u.t) :
    (u.coeff298 : ℚ) * pow2 (-298) = u.value := by
  have hv : ((u.m * 2 ^ (u.e - u.t + 298).toNat : ℕ) : ℚ) * pow2 (-298) =
      (u.m : ℚ) * pow2 (u.e - u.t) := by
    rw [Rat.natCast_mul, ← pow2_natCast, Rat.mul_assoc, ← pow2_add]
    congr 2; omega
  unfold coeff298 value
  cases u.negative
  · simpa [Rat.intCast_natCast] using hv
  · simp only [↓reduceIte, Rat.intCast_neg, Rat.intCast_natCast, Rat.neg_mul]
    rw [hv]

theorem bmod576 {v : ℤ} (h1 : -2 ^ 575 ≤ v) (h2 : v < 2 ^ 575) : v.bmod (2 ^ 576) = v := by
  apply Int.bmod_eq_of_le
  · have : ((2 ^ 576 : ℕ) : ℤ) / 2 = 2 ^ 575 := by decide
    omega
  · have : (((2 ^ 576 : ℕ) : ℤ) + 1) / 2 = 2 ^ 575 := by decide
    omega

theorem Reg.toInt_of_lt {r : Reg} (h : r.toNat < 2 ^ 575) : r.toInt = r.toNat := by
  rw [BitVec.toInt_eq_msb_cond, BitVec.msb_eq_decide]
  simp only [show 576 - 1 = 575 from rfl, decide_eq_true_eq]
  rw [if_neg (Nat.not_le.mpr h)]

theorem Unpacked.toReg_toInt {u : Unpacked} (hb : u.m * 2 ^ (u.e - u.t + 298).toNat < 2 ^ 575) :
    u.toReg.toInt = u.coeff298 := by
  have h575 : (2 : ℕ) ^ 575 < 2 ^ 576 := Nat.pow_lt_pow_right (by decide) (by decide)
  have hm : u.m < 2 ^ 576 := by
    have := Nat.le_mul_of_pos_right u.m (Nat.two_pow_pos (u.e - u.t + 298).toNat)
    omega
  have hr : (BitVec.ofNat 576 u.m <<< (u.e - u.t + 298).toNat).toNat =
      u.m * 2 ^ (u.e - u.t + 298).toNat := by
    rw [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hm, Nat.shiftLeft_eq,
      Nat.mod_eq_of_lt (by omega)]
  have hi := Reg.toInt_of_lt (hr ▸ hb)
  unfold toReg coeff298
  cases u.negative
  · simpa [hr] using hi
  · simp only [↓reduceIte]
    rw [BitVec.toInt_neg, hi, hr, bmod576] <;> omega

/-! ## Formats whose products fit the register -/

/-- The lowest grid exponent `e − t` of a format's finite values. -/
def Format.lowExp (f : Format) : ℤ := f.emin - f.mantissaBits

/-- A bound on the exponent `e` of a format's finite values. -/
def Format.highExp (f : Format) : ℤ := ((2 ^ f.exponentBits : ℕ) : ℤ) - f.bias

def InputFormat.lowExp : InputFormat → ℤ
  | .packed f => f.lowExp
  | .xf32 => fp32.emin - 10

def InputFormat.highExp : InputFormat → ℤ
  | .packed f => f.highExp
  | .xf32 => fp32.highExp

/-- The products of a model lie on the grid `2^-298` and have exponents at most `258`. -/
def Model.FitsReg (P : Model) : Prop :=
  -298 ≤ P.a.lowExp + P.b.lowExp ∧ P.a.highExp + P.b.highExp ≤ 258

instance (P : Model) : Decidable P.FitsReg := by unfold Model.FitsReg; infer_instance

theorem unpackFields_exp (f : Format) (negative : Bool) (E M : ℕ) (hE : E < 2 ^ f.exponentBits) :
    f.lowExp ≤ (f.unpackFields negative E M).e - (f.unpackFields negative E M).t ∧
      (f.unpackFields negative E M).e ≤ f.highExp := by
  have h1 : (1 : ℤ) ≤ ((2 ^ f.exponentBits : ℕ) : ℤ) := by
    have := Nat.two_pow_pos f.exponentBits; omega
  have h2 : (E : ℤ) < ((2 ^ f.exponentBits : ℕ) : ℤ) := by omega
  unfold Format.unpackFields Format.lowExp Format.highExp Format.emin
  generalize ((2 ^ f.exponentBits : ℕ) : ℤ) = B at h1 h2 ⊢
  split <;> (dsimp only; omega)

theorem decodeNat_exp {f : Format} {n : ℕ} {u : Unpacked} (h : f.decodeNat n = .finite u) :
    f.lowExp ≤ u.e - u.t ∧ u.e ≤ f.highExp := by
  have hE := Nat.mod_lt (n / 2 ^ f.mantissaBits) (Nat.two_pow_pos f.exponentBits)
  unfold Format.decodeNat at h
  dsimp only at h
  split at h
  · split at h
    · split at h <;> simp at h
    · simp only [Datum.finite.injEq] at h; subst h; exact unpackFields_exp _ _ _ _ hE
  · split at h
    · simp at h
    · simp only [Datum.finite.injEq] at h; subst h; exact unpackFields_exp _ _ _ _ hE

theorem read_exp {i : InputFormat} {w : i.Word} {u : Unpacked}
    (h : (i.read w).toFinite = some u) : i.lowExp ≤ u.e - u.t ∧ u.e ≤ i.highExp := by
  cases i with
  | packed f =>
    simp only [InputFormat.read, Format.decode] at h
    cases hd : f.decodeNat w.toNat <;> rw [hd] at h <;> simp [Datum.toFinite] at h
    subst h
    exact decodeNat_exp hd
  | xf32 =>
    simp only [InputFormat.read] at h
    cases hd : fp32.decode w <;> rw [hd] at h <;> simp [Datum.toFinite] at h
    subst h
    obtain ⟨h1, h2⟩ := decodeNat_exp (f := fp32) (n := BitVec.toNat w) hd
    obtain ⟨ht, _⟩ := decodeNat_bounded (f := fp32) (n := BitVec.toNat w) hd
    simp only [InputFormat.truncateXF32, InputFormat.lowExp, InputFormat.highExp]
    simp only [Format.lowExp, ht] at h1
    exact ⟨by simp only [Format.emin] at h1 ⊢; omega, h2⟩

theorem coeff298_natAbs (u : Unpacked) :
    u.coeff298.natAbs = u.m * 2 ^ (u.e - u.t + 298).toNat := by
  unfold Unpacked.coeff298
  cases u.negative <;> simp only [Bool.false_eq_true, ↓reduceIte, Int.natAbs_neg, Int.natAbs_natCast]

theorem coeff298_lt {u : Unpacked} {j : ℕ} (hg : -298 ≤ u.e - u.t) (hm : u.m < 2 ^ (u.t + j)) :
    u.coeff298.natAbs < 2 ^ ((u.e + 298 + j).toNat) := by
  rw [coeff298_natAbs]
  calc u.m * 2 ^ (u.e - u.t + 298).toNat < 2 ^ (u.t + j) * 2 ^ (u.e - u.t + 298).toNat :=
        Nat.mul_lt_mul_of_pos_right hm (Nat.two_pow_pos _)
    _ = 2 ^ ((u.e + 298 + j).toNat) := by rw [← Nat.pow_add]; congr 1; omega

/-- The products of a decoded block of a model that fits: on `2^-298`, exponent at most `258`. -/
theorem products_fit {P : Model} (hP : P.FitsReg) {x : BlockInput P} {px : Prepared}
    (h : prepare x = some px) : ∀ p ∈ px.p, -298 ≤ p.e - p.t ∧ p.e ≤ 258 ∧ p.m < 2 ^ (p.t + 2) := by
  obtain ⟨hlo, hhi⟩ := hP
  unfold prepare at h
  cases hA : x.a.mapM fun w => (P.a.read w).toFinite <;> rw [hA] at h <;> simp at h
  cases hB : x.b.mapM fun w => (P.b.read w).toFinite <;> rw [hB] at h <;> simp at h
  cases hC : (fp32.decode x.c).toFinite <;> rw [hC] at h <;> simp at h
  subst h
  intro p hp
  obtain ⟨a, ha, b, hb, rfl⟩ := mem_zipWith' hp
  obtain ⟨wa, _, hwa⟩ := mapM_mem_option hA a ha
  obtain ⟨wb, _, hwb⟩ := mapM_mem_option hB b hb
  obtain ⟨a1, a2⟩ := read_exp hwa
  obtain ⟨b1, b2⟩ := read_exp hwb
  have a3 := read_bounded hwa
  have b3 := read_bounded hwb
  simp only [Unpacked.mul]
  refine ⟨by omega, by omega, ?_⟩
  calc a.m * b.m < 2 ^ (a.t + 1) * 2 ^ (b.t + 1) := Nat.mul_lt_mul'' a3 b3
    _ = 2 ^ (a.t + b.t + 2) := by rw [← Nat.pow_add]; congr 1; omega


end MatrixCore
