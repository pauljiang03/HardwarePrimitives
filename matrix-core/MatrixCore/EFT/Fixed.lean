import MatrixCore.EFT.Register
import MatrixCore.EFT.Inputs

/-! # MC-EFT in a 576-bit register

The whole correction on 576-bit two's-complement registers in units of `2^-298`: the split at the
cut-off by masks, the sums, the guard by a trailing-zero count and comparisons, the fast path by
FP32 roundings of register sums, and the exact fallback. Exponents and shift counts are small
naturals. On every model that fits, it returns the same result as MC-EFT. -/

namespace MatrixCore

set_option exponentiation.threshold 1024

/-! ## Register arithmetic -/

namespace Reg

/-- The value `x.toInt · 2^-298` of a register. -/
def val (x : Reg) : ℚ := (x.toInt : ℚ) * pow2 (-298)

/-- The magnitude of a register. -/
def abs (x : Reg) : Reg := if x.msb then -x else x

/-- The low `s` bits of a register. -/
def lowBits (x : Reg) (s : ℕ) : Reg := x &&& (((1 : Reg) <<< s) - 1)

theorem toInt_add {a b : Reg} (ha : a.toInt.natAbs < 2 ^ 574) (hb : b.toInt.natAbs < 2 ^ 574) :
    (a + b).toInt = a.toInt + b.toInt := by
  rw [BitVec.toInt_add, bmod576] <;> omega

theorem toInt_sub {a b : Reg} (ha : a.toInt.natAbs < 2 ^ 574) (hb : b.toInt.natAbs < 2 ^ 574) :
    (a - b).toInt = a.toInt - b.toInt := by
  rw [BitVec.toInt_sub, bmod576] <;> omega

theorem toInt_neg {a : Reg} (ha : a.toInt.natAbs < 2 ^ 575) : (-a).toInt = -a.toInt := by
  rw [BitVec.toInt_neg, bmod576] <;> omega

theorem msb_iff {x : Reg} : x.msb = true ↔ x.toInt < 0 := by
  have hlt := x.isLt
  rw [BitVec.toInt_eq_msb_cond]
  cases x.msb <;> simp <;> omega

theorem abs_toNat {x : Reg} (hx : x.toInt.natAbs < 2 ^ 575) : x.abs.toNat = x.toInt.natAbs := by
  have hlt := x.isLt
  have hc := BitVec.toInt_eq_msb_cond x
  unfold abs
  cases hm : x.msb
  · simp only [hm, Bool.false_eq_true, ↓reduceIte] at hc ⊢; omega
  · simp only [hm, ↓reduceIte] at hc ⊢
    rw [BitVec.toNat_neg, Nat.mod_eq_of_lt (by omega)]; omega

theorem val_eq_zero_iff {x : Reg} : x.val = 0 ↔ x = 0 := by
  unfold val
  constructor
  · intro h
    have : (x.toInt : ℚ) = 0 := by
      rcases Rat.mul_eq_zero.mp h with h | h
      · exact h
      · exact absurd h (pow2_ne_zero _)
    apply BitVec.eq_of_toInt_eq
    have h0 : (0 : Reg).toInt = 0 := by decide
    rw [h0]; exact_mod_cast this
  · rintro rfl; simp

theorem val_inj {x y : Reg} : x.val = y.val ↔ x = y := by
  constructor
  · intro h
    unfold val at h
    have : (x.toInt : ℚ) = y.toInt := by
      have := congrArg (· * pow2 298) h
      simp only [Rat.mul_assoc, ← pow2_add] at this
      simpa [pow2_zero] using this
    exact BitVec.eq_of_toInt_eq (by exact_mod_cast this)
  · rintro rfl; rfl

theorem val_add {a b : Reg} (ha : a.toInt.natAbs < 2 ^ 574) (hb : b.toInt.natAbs < 2 ^ 574) :
    (a + b).val = a.val + b.val := by
  unfold val; rw [toInt_add ha hb, Rat.intCast_add, Rat.add_mul]

theorem val_sub {a b : Reg} (ha : a.toInt.natAbs < 2 ^ 574) (hb : b.toInt.natAbs < 2 ^ 574) :
    (a - b).val = a.val - b.val := by
  unfold val; rw [toInt_sub ha hb, Rat.intCast_sub]; grind

theorem val_neg {a : Reg} (ha : a.toInt.natAbs < 2 ^ 575) : (-a).val = -a.val := by
  unfold val; rw [toInt_neg ha, Rat.intCast_neg, Rat.neg_mul]

theorem absQ_val (x : Reg) : absQ x.val = (x.toInt.natAbs : ℚ) * pow2 (-298) := by
  unfold val; rw [absQ_mul_pos _ _ (pow2_pos _), absQ_intCast]

/-- The low bits are the Euclidean remainder of the signed value. -/
theorem lowBits_toInt (x : Reg) {s : ℕ} (hs : s ≤ 575) :
    ((x.lowBits s).toNat : ℤ) = x.toInt % (2 ^ s : ℕ) := by
  have hmask : ((1 : Reg) <<< s - 1).toNat = 2 ^ s - 1 := by
    have h1 : ((1 : Reg) <<< s).toNat = 2 ^ s := by
      rw [BitVec.toNat_shiftLeft, Reg.toNat_one, Nat.shiftLeft_eq, Nat.one_mul]
      exact Nat.mod_eq_of_lt (Nat.pow_lt_pow_right (by decide) (by omega))
    rw [BitVec.toNat_sub_of_le (by rw [BitVec.le_def, h1, Reg.toNat_one]; exact Nat.two_pow_pos s),
      h1, Reg.toNat_one]
  unfold lowBits
  rw [BitVec.toNat_and, hmask, Nat.and_two_pow_sub_one_eq_mod, BitVec.toInt_eq_msb_cond]
  have hdvd : ((2 ^ s : ℕ) : ℤ) ∣ ((2 ^ 576 : ℕ) : ℤ) := by
    have : 2 ^ 576 = 2 ^ s * 2 ^ (576 - s) := by rw [← Nat.pow_add]; congr 1; omega
    rw [this]; push_cast; exact Int.dvd_mul_right _ _
  split
  · rw [Int.sub_emod]
    have : ((2 ^ 576 : ℕ) : ℤ) % ((2 ^ s : ℕ) : ℤ) = 0 := Int.emod_eq_zero_of_dvd hdvd
    rw [this, Int.sub_zero, Int.emod_emod_of_dvd _ (Int.dvd_refl _)]
    exact Int.natCast_emod _ _
  · exact Int.natCast_emod _ _

end Reg

/-! ## The split by masks -/

/-- The high part at shift `s` (the cut-off `2^(s − 298)`): RD clears the low bits; truncation
clears them on the magnitude. -/
def splitHighReg : SplitRule → Reg → ℕ → Reg
  | .rd, x, s => x - x.lowBits s
  | .trunc, x, s => if x.msb then -((-x) - (-x).lowBits s) else x - x.lowBits s

theorem Reg.rd_toInt' (x : Reg) {s : ℕ} (hs : s ≤ 574) (hx : x.toInt.natAbs < 2 ^ 574) :
    (x - x.lowBits s).toInt = x.toInt - x.toInt % (2 ^ s : ℕ) := by
  have hl := Reg.lowBits_toInt x (s := s) (by omega)
  have hP : 2 ^ s ≤ 2 ^ 574 := Nat.pow_le_pow_right (by decide) hs
  have hlt : (x.lowBits s).toNat < 2 ^ s := by
    have := Int.emod_lt_of_pos x.toInt
      (show (0 : ℤ) < ((2 ^ s : ℕ) : ℤ) by exact_mod_cast Nat.two_pow_pos s)
    omega
  have hlb : (x.lowBits s).toInt = ((x.lowBits s).toNat : ℤ) := Reg.toInt_of_lt (by omega)
  rw [Reg.toInt_sub hx (by rw [hlb]; omega), hlb, hl]

theorem Reg.rd_toInt (x : Reg) {s : ℕ} (hs : s ≤ 574) (hx : x.toInt.natAbs < 2 ^ 574) :
    (x - x.lowBits s).toInt = (2 ^ s : ℕ) * (x.toInt / (2 ^ s : ℕ)) := by
  rw [Reg.rd_toInt' x hs hx, Int.emod_def, Int.sub_sub_self]

theorem Reg.rd_natAbs (x : Reg) {s : ℕ} (hs : s ≤ 574) (hx : x.toInt.natAbs < 2 ^ 574) :
    (x - x.lowBits s).toInt.natAbs < 2 ^ 575 := by
  have hP : 2 ^ s ≤ 2 ^ 574 := Nat.pow_le_pow_right (by decide) hs
  have hpos : (0 : ℤ) < ((2 ^ s : ℕ) : ℤ) := by exact_mod_cast Nat.two_pow_pos s
  have h0 := Int.emod_nonneg x.toInt (Int.ne_of_gt hpos)
  have h1 := Int.emod_lt_of_pos x.toInt hpos
  rw [Reg.rd_toInt' x hs hx]
  omega

theorem rdGrid_val (x : Reg) {s : ℕ} (hs : s ≤ 574) (hx : x.toInt.natAbs < 2 ^ 574) :
    rdGrid x.val ((s : ℤ) - 298) = (x - x.lowBits s).val := by
  have hdiv : x.val / pow2 ((s : ℤ) - 298) = (x.toInt : ℚ) / ((2 ^ s : ℕ) : ℚ) := by
    unfold Reg.val
    rw [Rat.div_def, Rat.mul_assoc, ← Rat.div_def, ← pow2_sub,
      show (-298 : ℤ) - ((s : ℤ) - 298) = -(s : ℤ) by omega, Rat.div_def, ← pow2_natCast]
    unfold pow2; rw [Rat.zpow_neg]
  unfold rdGrid
  rw [hdiv, floor_intCast_div _ _ (Nat.two_pow_pos s), Reg.val, Reg.rd_toInt x hs hx,
    Rat.intCast_mul, Rat.intCast_natCast, ← pow2_natCast,
    show pow2 ((s : ℤ) - 298) = pow2 (s : ℤ) * pow2 (-298) by rw [← pow2_add]; congr 1]
  grind

theorem truncGrid_val (x : Reg) {s : ℕ} (hs : s ≤ 574) (hx : x.toInt.natAbs < 2 ^ 574) :
    truncGrid x.val ((s : ℤ) - 298) = (splitHighReg .trunc x s).val := by
  have hneg : (-x).toInt.natAbs < 2 ^ 574 := by rw [Reg.toInt_neg (by omega)]; omega
  unfold truncGrid
  simp only [splitHighReg]
  by_cases hm : x.msb = true
  · have hv : x.val < 0 := by
      unfold Reg.val
      have := Reg.msb_iff.mp hm
      have hq : ((x.toInt : ℤ) : ℚ) < 0 := by exact_mod_cast this
      have := Rat.mul_lt_mul_of_pos_right hq (pow2_pos (-298))
      rwa [Rat.zero_mul] at this
    rw [if_pos hv, if_pos hm, Reg.val_neg (Reg.rd_natAbs (-x) hs hneg), ← rdGrid_val (-x) hs hneg,
      Reg.val_neg (by omega)]
    rfl
  · have hv : ¬ x.val < 0 := by
      unfold Reg.val
      have : ¬ x.toInt < 0 := fun h => hm (Reg.msb_iff.mpr h)
      have hq : (0 : ℚ) ≤ ((x.toInt : ℤ) : ℚ) := by exact_mod_cast (show 0 ≤ x.toInt by omega)
      exact Rat.not_lt.mpr (Rat.mul_nonneg hq (Rat.le_of_lt (pow2_pos _)))
    rw [if_neg hv, if_neg hm, ← rdGrid_val x hs hx]
    rfl

theorem splitHighReg_val (r : SplitRule) (x : Reg) {s : ℕ} (hs : s ≤ 574)
    (hx : x.toInt.natAbs < 2 ^ 574) :
    (splitHighReg r x s).val = r.high x.val ((s : ℤ) - 298) := by
  cases r
  · exact (truncGrid_val x hs hx).symm
  · exact (rdGrid_val x hs hx).symm

/-! ## The lowest bit by trailing zeros -/

/-- Trailing zeros of a register, by tests of the lowest bit and shifts by one. -/
def ctzReg : ℕ → Reg → ℕ
  | 0, _ => 0
  | fuel + 1, x => if x ≠ 0 ∧ x.getLsbD 0 = false then ctzReg fuel (x >>> 1) + 1 else 0

theorem ctzReg_eq : ∀ (fuel : ℕ) (x : Reg), ctzReg fuel x = trailingZerosAux fuel x.toNat
  | 0, _ => rfl
  | fuel + 1, x => by
    have h1 : x ≠ 0 ↔ x.toNat ≠ 0 := ⟨Reg.toNat_ne_zero, fun h hx => h (by rw [hx]; rfl)⟩
    have h2 : x.getLsbD 0 = false ↔ x.toNat % 2 = 0 := by
      rw [BitVec.getLsbD, Nat.testBit_zero]; simp
    have h3 : (x >>> 1).toNat = x.toNat / 2 := by
      rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, Nat.pow_one]
    unfold ctzReg trailingZerosAux
    by_cases hc : x.toNat ≠ 0 ∧ x.toNat % 2 = 0
    · rw [if_pos (⟨h1.mpr hc.1, h2.mpr hc.2⟩), if_pos hc, ctzReg_eq fuel, h3]
    · rw [if_neg (fun h => hc ⟨h1.mp h.1, h2.mp h.2⟩), if_neg hc]

/-- The lowest bit of a nonzero register value is its trailing-zero count, less `298`. -/
theorem lowestBitExp_val {x : Reg} (hx0 : x ≠ 0) (hx : x.toInt.natAbs < 2 ^ 575) :
    lowestBitExp x.val = (ctzReg 576 x.abs : ℤ) - 298 := by
  have hn := Reg.abs_toNat hx
  have hne : x.toInt.natAbs ≠ 0 := by
    intro h; apply hx0; apply BitVec.eq_of_toInt_eq
    have h0 : (0 : Reg).toInt = 0 := by decide
    rw [h0]; omega
  obtain ⟨v, o, ho, he⟩ := exists_two_pow_mul_odd x.toInt.natAbs (by omega)
  have hv : v < 576 := by
    have : 2 ^ v ≤ x.toInt.natAbs := by rw [he]; exact Nat.le_mul_of_pos_right _ (by omega)
    have := Nat.lt_of_le_of_lt this (show x.toInt.natAbs < 2 ^ 576 by omega)
    exact (Nat.pow_lt_pow_iff_right (by decide)).mp this
  rw [ctzReg_eq, hn, he, trailingZerosAux_pow_mul ho v 576 (by omega)]
  obtain ⟨k, hk, hko⟩ : ∃ k : ℤ, x.toInt = k * 2 ^ v ∧ k.natAbs = o := by
    rcases Int.natAbs_eq x.toInt with h | h
    · exact ⟨o, by rw [h, he] <;> (try push_cast) <;> (try grind), rfl⟩
    · exact ⟨-o, by rw [h, he] <;> (try push_cast) <;> (try grind), by simp⟩
  have hval : x.val = (k : ℚ) * pow2 ((v : ℤ) - 298) := by
    unfold Reg.val
    rw [hk, Rat.intCast_mul, show ((2 ^ v : ℤ) : ℚ) = pow2 (v : ℤ) by rw [pow2_natCast]; push_cast; rfl,
      Rat.mul_assoc, ← pow2_add]
    congr 2
  rw [hval, lowestBitExp_odd (by omega)]

/-! ## FP32 words and roundings in the register -/

/-- The register of a finite FP32 word. -/
def reg32 (w : F32) : Option Reg := (fp32.decode w).toFinite.map Unpacked.toReg

/-- FP32 rounding of a register value. -/
def roundSigned (x : Reg) : Option F32 := roundReg x.msb x.abs

/-- An FP32 operation: the rounded value, back in the register. -/
def roundBack (x : Reg) : Option Reg := (roundSigned x).bind reg32

/-- `x` is an FP32 value: rounding it gives it back. -/
def representableReg (x : Reg) : Bool := roundBack x == some x

theorem roundSigned_eq {x : Reg} (hx : x.toInt.natAbs < 2 ^ 575) : roundSigned x = rne32 x.val := by
  unfold roundSigned
  rw [roundReg_eq, Reg.abs_toNat hx, round298_eq]
  congr 2
  cases hm : x.msb
  · have : 0 ≤ x.toInt := by
      have := Reg.msb_iff (x := x); rw [hm] at this; simp at this; omega
    simp only [Bool.false_eq_true, ↓reduceIte]
    congr 1
    rw [show ((x.toInt.natAbs : ℕ) : ℚ) = ((x.toInt : ℤ) : ℚ) by
      rw [← Rat.intCast_natCast]; congr 1; omega]
  · have : x.toInt < 0 := Reg.msb_iff.mp hm
    simp only [↓reduceIte]
    congr 1
    rw [show -((x.toInt.natAbs : ℕ) : ℚ) = ((x.toInt : ℤ) : ℚ) by
      rw [← Rat.intCast_natCast, ← Rat.intCast_neg]; congr 1; omega]

theorem Unpacked.toReg_val {u : Unpacked} (hg : -298 ≤ u.e - u.t)
    (hb : u.m * 2 ^ (u.e - u.t + 298).toNat < 2 ^ 575) : u.toReg.val = u.value := by
  unfold Reg.val; rw [Unpacked.toReg_toInt hb]; exact Unpacked.coeff298_value hg

theorem decode32_reg {w : F32} {u : Unpacked} (h : fp32.decode w = .finite u) :
    u.toReg.val = u.value ∧ u.toReg.toInt.natAbs < 2 ^ 427 := by
  obtain ⟨ht, hm, he1, he2, _⟩ := decode32_finite_fields h
  have hg : -298 ≤ u.e - u.t := by omega
  have hc : u.m * 2 ^ (u.e - u.t + 298).toNat < 2 ^ 427 := by
    have := coeff298_lt (j := 1) hg (by rw [ht]; exact hm)
    rw [coeff298_natAbs] at this
    exact Nat.lt_of_lt_of_le this (Nat.pow_le_pow_right (by decide) (by omega))
  have h427 : (2 : ℕ) ^ 427 < 2 ^ 575 := Nat.pow_lt_pow_right (by decide) (by decide)
  refine ⟨Unpacked.toReg_val hg (by omega), ?_⟩
  rw [Unpacked.toReg_toInt (by omega), coeff298_natAbs]; exact hc

theorem reg32_spec {w : F32} : (∃ y, reg32 w = some y) ↔ ∃ d, value32 w = some d := by
  unfold reg32 value32
  cases (fp32.decode w).toFinite <;> simp

theorem reg32_val {w : F32} {y : Reg} (h : reg32 w = some y) :
    value32 w = some y.val ∧ y.toInt.natAbs < 2 ^ 427 := by
  unfold reg32 at h
  cases hd : fp32.decode w with
  | finite u =>
    rw [hd] at h
    simp only [Datum.toFinite, Option.map_some, Option.some.injEq] at h
    subst h
    obtain ⟨h1, h2⟩ := decode32_reg hd
    exact ⟨by rw [h1]; simp [value32, hd, Datum.toFinite], h2⟩
  | infinity _ => rw [hd] at h; simp [Datum.toFinite] at h
  | nan => rw [hd] at h; simp [Datum.toFinite] at h

/-- An FP32 operation on registers is FP32 addition on values. -/
theorem roundBack_val {x : Reg} (hx : x.toInt.natAbs < 2 ^ 575) :
    (roundBack x).map Reg.val = (rne32 x.val).bind value32 ∧
      ∀ y, roundBack x = some y → y.toInt.natAbs < 2 ^ 427 := by
  unfold roundBack
  rw [roundSigned_eq hx]
  constructor
  · cases hr : rne32 x.val with
    | none => rfl
    | some w =>
      simp only [Option.bind_some]
      cases hy : reg32 w with
      | none =>
        have : value32 w = none := by
          cases hv : value32 w with
          | none => rfl
          | some d => obtain ⟨y, hy'⟩ := reg32_spec.mpr ⟨d, hv⟩; rw [hy] at hy'; cases hy'
        rw [this]; rfl
      | some y => rw [(reg32_val hy).1]; rfl
  · intro y hy
    cases hr : rne32 x.val with
    | none => rw [hr] at hy; cases hy
    | some w => rw [hr] at hy; exact (reg32_val hy).2

theorem representableReg_iff {x : Reg} (hx : x.toInt.natAbs < 2 ^ 575) :
    representableReg x = representable32 x.val := by
  have hb := (roundBack_val hx).1
  unfold representableReg representable32
  cases hr : roundBack x with
  | none =>
    rw [hr] at hb
    simp only [Option.map_none] at hb
    rw [← hb]; rfl
  | some y =>
    rw [hr] at hb
    simp only [Option.map_some] at hb
    rw [← hb]
    by_cases hyx : y = x
    · subst hyx; simp
    · have : y.val ≠ x.val := fun h => hyx (Reg.val_inj.mp h)
      have h1 : (some y == some x) = false := beq_eq_false_iff_ne.mpr (fun h => hyx (Option.some.inj h))
      have h2 : (some y.val == some x.val) = false :=
        beq_eq_false_iff_ne.mpr (fun h => this (Option.some.inj h))
      rw [h1, h2]

/-! ## Sums and the parts of a term -/

/-- Modular additions of registers, from zero. -/
def sumRegs (xs : List Reg) : Reg := xs.foldl (· + ·) 0

theorem sumRegs_foldl (xs : List Reg) (acc : Reg)
    (h : acc.toInt.natAbs + magnitudeSum (xs.map BitVec.toInt) < 2 ^ 574) :
    (xs.foldl (· + ·) acc).toInt = acc.toInt + sumZ (xs.map BitVec.toInt) := by
  induction xs generalizing acc with
  | nil => simp [sumZ]
  | cons x xs ih =>
    simp only [List.foldl_cons, List.map_cons, sumZ]
    simp only [List.map_cons, magnitudeSum] at h
    have hstep := Reg.toInt_add (a := acc) (b := x) (by omega) (by omega)
    rw [ih _ (by rw [hstep]; omega), hstep]; omega

theorem sumRegs_toInt {xs : List Reg} (h : magnitudeSum (xs.map BitVec.toInt) < 2 ^ 574) :
    (sumRegs xs).toInt = sumZ (xs.map BitVec.toInt) := by
  have := sumRegs_foldl xs 0 (by simpa using h)
  simpa [sumRegs] using this

theorem sumRegs_val {xs : List Reg} (h : magnitudeSum (xs.map BitVec.toInt) < 2 ^ 574) :
    (sumRegs xs).val = sumQ (xs.map Reg.val) := by
  unfold Reg.val
  rw [sumRegs_toInt h]
  induction xs with
  | nil => simp [sumZ, sumQ]
  | cons x xs ih =>
    simp only [List.map_cons, sumZ, sumQ, Rat.intCast_add, Rat.add_mul]
    simp only [List.map_cons, magnitudeSum] at h
    rw [ih (by omega)]

theorem magnitudeSum_le_of {xs : List Reg} {B : ℕ} (h : ∀ x ∈ xs, x.toInt.natAbs ≤ B) :
    magnitudeSum (xs.map BitVec.toInt) ≤ xs.length * B := by
  have := magnitudeSum_le_length_mul (xs.map BitVec.toInt) B (by
    intro z hz; obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hz; exact h x hx)
  simpa using this

theorem splitHighReg_parts (r : SplitRule) (x : Reg) {s : ℕ} (hs : s ≤ 559)
    (hx : x.toInt.natAbs < 2 ^ 559) :
    (splitHighReg r x s).toInt.natAbs < 2 ^ 560 ∧
      (x - splitHighReg r x s).toInt.natAbs < 2 ^ s ∧
      (x - splitHighReg r x s).toInt = x.toInt - (splitHighReg r x s).toInt := by
  have hP : 2 ^ s ≤ 2 ^ 559 := Nat.pow_le_pow_right (by decide) hs
  have h574 : x.toInt.natAbs < 2 ^ 574 := Nat.lt_of_lt_of_le hx (Nat.pow_le_pow_right (by decide) (by decide))
  have hpos : (0 : ℤ) < ((2 ^ s : ℕ) : ℤ) := by exact_mod_cast Nat.two_pow_pos s
  have hneg : (-x).toInt = -x.toInt := Reg.toInt_neg (by omega)
  have hhi : (splitHighReg r x s).toInt = x.toInt - x.toInt % ((2 ^ s : ℕ) : ℤ) ∨
      (x.toInt < 0 ∧ (splitHighReg r x s).toInt = -((-x.toInt) - (-x.toInt) % ((2 ^ s : ℕ) : ℤ))) := by
    cases r
    · simp only [splitHighReg]
      by_cases hm : x.msb = true
      · right
        refine ⟨Reg.msb_iff.mp hm, ?_⟩
        rw [if_pos hm, Reg.toInt_neg (Reg.rd_natAbs (-x) (by omega) (by omega)),
          Reg.rd_toInt' (-x) (by omega) (by omega), hneg]
      · left; rw [if_neg hm, Reg.rd_toInt' x (by omega) h574]
    · left; exact Reg.rd_toInt' x (by omega) h574
  have h0 := Int.emod_nonneg x.toInt (Int.ne_of_gt hpos)
  have h1 := Int.emod_lt_of_pos x.toInt hpos
  have h2 := Int.emod_nonneg (-x.toInt) (Int.ne_of_gt hpos)
  have h3 := Int.emod_lt_of_pos (-x.toInt) hpos
  have hhb : (splitHighReg r x s).toInt.natAbs < 2 ^ 560 := by
    have : (2 : ℕ) ^ 560 = 2 ^ 559 + 2 ^ 559 := by rw [Nat.pow_succ]
    rcases hhi with h | ⟨_, h⟩ <;> rw [h] <;> omega
  have hsub := Reg.toInt_sub (a := x) (b := splitHighReg r x s) h574
    (Nat.lt_of_lt_of_le hhb (Nat.pow_le_pow_right (by decide) (by decide)))
  refine ⟨hhb, ?_, hsub⟩
  rw [hsub]
  rcases hhi with h | ⟨_, h⟩ <;> rw [h] <;> omega

/-! ## The correction on registers -/

/-- A split on registers: the cut-off `2^(s − 298)` and the terms with their rules. -/
structure RegSplit where
  s : ℕ
  terms : List (SplitRule × Reg)

namespace RegSplit

def highs (r : RegSplit) : List Reg := r.terms.map fun t => splitHighReg t.1 t.2 r.s

def lows (r : RegSplit) : List Reg := r.terms.map fun t => t.2 - splitHighReg t.1 t.2 r.s

def H (r : RegSplit) : Reg := sumRegs r.highs

/-- The shift of the lowest bit of the nonzero low parts, from the cut-off. -/
def lowShift (r : RegSplit) : ℕ :=
  r.lows.foldl (fun e x => if x = 0 then e else min e (ctzReg 576 x.abs)) r.s

def sumAbs (r : RegSplit) : Reg := sumRegs (r.lows.map Reg.abs)

/-- The guard on registers: the low parts' bits within 24 above a lowest bit at or above
`2^-149`, in range, and the overlap and `H` FP32 values. -/
def guard (r : RegSplit) (D : Reg) : Bool :=
  decide (149 ≤ r.lowShift) &&
  r.lows.all (fun x => x.abs.lowBits r.lowShift == 0) &&
  decide (r.sumAbs >>> r.lowShift < 16777216) &&
  decide (r.sumAbs < (1 : Reg) <<< 426) &&
  representableReg (D - r.H) && representableReg r.H

/-- FP32 summation of registers, left to right. -/
def naiveSumFrom : Reg → List Reg → Option Reg
  | acc, [] => some acc
  | acc, x :: xs => (roundBack (acc + x)).bind fun s => naiveSumFrom s xs

def fastPath (r : RegSplit) (D : Reg) : Option F32 :=
  (naiveSumFrom 0 r.lows).bind fun e =>
    (roundBack (D + -(D - r.H))).bind fun h => roundSigned (h + e)

def exactPath (r : RegSplit) : Option F32 := roundSigned (sumRegs (r.terms.map Prod.snd))

def run (r : RegSplit) (D : Reg) : EftResult :=
  if r.guard D then
    match r.fastPath D with
    | some b => .fast b
    | none => .outOfRange
  else
    match r.exactPath with
    | some b => .exact b
    | none => .outOfRange

/-- `r` holds the split `s`, with room for every sum. -/
structure Holds (r : RegSplit) (s : EftSplit) : Prop where
  shift : (r.s : ℤ) = s.q + 298
  terms : r.terms.map (fun t => (t.1, t.2.val)) = s.terms
  small : ∀ t ∈ r.terms, t.2.toInt.natAbs < 2 ^ 559
  count : r.terms.length ≤ 2 ^ 12
  le : r.s ≤ 559

variable {r : RegSplit} {s : EftSplit}

theorem Holds.highs_val (h : r.Holds s) : r.highs.map Reg.val = s.highs := by
  unfold highs EftSplit.highs
  rw [← h.terms, List.map_map, List.map_map]
  apply List.map_congr_left
  intro t ht
  simp only [Function.comp_apply]
  rw [splitHighReg_val t.1 t.2 (by have := h.le; omega)
    (Nat.lt_of_lt_of_le (h.small t ht) (Nat.pow_le_pow_right (by decide) (by decide)))]
  congr 1; have := h.shift; omega

theorem Holds.lows_val (h : r.Holds s) : r.lows.map Reg.val = s.lows := by
  unfold lows EftSplit.lows
  rw [← h.terms, List.map_map, List.map_map]
  apply List.map_congr_left
  intro t ht
  simp only [Function.comp_apply]
  have hp := splitHighReg_parts t.1 t.2 h.le (h.small t ht)
  have hv := splitHighReg_val t.1 t.2 (s := r.s) (by have := h.le; omega)
    (Nat.lt_of_lt_of_le (h.small t ht) (Nat.pow_le_pow_right (by decide) (by decide)))
  rw [show ((r.s : ℤ) - 298) = s.q by have := h.shift; omega] at hv
  unfold Reg.val at hv ⊢
  rw [hp.2.2, Rat.intCast_sub, ← hv]
  grind

theorem Holds.highs_small (h : r.Holds s) : ∀ x ∈ r.highs, x.toInt.natAbs < 2 ^ 560 := by
  intro x hx
  simp only [highs, List.mem_map] at hx
  obtain ⟨t, ht, rfl⟩ := hx
  exact (splitHighReg_parts t.1 t.2 h.le (h.small t ht)).1

theorem Holds.lows_small (h : r.Holds s) : ∀ x ∈ r.lows, x.toInt.natAbs < 2 ^ 559 := by
  intro x hx
  simp only [lows, List.mem_map] at hx
  obtain ⟨t, ht, rfl⟩ := hx
  exact Nat.lt_of_lt_of_le (splitHighReg_parts t.1 t.2 h.le (h.small t ht)).2.1
    (Nat.pow_le_pow_right (by decide) h.le)

theorem Holds.H_val (h : r.Holds s) : r.H.val = s.H ∧ r.H.toInt.natAbs < 2 ^ 573 := by
  have hm := magnitudeSum_le_of (fun x hx => Nat.le_of_lt (h.highs_small x hx))
  have hlen : r.highs.length ≤ 2 ^ 12 := by simpa [highs] using h.count
  have hb : r.highs.length * 2 ^ 560 ≤ 2 ^ 572 := by
    calc r.highs.length * 2 ^ 560 ≤ 2 ^ 12 * 2 ^ 560 := Nat.mul_le_mul_right _ hlen
      _ = 2 ^ 572 := by rw [← Nat.pow_add]
  have h572 : (2 : ℕ) ^ 572 < 2 ^ 574 := Nat.pow_lt_pow_right (by decide) (by decide)
  have h573 : (2 : ℕ) ^ 572 < 2 ^ 573 := Nat.pow_lt_pow_right (by decide) (by decide)
  refine ⟨?_, ?_⟩
  · unfold H EftSplit.H; rw [sumRegs_val (by omega), h.highs_val]
  · unfold H; rw [sumRegs_toInt (by omega)]
    have := sumZ_natAbs_le (r.highs.map BitVec.toInt); omega

theorem Holds.exact_val (h : r.Holds s) :
    (sumRegs (r.terms.map Prod.snd)).val = s.exact ∧
      (sumRegs (r.terms.map Prod.snd)).toInt.natAbs < 2 ^ 575 := by
  have hs : ∀ x ∈ r.terms.map Prod.snd, x.toInt.natAbs ≤ 2 ^ 559 := by
    intro x hx; obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hx; exact Nat.le_of_lt (h.small t ht)
  have hm := magnitudeSum_le_of hs
  have hlen : (r.terms.map Prod.snd).length ≤ 2 ^ 12 := by simpa using h.count
  have hb : (r.terms.map Prod.snd).length * 2 ^ 559 ≤ 2 ^ 571 := by
    calc (r.terms.map Prod.snd).length * 2 ^ 559 ≤ 2 ^ 12 * 2 ^ 559 := Nat.mul_le_mul_right _ hlen
      _ = 2 ^ 571 := by rw [← Nat.pow_add]
  have h571 : (2 : ℕ) ^ 571 < 2 ^ 574 := Nat.pow_lt_pow_right (by decide) (by decide)
  have h575 : (2 : ℕ) ^ 574 < 2 ^ 575 := Nat.pow_lt_pow_right (by decide) (by decide)
  refine ⟨?_, ?_⟩
  · rw [sumRegs_val (by omega), EftSplit.exact, ← h.terms, List.map_map, List.map_map]; rfl
  · rw [sumRegs_toInt (by omega)]
    have := sumZ_natAbs_le ((r.terms.map Prod.snd).map BitVec.toInt); omega

end RegSplit

/-! ## The guard on registers is the guard -/

theorem foldl_lowShift (xs : List Reg) (hx : ∀ x ∈ xs, x.toInt.natAbs < 2 ^ 575) :
    ∀ (e : ℕ) (e' : ℤ), (e : ℤ) = e' + 298 →
      ((xs.foldl (fun e x => if x = 0 then e else min e (ctzReg 576 x.abs)) e : ℕ) : ℤ) =
        (xs.map Reg.val).foldl lowBitStep e' + 298 := by
  induction xs with
  | nil => intro e e' he; simpa using he
  | cons x xs ih =>
    intro e e' he
    simp only [List.foldl_cons, List.map_cons]
    apply ih (fun y hy => hx y (List.mem_cons_of_mem _ hy))
    unfold lowBitStep
    by_cases h0 : x = 0
    · rw [if_pos h0, if_pos (Reg.val_eq_zero_iff.mpr h0)]; exact he
    · rw [if_neg h0, if_neg (fun h => h0 (Reg.val_eq_zero_iff.mp h)),
        lowestBitExp_val h0 (hx x (List.mem_cons_self ..))]
      omega

theorem onGrid_iff_dvd (X : ℤ) (g : ℤ) (k : ℕ) :
    OnGrid ((X : ℚ) * pow2 g) (g + k) ↔ ((2 ^ k : ℕ) : ℤ) ∣ X := by
  constructor
  · rintro ⟨j, hj⟩
    refine ⟨j, ?_⟩
    rw [pow2_add, pow2_natCast, show ((j : ℤ) : ℚ) * (pow2 g * ((2 ^ k : ℕ) : ℚ)) =
      (((2 ^ k : ℕ) * j : ℤ) : ℚ) * pow2 g by push_cast; grind] at hj
    have h2 := congrArg (· * pow2 (-g)) hj
    simp only [Rat.mul_assoc, ← pow2_add, show g + -g = 0 by omega, pow2_zero, Rat.mul_one] at h2
    exact_mod_cast h2
  · rintro ⟨j, rfl⟩
    refine ⟨j, ?_⟩
    rw [pow2_add, pow2_natCast]; push_cast; grind

theorem onGrid_iff_floor {x : ℚ} {g : ℤ} : OnGrid x g ↔ (((x / pow2 g).floor : ℤ) : ℚ) * pow2 g = x :=
  ⟨floor_div_mul_of_onGrid, fun h => ⟨_, h.symm⟩⟩

theorem eq_map_self_iff {l : List α} {f : α → α} : l = l.map f ↔ ∀ x ∈ l, f x = x := by
  induction l with
  | nil => simp
  | cons x xs ih =>
    simp only [List.map_cons, List.cons.injEq, List.mem_cons, forall_eq_or_imp]
    rw [← ih]; constructor <;> rintro ⟨h1, h2⟩ <;> exact ⟨h1.symm, h2⟩

theorem EftSplit.grid_check (s : EftSplit) :
    (s.lows == s.lowCoeffs.map fun (z : ℤ) => (z : ℚ) * pow2 s.lowBit) = true ↔
      ∀ x ∈ s.lows, OnGrid x s.lowBit := by
  have : s.lowCoeffs.map (fun (z : ℤ) => (z : ℚ) * pow2 s.lowBit) =
      s.lows.map fun x => (((x / pow2 s.lowBit).floor : ℤ) : ℚ) * pow2 s.lowBit := by
    simp [EftSplit.lowCoeffs, List.map_map, Function.comp_def]
  rw [this, beq_iff_eq, eq_map_self_iff]
  constructor
  · intro h x hx; exact onGrid_iff_floor.mpr (h x hx)
  · intro h x hx; exact onGrid_iff_floor.mp (h x hx)

theorem lowBits_abs_eq_zero {x : Reg} {k : ℕ} (hk : k ≤ 575) (hx : x.toInt.natAbs < 2 ^ 575) :
    (x.abs.lowBits k == 0) = true ↔ OnGrid x.val ((k : ℤ) - 298) := by
  have habs : x.abs.toInt = (x.toInt.natAbs : ℤ) := by
    rw [Reg.toInt_of_lt (by rw [Reg.abs_toNat hx]; omega), Reg.abs_toNat hx]
  have hl := Reg.lowBits_toInt x.abs hk
  rw [habs] at hl
  have hgrid : OnGrid x.val ((k : ℤ) - 298) ↔ ((2 ^ k : ℕ) : ℤ) ∣ x.toInt := by
    rw [show ((k : ℤ) - 298) = -298 + k by omega]; exact onGrid_iff_dvd _ _ _
  rw [beq_iff_eq, hgrid, BitVec.toNat_eq,
    show (0 : Reg).toNat = 0 from rfl]
  constructor
  · intro h0
    rw [h0] at hl
    exact Int.dvd_natAbs.mp (Int.dvd_of_emod_eq_zero hl.symm)
  · intro hd
    have := Int.emod_eq_zero_of_dvd (Int.dvd_natAbs.mpr hd)
    omega

theorem EftSplit.magnitudeSum_lowCoeffs (s : EftSplit) (hc : ∀ x ∈ s.lows, OnGrid x s.lowBit) :
    (magnitudeSum s.lowCoeffs : ℚ) * pow2 s.lowBit = sumQ (s.lows.map absQ) := by
  have hcoeffs : s.lowCoeffs.map (fun (z : ℤ) => (z : ℚ) * pow2 s.lowBit) = s.lows :=
    ((eq_map_self_iff.mpr fun x hx => onGrid_iff_floor.mp (hc x hx)).trans
      (by simp [EftSplit.lowCoeffs, List.map_map, Function.comp_def])).symm
  rw [← hcoeffs]
  clear hcoeffs hc
  generalize s.lowCoeffs = zs
  induction zs with
  | nil => simp [magnitudeSum, sumQ]
  | cons z zs ih =>
    simp only [magnitudeSum, List.map_cons, sumQ, Rat.natCast_add, Rat.add_mul, ih]
    rw [absQ_mul_pos _ _ (pow2_pos _), absQ_intCast]

namespace RegSplit

variable {r : RegSplit} {s : EftSplit}

theorem Holds.lows_small' (h : r.Holds s) : ∀ x ∈ r.lows, x.toInt.natAbs < 2 ^ 575 := fun x hx =>
  Nat.lt_of_lt_of_le (h.lows_small x hx) (Nat.pow_le_pow_right (by decide) (by decide))

theorem Holds.lowShift_eq (h : r.Holds s) : (r.lowShift : ℤ) = s.lowBit + 298 := by
  unfold lowShift
  rw [EftSplit.lowBit_eq, ← h.lows_val]
  exact foldl_lowShift r.lows h.lows_small' r.s s.q h.shift

theorem Holds.lowShift_le (h : r.Holds s) : r.lowShift ≤ 559 := by
  have h1 := h.lowShift_eq
  have h2 := (foldl_lowBitStep_le s.lows s.q).1
  rw [← EftSplit.lowBit_eq] at h2
  have := h.shift; have := h.le; omega

theorem Holds.check_eq (h : r.Holds s) :
    r.lows.all (fun x => x.abs.lowBits r.lowShift == 0) =
      (s.lows == s.lowCoeffs.map fun (z : ℤ) => (z : ℚ) * pow2 s.lowBit) := by
  have hls := h.lowShift_eq
  have hk : r.lowShift ≤ 575 := by have := h.lowShift_le; omega
  rw [Bool.eq_iff_iff, List.all_eq_true, EftSplit.grid_check, ← h.lows_val]
  constructor
  · intro hall y hy
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hy
    have := (lowBits_abs_eq_zero hk (h.lows_small' x hx)).mp (hall x hx)
    rwa [show ((r.lowShift : ℤ) - 298) = s.lowBit by omega] at this
  · intro hall x hx
    apply (lowBits_abs_eq_zero hk (h.lows_small' x hx)).mpr
    rw [show ((r.lowShift : ℤ) - 298) = s.lowBit by omega]
    exact hall _ (List.mem_map_of_mem hx)

theorem Holds.sumAbs_spec (h : r.Holds s) :
    (r.sumAbs.toNat : ℚ) * pow2 (-298) = sumQ (s.lows.map absQ) ∧ r.sumAbs.toNat < 2 ^ 572 := by
  have habs : ∀ x ∈ r.lows, x.abs.toInt = (x.toInt.natAbs : ℤ) := by
    intro x hx
    have hx' := h.lows_small' x hx
    rw [Reg.toInt_of_lt (by rw [Reg.abs_toNat hx']; omega), Reg.abs_toNat hx']
  have hmap : (r.lows.map Reg.abs).map BitVec.toInt = r.lows.map fun x => (x.toInt.natAbs : ℤ) := by
    rw [List.map_map]; exact List.map_congr_left fun x hx => habs x hx
  have hm : magnitudeSum ((r.lows.map Reg.abs).map BitVec.toInt) ≤ 2 ^ 571 := by
    have := magnitudeSum_le_of (xs := r.lows.map Reg.abs) (B := 2 ^ 559) (by
      intro y hy
      obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hy
      rw [habs x hx]; simpa using Nat.le_of_lt (h.lows_small x hx))
    have hlen : (r.lows.map Reg.abs).length ≤ 2 ^ 12 := by simpa [lows] using h.count
    calc _ ≤ (r.lows.map Reg.abs).length * 2 ^ 559 := this
      _ ≤ 2 ^ 12 * 2 ^ 559 := Nat.mul_le_mul_right _ hlen
      _ = 2 ^ 571 := by rw [← Nat.pow_add]
  have h571 : (2 : ℕ) ^ 571 < 2 ^ 574 := Nat.pow_lt_pow_right (by decide) (by decide)
  have hsum := sumRegs_toInt (xs := r.lows.map Reg.abs) (by omega)
  rw [hmap] at hsum
  have hnn : 0 ≤ sumZ (r.lows.map fun x => (x.toInt.natAbs : ℤ)) := by
    clear hsum hmap hm habs
    induction r.lows with
    | nil => simp [sumZ]
    | cons x xs ih => simp only [List.map_cons, sumZ]; omega
  have hz := sumZ_natAbs_le (r.lows.map fun x => (x.toInt.natAbs : ℤ))
  have hmag : magnitudeSum (r.lows.map fun x => (x.toInt.natAbs : ℤ)) ≤ 2 ^ 571 := by
    rw [← hmap]; exact hm
  have hnat : (r.sumAbs.toNat : ℤ) = sumZ (r.lows.map fun x => (x.toInt.natAbs : ℤ)) := by
    have hc := BitVec.toInt_eq_msb_cond r.sumAbs
    unfold sumAbs at hc ⊢
    rw [hsum] at hc
    have hlt := (sumRegs (r.lows.map Reg.abs)).isLt
    split at hc <;> omega
  refine ⟨?_, by omega⟩
  rw [← h.lows_val, List.map_map]
  have hq : ((r.sumAbs.toNat : ℕ) : ℚ) = ((sumZ (r.lows.map fun x => (x.toInt.natAbs : ℤ)) : ℤ) : ℚ) := by
    rw [← hnat]; rfl
  rw [hq]
  clear hq hnat hmag hz hnn hsum hm hmap habs
  induction r.lows with
  | nil => simp [sumZ, sumQ]
  | cons x xs ih =>
    simp only [List.map_cons, sumZ, sumQ, Rat.intCast_add, Rat.add_mul, ih, Function.comp_apply,
      Reg.absQ_val]
    rfl

theorem Holds.span_eq (h : r.Holds s) (hc : ∀ x ∈ s.lows, OnGrid x s.lowBit) :
    decide (r.sumAbs >>> r.lowShift < 16777216) = decide (magnitudeSum s.lowCoeffs < 2 ^ 24) ∧
      decide (r.sumAbs < (1 : Reg) <<< 426) =
        decide ((magnitudeSum s.lowCoeffs : ℚ) * pow2 s.lowBit < pow2 128) := by
  obtain ⟨hM, hMb⟩ := h.sumAbs_spec
  have hmag := EftSplit.magnitudeSum_lowCoeffs s hc
  rw [← hM] at hmag
  have hls := h.lowShift_eq
  have hkey : magnitudeSum s.lowCoeffs * 2 ^ r.lowShift = r.sumAbs.toNat := by
    have h2 := congrArg (· * pow2 298) hmag
    simp only [Rat.mul_assoc, ← pow2_add, show (-298 : ℤ) + 298 = 0 by omega, pow2_zero,
      Rat.mul_one] at h2
    rw [show s.lowBit + 298 = (r.lowShift : ℤ) by omega, pow2_natCast] at h2
    exact_mod_cast h2
  constructor
  · rw [Bool.eq_iff_iff, decide_eq_true_iff, decide_eq_true_iff, BitVec.lt_def,
      BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, ← hkey,
      Nat.mul_div_cancel _ (Nat.two_pow_pos _)]
    rfl
  · have h426 : ((1 : Reg) <<< 426).toNat = 2 ^ 426 := by
      rw [BitVec.toNat_shiftLeft, Reg.toNat_one, Nat.shiftLeft_eq, Nat.one_mul]
    have h128 : pow2 128 = ((2 ^ 426 : ℕ) : ℚ) * pow2 (-298) := by
      rw [← pow2_natCast, ← pow2_add]; rfl
    rw [Bool.eq_iff_iff, decide_eq_true_iff, decide_eq_true_iff, BitVec.lt_def, h426, hmag, h128]
    exact natCast_mul_pow2_lt_iff.symm

theorem Holds.repr_eq (h : r.Holds s) {D : Reg} (hD : D.toInt.natAbs < 2 ^ 427) :
    representableReg (D - r.H) = representable32 (s.overlap D.val) ∧
      representableReg r.H = representable32 s.H := by
  obtain ⟨hH, hHb⟩ := h.H_val
  have h427 : (2 : ℕ) ^ 427 < 2 ^ 574 := Nat.pow_lt_pow_right (by decide) (by decide)
  have h573 : (2 : ℕ) ^ 573 < 2 ^ 574 := Nat.pow_lt_pow_right (by decide) (by decide)
  have h575 : (2 : ℕ) ^ 574 < 2 ^ 575 := Nat.pow_lt_pow_right (by decide) (by decide)
  have hsub := Reg.toInt_sub (a := D) (b := r.H) (by omega) (by omega)
  refine ⟨?_, ?_⟩
  · rw [representableReg_iff (by rw [hsub]; omega), Reg.val_sub (by omega) (by omega), hH]; rfl
  · rw [representableReg_iff (by omega), hH]

theorem Holds.guard_eq (h : r.Holds s) {D : Reg} (hD : D.toInt.natAbs < 2 ^ 427) :
    r.guard D = s.guard D.val := by
  have hls := h.lowShift_eq
  have h149 : decide (149 ≤ r.lowShift) = decide (-149 ≤ s.lowBit) := by
    rw [Bool.eq_iff_iff, decide_eq_true_iff, decide_eq_true_iff]; omega
  obtain ⟨hr1, hr2⟩ := h.repr_eq hD
  unfold guard EftSplit.guard
  rw [h149, h.check_eq, hr1, hr2]
  by_cases hc : (s.lows == s.lowCoeffs.map fun (z : ℤ) => (z : ℚ) * pow2 s.lowBit) = true
  · obtain ⟨e3, e4⟩ := h.span_eq ((EftSplit.grid_check s).mp hc)
    rw [e3, e4]
  · simp only [Bool.not_eq_true] at hc; rw [hc]; simp

end RegSplit

/-! ## The fast path and the run -/

theorem naiveSumFrom_val : ∀ (xs : List Reg) (acc : Reg), acc.toInt.natAbs < 2 ^ 427 →
    (∀ x ∈ xs, x.toInt.natAbs < 2 ^ 573) →
    (RegSplit.naiveSumFrom acc xs).map Reg.val = naiveSum32From acc.val (xs.map Reg.val) ∧
      ∀ y, RegSplit.naiveSumFrom acc xs = some y → y.toInt.natAbs < 2 ^ 427
  | [], acc, ha, _ => ⟨rfl, fun y hy => by cases hy; exact ha⟩
  | x :: xs, acc, ha, hx => by
    have hx0 := hx x (List.mem_cons_self ..)
    have h427 : (2 : ℕ) ^ 427 < 2 ^ 574 := Nat.pow_lt_pow_right (by decide) (by decide)
    have h573 : (2 : ℕ) ^ 573 < 2 ^ 574 := Nat.pow_lt_pow_right (by decide) (by decide)
    have h575 : (2 : ℕ) ^ 574 < 2 ^ 575 := Nat.pow_lt_pow_right (by decide) (by decide)
    have hadd := Reg.toInt_add (a := acc) (b := x) (by omega) (by omega)
    obtain ⟨hb1, hb2⟩ := roundBack_val (x := acc + x) (by rw [hadd]; omega)
    have hv : (acc + x).val = acc.val + x.val := Reg.val_add (by omega) (by omega)
    simp only [RegSplit.naiveSumFrom, List.map_cons, naiveSum32From]
    cases hr : roundBack (acc + x) with
    | none =>
      rw [hr] at hb1
      refine ⟨?_, fun y hy => by simp at hy⟩
      unfold fp32Add; rw [← hv, ← hb1]; rfl
    | some y =>
      rw [hr] at hb1
      obtain ⟨ih1, ih2⟩ := naiveSumFrom_val xs y (hb2 y hr) (fun z hz => hx z (List.mem_cons_of_mem _ hz))
      refine ⟨?_, fun z hz => ih2 z (by simpa using hz)⟩
      unfold fp32Add; rw [← hv, ← hb1]
      simpa using ih1

namespace RegSplit

variable {r : RegSplit} {s : EftSplit}

theorem Holds.fastPath_eq (h : r.Holds s) {D : Reg} (hD : D.toInt.natAbs < 2 ^ 427) :
    r.fastPath D = s.fastPath D.val := by
  have h427 : (2 : ℕ) ^ 427 < 2 ^ 574 := Nat.pow_lt_pow_right (by decide) (by decide)
  have h559 : (2 : ℕ) ^ 559 < 2 ^ 573 := Nat.pow_lt_pow_right (by decide) (by decide)
  have h573 : (2 : ℕ) ^ 573 < 2 ^ 574 := Nat.pow_lt_pow_right (by decide) (by decide)
  have h575 : (2 : ℕ) ^ 574 < 2 ^ 575 := Nat.pow_lt_pow_right (by decide) (by decide)
  obtain ⟨hH, hHb⟩ := h.H_val
  obtain ⟨n1, n2⟩ := naiveSumFrom_val r.lows 0 (by decide)
    (fun x hx => Nat.lt_trans (h.lows_small x hx) h559)
  have hz : (0 : Reg).val = 0 := by simp [Reg.val]
  rw [hz, h.lows_val] at n1
  unfold fastPath EftSplit.fastPath naiveSum32
  cases hn : naiveSumFrom 0 r.lows with
  | none => rw [hn] at n1; rw [← n1]; rfl
  | some e =>
    rw [hn] at n1
    rw [← n1]
    simp only [Option.map_some, Option.bind_some]
    have hsub := Reg.toInt_sub (a := D) (b := r.H) (by omega) (by omega)
    have hneg := Reg.toInt_neg (a := D - r.H) (by rw [hsub]; omega)
    have hadd := Reg.toInt_add (a := D) (b := -(D - r.H)) (by omega) (by rw [hneg, hsub]; omega)
    obtain ⟨b1, b2⟩ := roundBack_val (x := D + -(D - r.H)) (by rw [hadd, hneg, hsub]; omega)
    have hv : (D + -(D - r.H)).val = D.val + -s.overlap D.val := by
      rw [Reg.val_add (by omega) (by rw [hneg, hsub]; omega), Reg.val_neg (by rw [hsub]; omega),
        Reg.val_sub (by omega) (by omega), hH]
      rfl
    unfold fp32Add
    rw [← hv]
    cases hb : roundBack (D + -(D - r.H)) with
    | none => rw [hb] at b1; rw [← b1]; rfl
    | some hreg =>
      rw [hb] at b1
      rw [← b1]
      simp only [Option.map_some, Option.bind_some]
      have he := n2 e hn
      have hh := b2 hreg hb
      have hadd' := Reg.toInt_add (a := hreg) (b := e) (by omega) (by omega)
      rw [roundSigned_eq (by rw [hadd']; omega), Reg.val_add (by omega) (by omega)]

theorem Holds.exactPath_eq (h : r.Holds s) (D : ℚ) : r.exactPath = s.exactPath D := by
  obtain ⟨h1, h2⟩ := h.exact_val
  unfold exactPath
  rw [roundSigned_eq h2, h1, EftSplit.exactPath_eq]

/-- The register correction returns what MC-EFT returns. -/
theorem Holds.run_eq (h : r.Holds s) {D : Reg} (hD : D.toInt.natAbs < 2 ^ 427) :
    r.run D = s.run D.val := by
  unfold run EftSplit.run
  rw [h.guard_eq hD, h.fastPath_eq hD, h.exactPath_eq D.val]
  rfl

end RegSplit

/-! ## MC-EFT on words, in the register -/

/-- Models whose blocks fit the register: products on `2^-298` with exponents at most `258`,
fewer than `2^12` products, and a zero `c` with exponent at most `127`. -/
def Model.FitsRun (P : Model) : Prop :=
  P.FitsReg ∧ P.nfma < 2 ^ 12 ∧ P.cZeroExp.all (· ≤ 127) = true

instance (P : Model) : Decidable P.FitsRun := by unfold Model.FitsRun; infer_instance

theorem foldl_maxExpStep_bound {B : ℤ} : ∀ (ps : List Unpacked) (acc : Option ℤ),
    (∀ v, acc = some v → v ≤ B) → (∀ p ∈ ps, p.e ≤ B) →
      ∀ r, ps.foldl maxExpStep acc = some r → r ≤ B
  | [], acc, ha, _, r, h => ha r h
  | p :: ps, acc, ha, hp, r, h => by
    simp only [List.foldl_cons] at h
    refine foldl_maxExpStep_bound ps _ ?_ (fun q hq => hp q (List.mem_cons_of_mem _ hq)) r h
    intro v hv
    have hpe := hp p (List.mem_cons_self ..)
    unfold maxExpStep at hv
    split at hv
    · exact ha v hv
    · simp only [Option.some.injEq] at hv
      cases acc with
      | none => simp at hv; omega
      | some w => have := ha w rfl; simp at hv; omega

theorem maxExp_bound {B : ℤ} {ps : List Unpacked} (hps : ∀ p ∈ ps, p.e ≤ B) :
    ∀ r, maxExp ps = some r → r ≤ B :=
  foldl_maxExpStep_bound ps none (by simp) hps

theorem alignExp_bound {B : ℤ} (P : Model) {ps : List Unpacked} (hps : ∀ p ∈ ps, p.e ≤ B) :
    ∀ r, alignExp P ps = some r → r ≤ B := by
  intro r h
  unfold alignExp at h
  split at h
  · have h1 := maxExp_bound (fun p hp => hps p (oddIndexed_subset _ p hp))
    have h2 := maxExp_bound (fun p hp => hps p (evenIndexed_subset _ p hp))
    revert h
    cases ho : maxExp (oddIndexed ps) <;> cases he : maxExp (evenIndexed ps) <;>
      simp [joinExp] <;> intro hr
    · exact hr ▸ h2 _ he
    · exact hr ▸ h1 _ ho
    · have := h1 _ ho; have := h2 _ he; omega
  · exact maxExp_bound hps r h

theorem hwGrid_bound {P : Model} {px : Prepared} {B : ℤ}
    (hA : ∀ e, alignExp P px.p = some e → e ≤ B) (hC : ∀ e, cExp P px.c = some e → e ≤ B) :
    ∀ g, hwGrid P px = some g → g ≤ B := by
  intro g h
  unfold hwGrid at h
  revert h
  cases ha : alignExp P px.p <;> cases hc : cExp P px.c <;> simp
  · intro hg; have := hC _ hc; omega
  · intro hg; have := hA _ ha; omega
  · rename_i e eC
    have := hA _ ha; have := hC _ hc
    split <;> simp <;> intro hg <;> omega

theorem cutoffAt_cases (P : Model) (px : Prepared) (g : ℤ) :
    cutoffAt P px g = g ∨ ∃ h, hwGrid P px = some h ∧ cutoffAt P px g = max g h := by
  unfold cutoffAt
  split
  · cases hw : hwGrid P px with
    | none => left; rfl
    | some h => right; exact ⟨h, rfl, rfl⟩
  · cases hw : hwGrid P px with
    | none => left; rfl
    | some h => right; exact ⟨h, rfl, rfl⟩
  · left; rfl

/-- The last bit of a decoded FP32 value: `2^-149` for zero, `2^(e − 23)` otherwise. -/
def ulpExpOf (u : Unpacked) : ℤ := if u.m = 0 then -149 else u.e - 23

theorem ulpExpOf_eq {w : F32} {u : Unpacked} (h : fp32.decode w = .finite u) :
    ulpExp32 u.value = ulpExpOf u := by
  unfold ulpExp32 ulpExpOf
  by_cases hm : u.m = 0
  · rw [if_pos ((Unpacked.value_eq_zero_iff u).mpr hm), if_pos hm]
  · rw [if_neg (fun h0 => hm ((Unpacked.value_eq_zero_iff u).mp h0)), if_neg hm,
      normExp_decode32 h hm]

/-- The register split of decoded operands at the cut-off for a decoded output `dU`. -/
def regSplit (P : Model) (px : Prepared) (dU : Unpacked) : RegSplit :=
  ⟨(cutoffAt P px (ulpExpOf dU) + 298).toNat,
    (cRule P px, px.c.toReg) :: px.p.map fun p => (.trunc, p.toReg)⟩

theorem regSplit_holds {Q : Model} (hQ : Q.cZeroExp.all (· ≤ 127) = true) {px : Prepared} {cw : F32}
    (hprod : ∀ p ∈ px.p, -298 ≤ p.e - p.t ∧ p.e ≤ 258 ∧ p.m < 2 ^ (p.t + 2))
    (hc : fp32.decode cw = .finite px.c) (hk : px.p.length < 2 ^ 12) {D : F32} {dU : Unpacked}
    (hd : fp32.decode D = .finite dU) : (regSplit Q px dU).Holds (eftSplit Q px dU.value) := by
  obtain ⟨hct, hcm, hce1, hce2, _⟩ := decode32_finite_fields hc
  obtain ⟨hdt, hdm, hde1, hde2, _⟩ := decode32_finite_fields hd
  have hg : -149 ≤ ulpExpOf dU ∧ ulpExpOf dU ≤ 104 := by unfold ulpExpOf; split <;> omega
  have hA := alignExp_bound Q (B := 258) (ps := px.p) (fun p hp => (hprod p hp).2.1)
  have hC : ∀ e, cExp Q px.c = some e → e ≤ 258 := by
    intro e he
    unfold cExp at he
    split at he
    · cases hz : Q.cZeroExp with
      | none => rw [hz] at he; cases he
      | some z => rw [hz] at he hQ; simp at he hQ; omega
    · simp at he; omega
  have hw := hwGrid_bound hA hC
  have hcut : -149 ≤ cutoffAt Q px (ulpExpOf dU) ∧ cutoffAt Q px (ulpExpOf dU) ≤ 258 := by
    rcases cutoffAt_cases Q px (ulpExpOf dU) with h | ⟨g, hg', h⟩
    · rw [h]; omega
    · rw [h]; have := hw g hg'; omega
  have hcg : -298 ≤ px.c.e - px.c.t := by omega
  have hcb : px.c.coeff298.natAbs < 2 ^ 428 := by
    have := coeff298_lt (j := 1) hcg (by rw [hct]; exact hcm)
    exact Nat.lt_of_lt_of_le this (Nat.pow_le_pow_right (by decide) (by omega))
  have hpb : ∀ p ∈ px.p, p.coeff298.natAbs < 2 ^ 558 := by
    intro p hp
    obtain ⟨p1, p2, p3⟩ := hprod p hp
    exact Nat.lt_of_lt_of_le (coeff298_lt (j := 2) p1 p3) (Nat.pow_le_pow_right (by decide) (by omega))
  have h428 : (2 : ℕ) ^ 428 < 2 ^ 559 := Nat.pow_lt_pow_right (by decide) (by decide)
  have h558 : (2 : ℕ) ^ 558 < 2 ^ 559 := Nat.pow_lt_pow_right (by decide) (by decide)
  have h575 : (2 : ℕ) ^ 559 < 2 ^ 575 := Nat.pow_lt_pow_right (by decide) (by decide)
  have hreg : ∀ u : Unpacked, -298 ≤ u.e - u.t → u.coeff298.natAbs < 2 ^ 559 →
      u.toReg.val = u.value ∧ u.toReg.toInt.natAbs < 2 ^ 559 := by
    intro u hu hb
    rw [coeff298_natAbs] at hb
    exact ⟨Unpacked.toReg_val hu (by omega), by rw [Unpacked.toReg_toInt (by omega), coeff298_natAbs]; exact hb⟩
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · show (((cutoffAt Q px (ulpExpOf dU) + 298).toNat : ℕ) : ℤ) = eftCutoff Q px dU.value + 298
    rw [eftCutoff_eq, ulpExpOf_eq hd]; omega
  · show _ = (cRule Q px, px.c.value) :: px.p.map fun p => (.trunc, p.value)
    simp only [regSplit, List.map_cons, List.map_map, Function.comp_def]
    rw [(hreg px.c hcg (by omega)).1]
    congr 1
    apply List.map_congr_left
    intro p hp
    rw [(hreg p (hprod p hp).1 (by have := hpb p hp; omega)).1]
  · intro t ht
    simp only [regSplit, List.mem_cons, List.mem_map] at ht
    rcases ht with rfl | ⟨p, hp, rfl⟩
    · exact (hreg px.c hcg (by omega)).2
    · exact (hreg p (hprod p hp).1 (by have := hpb p hp; omega)).2
  · simp only [regSplit, List.length_cons, List.length_map]; omega
  · show (cutoffAt Q px (ulpExpOf dU) + 298).toNat ≤ 559; omega

/-- MC-EFT on one block in the 576-bit register: the split, the sums, the guard, the fast path
and the exact fallback on registers, with exponents and shift counts as small naturals. -/
def mcEftFixed {P : Model} (x : BlockInput P) (D : F32) : Except EftError EftResult :=
  if x.a.length ≠ P.nfma ∨ x.b.length ≠ P.nfma then .error .wrongLength
  else
    match prepare x with
    | none => .error .nonfiniteInput
    | some px =>
      match (fp32.decode D).toFinite with
      | none => .error .nonfiniteOutput
      | some dU => .ok ((regSplit P px dU).run dU.toReg)

/-- MC-EFT on an inner product in the 576-bit register. -/
def mcEftDotFixed (P : Model) (a : List P.a.Word) (b : List P.b.Word) (c D : F32) :
    Except EftError EftResult :=
  if a.length ≠ b.length then .error .wrongLength
  else
    match prepare (P := P) ⟨a, b, c⟩ with
    | none => .error .nonfiniteInput
    | some px =>
      match (fp32.decode D).toFinite with
      | none => .error .nonfiniteOutput
      | some dU => .ok ((regSplit sfmaF32 px dU).run dU.toReg)

theorem decode_toFinite {w : F32} {u : Unpacked} (h : (fp32.decode w).toFinite = some u) :
    fp32.decode w = .finite u := toFinite_some h

/-- On every model that fits, the register correction of a block is MC-EFT. -/
theorem mcEftFixed_eq {P : Model} (hP : P.FitsRun) (x : BlockInput P) (D : F32) :
    mcEftFixed x D = mcEft x D := by
  obtain ⟨hR, hn, hz⟩ := hP
  unfold mcEftFixed mcEft
  by_cases hl : x.a.length ≠ P.nfma ∨ x.b.length ≠ P.nfma
  · rw [if_pos hl, if_pos hl]
  · rw [if_neg hl, if_neg hl]
    cases hp : prepare x with
    | none => rfl
    | some px =>
      simp only
      cases hd : (fp32.decode D).toFinite with
      | none =>
        have : value32 D = none := by simp [value32, hd]
        rw [this]
      | some dU =>
        have hv : value32 D = some dU.value := by simp [value32, hd]
        rw [hv]
        simp only
        have hk : px.p.length < 2 ^ 12 := by
          have := prepare_lengths hp; rw [Prepared.p_length]; omega
        have hH := regSplit_holds hz (products_fit hR hp) (toFinite_some (prepare_c hp)) hk
          (decode_toFinite hd)
        obtain ⟨hdv, hdb⟩ := decode32_reg (decode_toFinite hd)
        rw [hH.run_eq hdb, hdv]

/-- On every model that fits, the register correction of an inner product of fewer than `2^12`
products is MC-EFT. -/
theorem mcEftDotFixed_eq {P : Model} (hP : P.FitsReg) (a : List P.a.Word) (b : List P.b.Word)
    (c D : F32) (hk : a.length < 2 ^ 12) : mcEftDotFixed P a b c D = mcEftDot P a b c D := by
  unfold mcEftDotFixed mcEftDot
  by_cases hl : a.length ≠ b.length
  · rw [if_pos hl, if_pos hl]
  · rw [if_neg hl, if_neg hl]
    cases hp : prepare (P := P) ⟨a, b, c⟩ with
    | none => rfl
    | some px =>
      simp only
      cases hd : (fp32.decode D).toFinite with
      | none =>
        have : value32 D = none := by simp [value32, hd]
        rw [this]
      | some dU =>
        have hv : value32 D = some dU.value := by simp [value32, hd]
        rw [hv]
        simp only
        have hk' : px.p.length < 2 ^ 12 := by
          have := prepare_lengths hp; rw [Prepared.p_length]; simp only at this; omega
        have hH := regSplit_holds (Q := sfmaF32) (by decide) (products_fit hP hp)
          (toFinite_some (prepare_c hp)) hk' (decode_toFinite hd)
        obtain ⟨hdv, hdb⟩ := decode32_reg (decode_toFinite hd)
        rw [hH.run_eq hdb, hdv, dotSplit_eq]

theorem paper_models_fitRun :
    sfmaF32.FitsRun ∧ cdna1F16.FitsRun ∧ cdna1BF16.FitsRun ∧ cdna2F16.FitsRun ∧
      cdna2BF16.FitsRun ∧ cdna2BF16_1k.FitsRun ∧ cdna3F16.FitsRun ∧ cdna3BF16.FitsRun ∧
      cdna3XF32.FitsRun ∧ (cdna3FP8 e4m3fnuz e4m3fnuz).FitsRun ∧
      (cdna3FP8 e4m3fnuz e5m2fnuz).FitsRun ∧ (cdna3FP8 e5m2fnuz e4m3fnuz).FitsRun ∧
      (cdna3FP8 e5m2fnuz e5m2fnuz).FitsRun := by
  decide

end MatrixCore
