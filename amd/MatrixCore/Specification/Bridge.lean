import MatrixCore.Specification.Defs
import MatrixCore.MC.SpecialAgreement
import MatrixCore.Numerics.Uniqueness

/-! # Bridges between the specification and the implementation

Decoding, products, fixed-point alignment, normalization, and rounding of the specification
agree with the implementation's grid operations. -/

namespace MatrixCore.Spec

open MatrixCore

def layoutOf (f : Format) : Layout := ⟨f.exponentBits, f.mantissaBits, f.bias, f.specials == .fnuz⟩
def numOf (u : Unpacked) : Num := ⟨u.negative, u.m, u.t, u.e⟩
def operandOf : InputFormat → Operand
  | .packed f => .layout (layoutOf f)
  | .xf32 => .xf32

theorem two_zpow (e : ℤ) : (2 : ℚ) ^ e = pow2 e := rfl

theorem val_numOf (u : Unpacked) : (numOf u).val = u.value := by
  unfold Num.val numOf Unpacked.value
  cases u.negative <;> simp [two_zpow] <;> grind

theorem mul_numOf (a b : Unpacked) : mul (numOf a) (numOf b) = numOf (a.mul b) := rfl

theorem int_numOf_val (u : Unpacked) : ((numOf u).int : ℚ) * pow2 (u.e - u.t) = u.value := by
  unfold Num.int numOf Unpacked.value
  cases u.negative <;> simp [Rat.intCast_natCast]

/-! ## Decoding -/

theorem decode_eq (f : Format) (n : ℕ) : decode (layoutOf f) n = (f.decodeNat n).toFinite.map numOf := by
  unfold decode layoutOf Format.decodeNat Format.unpackFields Format.emin
  simp only
  generalize n % 2 ^ f.mantissaBits = F
  generalize n / 2 ^ f.mantissaBits % 2 ^ f.exponentBits = E
  generalize n / 2 ^ (f.mantissaBits + f.exponentBits) % 2 = s
  have hsb : (s == 1) = decide (s = 1) := by cases h : s == 1 <;> simp_all
  have hieee : (Specials.ieee == Specials.fnuz) = false := rfl
  have hfnuz : (Specials.fnuz == Specials.fnuz) = true := rfl
  rw [hsb]
  cases hsp : f.specials <;>
    by_cases h1 : E = 2 ^ f.exponentBits - 1 <;> by_cases h2 : E = 0 <;> by_cases h3 : F = 0 <;>
    by_cases h4 : s = 1 <;> simp_all [Datum.toFinite, numOf]

theorem operand_decode_eq (i : InputFormat) (w : i.Word) :
    (operandOf i).decode w.toNat = (i.read w).toFinite.map numOf := by
  cases i with
  | packed f => exact decode_eq f w.toNat
  | xf32 =>
    show (decode fp32 w.toNat).map _ = (match MatrixCore.fp32.decode w with
      | Datum.finite x => Datum.finite (InputFormat.truncateXF32 x) | d => d).toFinite.map numOf
    have h := decode_eq MatrixCore.fp32 w.toNat
    have hl : layoutOf MatrixCore.fp32 = fp32 := rfl
    rw [hl] at h
    rw [h]
    show _ = (match MatrixCore.Format.decodeNat MatrixCore.fp32 w.toNat with
      | Datum.finite x => Datum.finite (InputFormat.truncateXF32 x) | d => d).toFinite.map numOf
    cases MatrixCore.Format.decodeNat MatrixCore.fp32 w.toNat <;> rfl

theorem mapM_decode_eq (i : InputFormat) (ws : List i.Word) :
    (ws.map BitVec.toNat).mapM (operandOf i).decode =
      (ws.mapM fun w => (i.read w).toFinite).map (List.map numOf) := by
  induction ws with
  | nil => rfl
  | cons w ws ih =>
    simp only [List.map_cons, List.mapM_cons, ih, operand_decode_eq]
    cases (i.read w).toFinite <;> simp
    cases ws.mapM fun w => (i.read w).toFinite <;> simp

theorem value32_eq (w : F32) : value32 w = MatrixCore.value32 w := by
  unfold value32 MatrixCore.value32
  have h := decode_eq MatrixCore.fp32 w.toNat
  have hl : layoutOf MatrixCore.fp32 = fp32 := rfl
  rw [hl] at h
  rw [h]
  show _ = (MatrixCore.Format.decodeNat MatrixCore.fp32 w.toNat).toFinite.map Unpacked.value
  cases (MatrixCore.Format.decodeNat MatrixCore.fp32 w.toNat).toFinite <;> simp [val_numOf]

/-! ## Fixed-point alignment -/

theorem floor_shiftNat (M : ℕ) (s : ℤ) : ((M : ℚ) * pow2 s).floor = (shiftNat M s : ℤ) := by
  unfold shiftNat
  split
  · rename_i hs
    have : (M : ℚ) * pow2 s = ((M * 2 ^ s.toNat : ℕ) : ℤ) := by
      rw [show s = (s.toNat : ℤ) by omega, pow2_natCast]; push_cast; rfl
    rw [this, Rat.floor_intCast]
  · rename_i hs
    have hp : pow2 s = (((2 ^ (-s).toNat : ℕ) : ℚ))⁻¹ := by
      rw [← pow2_natCast, show ((-s).toNat : ℤ) = -s by omega]
      unfold pow2; rw [Rat.zpow_neg, Rat.inv_inv]
    rw [hp, ← Rat.div_def, show ((M : ℚ)) = ((M : ℤ) : ℚ) by rw [Rat.intCast_natCast],
      floor_intCast_div M (2 ^ (-s).toNat) (Nat.two_pow_pos _)]
    rfl

theorem shiftNat_zero (s : ℤ) : shiftNat 0 s = 0 := by unfold shiftNat; split <;> simp

/-- `alignTrunc` is magnitude truncation on the grid `2^(e − k)`. -/
theorem alignTrunc_eq (u : Unpacked) (e : ℤ) (k : ℕ) :
    (alignTrunc (numOf u) e k : ℚ) * pow2 (e - k) = truncGrid u.value (e - k) := by
  have hscale : absQ u.value / pow2 (e - k) = (u.m : ℚ) * pow2 (u.e - u.t - (e - k)) := by
    rw [Unpacked.absQ_value, div_pow2, Rat.mul_assoc, ← pow2_add,
      show u.e - (u.t : ℤ) + -(e - (k : ℤ)) = u.e - u.t - (e - k) by omega]
  have hfl := floor_shiftNat u.m (u.e - u.t - (e - k))
  rw [← hscale] at hfl
  unfold alignTrunc truncGrid
  simp only [numOf]
  by_cases hm : u.m = 0
  · have hv : u.value = 0 := (Unpacked.value_eq_zero_iff u).mpr hm
    rw [hv, hm, shiftNat_zero]
    have h0 : Rat.floor 0 = 0 := rfl
    have h1 : (0 : ℚ) / pow2 (e - k) = 0 := by rw [Rat.div_def, Rat.zero_mul]
    have h2 : ¬ ((0 : ℚ) < 0) := by decide
    by_cases hn : u.negative = true <;> simp [hn, h0, h1, h2]
  · by_cases hn : u.negative = true
    · have hneg : u.value < 0 := (Unpacked.value_neg_iff u).mpr ⟨hn, hm⟩
      rw [absQ_of_neg hneg] at hfl
      simp only [hn, ↓reduceIte, hneg, hfl, Rat.intCast_neg, Rat.intCast_natCast, Rat.neg_mul]
    · have hpos : ¬ u.value < 0 := fun h => hn ((Unpacked.value_neg_iff u).mp h).1
      rw [absQ_of_nonneg (by grind)] at hfl
      simp only [hn, Bool.false_eq_true, ↓reduceIte, hpos, hfl, Rat.intCast_natCast]

/-- `shiftRD` is RD from the grid `2^g` onto the grid `2^h`. -/
theorem shiftRD_eq (V : ℤ) (g h : ℤ) :
    (shiftRD V g h : ℚ) * pow2 h = rdGrid ((V : ℚ) * pow2 g) h := by
  unfold shiftRD rdGrid
  have hsc : (V : ℚ) * pow2 g / pow2 h = (V : ℚ) * pow2 (g - h) := by
    rw [div_pow2, Rat.mul_assoc, ← pow2_add, show g + -h = g - h by omega]
  rw [hsc]
  split
  · rename_i hle
    have : (V : ℚ) * pow2 (g - h) = ((V * 2 ^ (g - h).toNat : ℤ) : ℚ) := by
      rw [← intCast_mul_pow2_nat, show (((g - h).toNat : ℕ) : ℤ) = g - h by omega]
    rw [this, Rat.floor_intCast]
  · rename_i hlt
    have hp : pow2 (g - h) = (((2 ^ (h - g).toNat : ℕ) : ℚ))⁻¹ := by
      rw [← pow2_natCast, show ((h - g).toNat : ℤ) = -(g - h) by omega]
      unfold pow2; rw [Rat.zpow_neg, Rat.inv_inv]
    rw [hp, ← Rat.div_def, floor_intCast_div V _ (Nat.two_pow_pos _)]

/-! ## Exponents -/

theorem foldl_maxExp_some (l : List Unpacked) (v : ℤ) :
    l.foldl maxExpStep (some v) = some (((l.filter fun p => p.m ≠ 0).map Unpacked.e).foldl max v) := by
  induction l generalizing v with
  | nil => rfl
  | cons p l ih =>
    simp only [List.foldl_cons]
    by_cases hp : p.m = 0
    · simp [maxExpStep, hp, ih]
    · simp [maxExpStep, hp, ih]

theorem emax_eq (ps : List Unpacked) : emax (ps.map numOf) = maxExp ps := by
  have hf : ((ps.map numOf).filter fun p => p.M ≠ 0).map Num.e =
      (ps.filter fun p => p.m ≠ 0).map Unpacked.e := by
    rw [List.filter_map, List.map_map]; rfl
  unfold emax maxExp
  rw [hf]
  clear hf
  induction ps with
  | nil => rfl
  | cons p ps ih =>
    by_cases hp : p.m = 0
    · have h1 : (p :: ps).filter (fun p => decide (p.m ≠ 0)) =
          ps.filter (fun p => decide (p.m ≠ 0)) := by simp [hp]
      rw [h1, List.foldl_cons]; simp only [maxExpStep, if_pos hp]; exact ih
    · have h1 : (p :: ps).filter (fun p => decide (p.m ≠ 0)) =
          p :: ps.filter (fun p => decide (p.m ≠ 0)) := by simp [hp]
      rw [h1, List.map_cons, List.foldl_cons]
      simp only [maxExpStep, if_neg hp]
      rw [foldl_maxExp_some]
      rfl

end MatrixCore.Spec
