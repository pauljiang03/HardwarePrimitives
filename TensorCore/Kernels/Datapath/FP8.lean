import TensorCore.Kernels.Datapath.Correctness
import TensorCore.TC.GPUs

/-! # A bitvector datapath for the FP8 block FMAs

The datapath of `TensorCore.Datapath` covers FP16, BF16 and TF32 with `F ≥ 23` mantissa bits
after alignment: it shifts each significand left by `F − mantissaBits`. The FP8 block FMAs of Ada
and Hopper keep `F = 13` bits, fewer than `c`'s 23, so the alignment here first places every
significand on `L = max F 23` bits after the binary point, shifts it right by the exponent gap,
and then drops `L − F` more bits. For `F ≥ 23` the extra shift is zero and this is the alignment of
`Datapath.Term.aligned`. The accumulator has `F + 2` integer and mantissa bits, the carry bits and
a sign bit: 21 bits on Ada (`N_FMA = 16`) and 22 on Hopper (`N_FMA = 32`), as in *Accurate Models*
Table 3 plus the sign; it is sign-extended for the normalizer `Datapath.normalize`. Ada and Hopper
then clear the ten low mantissa bits of the binary32 word (a 13-bit block output).

`evalBlock8_eq`: on every input of the six FP8 models (Ada, Hopper and B200; E4M3 in the `e4m3x`
layout of `GPUs.lean`, and E5M2), the datapath returns the model's output word, or the same
error. -/

namespace TensorCore.Datapath.FP8

open TensorCore TensorCore.Datapath
open TensorCore.EFMachine (dyadic_div floor_nat_div mapM_project_eq mapM_bounds)

set_option exponentiation.threshold 1024
set_option maxRecDepth 8192

inductive FP8Variant where
  | adaE4M3 | adaE5M2 | hopperE4M3 | hopperE5M2 | blackwellE4M3 | blackwellE5M2
  deriving Repr, DecidableEq

def FP8Variant.model : FP8Variant → Model
  | .adaE4M3 => adaE4M3F32
  | .adaE5M2 => adaE5M2F32
  | .hopperE4M3 => hopperE4M3F32
  | .hopperE5M2 => hopperE5M2F32
  | .blackwellE4M3 => blackwellE4M3F32
  | .blackwellE5M2 => blackwellE5M2F32

def FP8Variant.e4m3 : FP8Variant → Bool
  | .adaE4M3 | .hopperE4M3 | .blackwellE4M3 => true
  | _ => false

/-- Ada and Hopper: 13-bit alignment and block output. -/
def FP8Variant.narrow : FP8Variant → Bool
  | .blackwellE4M3 | .blackwellE5M2 => false
  | _ => true

/-- F: the mantissa bits kept after alignment. -/
def fBits (v : FP8Variant) : BitVec 5 := if v.narrow then 13 else 25

/-- L = max F 23: the left shift places each significand on L bits after the binary point. -/
def lBits (v : FP8Variant) : BitVec 5 := if v.narrow then 23 else 25

/-- L − F. -/
def dropBits (v : FP8Variant) : ℕ := if v.narrow then 10 else 0

def wideWidth (v : FP8Variant) : ℕ := (lBits v).toNat + 2
def termWidth8 (v : FP8Variant) : ℕ := (fBits v).toNat + 2
def carryBits8 (v : FP8Variant) : ℕ := v.model.nfma.log2 + 1
def accWidth8 (v : FP8Variant) : ℕ := termWidth8 v + carryBits8 v + 1

/-- Field extraction for E4M3 (in the `e4m3x` layout: five exponent bits, bias 7) and E5M2 words;
infinities and NaNs are rejected. Exponents are biased by 128 as in `Datapath.Input`. -/
def decodeInput8 (e4 : Bool) (bits : F32) : Option Input :=
  let mb : ℕ := if e4 then 3 else 2
  let e := ((bits >>> mb) &&& 31).setWidth 9
  let m := (bits &&& (((1 : F32) <<< mb) - 1)).setWidth 11
  let negative := (bits >>> (mb + 5)) != 0
  let offset : Exp := if e4 then 121 else 113
  let frac : BitVec 5 := if e4 then 3 else 2
  if e == 31 then none
  else if e == 0 then
    if m == 0 then some ⟨negative, 0, 0, 128⟩
    else some ⟨negative, m, frac, offset + 1⟩
  else some ⟨negative, ((1 : BitVec 11) <<< mb) + m, frac, e + offset⟩

def decodeTerm8 (v : FP8Variant) (pair : v.model.Word × v.model.Word) : Option Datapath.Term := do
  let a ← decodeInput8 v.e4m3 (pair.1.zeroExtend 32)
  let b ← decodeInput8 v.e4m3 (pair.2.zeroExtend 32)
  return product a b

/-- Largest exponent of a nonzero term (the FP8 models have no minimum alignment exponent). -/
def alignExp8 (ts : List Datapath.Term) : Exp :=
  ts.foldl (fun e t => if t.significand == 0 then e
    else if e ≤ t.biasedExp then t.biasedExp else e) 0

/-- The term's magnitude truncated to the grid `2 ^ (e − 256 − F)`: placed on `L` bits after the
binary point, shifted right by the exponent gap, then by `L − F`. -/
def aligned8 (v : FP8Variant) (e : Exp) (t : Datapath.Term) : BitVec (termWidth8 v) :=
  (((t.significand.zeroExtend (wideWidth v) <<< (lBits v - t.mantissaBits)) >>>
    (e - t.biasedExp)) >>> dropBits v).setWidth (termWidth8 v)

def signedAligned8 (v : FP8Variant) (e : Exp) (t : Datapath.Term) : BitVec (accWidth8 v) :=
  let a := (aligned8 v e t).zeroExtend (accWidth8 v)
  if t.negative then -a else a

def accumulate8 (v : FP8Variant) (e : Exp) (ts : List Datapath.Term) : BitVec (accWidth8 v) :=
  ts.foldl (fun s t => s + signedAligned8 v e t) 0

/-- Ada and Hopper clear the ten low mantissa bits of the binary32 word. -/
def outputStage (v : FP8Variant) (bits : F32) : F32 :=
  if v.narrow then (bits >>> 10) <<< 10 else bits

/-- One FP8 block FMA, computed with bitvector operations only. -/
def evalBlock8 (v : FP8Variant) (x : BlockInput v.model) : Except ModelError F32 := do
  if x.products.length != v.model.nfma then throw .wrongProductCount
  let some c := decodeC x.c | throw .nonfiniteInput
  let some ps := x.products.mapM (decodeTerm8 v) | throw .nonfiniteInput
  let ts := c :: ps
  let e := alignExp8 ts
  let some bits := normalize ((accumulate8 v e ts).signExtend 40) e (fBits v)
    | throw .accumulatorOutOfRange
  return outputStage v bits

/-! ## Decoding -/

/-- The bounds of a decoded input, as a Boolean. -/
def boundsB (a : Input) : Bool :=
  decide (a.significand.toNat < 2 ^ (a.mantissaBits.toNat + 1)) && decide (a.mantissaBits.toNat ≤ 3) &&
    decide (2 ≤ a.biasedExp.toNat) && decide (a.biasedExp.toNat ≤ 255)

/-- Bounds of every decoded FP8 input, both layouts, all words (kernel-checked). -/
theorem decodeInput8_bounds_all (e4 : Bool) :
    ∀ n : ℕ, n < 512 → (decodeInput8 e4 (BitVec.ofNat 32 n)).all boundsB = true := by
  cases e4 <;> decide +kernel

theorem decodeInput8_e4m3x :
    ∀ n : ℕ, n < 512 → (decodeInput8 true (BitVec.ofNat 32 n)).map Input.decoded =
      (classify e4m3x (BitVec.ofNat 9 n)).finite := by
  decide +kernel

theorem decodeInput8_e5m2 :
    ∀ n : ℕ, n < 256 → (decodeInput8 false (BitVec.ofNat 32 n)).map Input.decoded =
      (classify e5m2 (BitVec.ofNat 8 n)).finite := by
  decide +kernel

theorem zeroExtend_eq_ofNat {w : ℕ} (x : BitVec w) : x.zeroExtend 32 = BitVec.ofNat 32 x.toNat := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_setWidth, BitVec.toNat_ofNat]

theorem decodeInput8_e4m3x' (w : BitVec 9) :
    (decodeInput8 true (w.zeroExtend 32)).map Input.decoded = (classify e4m3x w).finite := by
  have h := decodeInput8_e4m3x w.toNat w.isLt
  have h1 : BitVec.ofNat 9 w.toNat = w := by apply BitVec.eq_of_toNat_eq; simp
  rw [h1] at h
  rw [zeroExtend_eq_ofNat]
  exact h

theorem decodeInput8_e5m2' (w : BitVec 8) :
    (decodeInput8 false (w.zeroExtend 32)).map Input.decoded = (classify e5m2 w).finite := by
  have h := decodeInput8_e5m2 w.toNat w.isLt
  have h1 : BitVec.ofNat 8 w.toNat = w := by apply BitVec.eq_of_toNat_eq; simp
  rw [h1] at h
  rw [zeroExtend_eq_ofNat]
  exact h

theorem decodeInput8_model (v : FP8Variant) (word : v.model.Word) :
    (decodeInput8 v.e4m3 (word.zeroExtend 32)).map Input.decoded = v.model.decode word := by
  cases v
  · exact decodeInput8_e4m3x' word
  · exact decodeInput8_e5m2' word
  · exact decodeInput8_e4m3x' word
  · exact decodeInput8_e5m2' word
  · exact decodeInput8_e4m3x' word
  · exact decodeInput8_e5m2' word

theorem decodeInput8_bounds {v : FP8Variant} {word : v.model.Word} {a : Input}
    (h : decodeInput8 v.e4m3 (word.zeroExtend 32) = some a) :
    a.significand.toNat < 2 ^ (a.mantissaBits.toNat + 1) ∧ a.mantissaBits.toNat ≤ 3 ∧
      2 ≤ a.biasedExp.toNat ∧ a.biasedExp.toNat ≤ 255 := by
  rw [zeroExtend_eq_ofNat] at h
  have hw : word.toNat < 512 := by
    have hle : v.model.input.width ≤ 9 := by cases v <;> decide
    exact Nat.lt_of_lt_of_le word.isLt (Nat.pow_le_pow_right (by decide) hle)
  have := decodeInput8_bounds_all v.e4m3 word.toNat hw
  rw [h] at this
  simp only [Option.all_some, boundsB, Bool.and_eq_true, decide_eq_true_eq] at this
  exact ⟨this.1.1.1, this.1.1.2, this.1.2, this.2⟩

/-! ## Products -/

def Accepted8 (t : Datapath.Term) : Prop := t.Valid ∧ (t.significand ≠ 0 → 1 ≤ t.biasedExp.toNat)

theorem product_spec8 {a b : Input}
    (ha : a.significand.toNat < 2 ^ (a.mantissaBits.toNat + 1) ∧ a.mantissaBits.toNat ≤ 3 ∧
      2 ≤ a.biasedExp.toNat ∧ a.biasedExp.toNat ≤ 255)
    (hb : b.significand.toNat < 2 ^ (b.mantissaBits.toNat + 1) ∧ b.mantissaBits.toNat ≤ 3 ∧
      2 ≤ b.biasedExp.toNat ∧ b.biasedExp.toNat ≤ 255) :
    (product a b).denormalized = denormalizedMul a.decoded b.decoded ∧ Accepted8 (product a b) := by
  obtain ⟨ha1, ha2, ha3, ha4⟩ := ha
  obtain ⟨hb1, hb2, hb3, hb4⟩ := hb
  have hmul : (EFMachine.multiplySignificands a.significand b.significand).toNat =
      a.significand.toNat * b.significand.toNat := by
    have hlt : a.significand.toNat * b.significand.toNat < 2 ^ 24 := by
      have := Nat.mul_lt_mul'' a.significand.isLt b.significand.isLt
      omega
    unfold EFMachine.multiplySignificands
    rw [BitVec.toNat_mul, BitVec.toNat_setWidth, BitVec.toNat_setWidth,
      Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le a.significand.isLt (by decide)),
      Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le b.significand.isLt (by decide)), Nat.mod_eq_of_lt hlt]
  have hexp : (a.biasedExp + b.biasedExp).toNat = a.biasedExp.toNat + b.biasedExp.toNat := by
    rw [BitVec.toNat_add, Nat.mod_eq_of_lt (by change _ < 512; omega)]
  have hmb : (a.mantissaBits + b.mantissaBits).toNat = a.mantissaBits.toNat + b.mantissaBits.toNat := by
    rw [BitVec.toNat_add, Nat.mod_eq_of_lt (by change _ < 32; omega)]
  refine ⟨?_, ⟨?_, ?_⟩, ?_⟩
  · simp only [Term.denormalized, product, denormalizedMul, Input.decoded, hmul, hexp, hmb,
      DenormalizedProduct.mk.injEq]
    refine ⟨?_, by omega, by omega⟩
    cases a.negative <;> cases b.negative <;> simp [Int.neg_mul, Int.mul_neg]
  · simp only [product, hmul, hmb]
    have := Nat.mul_lt_mul'' ha1 hb1
    rw [← Nat.pow_add] at this
    rw [show a.mantissaBits.toNat + b.mantissaBits.toNat + 2 =
      a.mantissaBits.toNat + 1 + (b.mantissaBits.toNat + 1) by omega]
    exact this
  · simp only [product, hmb]; omega
  · intro _; simp only [product, hexp]; omega

theorem decodeTerm8_spec (v : FP8Variant) (pair : v.model.Word × v.model.Word) :
    (decodeTerm8 v pair).map Term.denormalized =
      ((do return (← v.model.decode pair.1, ← v.model.decode pair.2) :
        Option (Decoded × Decoded))).map (fun (a, b) => denormalizedMul a b) := by
  rw [← decodeInput8_model, ← decodeInput8_model]
  cases ha : decodeInput8 v.e4m3 (pair.1.zeroExtend 32) with
  | none => simp [decodeTerm8, ha]
  | some a =>
    cases hb : decodeInput8 v.e4m3 (pair.2.zeroExtend 32) with
    | none => simp [decodeTerm8, ha, hb]
    | some b =>
      simp only [decodeTerm8, ha, hb, Option.map_some, pure, bind, Option.bind]
      exact congrArg some (product_spec8 (decodeInput8_bounds ha) (decodeInput8_bounds hb)).1

theorem decodeTerm8_accepted {v : FP8Variant} {pair : v.model.Word × v.model.Word} {t : Datapath.Term}
    (h : decodeTerm8 v pair = some t) : Accepted8 t := by
  cases ha : decodeInput8 v.e4m3 (pair.1.zeroExtend 32) with
  | none => simp [decodeTerm8, ha] at h
  | some a =>
    cases hb : decodeInput8 v.e4m3 (pair.2.zeroExtend 32) with
    | none => simp [decodeTerm8, ha, hb] at h
    | some b =>
      simp [decodeTerm8, ha, hb] at h
      rw [← h]
      exact (product_spec8 (decodeInput8_bounds ha) (decodeInput8_bounds hb)).2

theorem decodeC_accepted8 {bits : F32} {c : Datapath.Term} (h : decodeC bits = some c) : Accepted8 c :=
  decodeC_accepted h

/-! ## Alignment and accumulation -/

theorem variant_bits (v : FP8Variant) :
    v.model.alignMantissaBits = (fBits v).toNat ∧ (lBits v).toNat = (fBits v).toNat + dropBits v ∧
      23 ≤ (lBits v).toNat ∧ (lBits v).toNat ≤ 25 ∧ v.model.eAlignMin = none ∧
      v.model.outputMantissaBits = (if v.narrow then 13 else 23) := by
  cases v <;> decide

theorem aligned8_toNat (v : FP8Variant) (e : Exp) (t : Datapath.Term) (ht : t.Valid)
    (he : t.biasedExp.toNat ≤ e.toNat) :
    (aligned8 v e t).toNat = t.significand.toNat * 2 ^ ((lBits v).toNat - t.mantissaBits.toNat) /
      2 ^ (e.toNat - t.biasedExp.toNat + dropBits v) := by
  obtain ⟨ht1, ht2⟩ := ht
  obtain ⟨_, hLF, hL, hL', _, _⟩ := variant_bits v
  have hsub : ((lBits v) - t.mantissaBits).toNat = (lBits v).toNat - t.mantissaBits.toNat := by
    rw [BitVec.toNat_sub_of_le (by rw [BitVec.le_def]; omega)]
  have hd : (e - t.biasedExp).toNat = e.toNat - t.biasedExp.toNat := by
    rw [BitVec.toNat_sub_of_le (by rw [BitVec.le_def]; exact he)]
  have hz : (t.significand.zeroExtend (wideWidth v)).toNat = t.significand.toNat := by
    rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt]
    exact Nat.lt_of_lt_of_le ht1 (Nat.pow_le_pow_right (by decide) (by unfold wideWidth; omega))
  have hfit : t.significand.toNat * 2 ^ ((lBits v).toNat - t.mantissaBits.toNat) <
      2 ^ wideWidth v := by
    have h := Nat.mul_lt_mul_of_pos_right ht1
      (Nat.two_pow_pos ((lBits v).toNat - t.mantissaBits.toNat))
    rw [← Nat.pow_add] at h
    exact Nat.lt_of_lt_of_le h (Nat.pow_le_pow_right (by decide) (by unfold wideWidth; omega))
  have hq : t.significand.toNat * 2 ^ ((lBits v).toNat - t.mantissaBits.toNat) /
      2 ^ (e.toNat - t.biasedExp.toNat) / 2 ^ dropBits v < 2 ^ termWidth8 v := by
    rw [Nat.div_div_eq_div_mul]
    apply Nat.div_lt_of_lt_mul
    calc t.significand.toNat * 2 ^ ((lBits v).toNat - t.mantissaBits.toNat)
        < 2 ^ wideWidth v := hfit
      _ ≤ 2 ^ (e.toNat - t.biasedExp.toNat) * 2 ^ dropBits v * 2 ^ termWidth8 v := by
          rw [← Nat.pow_add, ← Nat.pow_add]
          exact Nat.pow_le_pow_right (by decide) (by unfold wideWidth termWidth8; omega)
  unfold aligned8
  rw [BitVec.toNat_setWidth, BitVec.toNat_ushiftRight, BitVec.ushiftRight_eq',
    BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, Nat.shiftRight_eq_div_pow,
    BitVec.shiftLeft_eq', BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, hsub, hz,
    Nat.mod_eq_of_lt hfit, hd, Nat.mod_eq_of_lt hq, Nat.div_div_eq_div_mul, ← Nat.pow_add]

theorem truncBits_eq8 (v : FP8Variant) (e : Exp) (t : Datapath.Term) (ht : t.Valid)
    (he : t.significand ≠ 0 → t.biasedExp.toNat ≤ e.toNat) :
    truncBits t.denormalized.value ((e.toNat : ℤ) - 256 - (fBits v).toNat) =
      if t.negative then -((aligned8 v e t).toNat : ℤ) else ((aligned8 v e t).toNat : ℤ) := by
  by_cases hz : t.significand = 0
  · have h0 : t.significand.toNat = 0 := by rw [hz]; rfl
    have hv : t.denormalized.value = 0 := by
      simp [Term.denormalized, DenormalizedProduct.value, h0]
    have ha : (aligned8 v e t).toNat = 0 := by
      unfold aligned8
      rw [hz]
      simp
    rw [hv, truncBits_zero, ha]
    cases t.negative <;> simp
  · have hle := he hz
    rw [aligned8_toNat v e t ht hle]
    obtain ⟨_, hLF, hL, hL', _, _⟩ := variant_bits v
    have hmb := ht.2
    have hn : 0 < t.significand.toNat := by
      have : t.significand.toNat ≠ 0 := fun h => hz (BitVec.eq_of_toNat_eq h)
      omega
    have hq : (t.significand.toNat : ℚ) * pow2 (((t.biasedExp.toNat : ℤ) - 256) - t.mantissaBits.toNat) /
        pow2 ((e.toNat : ℤ) - 256 - (fBits v).toNat) =
        ((t.significand.toNat * 2 ^ ((lBits v).toNat - t.mantissaBits.toNat) : ℕ) : ℚ) /
          ((2 ^ (e.toNat - t.biasedExp.toNat + dropBits v) : ℕ) : ℚ) := by
      have h1 : (t.significand.toNat : ℚ) *
          pow2 (((t.biasedExp.toNat : ℤ) - 256) - t.mantissaBits.toNat) =
          ((t.significand.toNat * 2 ^ ((lBits v).toNat - t.mantissaBits.toNat) : ℕ) : ℚ) *
            pow2 ((t.biasedExp.toNat : ℤ) - 256 - (lBits v).toNat) := by
        rw [Rat.natCast_mul, Rat.mul_assoc, ← pow2_natCast, ← pow2_add]
        congr 2
        omega
      rw [h1, show (e.toNat : ℤ) - 256 - (fBits v).toNat =
          ((t.biasedExp.toNat : ℤ) - 256 - (lBits v).toNat) +
            ((e.toNat - t.biasedExp.toNat + dropBits v : ℕ) : ℤ) by omega]
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

theorem signedAligned8_eq (v : FP8Variant) (e : Exp) (t : Datapath.Term) :
    signedAligned8 v e t = BitVec.ofInt (accWidth8 v)
      (if t.negative then -((aligned8 v e t).toNat : ℤ) else ((aligned8 v e t).toNat : ℤ)) := by
  have hz : ((aligned8 v e t).zeroExtend (accWidth8 v)) =
      BitVec.ofInt (accWidth8 v) ((aligned8 v e t).toNat : ℤ) := by
    rw [BitVec.ofInt_natCast]
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
  unfold signedAligned8
  cases t.negative
  · simp only [Bool.false_eq_true, if_false]
    exact hz
  · simp only [if_true, BitVec.ofInt_neg, hz]

theorem accumulate8_eq (v : FP8Variant) (e : Exp) (ts : List Datapath.Term) (s : BitVec (accWidth8 v)) :
    ts.foldl (fun s t => s + signedAligned8 v e t) s =
      machineAccumulate (accWidth8 v) s (ts.map fun t =>
        if t.negative then -((aligned8 v e t).toNat : ℤ) else ((aligned8 v e t).toNat : ℤ)) := by
  induction ts generalizing s with
  | nil => rfl
  | cons t ts ih =>
    simp only [List.foldl_cons, List.map_cons, machineAccumulate]
    rw [ih, signedAligned8_eq]

/-- The two's complement accumulator holds the exact sum of the aligned terms. -/
theorem accumulate8_toInt (v : FP8Variant) (e : Exp) (ts : List Datapath.Term)
    (hlen : ts.length = v.model.nfma + 1) :
    (accumulate8 v e ts).toInt = sumZ (ts.map fun t =>
      if t.negative then -((aligned8 v e t).toNat : ℤ) else ((aligned8 v e t).toNat : ℤ)) := by
  unfold accumulate8
  rw [accumulate8_eq]
  apply machineAccumulate_of_coefficient_bound _ (termWidth8 v) (carryBits8 v)
  · intro z hz
    obtain ⟨t, _, rfl⟩ := List.mem_map.mp hz
    have := (aligned8 v e t).isLt
    cases t.negative <;> simp <;> omega
  · rw [List.length_map, hlen]
    exact Nat.lt_log2_self

/-- The bitvector accumulator, read on its grid, is the model's aligned accumulator. -/
theorem accumulator8_eq (v : FP8Variant) (ts : List Datapath.Term) (b : PreparedBlock)
    (hprof : b.model = v.model) (hterms : b.terms = ts.map Term.denormalized)
    (hacc : ∀ t ∈ ts, Accepted8 t) (hlen : ts.length = v.model.nfma + 1) :
    ((accumulate8 v (alignExp8 ts) ts).toInt : ℚ) *
      pow2 (((alignExp8 ts).toNat : ℤ) - 256 - (fBits v).toNat) = b.accumulator := by
  obtain ⟨hal, _, _, _, hnone, _⟩ := variant_bits v
  obtain ⟨hA1, hA2, hA3⟩ := alignFold_spec ts 0
  change (0 : Exp).toNat ≤ (alignExp8 ts).toNat at hA1
  change ∀ t ∈ ts, t.significand ≠ 0 → t.biasedExp.toNat ≤ (alignExp8 ts).toNat at hA2
  change alignExp8 ts = 0 ∨ ∃ t ∈ ts, t.significand ≠ 0 ∧ alignExp8 ts = t.biasedExp at hA3
  generalize hA : alignExp8 ts = A at hA1 hA2 hA3
  have htr : ∀ t ∈ ts, truncBits t.denormalized.value ((A.toNat : ℤ) - 256 - (fBits v).toNat) =
      if t.negative then -((aligned8 v A t).toNat : ℤ) else ((aligned8 v A t).toNat : ℤ) :=
    fun t ht => truncBits_eq8 v A t (hacc t ht).1 (hA2 t ht)
  rw [accumulate8_toInt v A ts hlen, ← List.map_congr_left htr]
  have hsig : ∀ t : Datapath.Term, t.denormalized.significand = 0 ↔ t.significand = 0 := by
    intro t
    have : t.significand = 0 ↔ t.significand.toNat = 0 :=
      ⟨fun h => by rw [h]; rfl, fun h => BitVec.eq_of_toNat_eq (by rw [h]; rfl)⟩
    rw [this]
    unfold Term.denormalized
    cases t.negative <;> simp
  unfold PreparedBlock.accumulator PreparedBlock.alignedBits
  rw [hterms, List.map_map]
  by_cases hall : ∀ t ∈ ts, t.significand = 0
  · have hv : ∀ t ∈ ts, t.denormalized.value = 0 := by
      intro t ht
      simp [DenormalizedProduct.value, (hsig t).mpr (hall t ht)]
    rw [sumZ_map_zero _ _ (fun t ht => by rw [hv t ht, truncBits_zero]),
      sumZ_map_zero _ _ (fun t ht => by simp only [Function.comp, hv t ht, truncBits_zero])]
    simp
  · have hex : ∃ t ∈ ts, t.significand ≠ 0 := by
      apply Classical.byContradiction
      intro h
      exact hall (fun t ht => Classical.byContradiction fun hz => h ⟨t, ht, hz⟩)
    obtain ⟨t0, ht0, hz0⟩ := hex
    have hmem : t0.denormalized ∈ b.terms := by rw [hterms]; exact List.mem_map_of_mem ht0
    obtain ⟨m, hm, hm0⟩ := maxTermExp_term b.terms t0.denormalized hmem (mt (hsig t0).mp hz0)
    have hup : m ≤ (A.toNat : ℤ) - 256 := by
      apply maxTermExp_upper b.terms _ _ m (by rw [hm]; rfl)
      intro u hu hnz
      rw [hterms] at hu
      obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hu
      have := hA2 t ht (mt (hsig t).mpr hnz)
      simp only [Term.denormalized]
      omega
    have hlow : ∀ t ∈ ts, t.significand ≠ 0 → (t.biasedExp.toNat : ℤ) - 256 ≤ m := by
      intro t ht hnz
      obtain ⟨m', hm', hle⟩ := maxTermExp_term b.terms t.denormalized
        (by rw [hterms]; exact List.mem_map_of_mem ht) (mt (hsig t).mp hnz)
      rw [hm] at hm'
      cases Option.some.inj hm'
      exact hle
    have hexp : b.alignExp = some ((A.toNat : ℤ) - 256) := by
      unfold PreparedBlock.alignExp Model.applyEAlignMin
      rw [hm, hprof, hnone]
      dsimp only
      congr 1
      rcases hA3 with h | ⟨t, ht, hnz, h⟩
      · exfalso
        have h1 := hA2 t0 ht0 hz0
        have h2 := (hacc t0 ht0).2 hz0
        rw [h] at h1
        change _ ≤ 0 at h1
        omega
      · have := hlow t ht hnz
        have : A.toNat = t.biasedExp.toNat := by rw [h]
        omega
    have hgrid : b.alignGridExponent = (A.toNat : ℤ) - 256 - (fBits v).toNat := by
      unfold PreparedBlock.alignGridExponent
      rw [hexp, hprof, hal]
      rfl
    rw [hgrid]
    rfl

/-! ## The output stage -/

theorem outputStage_eq (v : FP8Variant) (bits : F32) :
    outputStage v bits = truncateMantissa32 v.model.outputMantissaBits bits := by
  obtain ⟨_, _, _, _, _, hout⟩ := variant_bits v
  rw [hout]
  unfold outputStage
  cases hn : v.narrow
  · simp only [Bool.false_eq_true, ↓reduceIte, truncateMantissa32_23]
  · simp only [↓reduceIte]
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_shiftLeft, BitVec.toNat_ushiftRight, Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow,
      truncateMantissa32_toNat]
    have hlt := bits.isLt
    have hle : bits.toNat / 2 ^ 10 * 2 ^ 10 ≤ bits.toNat := Nat.div_mul_le_self _ _
    simp only [BitVec.toNat_ofNat, Nat.reduceMod, Nat.reduceSub]
    exact Nat.mod_eq_of_lt (by omega)

/-! ## The datapath computes the model -/

/-- The FP8 bitvector datapath returns the model's output word, or the same error, on every input
of the six FP8 models. -/
theorem evalBlock8_eq (v : FP8Variant) (x : BlockInput v.model) :
    evalBlock8 v x = (TensorCore.evalBlock x).map (·.output.bits) := by
  unfold evalBlock8 TensorCore.evalBlock
  by_cases hlen : x.products.length = v.model.nfma
  · simp only [hlen, bne_self_eq_false, Bool.false_eq_true, if_false]
    have hmap := mapM_project_eq (f := decodeTerm8 v) (v := Term.denormalized)
      (g := fun (a, b) => do return (← v.model.decode a, ← v.model.decode b))
      (w := fun (a, b) => denormalizedMul a b)
      (fun pair => by rcases pair with ⟨a, b⟩; exact decodeTerm8_spec v (a, b)) x.products
    have hcmap := decodeC_spec x.c
    cases hc : decodeC x.c with
    | none =>
      have hdc : decode32 x.c = none := by
        rw [hc] at hcmap
        cases hd : decode32 x.c with
        | none => rfl
        | some _ => rw [hd] at hcmap; simp at hcmap
      simp only [prepare, hdc]
      rfl
    | some c =>
      rw [hc] at hcmap
      obtain ⟨dc, hdc, hcs⟩ : ∃ dc, decode32 x.c = some dc ∧
          c.denormalized = ⟨dc.significand, dc.exponent, dc.mantissaBits⟩ := by
        cases hd : decode32 x.c with
        | none => rw [hd] at hcmap; simp at hcmap
        | some dc =>
          rw [hd] at hcmap
          exact ⟨dc, rfl, Option.some.inj hcmap⟩
      cases hps : x.products.mapM (decodeTerm8 v) with
      | none =>
        have hpp : prepareProducts v.model x.products = none := by
          unfold prepareProducts
          rw [hps] at hmap
          cases hq : x.products.mapM (fun (a, b) => do return (← v.model.decode a, ← v.model.decode b) :
              v.model.Word × v.model.Word → Option (Decoded × Decoded)) with
          | none => rfl
          | some _ => rw [hq] at hmap; simp at hmap
        simp only [prepare, hdc, hpp]
        rfl
      | some ps =>
        rw [hps] at hmap
        cases hpp : prepareProducts v.model x.products with
        | none =>
          unfold prepareProducts at hpp
          rw [hpp] at hmap
          simp at hmap
        | some ds =>
          unfold prepareProducts at hpp
          rw [hpp] at hmap
          simp only [Option.map_some, Option.some.injEq] at hmap
          have hprep : prepare x = some ⟨v.model, ds, dc⟩ := by
            simp only [prepare, hdc, prepareProducts, hpp]
          rw [hprep]
          dsimp only
          have hterms : (PreparedBlock.mk v.model ds dc).terms =
              (c :: ps).map Term.denormalized := by
            simp only [PreparedBlock.terms, List.map_cons, hcs]
            rw [hmap]
          obtain ⟨hpl, hpa⟩ := mapM_bounds (fun _ _ h => decodeTerm8_accepted h) hps
          have hacc : ∀ t ∈ c :: ps, Accepted8 t := by
            intro t ht
            rcases List.mem_cons.mp ht with rfl | ht
            · exact decodeC_accepted8 hc
            · exact hpa t ht
          have hlen' : (c :: ps).length = v.model.nfma + 1 := by
            simp [hpl, hlen]
          have hw : accWidth8 v ≤ 40 := by cases v <;> decide
          have hsx : ((accumulate8 v (alignExp8 (c :: ps)) (c :: ps)).signExtend 40).toInt =
              (accumulate8 v (alignExp8 (c :: ps)) (c :: ps)).toInt :=
            BitVec.toInt_signExtend_of_le hw
          rw [normalize_eq _ _ _ (by decide) (by decide), hsx,
            accumulator8_eq v _ _ rfl hterms hacc hlen']
          unfold evalPrepared
          cases hr : round32 .truncate (PreparedBlock.mk v.model ds dc).accumulator with
          | none => rfl
          | some bits =>
            have hfin := decode32_truncateMantissa32 (m := v.model.outputMantissaBits) (w := bits)
              (by
                obtain ⟨bits', d, hb', hd⟩ := round32_finite_exists .truncate _ (round32_range hr)
                rw [hr] at hb'
                cases Option.some.inj hb'
                simp [hd])
            cases hf : decode32 (truncateMantissa32 v.model.outputMantissaBits bits) with
            | none => simp [hf] at hfin
            | some d =>
              have hf' : finite32 (truncateMantissa32 v.model.outputMantissaBits bits) =
                  some ⟨_, d, hf⟩ := by
                unfold finite32
                split
                · rename_i he; rw [hf] at he; contradiction
                · rename_i d' he; rw [hf] at he; cases Option.some.inj he; rfl
              simp only [hf', outputStage_eq]
              rfl
  · have hb : (x.products.length != v.model.nfma) = true := by simpa using hlen
    rw [if_pos hb, if_pos hb]
    rfl

end TensorCore.Datapath.FP8
