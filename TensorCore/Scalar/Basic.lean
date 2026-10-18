import TensorCore.Numerics.Binary.RoundingContract

/-! Binary IEEE scalar values. -/

namespace TensorCore.IEEE

inductive BinaryFormat where
  | fp16 | fp32 | fp64
  deriving Repr, DecidableEq

def BinaryFormat.layout : BinaryFormat → Format
  | .fp16 => TensorCore.fp16
  | .fp32 => TensorCore.fp32
  | .fp64 => TensorCore.fp64

theorem BinaryFormat.valid (f : BinaryFormat) : f.layout.WellFormed := by
  cases f <;> decide +kernel

abbrev Word (f : BinaryFormat) := BitVec f.layout.width

def sign (f : BinaryFormat) (b : Word f) : Bool := binarySign f.layout b

def zero (f : BinaryFormat) (negative : Bool) : Word f :=
  (BinaryRep.zero f.layout f.valid negative).encode

def infinity (f : BinaryFormat) (negative : Bool) : Word f :=
  BitVec.ofNat _ ((if negative then 2 ^ (f.layout.mantissaBits + f.layout.exponentBits) else 0) +
    (2 ^ f.layout.exponentBits - 1) * 2 ^ f.layout.mantissaBits)

def quietBit (f : BinaryFormat) : ℕ := 2 ^ (f.layout.mantissaBits - 1)

def nan (f : BinaryFormat) (negative : Bool) (payload : ℕ) : Word f :=
  BitVec.ofNat _ ((infinity f negative).toNat + quietBit f + payload % quietBit f)

def maxFiniteWord (f : BinaryFormat) (negative : Bool) : Word f :=
  encodeBinary f.layout negative f.layout.emax ((2 ^ (f.layout.mantissaBits + 1) - 1 : ℕ) : ℤ)

inductive Datum where
  | finite (negative : Bool) (value : ℚ)
  | infinity (negative : Bool)
  | nan (negative : Bool) (signaling : Bool) (payload : ℕ)
  deriving Repr, DecidableEq

def decode (f : BinaryFormat) (b : Word f) : Datum :=
  match classify f.layout b with
  | .zero _ => .finite (sign f b) 0
  | .subnormal d | .normal d => .finite (sign f b) d.value
  | .infinity s => .infinity s
  | .nan => .nan (sign f b)
      (decide (b.toNat % 2 ^ f.layout.mantissaBits < quietBit f)) (b.toNat % quietBit f)

def Datum.isNaN : Datum → Bool
  | .nan .. => true
  | _ => false

def Datum.isSignaling : Datum → Bool
  | .nan _ s _ => s
  | _ => false

def Datum.isZero : Datum → Bool
  | .finite _ x => decide (x = 0)
  | _ => false

def Datum.isInfinite : Datum → Bool
  | .infinity _ => true
  | _ => false

def Datum.negative : Datum → Bool
  | .finite s _ | .infinity s | .nan s _ _ => s

def Datum.negate : Datum → Datum
  | .finite s x => .finite (!s) (-x)
  | .infinity s => .infinity (!s)
  | .nan s sig p => .nan s sig p

structure Flags where
  invalid : Bool := false
  divideByZero : Bool := false
  overflow : Bool := false
  underflow : Bool := false
  inexact : Bool := false
  deriving Repr, DecidableEq

def Flags.union (a b : Flags) : Flags :=
  ⟨a.invalid || b.invalid, a.divideByZero || b.divideByZero,
   a.overflow || b.overflow, a.underflow || b.underflow, a.inexact || b.inexact⟩

inductive Tininess where
  | beforeRounding | afterRounding
  deriving Repr, DecidableEq

structure Context where
  mode : BinaryRoundingMode := .nearestEven
  tininess : Tininess := .afterRounding
  deriving Repr, DecidableEq

structure Result (f : BinaryFormat) where
  bits : Word f
  flags : Flags := {}
  deriving Repr, DecidableEq

/-- Explicit sticky status accumulation; an operation only reports newly raised flags. -/
def Result.accumulate (r : Result f) (previous : Flags) : Flags := previous.union r.flags

theorem zero_value (f : BinaryFormat) (s : Bool) :
    binaryValue f.layout (zero f s) = some 0 := by
  have h := (BinaryRep.zero f.layout f.valid s).encode_value f.valid
  cases s <;> simpa [zero, BinaryRep.zero, BinaryRep.value] using h

theorem zero_sign (f : BinaryFormat) (s : Bool) : sign f (zero f s) = s :=
  (encodeBinary_fields f.layout f.valid (BinaryRep.zero f.layout f.valid s)).1

theorem decode_zero (f : BinaryFormat) (s : Bool) : decode f (zero f s) = .finite s 0 := by
  cases f <;> cases s <;> decide +kernel

theorem decode_infinity (f : BinaryFormat) (s : Bool) : decode f (infinity f s) = .infinity s := by
  cases f <;> cases s <;> decide +kernel

theorem decode_nan (f : BinaryFormat) (s : Bool) (p : ℕ) :
    decode f (nan f s p) = .nan s false (p % quietBit f) := by
  have hc : classify f.layout (nan f s p) = .nan := by
    cases f <;> cases s <;>
      simp [nan, infinity, quietBit, classify, classifyNat,
        BinaryFormat.layout, fp16, fp32, fp64, Format.width, BitVec.toNat_ofNat]
    all_goals split <;> (try omega)
    all_goals split <;> (try omega)
    all_goals rfl
  unfold decode
  rw [hc]
  cases f <;> cases s <;>
    simp [nan, infinity, quietBit, sign, binarySign, BinaryFormat.layout,
      fp16, fp32, fp64, Format.width, BitVec.toNat_ofNat]
  all_goals repeat' apply And.intro
  all_goals omega

theorem maxFiniteWord_value (f : BinaryFormat) (s : Bool) :
    binaryValue f.layout (maxFiniteWord f s) =
      some (if s then -f.layout.maxFinite else f.layout.maxFinite) := by
  have h := encodeBinary_value f.layout f.valid s f.layout.emax
    ((2 ^ (f.layout.mantissaBits + 1) - 1 : ℕ) : ℤ) (f.layout.emin_le_emax f.valid)
    (Int.le_refl _) (by cases f <;> decide +kernel) (by cases f <;> decide +kernel)
    (Or.inl (by cases f <;> decide +kernel))
  cases s <;> simpa [maxFiniteWord, Format.maxFinite, Rat.neg_mul, Rat.intCast_natCast] using h

theorem maxFiniteWord_sign (f : BinaryFormat) (s : Bool) :
    sign f (maxFiniteWord f s) = s := by
  cases f <;> cases s <;> decide +kernel

theorem maxFinite_positive (f : BinaryFormat) : 0 < f.layout.maxFinite := by
  cases f <;> decide +kernel

/-- Finite IEEE decoding agrees with the numerical value and encoded sign bit. -/
theorem decode_finite_iff (f : BinaryFormat) (b : Word f) (s : Bool) (v : ℚ) :
    decode f b = .finite s v ↔ binaryValue f.layout b = some v ∧ sign f b = s := by
  cases hc : classify f.layout b <;>
    simp [decode, binaryValue, hc, Classification.finite, Decoded.value, and_comm]

theorem flags_union_self (a : Flags) : a.union a = a := by cases a; simp [Flags.union]

theorem flags_union_assoc (a b c : Flags) : (a.union b).union c = a.union (b.union c) := by
  cases a; cases b; cases c; simp [Flags.union, Bool.or_assoc]

end TensorCore.IEEE
