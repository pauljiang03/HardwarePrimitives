import TCFloat.Monotonicity
import TensorCore.EFT.Encoded

/-! Arithmetic and representation bridges between the first-principles and FloatLib definitions. -/
namespace TCFloat.Equivalence
open FloatLib.Floats.Formats.BinaryInterchange

@[simp] theorem pow2_eq (e : Int) : TensorCore.pow2 e = TCFloat.pow2 e := rfl
@[simp] theorem abs_eq (x : Rat) : TensorCore.absQ x = |x| := by
  unfold TensorCore.absQ
  split <;> rename_i h
  · exact (abs_of_neg h).symm
  · exact (abs_of_nonneg (le_of_not_gt h)).symm
@[simp] theorem maxFinite_eq : TensorCore.maxFinite32 = TCFloat.maxFinite32 := rfl
@[simp] theorem truncCoeff_eq (x : Rat) (e : Int) :
    TensorCore.truncBits x e = TCFloat.truncCoeff x e := rfl
@[simp] theorem truncGrid_eq (x : Rat) (e : Int) :
    TensorCore.truncGrid x e = TCFloat.truncGrid x e := rfl
@[simp] theorem sumQ_eq (xs : List Rat) : TensorCore.sumQ xs = xs.sum := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [TensorCore.sumQ, ih]
@[simp] theorem sumZ_eq (xs : List Int) : TensorCore.sumZ xs = xs.sum := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [TensorCore.sumZ, ih]

/-- The `TensorCore` rounding modes as FloatLib's IEEE modes. -/
def mode : TensorCore.RoundingMode → Mode
  | .truncate => .towardZero
  | .nearestEven => .nearestEven

def term (d : TensorCore.Decoded) : Term :=
  ⟨FloatLib.Numerics.Dyadic.ofScaledInt d.significand (d.exponent-d.mantissaBits),
    d.exponent,d.mantissaBits⟩

def project (t : Term) : TensorCore.Decoded :=
  ⟨t.dyadic.signedSignificand,t.exponent,t.mantissaBits⟩

@[simp] theorem term_value (d : TensorCore.Decoded) : (term d).value = d.value := by
  simp [term, Term.value, TensorCore.Decoded.value, pow2,
    FloatLib.Numerics.Dyadic.ofScaledInt_toRat]

@[simp] theorem project_term (d : TensorCore.Decoded) : project (term d) = d := by
  rcases d with ⟨s,e,f⟩
  simp only [project,term,FloatLib.Numerics.Dyadic.ofScaledInt,FloatLib.Numerics.Dyadic.signedSignificand]
  by_cases h : s < 0
  · simp [h, abs_of_neg h]
  · simp [h, Int.natAbs_of_nonneg (le_of_not_gt h)]

/-- Canonical FloatLib terms: consistent scale metadata, with the source's single zero sign. -/
def CanonicalTerm := {t : Term // term (project t) = t}

/-- A two-sided representation equivalence, for arbitrary integer terms. -/
def termEquiv : TensorCore.Decoded ≃ CanonicalTerm where
  toFun d := ⟨term d, by simp⟩
  invFun t := project t.val
  left_inv := project_term
  right_inv t := Subtype.ext t.property

end TCFloat.Equivalence
