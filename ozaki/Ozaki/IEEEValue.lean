import Ozaki.SignedZero
import Ozaki.Bounded

/-! # IEEE values: signed zeros, infinities and NaN

The schemes compute rationals and report overflow as `none`. An IEEE binary format also has two
zeros, two infinities and NaN. `FVal` is such a datum: a finite value with its sign bit (`Signed`,
so `+0` and `−0` differ), `±Inf`, or NaN (payloads are not modeled).

For a binary format with `p` significand bits and exponents `emin … emax`:

* `roundF` is IEEE's round to nearest even into the format as a total function: the rounded value
  when its magnitude is at most the largest finite value, `±Inf` beyond (IEEE's overflow rule for
  round to nearest), and a zero result signed like the exact value, or by a given sign bit when the
  exact value is zero (`roundF_of_some`, `roundF_of_none`, `roundF_zero`);
* `mulF` and `addF` are IEEE multiplication and addition: the exact result rounded once, with
  IEEE's special cases: `NaN` propagates, `Inf · 0` and `Inf + (−Inf)` are `NaN`, an infinity
  absorbs finite values, signs of products are the exclusive or of the factors' signs, `x + (−x)`
  is `+0` and `(−0) + (−0)` is `−0` (`mulF_nan_left`, …, `addF_neg_self`, `addF_negZero`);
* `mulX` is the exact product with the same special cases, used by the dot product's
  specification. -/

local notation "ℕ" => Nat
local notation "ℤ" => Int
local notation "ℚ" => Rat

namespace Ozaki

/-- An IEEE binary floating-point datum: a finite value with its sign bit (which tells `+0` from
`−0`), an infinity with its sign, or NaN. -/
inductive FVal where
  | fin (s : Signed)
  | inf (neg : Bool)
  | nan
  deriving DecidableEq, Repr

/-- The finite part of a datum. -/
def finPart : FVal → Option Signed
  | .fin s => some s
  | _ => none

/-- The finite parts of a vector, `none` if an entry is infinite or NaN. -/
def finParts (xs : List FVal) : Option (List Signed) := xs.mapM finPart

/-- A datum of the format: a finite datum is a value of the format whose sign bit is its sign. -/
def FVal.InFormat (p : ℕ) (emin emax : ℤ) : FVal → Prop
  | .fin s => FormatValue p emin emax s.val ∧ s.WellFormed
  | _ => True

/-- **IEEE round to nearest even** of the exact value `q`: the rounded value when it is at most
the largest finite value, `±Inf` beyond; a zero result has the sign of `q`, or the sign bit `z`
when `q` itself is zero. -/
def roundF (p : ℕ) (emin emax : ℤ) (q : ℚ) (z : Bool) : FVal :=
  match roundRNE p emin emax q with
  | some r => .fin ⟨r, sumNeg q z⟩
  | none => .inf (decide (q < 0))

/-- The exact product of two data, with IEEE's special cases: NaN propagates, `Inf · 0` is NaN,
and the sign is the exclusive or of the factors' signs. -/
def mulX : FVal → FVal → FVal
  | .nan, _ => .nan
  | _, .nan => .nan
  | .inf a, .inf b => .inf (xor a b)
  | .inf a, .fin t => if t.val = 0 then .nan else .inf (xor a t.neg)
  | .fin s, .inf b => if s.val = 0 then .nan else .inf (xor s.neg b)
  | .fin s, .fin t => .fin ⟨s.val * t.val, xor s.neg t.neg⟩

/-- **IEEE multiplication**: the exact product, rounded to nearest even when finite. -/
def mulF (p : ℕ) (emin emax : ℤ) (a b : FVal) : FVal :=
  match mulX a b with
  | .fin s => roundF p emin emax s.val s.neg
  | v => v

/-- **IEEE addition** with round to nearest even: NaN propagates, `Inf + (−Inf)` is NaN, an
infinity absorbs finite values, and an exact zero sum is `−0` only when both operands are `−0`. -/
def addF (p : ℕ) (emin emax : ℤ) : FVal → FVal → FVal
  | .nan, _ => .nan
  | _, .nan => .nan
  | .inf a, .inf b => if a = b then .inf a else .nan
  | .inf a, .fin _ => .inf a
  | .fin _, .inf b => .inf b
  | .fin s, .fin t => roundF p emin emax (s.val + t.val) (s.neg && t.neg)

variable {p : ℕ} {emin emax : ℤ}

/-! ## Rounding -/

theorem roundF_of_some {q r : ℚ} (h : roundRNE p emin emax q = some r) (z : Bool) :
    roundF p emin emax q z = .fin ⟨r, sumNeg q z⟩ := by
  unfold roundF; rw [h]

theorem roundF_of_none {q : ℚ} (h : roundRNE p emin emax q = none) (z : Bool) :
    roundF p emin emax q z = .inf (decide (q < 0)) := by
  unfold roundF; rw [h]

/-- An exact zero rounds to the zero of the given sign. -/
theorem roundF_zero (z : Bool) : roundF p emin emax 0 z = .fin ⟨0, z⟩ := by
  rw [roundF_of_some (roundRNE_zero' p emin emax) z]
  rfl

/-- A value of the format rounds to itself. -/
theorem roundF_of_formatValue (hp : 0 < p) {v : ℚ} (hv : FormatValue p emin emax v) (z : Bool) :
    roundF p emin emax v z = .fin ⟨v, sumNeg v z⟩ :=
  roundF_of_some (roundRNE_of_formatValue hp hv) z

/-- **Overflow is `±Inf`**: rounding gives an infinity exactly when the round to nearest even
exceeds the largest finite value, and its sign is the exact value's. -/
theorem roundF_eq_inf_iff (q : ℚ) (z n : Bool) :
    roundF p emin emax q z = .inf n ↔ roundRNE p emin emax q = none ∧ n = decide (q < 0) := by
  unfold roundF
  cases roundRNE p emin emax q with
  | some r => simp
  | none => simp [eq_comm]

/-- A finite rounding is the round to nearest even. -/
theorem roundF_eq_fin_iff (q : ℚ) (z : Bool) (s : Signed) :
    roundF p emin emax q z = .fin s ↔
      roundRNE p emin emax q = some s.val ∧ s.neg = sumNeg q z := by
  unfold roundF
  cases roundRNE p emin emax q with
  | some r =>
    constructor
    · intro h; cases h; exact ⟨rfl, rfl⟩
    · rintro ⟨h1, h2⟩; cases h1; cases s; simp_all
  | none => simp

/-- Rounding never gives NaN. -/
theorem roundF_ne_nan (q : ℚ) (z : Bool) : roundF p emin emax q z ≠ .nan := by
  unfold roundF; split <;> simp

/-- A finite rounding is a value of the format whose sign bit is its sign. -/
theorem roundF_inFormat (hp : 0 < p) (hle : emin ≤ emax) (q : ℚ) (z : Bool) :
    (roundF p emin emax q z).InFormat p emin emax := by
  unfold roundF
  cases hr : roundRNE p emin emax q with
  | none => trivial
  | some r =>
    refine ⟨((roundRNE_nearest hp hle) q r hr).1, fun hr0 => ?_⟩
    obtain ⟨hq0, hs⟩ := sign_of_round (roundRNE_nearest hp hle) (roundRNE_zero' p emin emax) hr hr0
    show sumNeg q z = decide (r < 0)
    unfold sumNeg; rw [if_neg hq0, hs]

/-! ## The special-case table -/

@[simp] theorem mulF_nan_left (a : FVal) : mulF p emin emax .nan a = .nan := rfl

@[simp] theorem mulF_nan_right (a : FVal) : mulF p emin emax a .nan = .nan := by
  cases a <;> rfl

@[simp] theorem addF_nan_left (a : FVal) : addF p emin emax .nan a = .nan := rfl

@[simp] theorem addF_nan_right (a : FVal) : addF p emin emax a .nan = .nan := by
  cases a <;> rfl

/-- `Inf · 0` and `0 · Inf` are NaN, whatever the signs. -/
theorem mulF_inf_zero (a n : Bool) : mulF p emin emax (.inf a) (.fin ⟨0, n⟩) = .nan := rfl

theorem mulF_zero_inf (a n : Bool) : mulF p emin emax (.fin ⟨0, n⟩) (.inf a) = .nan := rfl

/-- An infinity times a nonzero finite value is an infinity with the product's sign. -/
theorem mulF_inf_fin (a : Bool) {s : Signed} (hs : s.val ≠ 0) :
    mulF p emin emax (.inf a) (.fin s) = .inf (xor a s.neg) := by
  simp [mulF, mulX, hs]

theorem mulF_inf_inf (a b : Bool) : mulF p emin emax (.inf a) (.inf b) = .inf (xor a b) := rfl

/-- The product of two finite values is their exact product rounded; a zero product has the
exclusive or of the signs. -/
theorem mulF_fin (s t : Signed) :
    mulF p emin emax (.fin s) (.fin t) = roundF p emin emax (s.val * t.val) (xor s.neg t.neg) := rfl

theorem mulF_zero (a b : Bool) (v : ℚ) :
    mulF p emin emax (.fin ⟨0, a⟩) (.fin ⟨v, b⟩) = .fin ⟨0, xor a b⟩ := by
  rw [mulF_fin]; simp only [Rat.zero_mul]; exact roundF_zero _

/-- `Inf + (−Inf)` is NaN. -/
theorem addF_inf_neg (a : Bool) : addF p emin emax (.inf a) (.inf (!a)) = .nan := by
  cases a <;> rfl

theorem addF_inf_inf (a : Bool) : addF p emin emax (.inf a) (.inf a) = .inf a := by
  unfold addF; simp

/-- An infinity absorbs a finite value. -/
theorem addF_inf_fin (a : Bool) (s : Signed) : addF p emin emax (.inf a) (.fin s) = .inf a := rfl

theorem addF_fin_inf (s : Signed) (b : Bool) : addF p emin emax (.fin s) (.inf b) = .inf b := rfl

/-- The sum of two finite values is their exact sum rounded. -/
theorem addF_fin (s t : Signed) :
    addF p emin emax (.fin s) (.fin t) = roundF p emin emax (s.val + t.val) (s.neg && t.neg) := rfl

/-- **`x + (−x) = +0`** under round to nearest. -/
theorem addF_neg_self (x : ℚ) (n : Bool) :
    addF p emin emax (.fin ⟨x, n⟩) (.fin ⟨-x, !n⟩) = .fin ⟨0, false⟩ := by
  rw [addF_fin]; simp only [Rat.add_neg_cancel]
  rw [roundF_zero]; cases n <;> rfl

/-- **`(−0) + (−0) = −0`**, and `(+0) + (−0) = +0`. -/
theorem addF_negZero : addF p emin emax (.fin ⟨0, true⟩) (.fin ⟨0, true⟩) = .fin ⟨0, true⟩ := by
  rw [addF_fin]; simp only [Rat.add_zero]; exact roundF_zero _

theorem addF_posZero_negZero :
    addF p emin emax (.fin ⟨0, false⟩) (.fin ⟨0, true⟩) = .fin ⟨0, false⟩ := by
  rw [addF_fin]; simp only [Rat.add_zero]; exact roundF_zero _

/-- Adding a finite value to `+0` rounds it; on a value of the format it is that value, except
that `(+0) + (−0)` is `+0`. -/
theorem addF_posZero (hp : 0 < p) {s : Signed} (hv : FormatValue p emin emax s.val) :
    addF p emin emax (.fin ⟨0, false⟩) (.fin s) = .fin ⟨s.val, sumNeg s.val false⟩ := by
  rw [addF_fin]; simp only [Rat.zero_add, Bool.false_and]
  exact roundF_of_formatValue hp hv false

/-- IEEE's operations agree with the round to nearest even on finite results. -/
theorem addF_fin_val {s t : Signed} {r : Signed}
    (h : addF p emin emax (.fin s) (.fin t) = .fin r) :
    roundRNE p emin emax (s.val + t.val) = some r.val :=
  ((roundF_eq_fin_iff _ _ _).mp h).1

theorem mulF_fin_val {s t : Signed} {r : Signed}
    (h : mulF p emin emax (.fin s) (.fin t) = .fin r) :
    roundRNE p emin emax (s.val * t.val) = some r.val :=
  ((roundF_eq_fin_iff _ _ _).mp h).1

end Ozaki
