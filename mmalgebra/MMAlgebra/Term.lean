import Ozaki.Basic

/-! # Reduction terms on any matrix multiplier

A schedule for one output entry of `D = C + AB` is a term built from the zero accumulator, the
initial accumulator `c`, block FMAs and binary32 additions. A `Machine` gives the term a value: a
block function on an accumulator word and a list of slots (a product or a zero pair), and an
addition, both possibly failing (overflow). A `hole` marks where a shared subterm is substituted.

The library uses Lean's rationals directly, like `Ozaki`, so that it can be imported beside either
hardware model; `ℕ` and `ℚ` are local notation. -/

local notation "ℕ" => Nat
local notation "ℚ" => Rat

namespace MMAlgebra

/-- A schedule for one output entry: the zero accumulator, the initial accumulator `c`, a hole
for a shared subterm, one block FMA with an accumulator subterm and a list of slots (product
indices, or `none` for a zero pair), or a binary32 addition. -/
inductive Term where
  | zero
  | init
  | hole
  | blk (t : Term) (slots : List (Option ℕ))
  | add (t u : Term)
  deriving Repr, DecidableEq

/-- Replace every hole of `r` by `s`. -/
def Term.subst : Term → Term → Term
  | .zero, _ => .zero
  | .init, _ => .init
  | .hole, s => s
  | .blk t I, s => .blk (t.subst s) I
  | .add t u, s => .add (t.subst s) (u.subst s)

/-- A matrix multiplier with a binary32 addition: accumulator words `β` with their values, product
operands `α` with the values of their products, the zero word, a block function and an addition. -/
structure Machine (α β : Type) where
  val : β → ℚ
  pval : α → ℚ
  zero : β
  val_zero : val zero = 0
  block : β → List (Option α) → Option β
  add : β → β → Option β

variable {α β : Type} (m : Machine α β)

/-- The exact sum of the products in a list of slots. -/
def Machine.slotVal (ps : List (Option α)) : ℚ := (ps.map fun o => (o.map m.pval).getD 0).sum

/-- The sum of the magnitudes of the products in a list of slots. -/
def Machine.slotAbs (ps : List (Option α)) : ℚ :=
  (ps.map fun o => Rat.abs ((o.map m.pval).getD 0)).sum

/-- The value of a term: `c` and the hole are given words, products come from `p`. -/
def eval (p : ℕ → α) (c h : β) : Term → Option β
  | .zero => some m.zero
  | .init => some c
  | .hole => some h
  | .blk t I => (eval p c h t).bind fun d => m.block d (I.map (Option.map p))
  | .add t u => (eval p c h t).bind fun x => (eval p c h u).bind fun y => m.add x y

/-- The exact value of a term, with values `vc` for `c` and `vh` for the hole. -/
def exact (p : ℕ → α) (vc vh : ℚ) : Term → ℚ
  | .zero => 0
  | .init => vc
  | .hole => vh
  | .blk t I => exact p vc vh t + m.slotVal (I.map (Option.map p))
  | .add t u => exact p vc vh t + exact p vc vh u

/-- The magnitude `Σ|aᵢbᵢ| + |c|` of a term, with `ac` for `|c|` and `ah` for the hole. -/
def mag (p : ℕ → α) (ac ah : ℚ) : Term → ℚ
  | .zero => 0
  | .init => ac
  | .hole => ah
  | .blk t I => mag p ac ah t + m.slotAbs (I.map (Option.map p))
  | .add t u => mag p ac ah t + mag p ac ah u

theorem Machine.slotVal_cons (o : Option α) (ps : List (Option α)) :
    m.slotVal (o :: ps) = (o.map m.pval).getD 0 + m.slotVal ps := by
  simp [Machine.slotVal]

theorem Machine.slotAbs_cons (o : Option α) (ps : List (Option α)) :
    m.slotAbs (o :: ps) = Rat.abs ((o.map m.pval).getD 0) + m.slotAbs ps := by
  simp [Machine.slotAbs]

theorem Machine.abs_slotVal_le (ps : List (Option α)) : Rat.abs (m.slotVal ps) ≤ m.slotAbs ps := by
  induction ps with
  | nil => simp [Machine.slotVal, Machine.slotAbs]
  | cons o ps ih =>
    rw [m.slotVal_cons, m.slotAbs_cons]
    have := Ozaki.abs_add_le ((o.map m.pval).getD 0) (m.slotVal ps)
    grind

theorem Machine.slotAbs_nonneg (ps : List (Option α)) : 0 ≤ m.slotAbs ps := by
  induction ps with
  | nil => simp [Machine.slotAbs]
  | cons o ps ih =>
    rw [m.slotAbs_cons]
    have := Ozaki.abs_nonneg ((o.map m.pval).getD 0)
    grind

theorem mag_nonneg (p : ℕ → α) {ac ah : ℚ} (hc : 0 ≤ ac) (hh : 0 ≤ ah) :
    ∀ t : Term, 0 ≤ mag m p ac ah t
  | .zero => by simp [mag]
  | .init => by simpa [mag] using hc
  | .hole => by simpa [mag] using hh
  | .blk t I => by
    have := mag_nonneg p hc hh t
    have := m.slotAbs_nonneg (I.map (Option.map p))
    simp only [mag]; grind
  | .add t u => by
    have := mag_nonneg p hc hh t
    have := mag_nonneg p hc hh u
    simp only [mag]; grind

/-- The exact value is at most the magnitude. -/
theorem abs_exact_le (p : ℕ → α) (vc vh : ℚ) :
    ∀ t : Term, Rat.abs (exact m p vc vh t) ≤ mag m p (Rat.abs vc) (Rat.abs vh) t
  | .zero => by simp [exact, mag]
  | .init => by simp [exact, mag]
  | .hole => by simp [exact, mag]
  | .blk t I => by
    have h1 := abs_exact_le p vc vh t
    have h2 := m.abs_slotVal_le (I.map (Option.map p))
    have h3 := Ozaki.abs_add_le (exact m p vc vh t) (m.slotVal (I.map (Option.map p)))
    simp only [exact, mag]; grind
  | .add t u => by
    have h1 := abs_exact_le p vc vh t
    have h2 := abs_exact_le p vc vh u
    have h3 := Ozaki.abs_add_le (exact m p vc vh t) (exact m p vc vh u)
    simp only [exact, mag]; grind

/-- Evaluating a substituted term evaluates the shared subterm once: if `s` evaluates to `o`,
then `r` with `s` in its holes evaluates as `r` with the hole word `o`. -/
theorem eval_subst (p : ℕ → α) (c h : β) {s : Term} {o : β} (hs : eval m p c h s = some o) :
    ∀ r : Term, eval m p c h (r.subst s) = eval m p c o r
  | .zero => rfl
  | .init => rfl
  | .hole => by simpa [Term.subst, eval] using hs
  | .blk t I => by simp only [Term.subst, eval, eval_subst p c h hs t]
  | .add t u => by simp only [Term.subst, eval, eval_subst p c h hs t, eval_subst p c h hs u]

end MMAlgebra
