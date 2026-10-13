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

/-! ## Leaves -/

/-- The product indices of a term, in order, with repetitions. -/
def Term.leaves : Term → List ℕ
  | .zero => []
  | .init => []
  | .hole => []
  | .blk t I => t.leaves ++ I.filterMap id
  | .add t u => t.leaves ++ u.leaves

/-- A term without holes whose blocks all have `K` slots. -/
def TermWF (K : ℕ) : Term → Prop
  | .zero => True
  | .init => True
  | .hole => False
  | .blk t I => TermWF K t ∧ I.length = K
  | .add t u => TermWF K t ∧ TermWF K u

/-- A term without holes. -/
def Term.NoHole : Term → Prop
  | .zero => True
  | .init => True
  | .hole => False
  | .blk t _ => t.NoHole
  | .add t u => t.NoHole ∧ u.NoHole

theorem TermWF.noHole {K : ℕ} : ∀ {t : Term}, TermWF K t → t.NoHole
  | .zero, _ => trivial
  | .init, _ => trivial
  | .hole, h => h
  | .blk t _, h => by
    show t.NoHole
    exact TermWF.noHole h.1
  | .add t u, h => by
    show t.NoHole ∧ u.NoHole
    exact ⟨TermWF.noHole h.1, TermWF.noHole h.2⟩

theorem slotVal_eq_leaves (p : ℕ → α) :
    ∀ I : List (Option ℕ), m.slotVal (I.map (Option.map p)) = ((I.filterMap id).map (m.pval ∘ p)).sum
  | [] => by simp [Machine.slotVal]
  | o :: I => by
    rw [List.map_cons, m.slotVal_cons, slotVal_eq_leaves p I]
    cases o <;> simp [Rat.zero_add]

theorem slotAbs_eq_leaves (p : ℕ → α) :
    ∀ I : List (Option ℕ),
      m.slotAbs (I.map (Option.map p)) = ((I.filterMap id).map fun i => Rat.abs (m.pval (p i))).sum
  | [] => by simp [Machine.slotAbs]
  | o :: I => by
    rw [List.map_cons, m.slotAbs_cons, slotAbs_eq_leaves p I]
    cases o <;> simp [Rat.zero_add]

/-- With `c = 0`, the exact value of a term without holes is the sum of its products. -/
theorem exact_eq_leaves (p : ℕ → α) (vh : ℚ) :
    ∀ t : Term, t.NoHole → exact m p 0 vh t = (t.leaves.map (m.pval ∘ p)).sum
  | .zero, _ => by simp [exact, Term.leaves]
  | .init, _ => by simp [exact, Term.leaves]
  | .hole, h => absurd h (by simp [Term.NoHole])
  | .blk t I, h => by
    simp only [exact, Term.leaves, List.map_append, List.sum_append, exact_eq_leaves p vh t h,
      slotVal_eq_leaves]
  | .add t u, h => by
    simp only [exact, Term.leaves, List.map_append, List.sum_append, exact_eq_leaves p vh t h.1,
      exact_eq_leaves p vh u h.2]

/-- With `c = 0`, the magnitude of a term without holes is the sum of its products' magnitudes. -/
theorem mag_eq_leaves (p : ℕ → α) (ah : ℚ) :
    ∀ t : Term, t.NoHole → mag m p 0 ah t = (t.leaves.map fun i => Rat.abs (m.pval (p i))).sum
  | .zero, _ => by simp [mag, Term.leaves]
  | .init, _ => by simp [mag, Term.leaves]
  | .hole, h => absurd h (by simp [Term.NoHole])
  | .blk t I, h => by
    simp only [mag, Term.leaves, List.map_append, List.sum_append, mag_eq_leaves p ah t h,
      slotAbs_eq_leaves]
  | .add t u, h => by
    simp only [mag, Term.leaves, List.map_append, List.sum_append, mag_eq_leaves p ah t h.1,
      mag_eq_leaves p ah u h.2]

/-! ## Positive and negative parts -/

/-- The positive part of a value. -/
def posPart (x : ℚ) : ℚ := if 0 ≤ x then x else 0

/-- The magnitude of the negative part of a value. -/
def negPart (x : ℚ) : ℚ := if 0 ≤ x then 0 else -x

theorem posPart_nonneg (x : ℚ) : 0 ≤ posPart x := by unfold posPart; split <;> grind
theorem negPart_nonneg (x : ℚ) : 0 ≤ negPart x := by unfold negPart; split <;> grind
theorem le_posPart (x : ℚ) : x ≤ posPart x := by unfold posPart; split <;> grind
theorem neg_negPart_le (x : ℚ) : -negPart x ≤ x := by unfold negPart; split <;> grind

/-- The total of the positive products in a list of slots. -/
def Machine.slotPos (ps : List (Option α)) : ℚ := (ps.map fun o => posPart ((o.map m.pval).getD 0)).sum

/-- The total magnitude of the negative products in a list of slots. -/
def Machine.slotNeg (ps : List (Option α)) : ℚ := (ps.map fun o => negPart ((o.map m.pval).getD 0)).sum

theorem Machine.slotPos_nonneg (ps : List (Option α)) : 0 ≤ m.slotPos ps := by
  induction ps with
  | nil => simp [Machine.slotPos]
  | cons o ps ih =>
    have := posPart_nonneg ((o.map m.pval).getD 0)
    simp only [Machine.slotPos, List.map_cons, List.sum_cons] at ih ⊢; grind

theorem Machine.slotNeg_nonneg (ps : List (Option α)) : 0 ≤ m.slotNeg ps := by
  induction ps with
  | nil => simp [Machine.slotNeg]
  | cons o ps ih =>
    have := negPart_nonneg ((o.map m.pval).getD 0)
    simp only [Machine.slotNeg, List.map_cons, List.sum_cons] at ih ⊢; grind

theorem Machine.slotVal_bounds (ps : List (Option α)) :
    -m.slotNeg ps ≤ m.slotVal ps ∧ m.slotVal ps ≤ m.slotPos ps := by
  induction ps with
  | nil => simp [Machine.slotNeg, Machine.slotPos, Machine.slotVal]
  | cons o ps ih =>
    have h1 := le_posPart ((o.map m.pval).getD 0)
    have h2 := neg_negPart_le ((o.map m.pval).getD 0)
    simp only [Machine.slotNeg, Machine.slotPos, Machine.slotVal, List.map_cons, List.sum_cons]
      at ih ⊢
    constructor <;> grind

/-- The total of the positive inputs of a term: its positive products, and `c` or the hole if
positive. -/
def posMag (p : ℕ → α) (vc vh : ℚ) : Term → ℚ
  | .zero => 0
  | .init => posPart vc
  | .hole => posPart vh
  | .blk t I => posMag p vc vh t + m.slotPos (I.map (Option.map p))
  | .add t u => posMag p vc vh t + posMag p vc vh u

/-- The total magnitude of the negative inputs of a term. -/
def negMag (p : ℕ → α) (vc vh : ℚ) : Term → ℚ
  | .zero => 0
  | .init => negPart vc
  | .hole => negPart vh
  | .blk t I => negMag p vc vh t + m.slotNeg (I.map (Option.map p))
  | .add t u => negMag p vc vh t + negMag p vc vh u

theorem posMag_nonneg (p : ℕ → α) (vc vh : ℚ) : ∀ t : Term, 0 ≤ posMag m p vc vh t
  | .zero => by simp [posMag]
  | .init => posPart_nonneg vc
  | .hole => posPart_nonneg vh
  | .blk t I => by
    have := posMag_nonneg p vc vh t; have := m.slotPos_nonneg (I.map (Option.map p))
    simp only [posMag]; grind
  | .add t u => by
    have := posMag_nonneg p vc vh t; have := posMag_nonneg p vc vh u
    simp only [posMag]; grind

theorem negMag_nonneg (p : ℕ → α) (vc vh : ℚ) : ∀ t : Term, 0 ≤ negMag m p vc vh t
  | .zero => by simp [negMag]
  | .init => negPart_nonneg vc
  | .hole => negPart_nonneg vh
  | .blk t I => by
    have := negMag_nonneg p vc vh t; have := m.slotNeg_nonneg (I.map (Option.map p))
    simp only [negMag]; grind
  | .add t u => by
    have := negMag_nonneg p vc vh t; have := negMag_nonneg p vc vh u
    simp only [negMag]; grind

/-- The exact value of a term lies between minus its negative total and its positive total. -/
theorem exact_bounds (p : ℕ → α) (vc vh : ℚ) :
    ∀ t : Term, -negMag m p vc vh t ≤ exact m p vc vh t ∧ exact m p vc vh t ≤ posMag m p vc vh t
  | .zero => by simp [exact, negMag, posMag]
  | .init => by simp only [exact, negMag, posMag]; exact ⟨neg_negPart_le vc, le_posPart vc⟩
  | .hole => by simp only [exact, negMag, posMag]; exact ⟨neg_negPart_le vh, le_posPart vh⟩
  | .blk t I => by
    have := exact_bounds p vc vh t; have := m.slotVal_bounds (I.map (Option.map p))
    simp only [exact, negMag, posMag]; constructor <;> grind
  | .add t u => by
    have := exact_bounds p vc vh t; have := exact_bounds p vc vh u
    simp only [exact, negMag, posMag]; constructor <;> grind

end MMAlgebra
