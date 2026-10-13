import MMAlgebraTC.Block

/-! # Chains of block FMAs and restriction to a support

A chain schedule for one output entry is a list of block FMAs, each a list of slots that hold a
product index or nothing (a zero pair), run from an accumulator `c`; each block's output word is
the next block's `c`. `chain_restrict` is the restriction law: on an input whose products outside a
set `S` are zero, a chain gives the output of the chain whose slots outside `S` are emptied. -/

open TensorCore

namespace MMAlgebra.TC

/-! ## Schedules and restriction to a support -/

/-- A chain schedule: blocks of slots, each slot a product index or empty. -/
abbrev Sched := List (List (Option ℕ))

def slotPair {p : Model} (a b : ℕ → p.Word) : Option ℕ → p.Word × p.Word
  | none => (0, 0)
  | some i => (a i, b i)

/-- Output of a chain of blocks from `c`. -/
def chainOut (p : Model) (a b : ℕ → p.Word) : F32 → Sched → Except ModelError F32
  | c, [] => .ok c
  | c, B :: σ => match blockOut (p := p) ⟨B.map (slotPair a b), c⟩ with
    | .error e => .error e
    | .ok d => chainOut p a b d σ

/-- Products outside `S` set to zero (through `a`). -/
def mask {p : Model} (S : ℕ → Bool) (a : ℕ → p.Word) : ℕ → p.Word :=
  fun i => if S i then a i else 0

/-- Empty every slot outside `S`. -/
def restrict (S : ℕ → Bool) (σ : Sched) : Sched :=
  σ.map (List.map (fun o => o.filter S))

/-- **Restriction.** On an input whose products outside `S` are zero, a chain gives the output of
the chain restricted to `S` (on any input agreeing on `S`). Needs the zero word to decode with
significand zero and every `b` word to be finite. -/
theorem chain_restrict (p : Model) (S : ℕ → Bool) (a b : ℕ → p.Word)
    (hz : ∃ z : Decoded, p.decode 0 = some z ∧ z.significand = 0)
    (hb : ∀ i, (p.decode (b i)).isSome) (c : F32) (σ : Sched) :
    chainOut p (mask S a) b c σ = chainOut p a b c (restrict S σ) := by
  obtain ⟨z, hz0, hzs⟩ := hz
  have hzero : ∀ i, ZeroPair p ((0 : p.Word), b i) := by
    intro i
    obtain ⟨db, hdb⟩ := Option.isSome_iff_exists.mp (hb i)
    exact ⟨z, db, hz0, hdb, by simp [hzs]⟩
  have hzz : ZeroPair p ((0 : p.Word), (0 : p.Word)) := ⟨z, z, hz0, hz0, by simp [hzs]⟩
  induction σ generalizing c with
  | nil => rfl
  | cons B σ ih =>
    have hblk : blockOut (p := p) ⟨B.map (slotPair (mask S a) b), c⟩ =
        blockOut (p := p) ⟨(B.map (fun o => o.filter S)).map (slotPair a b), c⟩ := by
      apply evalBlock_bits_zero
      rw [List.map_map]
      apply Rel2.same
      intro o
      cases o with
      | none => exact Or.inl rfl
      | some i =>
        by_cases hi : S i = true
        · left; simp [slotPair, mask, hi, Option.filter]
        · right
          have hi' : S i = false := by simpa using hi
          simp only [Function.comp, slotPair, mask, hi', Option.filter]
          exact ⟨hzero i, hzz⟩
    simp only [chainOut, restrict, List.map_cons] at ih ⊢
    rw [hblk]
    cases blockOut (p := p) ⟨(B.map (fun o => o.filter S)).map (slotPair a b), c⟩ with
    | error e => rfl
    | ok d => exact ih d

end MMAlgebra.TC
