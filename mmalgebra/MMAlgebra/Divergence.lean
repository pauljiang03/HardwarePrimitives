import MMAlgebra.Term

/-! # How far apart two schedules can be

A `Contract` bounds the error of one block FMA and of one binary32 addition, as the per-block
error theorems of the hardware models do. From it, `err` is a structural error bound for any
term: a block's accumulator is a computed value, so its magnitude is bounded by the magnitude of
its subterm plus that subterm's error.

* `eval_error`: a term's output is within `err` of its exact value;
* `divergence`: two terms with the same exact value, on one machine or on two, differ by at most
  the sum of their bounds;
* `divergence_shared`: when both terms contain the same subterm, evaluated on the same machine,
  that subterm counts as an exact leaf with the value it computed, so the bound counts only the
  work after the point where the schedules part. -/

local notation "ℕ" => Nat
local notation "ℚ" => Rat

namespace MMAlgebra

variable {α β : Type} (m : Machine α β)

/-- Error bounds of one block FMA and one addition: a block whose accumulator has magnitude at
most `A` is within `blockErr A ps` of the exact sum of its inputs, and an addition is within
`addRel` times the magnitudes of its operands plus `addAbs` (half the smallest subnormal step). -/
structure Contract where
  blockErr : ℚ → List (Option α) → ℚ
  block_le : ∀ d ps o A, Rat.abs (m.val d) ≤ A → m.block d ps = some o →
    Rat.abs (m.val o - (m.val d + m.slotVal ps)) ≤ blockErr A ps
  addRel : ℚ
  addRel_nonneg : 0 ≤ addRel
  addAbs : ℚ
  add_le : ∀ x y o, m.add x y = some o →
    Rat.abs (m.val o - (m.val x + m.val y)) ≤
      addRel * (Rat.abs (m.val x) + Rat.abs (m.val y)) + addAbs

variable {m}

/-- The structural error bound of a term, with `|c| = ac` and the hole's magnitude `ah` (the hole
itself is exact). -/
def err (K : Contract m) (p : ℕ → α) (ac ah : ℚ) : Term → ℚ
  | .zero => 0
  | .init => 0
  | .hole => 0
  | .blk t I => err K p ac ah t + K.blockErr (mag m p ac ah t + err K p ac ah t) (I.map (Option.map p))
  | .add t u => err K p ac ah t + err K p ac ah u +
      K.addRel * (mag m p ac ah t + err K p ac ah t + mag m p ac ah u + err K p ac ah u) + K.addAbs

/-- **Structural error bound.** A term that evaluates is within `err` of its exact value. -/
theorem eval_error (K : Contract m) (p : ℕ → α) (c h : β) :
    ∀ (t : Term) (o : β), eval m p c h t = some o →
      Rat.abs (m.val o - exact m p (m.val c) (m.val h) t) ≤
        err K p (Rat.abs (m.val c)) (Rat.abs (m.val h)) t
  | .zero, o, he => by
    simp only [eval, Option.some.injEq] at he; subst he
    have e : m.val m.zero - 0 = 0 := by rw [m.val_zero]; grind
    simp only [exact, err, e, Ozaki.abs_zero]; exact Rat.le_refl
  | .init, o, he => by
    simp only [eval, Option.some.injEq] at he; subst he
    have e : m.val c - m.val c = 0 := by grind
    simp only [exact, err, e, Ozaki.abs_zero]; exact Rat.le_refl
  | .hole, o, he => by
    simp only [eval, Option.some.injEq] at he; subst he
    have e : m.val h - m.val h = 0 := by grind
    simp only [exact, err, e, Ozaki.abs_zero]; exact Rat.le_refl
  | .blk t I, o, he => by
    simp only [eval] at he
    cases hd : eval m p c h t with
    | none => rw [hd] at he; simp at he
    | some d =>
      rw [hd] at he; simp only [Option.bind_some] at he
      have ih := eval_error K p c h t d hd
      have hex := abs_exact_le m p (m.val c) (m.val h) t
      have hA : Rat.abs (m.val d) ≤ mag m p (Rat.abs (m.val c)) (Rat.abs (m.val h)) t +
          err K p (Rat.abs (m.val c)) (Rat.abs (m.val h)) t := by
        have := Ozaki.abs_add_le (m.val d - exact m p (m.val c) (m.val h) t)
          (exact m p (m.val c) (m.val h) t)
        have e : m.val d - exact m p (m.val c) (m.val h) t + exact m p (m.val c) (m.val h) t =
          m.val d := by grind
        rw [e] at this; grind
      have hb := K.block_le d _ o _ hA he
      have tri := Ozaki.abs_add_le
        (m.val o - (m.val d + m.slotVal (I.map (Option.map p))))
        (m.val d - exact m p (m.val c) (m.val h) t)
      have e : m.val o - (m.val d + m.slotVal (I.map (Option.map p))) +
          (m.val d - exact m p (m.val c) (m.val h) t) =
          m.val o - exact m p (m.val c) (m.val h) (.blk t I) := by simp only [exact]; grind
      rw [e] at tri
      simp only [err]; grind
  | .add t u, o, he => by
    simp only [eval] at he
    cases hx : eval m p c h t with
    | none => rw [hx] at he; simp at he
    | some x =>
      cases hy : eval m p c h u with
      | none => rw [hx, hy] at he; simp at he
      | some y =>
        rw [hx, hy] at he; simp only [Option.bind_some] at he
        have ihx := eval_error K p c h t x hx
        have ihy := eval_error K p c h u y hy
        have ex := abs_exact_le m p (m.val c) (m.val h) t
        have ey := abs_exact_le m p (m.val c) (m.val h) u
        have hax : Rat.abs (m.val x) ≤ mag m p (Rat.abs (m.val c)) (Rat.abs (m.val h)) t +
            err K p (Rat.abs (m.val c)) (Rat.abs (m.val h)) t := by
          have := Ozaki.abs_add_le (m.val x - exact m p (m.val c) (m.val h) t)
            (exact m p (m.val c) (m.val h) t)
          have e : m.val x - exact m p (m.val c) (m.val h) t + exact m p (m.val c) (m.val h) t =
            m.val x := by grind
          rw [e] at this; grind
        have hay : Rat.abs (m.val y) ≤ mag m p (Rat.abs (m.val c)) (Rat.abs (m.val h)) u +
            err K p (Rat.abs (m.val c)) (Rat.abs (m.val h)) u := by
          have := Ozaki.abs_add_le (m.val y - exact m p (m.val c) (m.val h) u)
            (exact m p (m.val c) (m.val h) u)
          have e : m.val y - exact m p (m.val c) (m.val h) u + exact m p (m.val c) (m.val h) u =
            m.val y := by grind
          rw [e] at this; grind
        have ha := K.add_le x y o he
        have hmul : K.addRel * (Rat.abs (m.val x) + Rat.abs (m.val y)) ≤
            K.addRel * (mag m p (Rat.abs (m.val c)) (Rat.abs (m.val h)) t +
              err K p (Rat.abs (m.val c)) (Rat.abs (m.val h)) t +
              mag m p (Rat.abs (m.val c)) (Rat.abs (m.val h)) u +
              err K p (Rat.abs (m.val c)) (Rat.abs (m.val h)) u) :=
          Rat.mul_le_mul_of_nonneg_left (by grind) K.addRel_nonneg
        have t1 := Ozaki.abs_add_le (m.val o - (m.val x + m.val y))
          (m.val x - exact m p (m.val c) (m.val h) t)
        have t2 := Ozaki.abs_add_le
          (m.val o - (m.val x + m.val y) + (m.val x - exact m p (m.val c) (m.val h) t))
          (m.val y - exact m p (m.val c) (m.val h) u)
        have e : m.val o - (m.val x + m.val y) + (m.val x - exact m p (m.val c) (m.val h) t) +
            (m.val y - exact m p (m.val c) (m.val h) u) =
            m.val o - exact m p (m.val c) (m.val h) (.add t u) := by simp only [exact]; grind
        rw [e] at t2
        simp only [err]; grind

/-- **Divergence bound.** Two terms whose exact values agree (the same products and `c`), on one
machine or on two (the same schedule on two GPUs), differ by at most the sum of their bounds. -/
theorem divergence {α₁ β₁ α₂ β₂ : Type} {m₁ : Machine α₁ β₁} {m₂ : Machine α₂ β₂}
    (K₁ : Contract m₁) (K₂ : Contract m₂) (p₁ : ℕ → α₁) (p₂ : ℕ → α₂) (c₁ h₁ : β₁) (c₂ h₂ : β₂)
    (t₁ t₂ : Term) {o₁ : β₁} {o₂ : β₂}
    (he₁ : eval m₁ p₁ c₁ h₁ t₁ = some o₁) (he₂ : eval m₂ p₂ c₂ h₂ t₂ = some o₂)
    (hex : exact m₁ p₁ (m₁.val c₁) (m₁.val h₁) t₁ = exact m₂ p₂ (m₂.val c₂) (m₂.val h₂) t₂) :
    Rat.abs (m₁.val o₁ - m₂.val o₂) ≤
      err K₁ p₁ (Rat.abs (m₁.val c₁)) (Rat.abs (m₁.val h₁)) t₁ +
        err K₂ p₂ (Rat.abs (m₂.val c₂)) (Rat.abs (m₂.val h₂)) t₂ := by
  have e₁ := eval_error K₁ p₁ c₁ h₁ t₁ o₁ he₁
  have e₂ := eval_error K₂ p₂ c₂ h₂ t₂ o₂ he₂
  rw [Ozaki.abs_sub_comm (m₂.val o₂)] at e₂
  have := Ozaki.abs_add_le (m₁.val o₁ - exact m₁ p₁ (m₁.val c₁) (m₁.val h₁) t₁)
    (exact m₂ p₂ (m₂.val c₂) (m₂.val h₂) t₂ - m₂.val o₂)
  have e : m₁.val o₁ - exact m₁ p₁ (m₁.val c₁) (m₁.val h₁) t₁ +
      (exact m₂ p₂ (m₂.val c₂) (m₂.val h₂) t₂ - m₂.val o₂) = m₁.val o₁ - m₂.val o₂ := by
    rw [hex]; grind
  rw [e] at this; grind

/-- **Shared work does not diverge.** Two terms `r₁` and `r₂` that both contain the subterm `s` in
their holes, on one machine: if `s` evaluates to `w`, the two outputs differ by at most the bounds
of `r₁` and `r₂` with `s` as an exact leaf of value `w`. A shared prefix of a chain, or a shared
partial sum of a split-K, contributes nothing; only the work after the schedules part counts. -/
theorem divergence_shared (K : Contract m) (p : ℕ → α) (c h : β) {s : Term} {w : β}
    (hs : eval m p c h s = some w) (r₁ r₂ : Term) {o₁ o₂ : β}
    (he₁ : eval m p c h (r₁.subst s) = some o₁) (he₂ : eval m p c h (r₂.subst s) = some o₂)
    (hex : exact m p (m.val c) (m.val w) r₁ = exact m p (m.val c) (m.val w) r₂) :
    Rat.abs (m.val o₁ - m.val o₂) ≤
      err K p (Rat.abs (m.val c)) (Rat.abs (m.val w)) r₁ +
        err K p (Rat.abs (m.val c)) (Rat.abs (m.val w)) r₂ := by
  rw [eval_subst m p c h hs] at he₁ he₂
  exact divergence K K p p c w c w r₁ r₂ he₁ he₂ hex

end MMAlgebra
