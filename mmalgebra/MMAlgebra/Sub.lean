import MMAlgebra.Rigid

/-! # Machines on a subset of their inputs

On some formats a block can return `−0` from good inputs (a tiny negative product truncated or
rounded to zero), and then the laws of a rigid multiplier fail for terms. On the inputs whose products
are multiples of the binary32 grid every result is good again. `Machine.sub m P` is the machine `m`
on the inputs satisfying `P`; `eval_sub`: it evaluates terms as `m` does. `RigidAlg.sub`: the laws of
a rigid multiplier for chains on `m`, a commutative addition with `+0` as a unit, and good results
on inputs satisfying `P` give the laws of a rigid multiplier for terms on `m.sub P`.
`agree_of_good`: when a block holding a bad operand pair fails, two terms over the same products
that agree on every input of good pairs agree on every input. Hardware-independent. -/

local notation "ℕ" => Nat

namespace MMAlgebra

variable {α β : Type}

/-- The machine `m` on the inputs satisfying `P`. -/
def Machine.sub (m : Machine α β) (P : α → Prop) : Machine {a // P a} β where
  val := m.val
  pval q := m.pval q.1
  zero := m.zero
  val_zero := m.val_zero
  block d ps := m.block d (ps.map (Option.map Subtype.val))
  add := m.add

theorem eval_sub (m : Machine α β) (P : α → Prop) (p : ℕ → {a // P a}) (c h : β) :
    ∀ t : Term, eval (m.sub P) p c h t = eval m (fun i => (p i).1) c h t
  | .zero => rfl
  | .init => rfl
  | .hole => rfl
  | .blk t I => by
    simp only [eval, eval_sub m P p c h t]
    congr 1; funext d
    show m.block d ((I.map (Option.map p)).map (Option.map Subtype.val)) = _
    rw [List.map_map]
    congr 2; funext o; cases o <;> rfl
  | .add t u => by simp only [eval, eval_sub m P p c h t, eval_sub m P p c h u]; rfl

/-- **The laws of a rigid multiplier on a subset of the inputs.** -/
def RigidAlg.sub {m : Machine α β} {K : ℕ} (L : RigidLaws m K) (P : α → Prop) (hz : P L.z)
    (add_comm : ∀ x y, m.add x y = m.add y x)
    (add_zero : ∀ x, L.good x → m.add x m.zero = some x)
    (block_good : ∀ d (ps : List (Option {a // P a})) o,
      m.block d (ps.map (Option.map Subtype.val)) = some o → L.good o)
    (add_good : ∀ x y o, m.add x y = some o → L.good o) : RigidAlg (m.sub P) K where
  z := ⟨L.z, hz⟩
  good := L.good
  slot := fun d ps qs h => by
    show m.block d (ps.map (Option.map Subtype.val)) = m.block d (qs.map (Option.map Subtype.val))
    apply L.slot
    have e : ∀ rs : List (Option {a // P a}),
        (rs.map (Option.map Subtype.val)).map (·.getD L.z) = (rs.map (·.getD ⟨L.z, hz⟩)).map Subtype.val := by
      intro rs
      rw [List.map_map, List.map_map]
      congr 1; funext o; cases o <;> rfl
    rw [e ps, e qs, h]
  perm := fun d _ _ h => L.perm d (h.map _)
  zero_good := L.zero_good
  pass := fun d hd => by
    show m.block d ((List.replicate K none).map (Option.map Subtype.val)) = some d
    rw [List.map_replicate]
    exact L.pass d hd
  add_comm := add_comm
  add_zero := add_zero
  block_good := block_good
  add_good := add_good

/-! ## From good inputs to all inputs -/

theorem eval_congr (m : Machine α β) {p q : ℕ → α} (c h : β) :
    ∀ t : Term, (∀ i ∈ t.leaves, p i = q i) → eval m p c h t = eval m q c h t
  | .zero, _ => rfl
  | .init, _ => rfl
  | .hole, _ => rfl
  | .blk t I, hpq => by
    have ht := eval_congr m c h t (fun i hi => hpq i (by simp [Term.leaves, hi]))
    have hI : I.map (Option.map p) = I.map (Option.map q) := by
      apply List.map_congr_left
      intro o ho
      cases o with
      | none => rfl
      | some i =>
        have : i ∈ (Term.blk t I).leaves := by
          simp only [Term.leaves, List.mem_append, List.mem_filterMap, id_eq]
          exact Or.inr ⟨some i, ho, rfl⟩
        simp [hpq i this]
    simp only [eval, ht, hI]
  | .add t u, hpq => by
    simp only [eval,
      eval_congr m c h t (fun i hi => hpq i (by simp [Term.leaves, hi])),
      eval_congr m c h u (fun i hi => hpq i (by simp [Term.leaves, hi]))]

/-- A term holding a product whose block fails evaluates to `none`. -/
theorem eval_none_of_bad (m : Machine α β) (bad : α → Prop)
    (hblk : ∀ d (ps : List (Option α)) a, some a ∈ ps → bad a → m.block d ps = none)
    (p : ℕ → α) (c h : β) : ∀ t : Term, ∀ i ∈ t.leaves, bad (p i) → eval m p c h t = none
  | .zero, i, hi, _ => by simp [Term.leaves] at hi
  | .init, i, hi, _ => by simp [Term.leaves] at hi
  | .hole, i, hi, _ => by simp [Term.leaves] at hi
  | .blk t I, i, hi, hb => by
    simp only [Term.leaves, List.mem_append, List.mem_filterMap, id_eq] at hi
    simp only [eval]
    rcases hi with hi | ⟨o, ho, rfl⟩
    · rw [eval_none_of_bad m bad hblk p c h t i hi hb]; rfl
    · cases eval m p c h t with
      | none => rfl
      | some d =>
        exact hblk d _ (p i) (List.mem_map.mpr ⟨some i, ho, rfl⟩) hb
  | .add t u, i, hi, hb => by
    simp only [Term.leaves, List.mem_append] at hi
    simp only [eval]
    rcases hi with hi | hi
    · rw [eval_none_of_bad m bad hblk p c h t i hi hb]; rfl
    · cases eval m p c h t with
      | none => rfl
      | some x => rw [eval_none_of_bad m bad hblk p c h u i hi hb]; rfl

/-- **From good inputs to all inputs.** If a block holding a bad operand pair fails and some pair
is good, two terms over the same products that agree on every input of good pairs agree on every
input. -/
theorem agree_of_good (m : Machine α β) (bad : α → Prop)
    (hblk : ∀ d (ps : List (Option α)) a, some a ∈ ps → bad a → m.block d ps = none)
    (z : α) (hz : ¬ bad z) (c h : β) (t₁ t₂ : Term) (hl : ∀ i, i ∈ t₁.leaves ↔ i ∈ t₂.leaves)
    (hg : ∀ p : ℕ → α, (∀ i, ¬ bad (p i)) → eval m p c h t₁ = eval m p c h t₂) (p : ℕ → α) :
    eval m p c h t₁ = eval m p c h t₂ := by
  by_cases hb : ∃ i ∈ t₁.leaves, bad (p i)
  · obtain ⟨i, hi, hbi⟩ := hb
    rw [eval_none_of_bad m bad hblk p c h t₁ i hi hbi,
      eval_none_of_bad m bad hblk p c h t₂ i ((hl i).mp hi) hbi]
  · have hb' : ∀ i ∈ t₁.leaves, ¬ bad (p i) := fun i hi hbi => hb ⟨i, hi, hbi⟩
    classical
    let p' : ℕ → α := fun i => if bad (p i) then z else p i
    have e₁ : ∀ i ∈ t₁.leaves, p i = p' i := fun i hi => by simp [p', hb' i hi]
    have e₂ : ∀ i ∈ t₂.leaves, p i = p' i := fun i hi => by simp [p', hb' i ((hl i).mpr hi)]
    rw [eval_congr m c h t₁ e₁, eval_congr m c h t₂ e₂]
    apply hg
    intro i
    simp only [p']
    split
    · exact hz
    · assumption

end MMAlgebra
