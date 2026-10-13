import MMAlgebra.Rigid

/-! # Machines on a subset of their inputs

On some formats a block can return `−0` from good inputs (a tiny negative product truncated or
rounded to zero), and then the laws of a rigid multiplier fail for terms. On the inputs whose products
are multiples of the binary32 grid every result is good again. `Machine.sub m P` is the machine `m`
on the inputs satisfying `P`; `eval_sub`: it evaluates terms as `m` does. `RigidAlg.sub`: the laws of
a rigid multiplier for chains on `m`, a commutative addition with `+0` as a unit, and good results
on inputs satisfying `P` give the laws of a rigid multiplier for terms on `m.sub P`. Hardware-
independent. -/

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

end MMAlgebra
