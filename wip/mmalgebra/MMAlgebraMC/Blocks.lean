import MMAlgebraMC.Words

/-! # Block FMAs on the matrix-core machine

How a block of slots is prepared (`prepare_pairs`: the operand pairs are decoded together), the
multiset law for the correctly rounded and globally aligned models (`mc_perm`: CDNA 1, CDNA 3,
SFMA), and the grid of an fp16 product (`fp16_prod_onGrid`). -/

open MatrixCore Ozaki.MC

namespace MMAlgebra.MC

/-- Decode an operand pair. -/
def decPair (P : Model) (q : P.a.Word × P.b.Word) : Option (Unpacked × Unpacked) :=
  ((P.a.read q.1).toFinite).bind fun u => ((P.b.read q.2).toFinite).map fun v => (u, v)

theorem mapM_pairs {γ : Type} (P : Model) (k : List Unpacked → List Unpacked → Option γ) :
    ∀ qs : List (P.a.Word × P.b.Word),
      ((qs.map Prod.fst).mapM fun w => (P.a.read w).toFinite).bind (fun a =>
        ((qs.map Prod.snd).mapM fun w => (P.b.read w).toFinite).bind (k a)) =
      (qs.mapM (decPair P)).bind fun L => k (L.map Prod.fst) (L.map Prod.snd)
  | [] => rfl
  | q :: qs => by
    simp only [List.map_cons, List.mapM_cons, decPair]
    cases ha : (P.a.read q.1).toFinite with
    | none => simp
    | some u =>
      cases hb : (P.b.read q.2).toFinite with
      | none =>
        simp only [Option.bind_some, Option.map_none]
        cases (qs.map Prod.fst).mapM (fun w => (P.a.read w).toFinite) <;> simp
      | some v =>
        have ih := mapM_pairs P (fun as bs => k (u :: as) (v :: bs)) qs
        simp only [Option.bind_some, Option.map_some]
        simp only [Option.bind_eq_bind, Option.pure_def, Option.bind_assoc, Option.bind_some] at ih ⊢
        simp only [List.map_cons]
        exact ih

/-- **Preparing a block of operand pairs.** -/
theorem prepare_pairs (P : Model) (qs : List (P.a.Word × P.b.Word)) (d : F32) :
    prepare (P := P) ⟨qs.map Prod.fst, qs.map Prod.snd, d⟩ =
      (qs.mapM (decPair P)).bind fun L =>
        ((binary32.decode d).toFinite).map fun C => ⟨L.map Prod.fst, L.map Prod.snd, C⟩ := by
  unfold prepare
  simp only [Option.bind_eq_bind, Option.pure_def]
  refine (mapM_pairs P (fun a b => ((binary32.decode d).toFinite).bind fun c =>
    some (Prepared.mk a b c)) qs).trans ?_
  cases qs.mapM (decPair P) with
  | none => rfl
  | some L => cases (binary32.decode d).toFinite <;> rfl

theorem products_pairs (L : List (Unpacked × Unpacked)) (C : Unpacked) :
    (Prepared.mk (L.map Prod.fst) (L.map Prod.snd) C).p = L.map fun q => q.1.mul q.2 := by
  unfold Prepared.p
  induction L with
  | nil => rfl
  | cons q L ih => simp [ih]

/-- Relation between two optional lists: both fail, or both succeed with permuted results. -/
def PermOptM {γ : Type} : Option (List γ) → Option (List γ) → Prop
  | none, none => True
  | some u, some v => u.Perm v
  | _, _ => False

theorem mapM_permM {γ δ : Type} (f : γ → Option δ) {xs ys : List γ} (h : xs.Perm ys) :
    PermOptM (xs.mapM f) (ys.mapM f) := by
  induction h with
  | nil => simp [PermOptM]
  | @cons x l₁ l₂ _ ih =>
    simp only [List.mapM_cons]
    revert ih
    generalize List.mapM f l₁ = o₁
    generalize List.mapM f l₂ = o₂
    intro ih
    cases hx : f x <;> cases o₁ <;> cases o₂ <;> simp_all [PermOptM]
  | swap x y l =>
    simp only [List.mapM_cons]
    generalize List.mapM f l = o
    cases hx : f x <;> cases hy : f y <;> cases o <;> simp [PermOptM]
    exact List.Perm.swap _ _ _
  | trans _ _ ih₁ ih₂ =>
    revert ih₁ ih₂
    generalize List.mapM f _ = o₁
    generalize List.mapM f _ = o₂
    generalize List.mapM f _ = o₃
    intro h₁ h₂
    cases o₁ <;> cases o₂ <;> cases o₃ <;> simp_all [PermOptM]
    exact h₁.trans h₂

/-- The output word of a block whose prepared operands accumulate to the same value. -/
theorem blockBits_congr {P : Model} {x y : BlockInput P} (hla : x.a.length = y.a.length)
    (hlb : x.b.length = y.b.length)
    (hprep : (prepare x = none ∧ prepare y = none) ∨
      ∃ px py, prepare x = some px ∧ prepare y = some py ∧ accumulate P px = accumulate P py) :
    blockBits x = blockBits y := by
  unfold blockBits evalBlock
  rw [hla, hlb]
  split
  · rfl
  · rcases hprep with ⟨h₁, h₂⟩ | ⟨px, py, h₁, h₂, he⟩
    · rw [h₁, h₂]
    · rw [h₁, h₂]; simp only; rw [he]
      split <;> try rfl
      split <;> rfl

/-- **The multiset law** on the correctly rounded models (CDNA 1, SFMA) and on CDNA 3's global
alignment: a block depends on its slots as a multiset. -/
theorem mc_perm {P : Model}
    (hP : P.accumulation = .correctRounding ∨ P.accumulation = .globalAlignment) (d : F32)
    {ps qs : List (Option (P.a.Word × P.b.Word))} (h : ps.Perm qs) :
    (mcMachine P).block d ps = (mcMachine P).block d qs := by
  show (blockBits (P := P) ⟨(slotPairs P ps).map Prod.fst, (slotPairs P ps).map Prod.snd, d⟩).toOption =
    (blockBits (P := P) ⟨(slotPairs P qs).map Prod.fst, (slotPairs P qs).map Prod.snd, d⟩).toOption
  have hs : (slotPairs P ps).Perm (slotPairs P qs) := h.map _
  congr 1
  apply blockBits_congr (by simp [hs.length_eq]) (by simp [hs.length_eq])
  simp only [prepare_pairs]
  have hm := mapM_permM (decPair P) hs
  cases hx : (slotPairs P ps).mapM (decPair P) with
  | none =>
    cases hy : (slotPairs P qs).mapM (decPair P) with
    | none => left; simp
    | some L₂ => rw [hx, hy] at hm; exact hm.elim
  | some L₁ =>
    cases hy : (slotPairs P qs).mapM (decPair P) with
    | none => rw [hx, hy] at hm; exact hm.elim
    | some L₂ =>
      rw [hx, hy] at hm
      cases hc : (binary32.decode d).toFinite with
      | none => left; simp
      | some C =>
        right
        refine ⟨⟨L₁.map Prod.fst, L₁.map Prod.snd, C⟩, ⟨L₂.map Prod.fst, L₂.map Prod.snd, C⟩,
          by simp, by simp, ?_⟩
        exact accumulate_perm hP (by rw [products_pairs, products_pairs]; exact hm.map _) rfl

/-! ## Grids of fp16 products -/

theorem decodeNat_e {f : Format} {n : ℕ} {u : Unpacked} (h : f.decodeNat n = .finite u) :
    f.emin ≤ u.e ∧ u.t = f.mantissaBits := by
  unfold Format.decodeNat at h
  dsimp only at h
  have key : ∀ (neg : Bool) (E M : ℕ), f.unpackFields neg E M = u →
      f.emin ≤ u.e ∧ u.t = f.mantissaBits := by
    intro neg E M he
    subst he
    unfold Format.unpackFields Format.emin
    split <;> simp <;> omega
  split at h
  · split at h
    · split at h <;> simp at h
    · simp only [Datum.finite.injEq] at h; exact key _ _ _ h
  · split at h
    · simp at h
    · simp only [Datum.finite.injEq] at h; exact key _ _ _ h

theorem unpacked_onGrid (u : Unpacked) : OnGrid u.value (u.e - u.t) := by
  unfold Unpacked.value
  split
  · exact ⟨-(u.m : ℤ), by rw [Rat.intCast_neg, Rat.intCast_natCast]⟩
  · exact ⟨(u.m : ℤ), by rw [Rat.intCast_natCast]⟩

/-- A decoded operand of a packed format is a multiple of `2^(emin − mantissaBits)`. -/
theorem read_onGrid {f : Format} {w : (InputFormat.packed f).Word} {u : Unpacked}
    (h : ((InputFormat.packed f).read w).toFinite = some u) :
    OnGrid u.value (f.emin - f.mantissaBits) := by
  simp only [InputFormat.read, Format.decode] at h
  cases hd : f.decodeNat w.toNat <;> rw [hd] at h <;> simp [Datum.toFinite] at h
  subst h
  obtain ⟨he, ht⟩ := decodeNat_e hd
  exact (unpacked_onGrid _).mono (by rw [ht]; omega)

theorem onGrid_mul {x y : ℚ} {g h : ℤ} (hx : OnGrid x g) (hy : OnGrid y h) : OnGrid (x * y) (g + h) := by
  obtain ⟨a, rfl⟩ := hx
  obtain ⟨b, rfl⟩ := hy
  refine ⟨a * b, ?_⟩
  rw [pow2_add, Rat.intCast_mul]; grind

/-- Rounding down or truncating a multiple of `2^g` to any grid gives a multiple of `2^g`. -/
theorem rdGrid_onGrid' {x : ℚ} {g : ℤ} (hx : OnGrid x g) (e : ℤ) : OnGrid (rdGrid x e) g := by
  by_cases h : g ≤ e
  · exact (rdGrid_onGrid x e).mono h
  · rw [rdGrid_of_onGrid (hx.mono (by omega))]; exact hx

theorem truncGrid_onGrid' {x : ℚ} {g : ℤ} (hx : OnGrid x g) (e : ℤ) : OnGrid (truncGrid x e) g := by
  by_cases h : g ≤ e
  · exact (truncGrid_onGrid x e).mono h
  · rw [truncGrid_of_onGrid (hx.mono (by omega))]; exact hx

end MMAlgebra.MC
