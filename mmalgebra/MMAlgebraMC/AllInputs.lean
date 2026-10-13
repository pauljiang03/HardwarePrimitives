import MMAlgebraMC.PairwiseMC
import MMAlgebra.Sub

/-! # CDNA 1 and CDNA 2 on every input

A matrix-core block holding an operand pair with a non-finite word fails (`mc_block_bad`), so a
term holding such a product evaluates to `none`, and two terms over the same products that agree
on every input of finite operands agree on every input (`MMAlgebra.agree_of_good`). With the
theorems on finite inputs: two terms are equivalent on CDNA 1 fp16 exactly when their correctly
rounded normal forms agree (`cdna1_term_equiv_all`), and on CDNA 2 fp16 exactly when their binary
summation trees agree (`cdna2_term_equiv_all`), over every input; the merge laws of CDNA 1 and the
`c`-split law of CDNA 2 hold on every input. -/

open MatrixCore Ozaki.MC

namespace MMAlgebra.MC

/-- An operand pair with a non-finite word. -/
def BadPair (P : Model) (q : P.a.Word × P.b.Word) : Prop := (decPair P q).isSome = false

theorem mapM_none_of_mem {γ δ : Type} (f : γ → Option δ) :
    ∀ {xs : List γ} {x : γ}, x ∈ xs → f x = none → xs.mapM f = none
  | [], _, hx, _ => by simp at hx
  | y :: ys, x, hx, hf => by
    simp only [List.mapM_cons]
    rcases List.mem_cons.mp hx with rfl | hx
    · simp [hf]
    · cases hy : f y with
      | none => simp
      | some b => simp [mapM_none_of_mem f hx hf]

/-- **A matrix-core block holding a pair with a non-finite word fails.** -/
theorem mc_block_bad (P : Model) (d : F32) (ps : List (Option (P.a.Word × P.b.Word)))
    (a : P.a.Word × P.b.Word) (ha : some a ∈ ps) (hb : BadPair P a) : (mcMachine P).block d ps = none := by
  show (blockBits (P := P) ⟨(slotPairs P ps).map Prod.fst, (slotPairs P ps).map Prod.snd, d⟩).toOption = none
  have hm : (slotPairs P ps).mapM (decPair P) = none := by
    apply mapM_none_of_mem _ (x := a)
    · exact List.mem_map.mpr ⟨some a, ha, rfl⟩
    · unfold BadPair at hb
      cases h : decPair P a with
      | none => rfl
      | some _ => rw [h] at hb; cases hb
  have hp : prepare (P := P) ⟨(slotPairs P ps).map Prod.fst, (slotPairs P ps).map Prod.snd, d⟩ = none := by
    rw [prepare_pairs, hm]; rfl
  unfold blockBits evalBlock
  split
  · rfl
  · rw [hp]; rfl

theorem not_bad_of_finite {P : Model} {q : P.a.Word × P.b.Word}
    (h : ((P.a.read q.1).toFinite).isSome ∧ ((P.b.read q.2).toFinite).isSome) : ¬ BadPair P q := by
  obtain ⟨u, hu⟩ := Option.isSome_iff_exists.mp h.1
  obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp h.2
  unfold BadPair decPair
  simp [hu, hv]

theorem finite_of_not_bad {P : Model} {q : P.a.Word × P.b.Word} (h : ¬ BadPair P q) :
    ((P.a.read q.1).toFinite).isSome ∧ ((P.b.read q.2).toFinite).isSome := by
  unfold BadPair decPair at h
  cases hu : (P.a.read q.1).toFinite with
  | none => rw [hu] at h; simp at h
  | some u =>
    cases hv : (P.b.read q.2).toFinite with
    | none => rw [hu, hv] at h; simp at h
    | some v => simp

/-- Two terms over the same products that agree on every input of finite operands agree on every
input, on every matrix-core model whose zero pair is finite. -/
theorem mc_agree_all (P : Model) (hz : ¬ BadPair P (0, 0)) (t₁ t₂ : MMAlgebra.Term)
    (hl : ∀ i, i ∈ t₁.leaves ↔ i ∈ t₂.leaves)
    (hg : ∀ q, FiniteIn P q → MMAlgebra.eval (mcMachine P) q 0 0 t₁ = MMAlgebra.eval (mcMachine P) q 0 0 t₂)
    (q : ℕ → P.a.Word × P.b.Word) :
    MMAlgebra.eval (mcMachine P) q 0 0 t₁ = MMAlgebra.eval (mcMachine P) q 0 0 t₂ :=
  MMAlgebra.agree_of_good (mcMachine P) (BadPair P) (mc_block_bad P) (0, 0) hz 0 0 t₁ t₂ hl
    (fun p hp => hg p (fun i => finite_of_not_bad (hp i))) q

theorem cdna1_zero_ok : ¬ BadPair cdna1F16 (0, 0) := by unfold BadPair; decide +kernel
theorem cdna2_zero_ok : ¬ BadPair cdna2F16 (0, 0) := by unfold BadPair; decide +kernel

/-- **CDNA 1 (fp16): two terms are equivalent on every input exactly when their correctly rounded
normal forms agree.** -/
theorem cdna1_term_equiv_all (t₁ t₂ : MMAlgebra.Term) (hw₁ : MMAlgebra.TermWF 4 t₁)
    (hw₂ : MMAlgebra.TermWF 4 t₂) (n₁ : t₁.leaves.Nodup) (n₂ : t₂.leaves.Nodup)
    (hl : ∀ i, i ∈ t₁.leaves ↔ i ∈ t₂.leaves) :
    (∀ q, MMAlgebra.eval (mcMachine cdna1F16) q 0 0 t₁ = MMAlgebra.eval (mcMachine cdna1F16) q 0 0 t₂) ↔
      MMAlgebra.nfC t₁ = MMAlgebra.nfC t₂ := by
  rw [← cdna1_term_equiv_iff t₁ t₂ hw₁ hw₂ n₁ n₂ hl]
  exact ⟨fun h q _ => h q, fun h q => mc_agree_all cdna1F16 cdna1_zero_ok t₁ t₂ hl h q⟩

/-- **CDNA 2 (fp16): two terms are equivalent on every input exactly when their binary summation
trees agree.** -/
theorem cdna2_term_equiv_all (t₁ t₂ : MMAlgebra.Term) (hw₁ : MMAlgebra.TermWF 4 t₁)
    (hw₂ : MMAlgebra.TermWF 4 t₂) (n₁ : t₁.leaves.Nodup) (n₂ : t₂.leaves.Nodup)
    (hl : ∀ i, i ∈ t₁.leaves ↔ i ∈ t₂.leaves) :
    (∀ q, MMAlgebra.eval (mcMachine cdna2F16) q 0 0 t₁ = MMAlgebra.eval (mcMachine cdna2F16) q 0 0 t₂) ↔
      MMAlgebra.nfP t₁ = MMAlgebra.nfP t₂ := by
  rw [← cdna2_term_equiv_iff t₁ t₂ hw₁ hw₂ n₁ n₂ hl]
  exact ⟨fun h q _ => h q, fun h q => mc_agree_all cdna2F16 cdna2_zero_ok t₁ t₂ hl h q⟩

/-- **The merge law of CDNA 1 on every input**: `[x] [J] = [x J]`. -/
theorem cdna1_merge_all {x : ℕ} (B₁ B₂ B : List (Option ℕ)) (h₁ : MMAlgebra.blockLeaves B₁ = [x])
    (hB : (MMAlgebra.blockLeaves B).Perm (x :: MMAlgebra.blockLeaves B₂))
    (l₁ : B₁.length = 4) (l₂ : B₂.length = 4) (l : B.length = 4)
    (hn : (x :: MMAlgebra.blockLeaves B₂).Nodup) (q : ℕ → cdna1F16.a.Word × cdna1F16.b.Word) :
    MMAlgebra.eval (mcMachine cdna1F16) q 0 0 (.blk (.blk .zero B₁) B₂) =
      MMAlgebra.eval (mcMachine cdna1F16) q 0 0 (.blk .zero B) := by
  refine mc_agree_all cdna1F16 cdna1_zero_ok _ _ (fun i => ?_)
    (fun q hq => cdna1_merge B₁ B₂ B h₁ hB l₁ l₂ l hn q hq) q
  show i ∈ ([] ++ MMAlgebra.blockLeaves B₁) ++ MMAlgebra.blockLeaves B₂ ↔
    i ∈ [] ++ MMAlgebra.blockLeaves B
  rw [h₁, List.nil_append, List.nil_append, hB.mem_iff]
  rfl

/-- **Two one-product blocks added on CDNA 1, on every input**: `[x] ⊕ [y] = [x y]`. -/
theorem cdna1_add_merge_all {x y : ℕ} (B₁ B₂ B : List (Option ℕ)) (h₁ : MMAlgebra.blockLeaves B₁ = [x])
    (h₂ : MMAlgebra.blockLeaves B₂ = [y]) (hB : (MMAlgebra.blockLeaves B).Perm [x, y])
    (l₁ : B₁.length = 4) (l₂ : B₂.length = 4) (l : B.length = 4) (hxy : x ≠ y)
    (q : ℕ → cdna1F16.a.Word × cdna1F16.b.Word) :
    MMAlgebra.eval (mcMachine cdna1F16) q 0 0 (.add (.blk .zero B₁) (.blk .zero B₂)) =
      MMAlgebra.eval (mcMachine cdna1F16) q 0 0 (.blk .zero B) := by
  refine mc_agree_all cdna1F16 cdna1_zero_ok _ _ (fun i => ?_)
    (fun q hq => cdna1_add_merge B₁ B₂ B h₁ h₂ hB l₁ l₂ l hxy q hq) q
  show i ∈ ([] ++ MMAlgebra.blockLeaves B₁) ++ ([] ++ MMAlgebra.blockLeaves B₂) ↔
    i ∈ [] ++ MMAlgebra.blockLeaves B
  rw [h₁, h₂, List.nil_append, List.nil_append, List.nil_append, hB.mem_iff]
  rfl

/-- **The `c`-split law of CDNA 2 on every input**: `blk(t, I) = t ⊕ blk(0, I)`. -/
theorem cdna2_csplit_all (t : MMAlgebra.Term) (I : List (Option ℕ)) (hw : MMAlgebra.TermWF 4 t)
    (hI : I.length = 4) (hn : (MMAlgebra.Term.blk t I).leaves.Nodup)
    (q : ℕ → cdna2F16.a.Word × cdna2F16.b.Word) :
    MMAlgebra.eval (mcMachine cdna2F16) q 0 0 (.blk t I) =
      MMAlgebra.eval (mcMachine cdna2F16) q 0 0 (.add t (.blk .zero I)) := by
  refine mc_agree_all cdna2F16 cdna2_zero_ok _ _ (fun i => ?_)
    (fun q hq => cdna2_csplit t I hw hI hn q hq) q
  show i ∈ t.leaves ++ MMAlgebra.blockLeaves I ↔ i ∈ t.leaves ++ ([] ++ MMAlgebra.blockLeaves I)
  rw [List.nil_append]

end MMAlgebra.MC
