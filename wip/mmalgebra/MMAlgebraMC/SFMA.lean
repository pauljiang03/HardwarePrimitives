import MMAlgebraMC.Contracts
import MMAlgebra.Sub

/-! # Completeness for terms on SFMA

SFMA (binary32 inputs on CDNA 1, 2 and 3) runs blocks of one product, correctly rounded. A binary32
product is exact but can lie below binary32's grid, and then a block from `+0` can return `−0`. On
operand pairs whose product is a multiple of `2^-149` (`SfmaOK`: exponent fields summing to at least
151, or the zero pair) every result is good, and SFMA has the laws of a rigid multiplier
(`sfmaAlg`, on the machine `sfmaM` of these pairs). With fingerprint tables over the normal forms
whose blocks hold one product (3 on two products, 18 on three), two terms over the same products
with different rigid normal forms differ on such an input (`sfma_term_complete`), and two terms are
equivalent on these inputs exactly when their normal forms agree (`sfma_term_equiv_iff`). -/

open MatrixCore Ozaki.MC

namespace MMAlgebra.MC

/-- The exponent field of a binary32 word, at least 1: its value is a multiple of `2^(ex32 w − 150)`. -/
def ex32 (w : F32) : ℕ := max (w.toNat / 8388608 % 256) 1

/-- An SFMA operand pair whose product is a multiple of `2^-149`. -/
def SfmaOK (q : sfmaF32.a.Word × sfmaF32.b.Word) : Prop := q = (0, 0) ∨ 151 ≤ ex32 q.1 + ex32 q.2

instance (q : sfmaF32.a.Word × sfmaF32.b.Word) : Decidable (SfmaOK q) := by
  unfold SfmaOK; infer_instance

/-- The admissible SFMA operand pairs. -/
abbrev SfmaIn : Type := {q : sfmaF32.a.Word × sfmaF32.b.Word // SfmaOK q}

theorem read32_onGrid (w : F32) {u : Unpacked} (h : (fp32.decode w).toFinite = some u) :
    OnGrid u.value ((ex32 w : ℤ) - 150) := by
  have hu := decode32_val w h
  unfold ex32
  by_cases hE : w.toNat / 8388608 % 256 = 0
  · rw [if_pos hE] at hu; subst hu
    rw [hE]
    exact (unpacked_onGrid _).mono (by dsimp only; omega)
  · rw [if_neg hE] at hu; subst hu
    rw [show max (w.toNat / 8388608 % 256) 1 = w.toNat / 8388608 % 256 by omega]
    exact (unpacked_onGrid _).mono (by dsimp only; omega)

theorem sfma_pval_onGrid (q : sfmaF32.a.Word × sfmaF32.b.Word) (hq : SfmaOK q) :
    OnGrid ((mcMachine sfmaF32).pval q) (-149) := by
  rcases hq with rfl | hq
  · have : (mcMachine sfmaF32).pval (0, 0) = 0 := by decide +kernel
    rw [this]; exact OnGrid.zero _
  show OnGrid (sfmaF32.a.wordValue q.1 * sfmaF32.b.wordValue q.2) (-149)
  unfold InputFormat.wordValue
  cases hu : (sfmaF32.a.read q.1).toFinite with
  | none => simp only [Option.map_none, Option.getD_none, Rat.zero_mul]; exact OnGrid.zero _
  | some u =>
    cases hv : (sfmaF32.b.read q.2).toFinite with
    | none => simp only [Option.map_none, Option.getD_none, Rat.mul_zero]; exact OnGrid.zero _
    | some v =>
      simp only [Option.map_some, Option.getD_some]
      have gu := read32_onGrid q.1 hu
      have gv := read32_onGrid q.2 hv
      exact (onGrid_mul gu gv).mono (by omega)

/-- The SFMA machine on admissible operand pairs. -/
abbrev sfmaM : MMAlgebra.Machine SfmaIn F32 := (mcMachine sfmaF32).sub SfmaOK

/-! ## The laws -/

/-- **SFMA blocks on admissible pairs return good words.** -/
theorem sfma_block_good (d : F32) (ps : List (Option SfmaIn)) (o : F32)
    (h : sfmaM.block d ps = some o) : GoodW o := by
  have h' : (blockBits (P := sfmaF32) ⟨(slotPairs sfmaF32 (ps.map (Option.map Subtype.val))).map Prod.fst,
      (slotPairs sfmaF32 (ps.map (Option.map Subtype.val))).map Prod.snd, d⟩).toOption = some o := h
  unfold blockBits at h'
  cases ht : evalBlock (P := sfmaF32) ⟨(slotPairs sfmaF32 (ps.map (Option.map Subtype.val))).map Prod.fst,
      (slotPairs sfmaF32 (ps.map (Option.map Subtype.val))).map Prod.snd, d⟩ with
  | error e => rw [ht] at h'; simp [Except.map, Except.toOption] at h'
  | ok t =>
    rw [ht] at h'
    simp only [Except.map, Except.toOption, Option.some.injEq] at h'
    subst h'
    obtain ⟨_, _, _, ha, hd⟩ := evalBlock_ok ht
    rw [accumulate_correctRounding rfl rfl] at ha
    injection ha with ha
    rw [← ha] at hd
    obtain ⟨L, C, hL, hC, hpr⟩ := evalBlock_pairs ht
    apply fl32_good _ hd
    unfold Prepared.exact
    rw [hpr, products_pairs, sumQ_eq, List.map_map]
    refine OnGrid.add ?_ ?_
    · have hsum : ∀ (qs : List (sfmaF32.a.Word × sfmaF32.b.Word)) (L : List (Unpacked × Unpacked)),
          (∀ q ∈ qs, SfmaOK q) → qs.mapM (decPair sfmaF32) = some L →
          OnGrid (L.map (Unpacked.value ∘ fun q => q.1.mul q.2)).sum (-149) := by
        intro qs
        induction qs with
        | nil =>
          intro L _ h
          simp only [List.mapM_nil, Option.pure_def, Option.some.injEq] at h; subst h
          exact OnGrid.zero _
        | cons q qs ih =>
          intro L hok h
          simp only [List.mapM_cons] at h
          cases hq : decPair sfmaF32 q with
          | none => simp [hq] at h
          | some uv =>
            cases hqs : qs.mapM (decPair sfmaF32) with
            | none => simp [hq, hqs] at h
            | some L' =>
              simp only [hq, hqs, Option.bind_eq_bind, Option.bind_some, Option.pure_def,
                Option.some.injEq] at h
              subst h
              simp only [List.map_cons, List.sum_cons]
              refine OnGrid.add ?_ (ih L' (fun q' hq' => hok q' (by simp [hq'])) hqs)
              obtain ⟨u, v⟩ := uv
              show OnGrid (u.mul v).value (-149)
              rw [← pval_decPair hq]
              exact sfma_pval_onGrid q (hok q (by simp))
      apply hsum _ L _ hL
      intro q hq
      simp only [slotPairs, List.map_map, List.mem_map] at hq
      obtain ⟨o, _, rfl⟩ := hq
      cases o with
      | none => left; rfl
      | some x => exact x.2
    · have hval : value32 d = some C.value := by unfold value32; rw [hC]; rfl
      exact value32_onGrid hval

/-- **An empty SFMA block passes a good accumulator through.** -/
theorem sfma_pass (d : F32) (hd : GoodW d) :
    (mcMachine sfmaF32).block d [none] = some d := by
  obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp hd.1
  obtain ⟨C, hC, rfl⟩ : ∃ C, (fp32.decode d).toFinite = some C ∧ C.value = v := by
    unfold value32 at hv
    cases hc : (fp32.decode d).toFinite with
    | none => rw [hc] at hv; cases hv
    | some C => rw [hc] at hv; exact ⟨C, rfl, Option.some.inj hv⟩
  show (blockBits (P := sfmaF32) ⟨(slotPairs sfmaF32 [none]).map Prod.fst,
    (slotPairs sfmaF32 [none]).map Prod.snd, d⟩).toOption = some d
  have hz : decPair sfmaF32 (0, 0) = some (⟨false, 0, -126, 23⟩, ⟨false, 0, -126, 23⟩) := by
    decide +kernel
  have hslot : slotPairs sfmaF32 [none] = [(0, 0)] := rfl
  have hprep : prepare (P := sfmaF32) ⟨(slotPairs sfmaF32 [none]).map Prod.fst,
      (slotPairs sfmaF32 [none]).map Prod.snd, d⟩ =
      some ⟨[⟨false, 0, -126, 23⟩], [⟨false, 0, -126, 23⟩], C⟩ := by
    rw [hslot, prepare_pairs]
    simp only [List.mapM_cons, List.mapM_nil, hz]
    rw [Option.bind_eq_bind]
    simp only [Option.bind_some, Option.pure_def, hC, Option.map_some]
    rfl
  have hexact : (Prepared.mk [⟨false, 0, -126, 23⟩] [⟨false, 0, -126, 23⟩] C).exact = C.value := by
    rw [Prepared.exact_eq]
    show sumQ [_] + C.value = C.value
    have : sumQ [(0 : ℚ) * 0] = 0 := by decide +kernel
    simp only [Unpacked.value] at this ⊢
    grind
  unfold blockBits evalBlock
  simp only [List.length_map, hslot]
  rw [if_neg (by decide)]
  rw [hslot] at hprep
  rw [hprep]
  simp only
  rw [accumulate_correctRounding rfl rfl, hexact]
  simp only
  have hval : value32 d = some C.value := by unfold value32; rw [hC]; rfl
  rw [show (!sfmaF32.subnormals) = false from rfl, fl32_value_self hval hd.2]
  rfl

/-- The laws of a rigid multiplier for chains on SFMA. -/
def sfmaLaws : MMAlgebra.RigidLaws (mcMachine sfmaF32) 1 where
  z := (0, 0)
  good := GoodW
  slot := fun d ps qs h => by
    show (blockBits (P := sfmaF32) ⟨(slotPairs sfmaF32 ps).map Prod.fst,
      (slotPairs sfmaF32 ps).map Prod.snd, d⟩).toOption =
      (blockBits (P := sfmaF32) ⟨(slotPairs sfmaF32 qs).map Prod.fst,
      (slotPairs sfmaF32 qs).map Prod.snd, d⟩).toOption
    unfold slotPairs; rw [h]
  perm := fun d _ _ h => mc_perm (Or.inl rfl) d h
  zero_good := mc_zero_good
  pass := sfma_pass

/-- The laws of a rigid multiplier on SFMA, on admissible operand pairs. -/
def sfmaAlg : MMAlgebra.RigidAlg sfmaM 1 :=
  MMAlgebra.RigidAlg.sub sfmaLaws SfmaOK (Or.inl rfl) (mc_add_comm sfmaF32) (mc_add_zero sfmaF32)
    sfma_block_good (mc_add_good sfmaF32)

/-! ## Fingerprint tables and theorems -/

/-- An input with the operand pairs of a list at `0, 1, 2, …` and zero pairs elsewhere. -/
def sfmaInput (ws : List SfmaIn) : ℕ → SfmaIn := fun j => ws.getD j ⟨(0, 0), Or.inl rfl⟩

/-- SFMA: an input on two products that separates the three valid normal forms. -/
def sfmaIn2 : List (ℕ → SfmaIn) :=
  [sfmaInput [⟨(0xc13f070a, 0x4060f954), by decide⟩, ⟨(0x4051ce2e, 0x41280000), by decide⟩]]

/-- SFMA: inputs on three products that separate the 18 valid normal forms. -/
def sfmaIn3 : List (ℕ → SfmaIn) :=
  [sfmaInput [⟨(0xbff3222b, 0xbf400000), by decide⟩, ⟨(0xbfffffff, 0xc6079efd), by decide⟩,
     ⟨(0x460ac12e, 0xbfd34a82), by decide⟩],
   sfmaInput [⟨(0xbc62fe15, 0x3f8a01a9), by decide⟩, ⟨(0x3c7fffff, 0x3f0e052c), by decide⟩,
     ⟨(0x3c31f311, 0xbc61f3d3), by decide⟩]]

theorem sfma_table2 : ((MMAlgebra.codes2All.filter fun κ =>
    MMAlgebra.rvalid (MMAlgebra.LTree.realize2 κ 0 1) && MMAlgebra.rfits 1 (MMAlgebra.LTree.realize2 κ 0 1)).map
      fun κ => sfmaIn2.map fun q => MMAlgebra.evR sfmaM 1 q (MMAlgebra.LTree.realize2 κ 0 1)).Nodup := by
  decide +kernel

theorem sfma_table3 : ((MMAlgebra.codes3All.filter fun κ =>
    MMAlgebra.rvalid (κ.realize 0 1 2) && MMAlgebra.rfits 1 (κ.realize 0 1 2)).map
      fun κ => sfmaIn3.map fun q => MMAlgebra.evR sfmaM 1 q (κ.realize 0 1 2)).Nodup := by
  decide +kernel

/-- **SFMA, completeness for terms.** Two terms with one-slot blocks over the same products, each
once, with different rigid normal forms differ on an input of admissible pairs (products multiples
of `2^-149`) that is zero outside at most three of the products. -/
theorem sfma_term_complete (t₁ t₂ : MMAlgebra.Term) (hw₁ : MMAlgebra.TermWF 1 t₁)
    (hw₂ : MMAlgebra.TermWF 1 t₂) (n₁ : t₁.leaves.Nodup) (n₂ : t₂.leaves.Nodup)
    (hl : ∀ i, i ∈ t₁.leaves ↔ i ∈ t₂.leaves) (hne : MMAlgebra.nfR t₁ ≠ MMAlgebra.nfR t₂) :
    ∃ (s : List ℕ) (q : ℕ → sfmaF32.a.Word × sfmaF32.b.Word), s.length ≤ 3 ∧
      (∀ i, i ∉ s → q i = (0, 0)) ∧ (∀ i, SfmaOK (q i)) ∧
      MMAlgebra.eval (mcMachine sfmaF32) q 0 0 t₁ ≠ MMAlgebra.eval (mcMachine sfmaF32) q 0 0 t₂ := by
  obtain ⟨s, q, hs, hz, hq⟩ := MMAlgebra.rigid_term_complete_fits sfmaAlg sfmaIn2 sfmaIn3
    sfma_table2 sfma_table3 t₁ t₂ hw₁ hw₂ n₁ n₂ hl hne
  refine ⟨s, fun i => (q i).1, hs, fun i hi => by show (q i).1 = (0, 0); rw [hz i hi]; rfl, fun i => (q i).2, ?_⟩
  rw [← MMAlgebra.eval_sub, ← MMAlgebra.eval_sub]
  exact hq

/-- **SFMA: on admissible inputs, terms are equivalent exactly when their normal forms agree.** -/
theorem sfma_term_equiv_iff (t₁ t₂ : MMAlgebra.Term) (hw₁ : MMAlgebra.TermWF 1 t₁)
    (hw₂ : MMAlgebra.TermWF 1 t₂) (n₁ : t₁.leaves.Nodup) (n₂ : t₂.leaves.Nodup)
    (hl : ∀ i, i ∈ t₁.leaves ↔ i ∈ t₂.leaves) :
    (∀ q : ℕ → sfmaF32.a.Word × sfmaF32.b.Word, (∀ i, SfmaOK (q i)) →
      MMAlgebra.eval (mcMachine sfmaF32) q 0 0 t₁ = MMAlgebra.eval (mcMachine sfmaF32) q 0 0 t₂) ↔
      MMAlgebra.nfR t₁ = MMAlgebra.nfR t₂ := by
  constructor
  · intro h
    apply Classical.byContradiction; intro hne
    obtain ⟨_, q, _, _, hok, hq⟩ := sfma_term_complete t₁ t₂ hw₁ hw₂ n₁ n₂ hl hne
    exact hq (h q hok)
  · intro h q hok
    have e₁ := MMAlgebra.rigid_sound sfmaAlg (fun i => ⟨q i, hok i⟩) t₁ hw₁ n₁
    have e₂ := MMAlgebra.rigid_sound sfmaAlg (fun i => ⟨q i, hok i⟩) t₂ hw₂ n₂
    rw [h] at e₁
    have := e₁.trans e₂.symm
    rw [MMAlgebra.eval_sub, MMAlgebra.eval_sub] at this
    exact this

end MMAlgebra.MC
