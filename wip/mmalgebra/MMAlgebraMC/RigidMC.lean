import MMAlgebra.Rigid
import MMAlgebraMC.Blocks

/-! # Completeness for terms on CDNA 3

CDNA 3 fp16 (`global_alignment`) satisfies every law of a rigid multiplier (`cdna3Alg`): a block
depends on its products as a multiset (`mc_perm`), an empty block passes a finite accumulator
other than `−0` through (`cdna3_pass`), and every block result is such a value, because the
accumulated sum of fp16 products and a binary32 `c` is a multiple of `2^-149`
(`alignedAccumulation_onGrid`). With kernel-checked fingerprint tables, two terms are equivalent
on CDNA 3 exactly when their rigid normal forms agree (`cdna3_term_equiv_iff`). -/

open MatrixCore Ozaki.MC

namespace MMAlgebra.MC

theorem mapM_mem {γ δ : Type} (f : γ → Option δ) :
    ∀ {xs : List γ} {ys : List δ}, xs.mapM f = some ys → ∀ y ∈ ys, ∃ x ∈ xs, f x = some y
  | [], ys, h => by
    simp only [List.mapM_nil, Option.pure_def, Option.some.injEq] at h
    subst h; simp
  | x :: xs, ys, h => by
    simp only [List.mapM_cons] at h
    cases hb : f x with
    | none => simp [hb] at h
    | some b =>
      cases hbs : xs.mapM f with
      | none => simp [hb, hbs] at h
      | some bs =>
        simp only [hb, hbs, Option.bind_eq_bind, Option.bind_some, Option.pure_def,
          Option.some.injEq] at h
        subst h
        intro y hy
        rcases List.mem_cons.mp hy with rfl | hy
        · exact ⟨x, by simp, hb⟩
        · obtain ⟨x', hx', h'⟩ := mapM_mem f hbs y hy
          exact ⟨x', by simp [hx'], h'⟩

/-- **The accumulated sum of CDNA 3 is a multiple of `2^-149`** when the products and `c` are. -/
theorem alignedAccumulation_onGrid {P : Model} (hP : P.accumulation = .globalAlignment)
    {x : Prepared} (hp : ∀ p ∈ x.p, OnGrid p.value (-149)) (hc : OnGrid x.c.value (-149)) :
    OnGrid (alignedAccumulation P x) (-149) := by
  have hps : OnGrid (productSum P x.p).2 (-149) := by
    unfold productSum; rw [hP]; simp only
    unfold alignedSum
    split
    · exact OnGrid.zero _
    · simp only
      apply onGrid_sumQ
      intro y hy
      obtain ⟨p, hpm, rfl⟩ := List.mem_map.mp hy
      exact truncGrid_onGrid' (hp p hpm) _
  unfold alignedAccumulation lateSum
  simp only
  split
  · exact hps
  · split
    · split
      · apply OnGrid.add hps
        unfold shiftedC
        split
        · split
          · exact OnGrid.zero _
          · exact rdGrid_onGrid' hc _
        · exact rdGrid_onGrid' hc _
      · unfold shiftedSum normalizeRD
        split
        · exact OnGrid.zero _
        · exact rdGrid_onGrid' (OnGrid.add (rdGrid_onGrid' hps _) hc) _
    · unfold shiftedSum normalizeRD
      split
      · exact OnGrid.zero _
      · exact rdGrid_onGrid' (OnGrid.add (rdGrid_onGrid' hps _) hc) _

/-- Prepared operands of a block on fp16 words: the products are multiples of `2^-48` and `c` a
binary32 value. -/
theorem fp16_prepared {P : Model} (ha : P.a = .packed fp16) (hb : P.b = .packed fp16)
    {qs : List (P.a.Word × P.b.Word)} {d : F32} {px : Prepared}
    (h : prepare (P := P) ⟨qs.map Prod.fst, qs.map Prod.snd, d⟩ = some px) :
    (∀ p ∈ px.p, OnGrid p.value (-149)) ∧ OnGrid px.c.value (-149) := by
  rw [prepare_pairs] at h
  cases hL : qs.mapM (decPair P) with
  | none => rw [hL] at h; cases h
  | some L =>
    rw [hL] at h
    cases hC : (fp32.decode d).toFinite with
    | none => rw [hC] at h; cases h
    | some C =>
      rw [hC] at h
      simp only [Option.bind_some, Option.map_some, Option.some.injEq] at h
      subst h
      refine ⟨?_, ?_⟩
      · rw [products_pairs]
        intro p hp
        obtain ⟨⟨u, v⟩, huv, rfl⟩ := List.mem_map.mp hp
        obtain ⟨q, _, hq⟩ := mapM_mem _ hL _ huv
        simp only [decPair] at hq
        cases hu : (P.a.read q.1).toFinite with
        | none => rw [hu] at hq; cases hq
        | some u' =>
          cases hv : (P.b.read q.2).toFinite with
          | none => rw [hu, hv] at hq; cases hq
          | some v' =>
            rw [hu, hv] at hq
            simp only [Option.bind_some, Option.map_some, Option.some.injEq, Prod.mk.injEq] at hq
            obtain ⟨rfl, rfl⟩ := hq
            have gu : OnGrid u'.value (-24) := by
              revert hu; generalize q.1 = w; revert w; rw [ha]; intro w hu
              exact read_onGrid hu
            have gv : OnGrid v'.value (-24) := by
              revert hv; generalize q.2 = w; revert w; rw [hb]; intro w hv
              exact read_onGrid hv
            simp only
            rw [Unpacked.value_mul]
            exact (onGrid_mul gu gv).mono (by omega)
      · have : value32 d = some C.value := by unfold value32; rw [hC]; rfl
        exact value32_onGrid this

/-- **CDNA 3 block results are good**: finite, and never `−0`. -/
theorem cdna3_block_good (d : F32) (ps : List (Option (cdna3F16.a.Word × cdna3F16.b.Word))) (o : F32)
    (h : (mcMachine cdna3F16).block d ps = some o) : GoodW o := by
  have h' : (blockBits (P := cdna3F16) ⟨(slotPairs cdna3F16 ps).map Prod.fst,
      (slotPairs cdna3F16 ps).map Prod.snd, d⟩).toOption = some o := h
  unfold blockBits at h'
  cases ht : evalBlock (P := cdna3F16) ⟨(slotPairs cdna3F16 ps).map Prod.fst,
      (slotPairs cdna3F16 ps).map Prod.snd, d⟩ with
  | error e => rw [ht] at h'; simp [Except.map, Except.toOption] at h'
  | ok t =>
    rw [ht] at h'
    simp only [Except.map, Except.toOption, Option.some.injEq] at h'
    subst h'
    obtain ⟨_, _, hp, ha, hd⟩ := evalBlock_ok ht
    obtain ⟨g₁, g₂⟩ := fp16_prepared rfl rfl hp
    have hs : t.sAcc = alignedAccumulation cdna3F16 t.prepared := by
      unfold accumulate at ha
      split at ha
      · cases ha
      · injection ha with ha; exact ha.symm
    rw [hs] at hd
    exact fl32_good (alignedAccumulation_onGrid rfl g₁ g₂) hd

/-- **An empty CDNA 3 block passes a good accumulator through.** -/
theorem cdna3_pass (d : F32) (hd : GoodW d) :
    (mcMachine cdna3F16).block d (List.replicate 8 none) = some d := by
  obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp hd.1
  obtain ⟨C, hC, rfl⟩ : ∃ C, (fp32.decode d).toFinite = some C ∧ C.value = v := by
    unfold value32 at hv
    cases hc : (fp32.decode d).toFinite with
    | none => rw [hc] at hv; cases hv
    | some C => rw [hc] at hv; exact ⟨C, rfl, Option.some.inj hv⟩
  show (blockBits (P := cdna3F16) ⟨(slotPairs cdna3F16 (List.replicate 8 none)).map Prod.fst,
    (slotPairs cdna3F16 (List.replicate 8 none)).map Prod.snd, d⟩).toOption = some d
  have hz : decPair cdna3F16 (0, 0) = some (⟨false, 0, -14, 10⟩, ⟨false, 0, -14, 10⟩) := by
    decide +kernel
  have hslot : slotPairs cdna3F16 (List.replicate 8 none) = List.replicate 8 (0, 0) := by
    simp [slotPairs]
  have hL : (List.replicate 8 ((0, 0) : cdna3F16.a.Word × cdna3F16.b.Word)).mapM (decPair cdna3F16) =
      some (List.replicate 8 (⟨false, 0, -14, 10⟩, ⟨false, 0, -14, 10⟩)) := by
    simp only [List.replicate, List.mapM_cons, List.mapM_nil, hz]; rfl
  have hprep : prepare (P := cdna3F16) ⟨(slotPairs cdna3F16 (List.replicate 8 none)).map Prod.fst,
      (slotPairs cdna3F16 (List.replicate 8 none)).map Prod.snd, d⟩ =
      some ⟨List.replicate 8 ⟨false, 0, -14, 10⟩, List.replicate 8 ⟨false, 0, -14, 10⟩, C⟩ := by
    rw [hslot, prepare_pairs, hL, Option.bind_some, hC]; rfl
  have hacc : accumulate cdna3F16
      ⟨List.replicate 8 ⟨false, 0, -14, 10⟩, List.replicate 8 ⟨false, 0, -14, 10⟩, C⟩ =
      .ok (lateSum cdna3F16 none 0 C) := by
    have hov : Prepared.productOverflows
        ⟨List.replicate 8 ⟨false, 0, -14, 10⟩, List.replicate 8 ⟨false, 0, -14, 10⟩, C⟩ = false := by
      show (List.zipWith Unpacked.mul (List.replicate 8 ⟨false, 0, -14, 10⟩)
        (List.replicate 8 ⟨false, 0, -14, 10⟩)).any (fun p => decide (pow2 128 ≤ absQ p.value)) = false
      decide +kernel
    unfold accumulate
    rw [hov]
    rfl
  have hsum : lateSum cdna3F16 none 0 C = C.value := by
    have hl : ∀ eC, cExp cdna3F16 C = some eC →
        lateSum cdna3F16 none 0 C = normalizeRD 31 (rdMantissa 0 eC 32 + C.value) := by
      intro eC he; unfold lateSum; rw [he]; rfl
    obtain ⟨eC, he⟩ : ∃ eC, cExp cdna3F16 C = some eC := by
      unfold cExp; split
      · exact ⟨-126, rfl⟩
      · exact ⟨_, rfl⟩
    rw [hl eC he, show rdMantissa (0 : ℚ) eC 32 = 0 from rdGrid_zero _, Rat.zero_add]
    unfold normalizeRD
    split
    · rename_i h; rw [h]
    · rename_i hne
      show rdGrid C.value (normExp (absQ C.value) - ((31 : ℕ) : ℤ)) = C.value
      apply rdGrid_of_onGrid
      have hval : value32 d = some C.value := by unfold value32; rw [hC]; rfl
      obtain ⟨k, e, h1, h2, h3, he⟩ := value32_finiteValue hval
      have hpos := absQ_pos hne
      obtain ⟨hb1, hb2, hb3⟩ := normExp_bounds hpos
      have hle : normExp (absQ C.value) ≤ e := by
        apply Classical.byContradiction; intro hlt
        have hne' : normExp (absQ C.value) ≠ -126 := by omega
        have hlo := hb2 hne'
        have hk : absQ (k : ℚ) < 16777216 := by
          rw [absQ_intCast]; exact_mod_cast (show k.natAbs < 16777216 from h3)
        have hp := pow2_pos (e - 23)
        have hup : absQ C.value < 16777216 * pow2 (e - 23) := by
          rw [he, absQ_mul_pos _ _ hp]
          exact Rat.mul_lt_mul_of_pos_right hk hp
        have e24 : (16777216 : ℚ) * pow2 (e - 23) = pow2 (e + 1) := by
          rw [show e + 1 = 24 + (e - 23) by omega, pow2_add]; rfl
        have hmono : pow2 (e + 1) ≤ pow2 (normExp (absQ C.value)) := pow2_le_of_le (by omega)
        grind
      rw [he] at hle ⊢
      exact onGrid_intCast_mul k (e - 23) _ (by omega)
  unfold blockBits evalBlock
  simp only [List.length_map, List.length_replicate, hslot]
  rw [if_neg (by decide)]
  rw [hslot] at hprep
  rw [hprep]
  simp only
  rw [hacc, hsum]
  simp only
  have hval : value32 d = some C.value := by unfold value32; rw [hC]; rfl
  rw [show (!cdna3F16.subnormals) = false from rfl, fl32_value_self hval hd.2]
  rfl

/-- The laws of a rigid multiplier, for CDNA 3 fp16. -/
def cdna3Alg : MMAlgebra.RigidAlg (mcMachine cdna3F16) 8 where
  z := (0, 0)
  good := GoodW
  slot := fun d ps qs h => by
    show (blockBits (P := cdna3F16) ⟨(slotPairs cdna3F16 ps).map Prod.fst,
      (slotPairs cdna3F16 ps).map Prod.snd, d⟩).toOption =
      (blockBits (P := cdna3F16) ⟨(slotPairs cdna3F16 qs).map Prod.fst,
      (slotPairs cdna3F16 qs).map Prod.snd, d⟩).toOption
    unfold slotPairs; rw [h]
  perm := fun d _ _ h => mc_perm (Or.inr rfl) d h
  zero_good := mc_zero_good
  pass := cdna3_pass
  add_comm := mc_add_comm _
  add_zero := mc_add_zero _
  block_good := cdna3_block_good
  add_good := mc_add_good _

/-! ## Fingerprint tables and theorems -/

/-- An input with the operand pairs of a list at `0, 1, 2, …` and zero pairs elsewhere. -/
def wordsInput (ws : List (cdna3F16.a.Word × cdna3F16.b.Word)) : ℕ → cdna3F16.a.Word × cdna3F16.b.Word :=
  fun j => ws.getD j (0, 0)

/-- CDNA 3: inputs on two products that separate the four valid normal forms. -/
def cdna3In2 : List (ℕ → cdna3F16.a.Word × cdna3F16.b.Word) :=
  [wordsInput [(0x89d5, 0xad23), (0xb7c6, 0x370e)], wordsInput [(0xc3d8, 0xdfeb), (0x47da, 0x3bf5)]]

/-- CDNA 3: inputs on three products that separate the 28 valid normal forms. -/
def cdna3In3 : List (ℕ → cdna3F16.a.Word × cdna3F16.b.Word) :=
  [wordsInput [(0xecbb, 0x0d73), (0x47eb, 0x06f7), (0xbbd1, 0xbf8f)],
   wordsInput [(0x8549, 0x7a45), (0x91a3, 0xd945), (0x47a3, 0x03d1)],
   wordsInput [(0xb800, 0x0b00), (0x35c1, 0x4d00), (0xf450, 0x6d5f)],
   wordsInput [(0xc3dc, 0x8b5a), (0xfa6e, 0xecf1), (0xc3b6, 0xc3c0)],
   wordsInput [(0x43d6, 0x758f), (0x4383, 0xda9d), (0x3c14, 0x3bcd)],
   wordsInput [(0x20d4, 0x47cc), (0xbbe6, 0xa499), (0x47fd, 0x55b3)],
   wordsInput [(0xdc9e, 0x47a5), (0x7bbc, 0xc8bf), (0xbfba, 0xc3c1)]]

theorem cdna3_table2 : ((MMAlgebra.codes2All.filter fun κ => MMAlgebra.rvalid (MMAlgebra.LTree.realize2 κ 0 1)).map
    fun κ => cdna3In2.map fun q => MMAlgebra.evR (mcMachine cdna3F16) 8 q (MMAlgebra.LTree.realize2 κ 0 1)).Nodup := by
  decide +kernel

theorem cdna3_table3 : ((MMAlgebra.codes3All.filter fun κ => MMAlgebra.rvalid (κ.realize 0 1 2)).map
    fun κ => cdna3In3.map fun q => MMAlgebra.evR (mcMachine cdna3F16) 8 q (κ.realize 0 1 2)).Nodup := by
  decide +kernel

/-- **CDNA 3 (fp16), completeness for terms.** Two terms from `+0` with blocks of 8 slots over
the same products, each once, with different normal forms differ on an input that is zero outside
at most three of the products. -/
theorem cdna3_term_complete (t₁ t₂ : MMAlgebra.Term) (hw₁ : MMAlgebra.TermWF 8 t₁)
    (hw₂ : MMAlgebra.TermWF 8 t₂) (n₁ : t₁.leaves.Nodup) (n₂ : t₂.leaves.Nodup)
    (hl : ∀ i, i ∈ t₁.leaves ↔ i ∈ t₂.leaves) (hne : MMAlgebra.nfR t₁ ≠ MMAlgebra.nfR t₂) :
    ∃ (s : List ℕ) (q : ℕ → cdna3F16.a.Word × cdna3F16.b.Word), s.length ≤ 3 ∧
      (∀ i, i ∉ s → q i = (0, 0)) ∧
      MMAlgebra.eval (mcMachine cdna3F16) q 0 0 t₁ ≠ MMAlgebra.eval (mcMachine cdna3F16) q 0 0 t₂ :=
  MMAlgebra.rigid_term_complete cdna3Alg cdna3In2 cdna3In3 cdna3_table2 cdna3_table3
    t₁ t₂ hw₁ hw₂ n₁ n₂ hl hne

/-- **CDNA 3 (fp16): terms are equivalent exactly when their normal forms agree.** -/
theorem cdna3_term_equiv_iff (t₁ t₂ : MMAlgebra.Term) (hw₁ : MMAlgebra.TermWF 8 t₁)
    (hw₂ : MMAlgebra.TermWF 8 t₂) (n₁ : t₁.leaves.Nodup) (n₂ : t₂.leaves.Nodup)
    (hl : ∀ i, i ∈ t₁.leaves ↔ i ∈ t₂.leaves) :
    (∀ q, MMAlgebra.eval (mcMachine cdna3F16) q 0 0 t₁ = MMAlgebra.eval (mcMachine cdna3F16) q 0 0 t₂) ↔
      MMAlgebra.nfR t₁ = MMAlgebra.nfR t₂ := by
  constructor
  · intro h
    apply Classical.byContradiction; intro hne
    obtain ⟨_, q, _, _, hq⟩ := cdna3_term_complete t₁ t₂ hw₁ hw₂ n₁ n₂ hl hne
    exact hq (h q)
  · intro h q
    have e₁ := MMAlgebra.rigid_sound cdna3Alg q t₁ hw₁ n₁
    have e₂ := MMAlgebra.rigid_sound cdna3Alg q t₂ hw₂ n₂
    rw [h] at e₁
    exact e₁.trans e₂.symm

/-- CDNA 3: the products of `cdna3_pair`; `[x] [y]` and `[x y]` give `0x3d2d1ec2`, `[y] [x]` gives
`0x3d2d1ec3`. -/
def cdna3Witness : MMAlgebra.PairWitness cdna3Alg.toRigidLaws where
  a := (0x02e6, 0x0b09)
  b := (0x37ea, 0x2d78)
  vx := 0x322320b0
  vy := 0x3d2d1ec0
  vxy := 0x3d2d1ec2
  vlt := 0x3d2d1ec2
  vgt := 0x3d2d1ec3
  e₁ := by decide +kernel
  e₂ := by decide +kernel
  e₃ := by decide +kernel
  e₄ := by decide +kernel
  e₅ := by decide +kernel
  g₁ := by show GoodW _; decide
  g₂ := by show GoodW _; decide
  g₃ := by show GoodW _; decide
  g₄ := by show GoodW _; decide
  g₅ := by show GoodW _; decide
  sep := by decide

/-- **CDNA 3 (fp16): chains are equivalent exactly when their ordered partitions agree.** -/
theorem cdna3_chain_equiv_iff (σ τ : MMAlgebra.Chain) (hσ : ∀ B ∈ σ, B.length = 8)
    (hτ : ∀ B ∈ τ, B.length = 8) (nσ : σ.leaves.Nodup) (nτ : τ.leaves.Nodup)
    (hl : ∀ i, i ∈ σ.leaves ↔ i ∈ τ.leaves) :
    (∀ p, MMAlgebra.runChain (mcMachine cdna3F16) p 0 σ =
        MMAlgebra.runChain (mcMachine cdna3F16) p 0 τ) ↔ σ.nf = τ.nf :=
  MMAlgebra.chain_equiv_iff cdna3Alg.toRigidLaws (by decide) cdna3Witness cdna3_block_good
    σ τ hσ hτ nσ nτ hl

end MMAlgebra.MC
