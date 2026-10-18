import MMAlgebraMC.RigidMC
import MMAlgebraMC.Contracts
import MMAlgebra.Sub

/-! # CDNA 3 bf16 and xf32: completeness for chains, and for terms on grid inputs

CDNA 3 bf16 (`N_FMA = 8`) and xf32 (`N_FMA = 4`) use the same global alignment with late `c` as
CDNA 3 fp16, so a block depends on its products as a multiset (`mc_perm`). The missing law was the
pass-through of an empty block (`cdna3BF16_pass`, `cdna3XF32_pass`: with no nonzero product, `c`
is added to an exact zero sum and returned). With kernel-checked base witnesses, completeness for
chains follows from the generic theorem (`cdna3BF16_chain_complete`, `cdna3XF32_chain_complete`).

On operand pairs whose product is a multiple of `2^-149` (`MGridOK`) every CDNA 3 block result is
a finite value other than `−0` (`ga_sub_block_good`: the aligned accumulation of grid products and
a binary32 `c` stays on the grid, as for fp16), so CDNA 3 bf16 and xf32 have the laws of a rigid
multiplier for terms on those inputs. With kernel-checked fingerprint tables, two terms over the
same products are equivalent on those inputs exactly when their rigid normal forms agree
(`cdna3BF16_term_equiv_iff`, `cdna3XF32_term_equiv_iff`). -/

open MatrixCore Ozaki.MC MMAlgebra.MC

namespace MMAlgebra.MC.CDNA3

/-- **An empty CDNA 3 block (cdna3BF16) passes a good accumulator through.** -/
theorem cdna3BF16_pass (d : F32) (hd : GoodW d) :
    (mcMachine cdna3BF16).block d (List.replicate 8 none) = some d := by
  obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp hd.1
  obtain ⟨C, hC, rfl⟩ : ∃ C, (fp32.decode d).toFinite = some C ∧ C.value = v := by
    unfold value32 at hv
    cases hc : (fp32.decode d).toFinite with
    | none => rw [hc] at hv; cases hv
    | some C => rw [hc] at hv; exact ⟨C, rfl, Option.some.inj hv⟩
  show (blockBits (P := cdna3BF16) ⟨(slotPairs cdna3BF16 (List.replicate 8 none)).map Prod.fst,
    (slotPairs cdna3BF16 (List.replicate 8 none)).map Prod.snd, d⟩).toOption = some d
  have hz : decPair cdna3BF16 (0, 0) = some (⟨false, 0, -126, 7⟩, ⟨false, 0, -126, 7⟩) := by
    decide +kernel
  have hslot : slotPairs cdna3BF16 (List.replicate 8 none) = List.replicate 8 (0, 0) := by
    simp [slotPairs]
  have hL : (List.replicate 8 ((0, 0) : cdna3BF16.a.Word × cdna3BF16.b.Word)).mapM (decPair cdna3BF16) =
      some (List.replicate 8 (⟨false, 0, -126, 7⟩, ⟨false, 0, -126, 7⟩)) := by
    simp only [List.replicate, List.mapM_cons, List.mapM_nil, hz]; rfl
  have hprep : prepare (P := cdna3BF16) ⟨(slotPairs cdna3BF16 (List.replicate 8 none)).map Prod.fst,
      (slotPairs cdna3BF16 (List.replicate 8 none)).map Prod.snd, d⟩ =
      some ⟨List.replicate 8 ⟨false, 0, -126, 7⟩, List.replicate 8 ⟨false, 0, -126, 7⟩, C⟩ := by
    rw [hslot, prepare_pairs, hL, Option.bind_some, hC]; rfl
  have hacc : accumulate cdna3BF16
      ⟨List.replicate 8 ⟨false, 0, -126, 7⟩, List.replicate 8 ⟨false, 0, -126, 7⟩, C⟩ =
      .ok (lateSum cdna3BF16 none 0 C) := by
    have hov : Prepared.productOverflows
        ⟨List.replicate 8 ⟨false, 0, -126, 7⟩, List.replicate 8 ⟨false, 0, -126, 7⟩, C⟩ = false := by
      show (List.zipWith Unpacked.mul (List.replicate 8 ⟨false, 0, -126, 7⟩)
        (List.replicate 8 ⟨false, 0, -126, 7⟩)).any (fun p => decide (pow2 128 ≤ absQ p.value)) = false
      decide +kernel
    unfold accumulate
    rw [hov]
    rfl
  have hsum : lateSum cdna3BF16 none 0 C = C.value := by
    have hl : ∀ eC, cExp cdna3BF16 C = some eC →
        lateSum cdna3BF16 none 0 C = normalizeRD 31 (rdMantissa 0 eC 32 + C.value) := by
      intro eC he; unfold lateSum; rw [he]; rfl
    obtain ⟨eC, he⟩ : ∃ eC, cExp cdna3BF16 C = some eC := by
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
  rw [show (!cdna3BF16.subnormals) = false from rfl, fl32_value_self hval hd.2]
  rfl

/-- **An empty CDNA 3 block (cdna3XF32) passes a good accumulator through.** -/
theorem cdna3XF32_pass (d : F32) (hd : GoodW d) :
    (mcMachine cdna3XF32).block d (List.replicate 4 none) = some d := by
  obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp hd.1
  obtain ⟨C, hC, rfl⟩ : ∃ C, (fp32.decode d).toFinite = some C ∧ C.value = v := by
    unfold value32 at hv
    cases hc : (fp32.decode d).toFinite with
    | none => rw [hc] at hv; cases hv
    | some C => rw [hc] at hv; exact ⟨C, rfl, Option.some.inj hv⟩
  show (blockBits (P := cdna3XF32) ⟨(slotPairs cdna3XF32 (List.replicate 4 none)).map Prod.fst,
    (slotPairs cdna3XF32 (List.replicate 4 none)).map Prod.snd, d⟩).toOption = some d
  have hz : decPair cdna3XF32 (0, 0) = some (⟨false, 0, -126, 10⟩, ⟨false, 0, -126, 10⟩) := by
    decide +kernel
  have hslot : slotPairs cdna3XF32 (List.replicate 4 none) = List.replicate 4 (0, 0) := by
    simp [slotPairs]
  have hL : (List.replicate 4 ((0, 0) : cdna3XF32.a.Word × cdna3XF32.b.Word)).mapM (decPair cdna3XF32) =
      some (List.replicate 4 (⟨false, 0, -126, 10⟩, ⟨false, 0, -126, 10⟩)) := by
    simp only [List.replicate, List.mapM_cons, List.mapM_nil, hz]; rfl
  have hprep : prepare (P := cdna3XF32) ⟨(slotPairs cdna3XF32 (List.replicate 4 none)).map Prod.fst,
      (slotPairs cdna3XF32 (List.replicate 4 none)).map Prod.snd, d⟩ =
      some ⟨List.replicate 4 ⟨false, 0, -126, 10⟩, List.replicate 4 ⟨false, 0, -126, 10⟩, C⟩ := by
    rw [hslot, prepare_pairs, hL, Option.bind_some, hC]; rfl
  have hacc : accumulate cdna3XF32
      ⟨List.replicate 4 ⟨false, 0, -126, 10⟩, List.replicate 4 ⟨false, 0, -126, 10⟩, C⟩ =
      .ok (lateSum cdna3XF32 none 0 C) := by
    have hov : Prepared.productOverflows
        ⟨List.replicate 4 ⟨false, 0, -126, 10⟩, List.replicate 4 ⟨false, 0, -126, 10⟩, C⟩ = false := by
      show (List.zipWith Unpacked.mul (List.replicate 4 ⟨false, 0, -126, 10⟩)
        (List.replicate 4 ⟨false, 0, -126, 10⟩)).any (fun p => decide (pow2 128 ≤ absQ p.value)) = false
      decide +kernel
    unfold accumulate
    rw [hov]
    rfl
  have hsum : lateSum cdna3XF32 none 0 C = C.value := by
    have hl : ∀ eC, cExp cdna3XF32 C = some eC →
        lateSum cdna3XF32 none 0 C = normalizeRD 31 (rdMantissa 0 eC 32 + C.value) := by
      intro eC he; unfold lateSum; rw [he]; rfl
    obtain ⟨eC, he⟩ : ∃ eC, cExp cdna3XF32 C = some eC := by
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
  rw [show (!cdna3XF32.subnormals) = false from rfl, fl32_value_self hval hd.2]
  rfl

/-- The laws of a rigid multiplier for chains, for cdna3BF16. -/
def cdna3BF16Laws : MMAlgebra.RigidLaws (mcMachine cdna3BF16) 8 where
  z := (0, 0)
  good := GoodW
  slot := fun d ps qs h => by
    show (blockBits (P := cdna3BF16) ⟨(slotPairs cdna3BF16 ps).map Prod.fst,
      (slotPairs cdna3BF16 ps).map Prod.snd, d⟩).toOption =
      (blockBits (P := cdna3BF16) ⟨(slotPairs cdna3BF16 qs).map Prod.fst,
      (slotPairs cdna3BF16 qs).map Prod.snd, d⟩).toOption
    unfold slotPairs; rw [h]
  perm := fun d _ _ h => mc_perm (Or.inr rfl) d h
  zero_good := mc_zero_good
  pass := cdna3BF16_pass

def cdna3BF16Witness : MMAlgebra.PairWitness cdna3BF16Laws where
  a := (0x3d63, 0xbfee)
  b := (0x334c, 0xbfe4)
  vx := 0xbdd30a00
  vy := 0xb3b5b000
  vxy := 0xbdd30a0b
  vlt := 0xbdd30a0b
  vgt := 0xbdd30a0c
  e₁ := by decide +kernel
  e₂ := by decide +kernel
  e₃ := by decide +kernel
  e₄ := by decide +kernel
  e₅ := by decide +kernel
  g₁ := by show GoodW _; decide +kernel
  g₂ := by show GoodW _; decide +kernel
  g₃ := by show GoodW _; decide +kernel
  g₄ := by show GoodW _; decide +kernel
  g₅ := by show GoodW _; decide +kernel
  sep := by decide

/-- **cdna3BF16, completeness for chains**: two chains from `+0` over the same products, each once,
with different ordered partitions, differ on an input supported on two products. -/
theorem cdna3BF16_chain_complete (σ τ : MMAlgebra.Chain) (hσ : ∀ B ∈ σ, B.length = 8)
    (hτ : ∀ B ∈ τ, B.length = 8) (nσ : σ.leaves.Nodup) (nτ : τ.leaves.Nodup)
    (hl : ∀ i, i ∈ σ.leaves ↔ i ∈ τ.leaves) (hne : σ.nf ≠ τ.nf) :
    ∃ (x y : ℕ) (q : ℕ → cdna3BF16.a.Word × cdna3BF16.b.Word), x ≠ y ∧
      (∀ i, i ≠ x → i ≠ y → q i = (0, 0)) ∧
      MMAlgebra.runChain (mcMachine cdna3BF16) q 0 σ ≠ MMAlgebra.runChain (mcMachine cdna3BF16) q 0 τ :=
  MMAlgebra.chain_complete cdna3BF16Laws (by decide) cdna3BF16Witness σ τ hσ hτ nσ nτ hl hne

/-- The laws of a rigid multiplier for chains, for cdna3XF32. -/
def cdna3XF32Laws : MMAlgebra.RigidLaws (mcMachine cdna3XF32) 4 where
  z := (0, 0)
  good := GoodW
  slot := fun d ps qs h => by
    show (blockBits (P := cdna3XF32) ⟨(slotPairs cdna3XF32 ps).map Prod.fst,
      (slotPairs cdna3XF32 ps).map Prod.snd, d⟩).toOption =
      (blockBits (P := cdna3XF32) ⟨(slotPairs cdna3XF32 qs).map Prod.fst,
      (slotPairs cdna3XF32 qs).map Prod.snd, d⟩).toOption
    unfold slotPairs; rw [h]
  perm := fun d _ _ h => mc_perm (Or.inr rfl) d h
  zero_good := mc_zero_good
  pass := cdna3XF32_pass

def cdna3XF32Witness : MMAlgebra.PairWitness cdna3XF32Laws where
  a := (0x3d63c000, 0xbfeec000)
  b := (0x334c2000, 0xbfe4e000)
  vx := 0xbdd46750
  vy := 0xb3b67f1c
  vxy := 0xbdd4675b
  vlt := 0xbdd4675b
  vgt := 0xbdd4675c
  e₁ := by decide +kernel
  e₂ := by decide +kernel
  e₃ := by decide +kernel
  e₄ := by decide +kernel
  e₅ := by decide +kernel
  g₁ := by show GoodW _; decide +kernel
  g₂ := by show GoodW _; decide +kernel
  g₃ := by show GoodW _; decide +kernel
  g₄ := by show GoodW _; decide +kernel
  g₅ := by show GoodW _; decide +kernel
  sep := by decide

/-- **cdna3XF32, completeness for chains**: two chains from `+0` over the same products, each once,
with different ordered partitions, differ on an input supported on two products. -/
theorem cdna3XF32_chain_complete (σ τ : MMAlgebra.Chain) (hσ : ∀ B ∈ σ, B.length = 4)
    (hτ : ∀ B ∈ τ, B.length = 4) (nσ : σ.leaves.Nodup) (nτ : τ.leaves.Nodup)
    (hl : ∀ i, i ∈ σ.leaves ↔ i ∈ τ.leaves) (hne : σ.nf ≠ τ.nf) :
    ∃ (x y : ℕ) (q : ℕ → cdna3XF32.a.Word × cdna3XF32.b.Word), x ≠ y ∧
      (∀ i, i ≠ x → i ≠ y → q i = (0, 0)) ∧
      MMAlgebra.runChain (mcMachine cdna3XF32) q 0 σ ≠ MMAlgebra.runChain (mcMachine cdna3XF32) q 0 τ :=
  MMAlgebra.chain_complete cdna3XF32Laws (by decide) cdna3XF32Witness σ τ hσ hτ nσ nτ hl hne

/-- An operand pair whose product is a multiple of `2^-149`. -/
def MGridOK (P : Model) (q : P.a.Word × P.b.Word) : Prop := ((mcMachine P).pval q * pow2 149).den = 1

instance (P : Model) (q : P.a.Word × P.b.Word) : Decidable (MGridOK P q) := by
  unfold MGridOK; infer_instance

theorem mgridOK_onGrid {P : Model} {q : P.a.Word × P.b.Word} (h : MGridOK P q) :
    OnGrid ((mcMachine P).pval q) (-149) := by
  refine ⟨((mcMachine P).pval q * pow2 149).num, ?_⟩
  have e : (mcMachine P).pval q * pow2 149 = (((mcMachine P).pval q * pow2 149).num : ℚ) :=
    Rat.ext (by simp) (by rw [Rat.den_intCast]; exact h)
  rw [← e, Rat.mul_assoc, ← pow2_add]
  show _ = _ * pow2 0
  rw [show pow2 0 = 1 by decide +kernel, Rat.mul_one]

theorem mgridOK_zero (P : Model) (h : (mcMachine P).pval (0, 0) = 0) : MGridOK P (0, 0) := by
  unfold MGridOK; rw [h, Rat.zero_mul]; rfl

/-- **On grid operand pairs, global-alignment blocks return good words.** -/
theorem ga_sub_block_good (P : Model) (hP : P.accumulation = .globalAlignment)
    (hsub : P.subnormals = true) (hz0 : (mcMachine P).pval (0, 0) = 0) (d : F32)
    (ps : List (Option {q : P.a.Word × P.b.Word // MGridOK P q})) (o : F32)
    (h : (mcMachine P).block d (ps.map (Option.map Subtype.val)) = some o) : GoodW o := by
  have h' : (blockBits (P := P) ⟨(slotPairs P (ps.map (Option.map Subtype.val))).map Prod.fst,
      (slotPairs P (ps.map (Option.map Subtype.val))).map Prod.snd, d⟩).toOption = some o := h
  unfold blockBits at h'
  cases ht : evalBlock (P := P) ⟨(slotPairs P (ps.map (Option.map Subtype.val))).map Prod.fst,
      (slotPairs P (ps.map (Option.map Subtype.val))).map Prod.snd, d⟩ with
  | error e => rw [ht] at h'; simp [Except.map, Except.toOption] at h'
  | ok t =>
    rw [ht] at h'
    simp only [Except.map, Except.toOption, Option.some.injEq] at h'
    subst h'
    obtain ⟨_, _, _, ha, hd⟩ := evalBlock_ok ht
    obtain ⟨L, C, hL, hC, hpr⟩ := evalBlock_pairs ht
    have hs : t.sAcc = alignedAccumulation P t.prepared := by
      unfold accumulate at ha
      split at ha
      · cases ha
      · rw [hP] at ha; injection ha with ha; exact ha.symm
    rw [hs, hsub] at hd
    apply fl32_good _ hd
    apply alignedAccumulation_onGrid hP
    · rw [hpr, products_pairs]
      intro p hp
      obtain ⟨uv, huv, rfl⟩ := List.mem_map.mp hp
      obtain ⟨q, hq, hdec⟩ := mapM_mem (decPair P) hL uv huv
      obtain ⟨u, v⟩ := uv
      show OnGrid (u.mul v).value (-149)
      rw [← pval_decPair hdec]
      simp only [slotPairs, List.map_map, List.mem_map] at hq
      obtain ⟨o, _, rfl⟩ := hq
      cases o with
      | none =>
        show OnGrid ((mcMachine P).pval (0, 0)) (-149)
        rw [hz0]; exact OnGrid.zero _
      | some x => exact mgridOK_onGrid x.2
    · rw [hpr]
      have hval : value32 d = some C.value := by unfold value32; rw [hC]; rfl
      exact value32_onGrid hval

/-- An input with the operand pairs of a list at `0, 1, 2, …` and zero pairs elsewhere. -/
def mgridInput (P : Model) (hz : MGridOK P (0, 0)) (ws : List {q : P.a.Word × P.b.Word // MGridOK P q}) :
    ℕ → {q : P.a.Word × P.b.Word // MGridOK P q} :=
  fun j => ws.getD j ⟨(0, 0), hz⟩

theorem cdna3BF16_pval0 : (mcMachine cdna3BF16).pval (0, 0) = 0 := by decide +kernel
theorem cdna3XF32_pval0 : (mcMachine cdna3XF32).pval (0, 0) = 0 := by decide +kernel
theorem cdna3BF16_zeroOK : MGridOK cdna3BF16 (0, 0) := mgridOK_zero _ cdna3BF16_pval0
theorem cdna3XF32_zeroOK : MGridOK cdna3XF32 (0, 0) := mgridOK_zero _ cdna3XF32_pval0

def cdna3BF16In2 : List (ℕ → {q : cdna3BF16.a.Word × cdna3BF16.b.Word // MGridOK cdna3BF16 q}) :=
  [mgridInput cdna3BF16 cdna3BF16_zeroOK [⟨(0xbc2a, 0xc0db), by decide +kernel⟩, ⟨(0xc6ea, 0x40a6), by decide +kernel⟩],
   mgridInput cdna3BF16 cdna3BF16_zeroOK [⟨(0x3f09, 0xc0a8), by decide +kernel⟩, ⟨(0xb583, 0xc0b0), by decide +kernel⟩]]

def cdna3BF16In3 : List (ℕ → {q : cdna3BF16.a.Word × cdna3BF16.b.Word // MGridOK cdna3BF16 q}) :=
  [mgridInput cdna3BF16 cdna3BF16_zeroOK [⟨(0x3136, 0x40f3), by decide +kernel⟩, ⟨(0xbdf8, 0x3f50), by decide +kernel⟩, ⟨(0x3ca8, 0x416a), by decide +kernel⟩],
   mgridInput cdna3BF16 cdna3BF16_zeroOK [⟨(0x406b, 0x3fd5), by decide +kernel⟩, ⟨(0xbf5c, 0x40c1), by decide +kernel⟩, ⟨(0xb494, 0x4136), by decide +kernel⟩],
   mgridInput cdna3BF16 cdna3BF16_zeroOK [⟨(0xc075, 0x3f56), by decide +kernel⟩, ⟨(0x4597, 0xc150), by decide +kernel⟩, ⟨(0xbe56, 0xbebd), by decide +kernel⟩],
   mgridInput cdna3BF16 cdna3BF16_zeroOK [⟨(0x4002, 0x3eb5), by decide +kernel⟩, ⟨(0x3c14, 0x3ef6), by decide +kernel⟩, ⟨(0x3474, 0x3f48), by decide +kernel⟩],
   mgridInput cdna3BF16 cdna3BF16_zeroOK [⟨(0x3d4e, 0x40d2), by decide +kernel⟩, ⟨(0xbcad, 0xc0da), by decide +kernel⟩, ⟨(0x4719, 0x3e0b), by decide +kernel⟩],
   mgridInput cdna3BF16 cdna3BF16_zeroOK [⟨(0xb1cb, 0xc116), by decide +kernel⟩, ⟨(0x3e58, 0xbf97), by decide +kernel⟩, ⟨(0x3586, 0xc02b), by decide +kernel⟩],
   mgridInput cdna3BF16 cdna3BF16_zeroOK [⟨(0x46da, 0xc171), by decide +kernel⟩, ⟨(0x3dd4, 0x40ee), by decide +kernel⟩, ⟨(0x3166, 0x401d), by decide +kernel⟩]]

theorem cdna3BF16_table2 : ((MMAlgebra.codes2All.filter fun κ =>
    MMAlgebra.rvalid (MMAlgebra.LTree.realize2 κ 0 1)).map fun κ => cdna3BF16In2.map fun q =>
      MMAlgebra.evR ((mcMachine cdna3BF16).sub (MGridOK cdna3BF16)) 8 q (MMAlgebra.LTree.realize2 κ 0 1)).Nodup := by
  decide +kernel

theorem cdna3BF16_table3 : ((MMAlgebra.codes3All.filter fun κ => MMAlgebra.rvalid (κ.realize 0 1 2)).map
    fun κ => cdna3BF16In3.map fun q =>
      MMAlgebra.evR ((mcMachine cdna3BF16).sub (MGridOK cdna3BF16)) 8 q (κ.realize 0 1 2)).Nodup := by
  decide +kernel

/-- The laws of a rigid multiplier for terms, for cdna3BF16 on operand pairs with products on the
binary32 grid. -/
def cdna3BF16Alg : MMAlgebra.RigidAlg ((mcMachine cdna3BF16).sub (MGridOK cdna3BF16)) 8 :=
  MMAlgebra.RigidAlg.sub cdna3BF16Laws (MGridOK cdna3BF16) cdna3BF16_zeroOK
    (mc_add_comm _) (fun x hx => mc_add_zero _ x hx) (ga_sub_block_good cdna3BF16 rfl rfl cdna3BF16_pval0) (mc_add_good _)

/-- **cdna3BF16: on inputs whose products are multiples of `2^-149`, two terms over the same products
are equivalent exactly when their rigid normal forms agree.** -/
theorem cdna3BF16_term_equiv_iff (t₁ t₂ : MMAlgebra.Term) (hw₁ : MMAlgebra.TermWF 8 t₁)
    (hw₂ : MMAlgebra.TermWF 8 t₂) (n₁ : t₁.leaves.Nodup) (n₂ : t₂.leaves.Nodup)
    (hl : ∀ i, i ∈ t₁.leaves ↔ i ∈ t₂.leaves) :
    (∀ q : ℕ → cdna3BF16.a.Word × cdna3BF16.b.Word, (∀ i, MGridOK cdna3BF16 (q i)) →
      MMAlgebra.eval (mcMachine cdna3BF16) q 0 0 t₁ = MMAlgebra.eval (mcMachine cdna3BF16) q 0 0 t₂) ↔
      MMAlgebra.nfR t₁ = MMAlgebra.nfR t₂ := by
  constructor
  · intro h
    apply Classical.byContradiction; intro hne
    obtain ⟨_, q, _, _, hq⟩ := MMAlgebra.rigid_term_complete cdna3BF16Alg cdna3BF16In2 cdna3BF16In3
      cdna3BF16_table2 cdna3BF16_table3 t₁ t₂ hw₁ hw₂ n₁ n₂ hl hne
    apply hq
    rw [MMAlgebra.eval_sub, MMAlgebra.eval_sub]
    exact h _ (fun i => (q i).2)
  · intro h q hok
    have e₁ := MMAlgebra.rigid_sound cdna3BF16Alg (fun i => ⟨q i, hok i⟩) t₁ hw₁ n₁
    have e₂ := MMAlgebra.rigid_sound cdna3BF16Alg (fun i => ⟨q i, hok i⟩) t₂ hw₂ n₂
    rw [h] at e₁
    have := e₁.trans e₂.symm
    rw [MMAlgebra.eval_sub, MMAlgebra.eval_sub] at this
    exact this

def cdna3XF32In2 : List (ℕ → {q : cdna3XF32.a.Word × cdna3XF32.b.Word // MGridOK cdna3XF32 q}) :=
  [mgridInput cdna3XF32 cdna3XF32_zeroOK [⟨(0x3dfa8000, 0xc16a6000), by decide +kernel⟩, ⟨(0xc7c0e000, 0xc0cb4000), by decide +kernel⟩],
   mgridInput cdna3XF32 cdna3XF32_zeroOK [⟨(0x40676000, 0xc0eb4000), by decide +kernel⟩, ⟨(0xc71e0000, 0x3eb22000), by decide +kernel⟩],
   mgridInput cdna3XF32 cdna3XF32_zeroOK [⟨(0xbeb6c000, 0xbf030000), by decide +kernel⟩, ⟨(0xb5fd8000, 0x40e08000), by decide +kernel⟩]]

def cdna3XF32In3 : List (ℕ → {q : cdna3XF32.a.Word × cdna3XF32.b.Word // MGridOK cdna3XF32 q}) :=
  [mgridInput cdna3XF32 cdna3XF32_zeroOK [⟨(0x30f6a000, 0xbefc2000), by decide +kernel⟩, ⟨(0xb3f2e000, 0x41232000), by decide +kernel⟩, ⟨(0xb4bf8000, 0xc0518000), by decide +kernel⟩],
   mgridInput cdna3XF32 cdna3XF32_zeroOK [⟨(0x359da000, 0x4003c000), by decide +kernel⟩, ⟨(0xc06b6000, 0xbf2f0000), by decide +kernel⟩, ⟨(0xb32fe000, 0xc1730000), by decide +kernel⟩],
   mgridInput cdna3XF32 cdna3XF32_zeroOK [⟨(0xc6c00000, 0x3e76c000), by decide +kernel⟩, ⟨(0x46588000, 0x3e92a000), by decide +kernel⟩, ⟨(0x3fd70000, 0xc159a000), by decide +kernel⟩],
   mgridInput cdna3XF32 cdna3XF32_zeroOK [⟨(0xc41fa000, 0x3eae4000), by decide +kernel⟩, ⟨(0x326be000, 0x4010c000), by decide +kernel⟩, ⟨(0xc8474000, 0xbf7d6000), by decide +kernel⟩],
   mgridInput cdna3XF32 cdna3XF32_zeroOK [⟨(0x45922000, 0x3f920000), by decide +kernel⟩, ⟨(0xbf118000, 0x40f96000), by decide +kernel⟩, ⟨(0x30da0000, 0xbf37a000), by decide +kernel⟩],
   mgridInput cdna3XF32 cdna3XF32_zeroOK [⟨(0x315ee000, 0x3e2a0000), by decide +kernel⟩, ⟨(0xb1e24000, 0x3fcd8000), by decide +kernel⟩, ⟨(0x3d6a0000, 0x3fc4e000), by decide +kernel⟩],
   mgridInput cdna3XF32 cdna3XF32_zeroOK [⟨(0x3ce18000, 0xbe71a000), by decide +kernel⟩, ⟨(0x40386000, 0xbf910000), by decide +kernel⟩, ⟨(0xb5f20000, 0xc169e000), by decide +kernel⟩]]

theorem cdna3XF32_table2 : ((MMAlgebra.codes2All.filter fun κ =>
    MMAlgebra.rvalid (MMAlgebra.LTree.realize2 κ 0 1)).map fun κ => cdna3XF32In2.map fun q =>
      MMAlgebra.evR ((mcMachine cdna3XF32).sub (MGridOK cdna3XF32)) 4 q (MMAlgebra.LTree.realize2 κ 0 1)).Nodup := by
  decide +kernel

theorem cdna3XF32_table3 : ((MMAlgebra.codes3All.filter fun κ => MMAlgebra.rvalid (κ.realize 0 1 2)).map
    fun κ => cdna3XF32In3.map fun q =>
      MMAlgebra.evR ((mcMachine cdna3XF32).sub (MGridOK cdna3XF32)) 4 q (κ.realize 0 1 2)).Nodup := by
  decide +kernel

/-- The laws of a rigid multiplier for terms, for cdna3XF32 on operand pairs with products on the
binary32 grid. -/
def cdna3XF32Alg : MMAlgebra.RigidAlg ((mcMachine cdna3XF32).sub (MGridOK cdna3XF32)) 4 :=
  MMAlgebra.RigidAlg.sub cdna3XF32Laws (MGridOK cdna3XF32) cdna3XF32_zeroOK
    (mc_add_comm _) (fun x hx => mc_add_zero _ x hx) (ga_sub_block_good cdna3XF32 rfl rfl cdna3XF32_pval0) (mc_add_good _)

/-- **cdna3XF32: on inputs whose products are multiples of `2^-149`, two terms over the same products
are equivalent exactly when their rigid normal forms agree.** -/
theorem cdna3XF32_term_equiv_iff (t₁ t₂ : MMAlgebra.Term) (hw₁ : MMAlgebra.TermWF 4 t₁)
    (hw₂ : MMAlgebra.TermWF 4 t₂) (n₁ : t₁.leaves.Nodup) (n₂ : t₂.leaves.Nodup)
    (hl : ∀ i, i ∈ t₁.leaves ↔ i ∈ t₂.leaves) :
    (∀ q : ℕ → cdna3XF32.a.Word × cdna3XF32.b.Word, (∀ i, MGridOK cdna3XF32 (q i)) →
      MMAlgebra.eval (mcMachine cdna3XF32) q 0 0 t₁ = MMAlgebra.eval (mcMachine cdna3XF32) q 0 0 t₂) ↔
      MMAlgebra.nfR t₁ = MMAlgebra.nfR t₂ := by
  constructor
  · intro h
    apply Classical.byContradiction; intro hne
    obtain ⟨_, q, _, _, hq⟩ := MMAlgebra.rigid_term_complete cdna3XF32Alg cdna3XF32In2 cdna3XF32In3
      cdna3XF32_table2 cdna3XF32_table3 t₁ t₂ hw₁ hw₂ n₁ n₂ hl hne
    apply hq
    rw [MMAlgebra.eval_sub, MMAlgebra.eval_sub]
    exact h _ (fun i => (q i).2)
  · intro h q hok
    have e₁ := MMAlgebra.rigid_sound cdna3XF32Alg (fun i => ⟨q i, hok i⟩) t₁ hw₁ n₁
    have e₂ := MMAlgebra.rigid_sound cdna3XF32Alg (fun i => ⟨q i, hok i⟩) t₂ hw₂ n₂
    rw [h] at e₁
    have := e₁.trans e₂.symm
    rw [MMAlgebra.eval_sub, MMAlgebra.eval_sub] at this
    exact this

end MMAlgebra.MC.CDNA3
