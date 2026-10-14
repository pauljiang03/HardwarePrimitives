import MMAlgebraTC.ChainVariants
import MMAlgebraTC.TermComplete
import MMAlgebraTC.Contract
import MMAlgebra.Sub

/-! # Completeness for terms on the bf16 and tf32 Tensor Core models

A bf16 or tf32 product can lie below binary32's grid, and a block holding only such a product
truncates it to zero, so from good inputs a block can return `−0` and the laws of a rigid multiplier
fail for terms. On operand pairs whose product is a multiple of `2^-149` (`GridOK`) every term of a
block lies on the binary32 grid, and a block never returns `−0` (`tc_sub_block_good`). With the
laws for chains (`tcLaws`) these are the laws of a rigid multiplier on such inputs
(`MMAlgebra.RigidAlg.sub`), and kernel-checked fingerprint tables give completeness for terms, and
equivalence exactly when the normal forms agree, on A100 and H100 bf16 and on A100 and H100 tf32
(`a100bf16_term_equiv_iff`, …). -/

open TensorCore Ozaki Ozaki.TC

namespace MMAlgebra.TC

/-- An operand pair whose product is a multiple of `2^-149`. -/
def GridOK (p : Model) (q : p.Word × p.Word) : Prop := ((tcMachine p).pval q * pow2 149).den = 1

instance (p : Model) (q : p.Word × p.Word) : Decidable (GridOK p q) := by
  unfold GridOK; infer_instance

theorem gridOK_onGridQ {p : Model} {q : p.Word × p.Word} (h : GridOK p q) :
    OnGridQ ((tcMachine p).pval q) (-149) := by
  refine ⟨((tcMachine p).pval q * pow2 149).num, ?_⟩
  have e : (tcMachine p).pval q * pow2 149 = (((tcMachine p).pval q * pow2 149).num : ℚ) :=
    Rat.ext (by simp) (by rw [Rat.den_intCast]; exact h)
  rw [← e, Rat.mul_assoc, ← pow2_add]
  show _ = _ * pow2 0
  rw [show pow2 0 = 1 by decide +kernel, Rat.mul_one]

theorem gridOK_zero (p : Model) (hz : p.decode 0 = some ⟨0, 0, 0⟩) : GridOK p (0, 0) := by
  unfold GridOK
  show (wordValue p 0 * wordValue p 0 * pow2 149).den = 1
  rw [wordValue_zero_of p hz, Rat.zero_mul, Rat.zero_mul]
  rfl

/-- **A block whose terms lie on the binary32 grid never returns `−0`**, with a binary32 block
output. -/
theorem blockOut_ne_negZero_of {p : Model} {x : BlockInput p} {d : F32}
    (hg : ∀ b, prepare x = some b → OnGridQ b.accumulator (-149)) (h : blockOut x = .ok d)
    (hw : 23 ≤ p.outputFracBits) :
    d ≠ 0x80000000 := by
  unfold blockOut at h
  cases ht : evalBlock x with
  | error e => rw [ht] at h; simp [Except.map] at h
  | ok t =>
    rw [ht] at h
    simp only [Except.map, Except.ok.injEq] at h
    subst h
    unfold evalBlock at ht
    split at ht
    · cases ht
    · cases hp : prepare x with
      | none => rw [hp] at ht; cases ht
      | some b =>
        rw [hp] at ht
        simp only at ht
        have hout := evalPrepared_output ht (by rw [prepare_model hp]; exact hw)
        intro hneg
        by_cases hz : b.accumulator = 0
        · rw [hz] at hout
          have h0 : round32 .truncate 0 = some 0 := by decide +kernel
          rw [h0, hneg] at hout
          exact absurd (Option.some.inj hout) (by decide)
        · obtain ⟨b', hb', hd', _, _⟩ :=
            round32_nonzero_spec .truncate b.accumulator hz (round32_range hout)
          rw [hout, hneg] at hb'
          cases Option.some.inj hb'
          have hv : value32 (0x80000000 : F32) = some 0 := by decide +kernel
          rw [hv] at hd'
          exact signedRounded_ne_zero (hg b hp) hz (round32_range hout) (Option.some.inj hd').symm

/-- The terms of a block whose operand pairs are `(0, 0)` or have products on the binary32 grid lie
on the binary32 grid. -/
theorem terms_onGridQ_of {p : Model}
    {ps : List (p.Word × p.Word)} (hps : ∀ q ∈ ps, OnGridQ ((tcMachine p).pval q) (-149))
    {d : F32} {b : PreparedBlock} (hp : prepare ⟨ps, d⟩ = some b) :
    ∀ t ∈ b.terms, OnGridQ t.value (-149) := by
  unfold prepare at hp
  cases hc : decode32 d with
  | none => simp [hc] at hp
  | some dc =>
    cases hpp : prepareProducts p ps with
    | none => simp [hc, hpp] at hp
    | some ds =>
      simp only [hc, hpp, Option.some.injEq] at hp
      subst hp
      intro t ht
      simp only [PreparedBlock.terms, List.mem_cons, List.mem_map] at ht
      rcases ht with rfl | ⟨⟨da, db⟩, hd, rfl⟩
      · exact decode32_onGridQ hc
      · obtain ⟨q, hq, ha, hb⟩ := prepareProducts_mem hpp (da, db) hd
        rw [denormalizedProduct_value]
        have e : (tcMachine p).pval q = da.value * db.value := by
          show wordValue p q.1 * wordValue p q.2 = _
          simp only [wordValue, decodeD, ha, hb, Option.getD_some]
        rw [← e]
        exact hps q hq

/-- **On operand pairs with products on the binary32 grid, Tensor Core blocks return good words.** -/
theorem tc_sub_block_good (p : Model) (hz : p.decode 0 = some ⟨0, 0, 0⟩)
    (hw : 23 ≤ p.outputFracBits) (d : F32)
    (ps : List (Option {q : p.Word × p.Word // GridOK p q})) (o : F32)
    (h : (tcMachine p).block d (ps.map (Option.map Subtype.val)) = some o) : Good o := by
  have h' : (blockOut (p := p) ⟨slotPairs p (ps.map (Option.map Subtype.val)), d⟩).toOption = some o := h
  have hps : ∀ q ∈ slotPairs p (ps.map (Option.map Subtype.val)), OnGridQ ((tcMachine p).pval q) (-149) := by
    intro q hq
    simp only [slotPairs, List.map_map, List.mem_map] at hq
    obtain ⟨o, _, rfl⟩ := hq
    cases o with
    | none => exact gridOK_onGridQ (gridOK_zero p hz)
    | some x => exact gridOK_onGridQ x.2
  cases hb : blockOut (p := p) ⟨slotPairs p (ps.map (Option.map Subtype.val)), d⟩ with
  | error e => rw [hb] at h'; simp [Except.toOption] at h'
  | ok o' =>
    rw [hb] at h'
    simp only [Except.toOption, Option.some.injEq] at h'
    subst h'
    refine ⟨?_, blockOut_ne_negZero_of (fun b hp => ?_) hb hw⟩
    · unfold blockOut at hb
      cases ht : evalBlock (p := p) ⟨slotPairs p (ps.map (Option.map Subtype.val)), d⟩ with
      | error e => rw [ht] at hb; simp [Except.map] at hb
      | ok t =>
        rw [ht] at hb
        simp only [Except.map, Except.ok.injEq] at hb
        subst hb
        rw [finite32_self]; rfl
    · rw [accumulator_value]
      apply onGridQ_sumQ
      intro y hy
      obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hy
      exact onGridQ_truncGrid (terms_onGridQ_of hps hp t ht) _

/-- The laws of a rigid multiplier on a Tensor Core model, on operand pairs with products on the
binary32 grid. -/
def tcSubAlg (p : Model) (hF : 23 ≤ p.alignFracBits)
    (hout : 23 ≤ p.outputFracBits) (hmin : ∀ f ∈ p.eAlignMin, f ≤ -126)
    (hz : p.decode 0 = some ⟨0, 0, 0⟩) : MMAlgebra.RigidAlg ((tcMachine p).sub (GridOK p)) p.nfma :=
  MMAlgebra.RigidAlg.sub (tcLaws p hF hout hmin hz) (GridOK p) (gridOK_zero p hz) (tc_add_comm p)
    (fun x hx => tc_add_zero p x hx) (tc_sub_block_good p hz hout) (tc_add_good p)

/-- **Completeness for terms on a Tensor Core model, on inputs with products on the binary32
grid**, from fingerprint tables. -/
theorem tc_sub_term_complete (p : Model) (hF : 23 ≤ p.alignFracBits)
    (hout : 23 ≤ p.outputFracBits)
    (hmin : ∀ f ∈ p.eAlignMin, f ≤ -126) (hz : p.decode 0 = some ⟨0, 0, 0⟩)
    (ins2 ins3 : List (ℕ → {q : p.Word × p.Word // GridOK p q}))
    (hnd2 : ((MMAlgebra.codes2All.filter fun κ => MMAlgebra.rvalid (MMAlgebra.LTree.realize2 κ 0 1)).map
      fun κ => ins2.map fun q => MMAlgebra.evR ((tcMachine p).sub (GridOK p)) p.nfma q
        (MMAlgebra.LTree.realize2 κ 0 1)).Nodup)
    (hnd3 : ((MMAlgebra.codes3All.filter fun κ => MMAlgebra.rvalid (κ.realize 0 1 2)).map
      fun κ => ins3.map fun q => MMAlgebra.evR ((tcMachine p).sub (GridOK p)) p.nfma q
        (κ.realize 0 1 2)).Nodup)
    (t₁ t₂ : MMAlgebra.Term) (hw₁ : MMAlgebra.TermWF p.nfma t₁) (hw₂ : MMAlgebra.TermWF p.nfma t₂)
    (n₁ : t₁.leaves.Nodup) (n₂ : t₂.leaves.Nodup) (hl : ∀ i, i ∈ t₁.leaves ↔ i ∈ t₂.leaves)
    (hne : MMAlgebra.nfR t₁ ≠ MMAlgebra.nfR t₂) :
    ∃ (s : List ℕ) (q : ℕ → p.Word × p.Word), s.length ≤ 3 ∧ (∀ i, i ∉ s → q i = (0, 0)) ∧
      (∀ i, GridOK p (q i)) ∧
      MMAlgebra.eval (tcMachine p) q 0 0 t₁ ≠ MMAlgebra.eval (tcMachine p) q 0 0 t₂ := by
  obtain ⟨s, q, hs, hzq, hq⟩ := MMAlgebra.rigid_term_complete (tcSubAlg p hF hout hmin hz) ins2 ins3
    hnd2 hnd3 t₁ t₂ hw₁ hw₂ n₁ n₂ hl hne
  refine ⟨s, fun i => (q i).1, hs, fun i hi => by show (q i).1 = (0, 0); rw [hzq i hi]; rfl,
    fun i => (q i).2, ?_⟩
  rw [← MMAlgebra.eval_sub, ← MMAlgebra.eval_sub]
  exact hq

/-- **On inputs with products on the binary32 grid, terms are equivalent exactly when their normal
forms agree**, from fingerprint tables. -/
theorem tc_sub_term_equiv_iff (p : Model) (hF : 23 ≤ p.alignFracBits)
    (hout : 23 ≤ p.outputFracBits)
    (hmin : ∀ f ∈ p.eAlignMin, f ≤ -126) (hz : p.decode 0 = some ⟨0, 0, 0⟩)
    (ins2 ins3 : List (ℕ → {q : p.Word × p.Word // GridOK p q}))
    (hnd2 : ((MMAlgebra.codes2All.filter fun κ => MMAlgebra.rvalid (MMAlgebra.LTree.realize2 κ 0 1)).map
      fun κ => ins2.map fun q => MMAlgebra.evR ((tcMachine p).sub (GridOK p)) p.nfma q
        (MMAlgebra.LTree.realize2 κ 0 1)).Nodup)
    (hnd3 : ((MMAlgebra.codes3All.filter fun κ => MMAlgebra.rvalid (κ.realize 0 1 2)).map
      fun κ => ins3.map fun q => MMAlgebra.evR ((tcMachine p).sub (GridOK p)) p.nfma q
        (κ.realize 0 1 2)).Nodup)
    (t₁ t₂ : MMAlgebra.Term) (hw₁ : MMAlgebra.TermWF p.nfma t₁) (hw₂ : MMAlgebra.TermWF p.nfma t₂)
    (n₁ : t₁.leaves.Nodup) (n₂ : t₂.leaves.Nodup) (hl : ∀ i, i ∈ t₁.leaves ↔ i ∈ t₂.leaves) :
    (∀ q : ℕ → p.Word × p.Word, (∀ i, GridOK p (q i)) →
      MMAlgebra.eval (tcMachine p) q 0 0 t₁ = MMAlgebra.eval (tcMachine p) q 0 0 t₂) ↔
      MMAlgebra.nfR t₁ = MMAlgebra.nfR t₂ := by
  constructor
  · intro h
    apply Classical.byContradiction; intro hne
    obtain ⟨_, q, _, _, hok, hq⟩ := tc_sub_term_complete p hF hout hmin hz ins2 ins3 hnd2 hnd3
      t₁ t₂ hw₁ hw₂ n₁ n₂ hl hne
    exact hq (h q hok)
  · intro h q hok
    have e₁ := MMAlgebra.rigid_sound (tcSubAlg p hF hout hmin hz) (fun i => ⟨q i, hok i⟩) t₁ hw₁ n₁
    have e₂ := MMAlgebra.rigid_sound (tcSubAlg p hF hout hmin hz) (fun i => ⟨q i, hok i⟩) t₂ hw₂ n₂
    rw [h] at e₁
    have := e₁.trans e₂.symm
    rw [MMAlgebra.eval_sub, MMAlgebra.eval_sub] at this
    exact this

/-! ## Fingerprint tables -/

/-- An input with the operand pairs of a list at `0, 1, 2, …` and zero pairs elsewhere. -/
def gridInput (p : Model) (hz : p.decode 0 = some ⟨0, 0, 0⟩)
    (ws : List {q : p.Word × p.Word // GridOK p q}) : ℕ → {q : p.Word × p.Word // GridOK p q} :=
  fun j => ws.getD j ⟨(0, 0), gridOK_zero p hz⟩

/-! ### A100 (bf16) -/

def a100bf16In2 : List (ℕ → {q : a100BF16F32.Word × a100BF16F32.Word // GridOK a100BF16F32 q}) :=
  [gridInput a100BF16F32 (bf16_decode_zero 8 1 _) [⟨(0x4036, 0xbf57), by decide +kernel⟩, ⟨(0xbf13, 0xc5f9), by decide +kernel⟩],
   gridInput a100BF16F32 (bf16_decode_zero 8 1 _) [⟨(0xc5ff, 0x4081), by decide +kernel⟩, ⟨(0x3a96, 0x3f7f), by decide +kernel⟩]]

def a100bf16In3 : List (ℕ → {q : a100BF16F32.Word × a100BF16F32.Word // GridOK a100BF16F32 q}) :=
  [gridInput a100BF16F32 (bf16_decode_zero 8 1 _) [⟨(0x3f00, 0xbab5), by decide +kernel⟩, ⟨(0xc26a, 0xc217), by decide +kernel⟩, ⟨(0xc232, 0x423a), by decide +kernel⟩],
   gridInput a100BF16F32 (bf16_decode_zero 8 1 _) [⟨(0xc01b, 0xc5c6), by decide +kernel⟩, ⟨(0xc235, 0xceb4), by decide +kernel⟩, ⟨(0xc0bb, 0xc5ab), by decide +kernel⟩],
   gridInput a100BF16F32 (bf16_decode_zero 8 1 _) [⟨(0xceea, 0x3fe9), by decide +kernel⟩, ⟨(0x427f, 0x3ff0), by decide +kernel⟩, ⟨(0x4001, 0x45c0), by decide +kernel⟩],
   gridInput a100BF16F32 (bf16_decode_zero 8 1 _) [⟨(0x3fdc, 0xc065), by decide +kernel⟩, ⟨(0xceff, 0xbe20), by decide +kernel⟩, ⟨(0xc073, 0x4236), by decide +kernel⟩],
   gridInput a100BF16F32 (bf16_decode_zero 8 1 _) [⟨(0xbf40, 0xc5e8), by decide +kernel⟩, ⟨(0x40c7, 0xcefb), by decide +kernel⟩, ⟨(0xcef8, 0xc0e0), by decide +kernel⟩],
   gridInput a100BF16F32 (bf16_decode_zero 8 1 _) [⟨(0xc0e1, 0xc0ef), by decide +kernel⟩, ⟨(0xbf81, 0x4084), by decide +kernel⟩, ⟨(0x45f7, 0x40cd), by decide +kernel⟩],
   gridInput a100BF16F32 (bf16_decode_zero 8 1 _) [⟨(0xc26d, 0x3f00), by decide +kernel⟩, ⟨(0x4200, 0xc0c7), by decide +kernel⟩, ⟨(0xc5ad, 0xc5e8), by decide +kernel⟩]]

theorem a100bf16_table2 : ((MMAlgebra.codes2All.filter fun κ =>
    MMAlgebra.rvalid (MMAlgebra.LTree.realize2 κ 0 1)).map fun κ => a100bf16In2.map fun q =>
      MMAlgebra.evR ((tcMachine a100BF16F32).sub (GridOK a100BF16F32)) a100BF16F32.nfma q (MMAlgebra.LTree.realize2 κ 0 1)).Nodup := by
  decide +kernel

theorem a100bf16_table3 : ((MMAlgebra.codes3All.filter fun κ => MMAlgebra.rvalid (κ.realize 0 1 2)).map
    fun κ => a100bf16In3.map fun q =>
      MMAlgebra.evR ((tcMachine a100BF16F32).sub (GridOK a100BF16F32)) a100BF16F32.nfma q (κ.realize 0 1 2)).Nodup := by
  decide +kernel

/-- **A100 (bf16): on inputs with products on the binary32 grid, terms are equivalent exactly when their
normal forms agree.** -/
theorem a100bf16_term_equiv_iff (t₁ t₂ : MMAlgebra.Term) (hw₁ : MMAlgebra.TermWF 8 t₁)
    (hw₂ : MMAlgebra.TermWF 8 t₂) (n₁ : t₁.leaves.Nodup) (n₂ : t₂.leaves.Nodup)
    (hl : ∀ i, i ∈ t₁.leaves ↔ i ∈ t₂.leaves) :
    (∀ q : ℕ → a100BF16F32.Word × a100BF16F32.Word, (∀ i, GridOK a100BF16F32 (q i)) →
      MMAlgebra.eval (tcMachine a100BF16F32) q 0 0 t₁ = MMAlgebra.eval (tcMachine a100BF16F32) q 0 0 t₂) ↔
      MMAlgebra.nfR t₁ = MMAlgebra.nfR t₂ :=
  tc_sub_term_equiv_iff a100BF16F32 (by decide) (by decide) (by simp [a100BF16F32, bf16Fp32Model]) (bf16_decode_zero 8 1 _) a100bf16In2 a100bf16In3
    a100bf16_table2 a100bf16_table3 t₁ t₂ hw₁ hw₂ n₁ n₂ hl

/-! ### H100 (bf16) -/

def h100bf16In2 : List (ℕ → {q : hopperBF16F32.Word × hopperBF16F32.Word // GridOK hopperBF16F32 q}) :=
  [gridInput hopperBF16F32 (bf16_decode_zero 16 2 _) [⟨(0x3fa8, 0xc0be), by decide +kernel⟩, ⟨(0xbaeb, 0xcebb), by decide +kernel⟩],
   gridInput hopperBF16F32 (bf16_decode_zero 16 2 _) [⟨(0xc06d, 0xcecd), by decide +kernel⟩, ⟨(0xc270, 0x3fbd), by decide +kernel⟩]]

def h100bf16In3 : List (ℕ → {q : hopperBF16F32.Word × hopperBF16F32.Word // GridOK hopperBF16F32 q}) :=
  [gridInput hopperBF16F32 (bf16_decode_zero 16 2 _) [⟨(0x2bc0, 0xce81), by decide +kernel⟩, ⟨(0x3a9e, 0x3f9a), by decide +kernel⟩, ⟨(0xabf4, 0x4273), by decide +kernel⟩],
   gridInput hopperBF16F32 (bf16_decode_zero 16 2 _) [⟨(0xbe02, 0x409a), by decide +kernel⟩, ⟨(0xcef8, 0x3a80), by decide +kernel⟩, ⟨(0x3e6c, 0xc048), by decide +kernel⟩],
   gridInput hopperBF16F32 (bf16_decode_zero 16 2 _) [⟨(0xcef6, 0x3e7f), by decide +kernel⟩, ⟨(0xc0e0, 0xbf54), by decide +kernel⟩, ⟨(0x4200, 0x3e23), by decide +kernel⟩],
   gridInput hopperBF16F32 (bf16_decode_zero 16 2 _) [⟨(0xba80, 0x4207), by decide +kernel⟩, ⟨(0xbe5d, 0x409c), by decide +kernel⟩, ⟨(0xbaff, 0xcebd), by decide +kernel⟩],
   gridInput hopperBF16F32 (bf16_decode_zero 16 2 _) [⟨(0x45f8, 0xce81), by decide +kernel⟩, ⟨(0xceb8, 0xceba), by decide +kernel⟩, ⟨(0x3a92, 0xc5b7), by decide +kernel⟩],
   gridInput hopperBF16F32 (bf16_decode_zero 16 2 _) [⟨(0xbf01, 0x3aff), by decide +kernel⟩, ⟨(0x4062, 0xbe1f), by decide +kernel⟩, ⟨(0xabf2, 0xc5bb), by decide +kernel⟩]]

theorem h100bf16_table2 : ((MMAlgebra.codes2All.filter fun κ =>
    MMAlgebra.rvalid (MMAlgebra.LTree.realize2 κ 0 1)).map fun κ => h100bf16In2.map fun q =>
      MMAlgebra.evR ((tcMachine hopperBF16F32).sub (GridOK hopperBF16F32)) hopperBF16F32.nfma q (MMAlgebra.LTree.realize2 κ 0 1)).Nodup := by
  decide +kernel

theorem h100bf16_table3 : ((MMAlgebra.codes3All.filter fun κ => MMAlgebra.rvalid (κ.realize 0 1 2)).map
    fun κ => h100bf16In3.map fun q =>
      MMAlgebra.evR ((tcMachine hopperBF16F32).sub (GridOK hopperBF16F32)) hopperBF16F32.nfma q (κ.realize 0 1 2)).Nodup := by
  decide +kernel

/-- **H100 (bf16): on inputs with products on the binary32 grid, terms are equivalent exactly when their
normal forms agree.** -/
theorem h100bf16_term_equiv_iff (t₁ t₂ : MMAlgebra.Term) (hw₁ : MMAlgebra.TermWF 16 t₁)
    (hw₂ : MMAlgebra.TermWF 16 t₂) (n₁ : t₁.leaves.Nodup) (n₂ : t₂.leaves.Nodup)
    (hl : ∀ i, i ∈ t₁.leaves ↔ i ∈ t₂.leaves) :
    (∀ q : ℕ → hopperBF16F32.Word × hopperBF16F32.Word, (∀ i, GridOK hopperBF16F32 (q i)) →
      MMAlgebra.eval (tcMachine hopperBF16F32) q 0 0 t₁ = MMAlgebra.eval (tcMachine hopperBF16F32) q 0 0 t₂) ↔
      MMAlgebra.nfR t₁ = MMAlgebra.nfR t₂ :=
  tc_sub_term_equiv_iff hopperBF16F32 (by decide) (by decide) (by simp [hopperBF16F32, bf16Fp32Model]) (bf16_decode_zero 16 2 _) h100bf16In2 h100bf16In3
    h100bf16_table2 h100bf16_table3 t₁ t₂ hw₁ hw₂ n₁ n₂ hl

/-! ### A100 (tf32) -/

def a100tf32In2 : List (ℕ → {q : a100TF32F32.Word × a100TF32F32.Word // GridOK a100TF32F32 q}) :=
  [gridInput a100TF32F32 (tf19_decode_zero 4 1 _) [⟨(0x6019b, 0x2753f), by decide +kernel⟩, ⟨(0x61200, 0x677bd), by decide +kernel⟩],
   gridInput a100TF32F32 (tf19_decode_zero 4 1 _) [⟨(0x604dd, 0x677ff), by decide +kernel⟩, ⟨(0x62c39, 0x1ffff), by decide +kernel⟩]]

def a100tf32In3 : List (ℕ → {q : a100TF32F32.Word × a100TF32F32.Word // GridOK a100TF32F32 q}) :=
  [gridInput a100TF32F32 (tf19_decode_zero 4 1 _) [⟨(0x6769c, 0x1fc00), by decide +kernel⟩, ⟨(0x2045d, 0x62e8c), by decide +kernel⟩, ⟨(0x1fb61, 0x27718), by decide +kernel⟩],
   gridInput a100TF32F32 (tf19_decode_zero 4 1 _) [⟨(0x5fc01, 0x2003d), by decide +kernel⟩, ⟨(0x6107a, 0x1f870), by decide +kernel⟩, ⟨(0x5d4f3, 0x27534), by decide +kernel⟩],
   gridInput a100TF32F32 (tf19_decode_zero 4 1 _) [⟨(0x1d600, 0x5f9e8), by decide +kernel⟩, ⟨(0x6127c, 0x1f85f), by decide +kernel⟩, ⟨(0x21203, 0x213ff), by decide +kernel⟩],
   gridInput a100TF32F32 (tf19_decode_zero 4 1 _) [⟨(0x61034, 0x203a8), by decide +kernel⟩, ⟨(0x1fb40, 0x1f095), by decide +kernel⟩, ⟨(0x1d400, 0x1d53d), by decide +kernel⟩],
   gridInput a100TF32F32 (tf19_decode_zero 4 1 _) [⟨(0x613ff, 0x62d31), by decide +kernel⟩, ⟨(0x62ca9, 0x2130c), by decide +kernel⟩, ⟨(0x5d768, 0x207e7), by decide +kernel⟩],
   gridInput a100TF32F32 (tf19_decode_zero 4 1 _) [⟨(0x22ff2, 0x55e17), by decide +kernel⟩, ⟨(0x276e8, 0x1ffff), by decide +kernel⟩, ⟨(0x22fe1, 0x62fc5), by decide +kernel⟩],
   gridInput a100TF32F32 (tf19_decode_zero 4 1 _) [⟨(0x612c7, 0x1fe00), by decide +kernel⟩, ⟨(0x22f05, 0x22ef1), by decide +kernel⟩, ⟨(0x1fbff, 0x1ffee), by decide +kernel⟩]]

theorem a100tf32_table2 : ((MMAlgebra.codes2All.filter fun κ =>
    MMAlgebra.rvalid (MMAlgebra.LTree.realize2 κ 0 1)).map fun κ => a100tf32In2.map fun q =>
      MMAlgebra.evR ((tcMachine a100TF32F32).sub (GridOK a100TF32F32)) a100TF32F32.nfma q (MMAlgebra.LTree.realize2 κ 0 1)).Nodup := by
  decide +kernel

theorem a100tf32_table3 : ((MMAlgebra.codes3All.filter fun κ => MMAlgebra.rvalid (κ.realize 0 1 2)).map
    fun κ => a100tf32In3.map fun q =>
      MMAlgebra.evR ((tcMachine a100TF32F32).sub (GridOK a100TF32F32)) a100TF32F32.nfma q (κ.realize 0 1 2)).Nodup := by
  decide +kernel

/-- **A100 (tf32): on inputs with products on the binary32 grid, terms are equivalent exactly when their
normal forms agree.** -/
theorem a100tf32_term_equiv_iff (t₁ t₂ : MMAlgebra.Term) (hw₁ : MMAlgebra.TermWF 4 t₁)
    (hw₂ : MMAlgebra.TermWF 4 t₂) (n₁ : t₁.leaves.Nodup) (n₂ : t₂.leaves.Nodup)
    (hl : ∀ i, i ∈ t₁.leaves ↔ i ∈ t₂.leaves) :
    (∀ q : ℕ → a100TF32F32.Word × a100TF32F32.Word, (∀ i, GridOK a100TF32F32 (q i)) →
      MMAlgebra.eval (tcMachine a100TF32F32) q 0 0 t₁ = MMAlgebra.eval (tcMachine a100TF32F32) q 0 0 t₂) ↔
      MMAlgebra.nfR t₁ = MMAlgebra.nfR t₂ :=
  tc_sub_term_equiv_iff a100TF32F32 (by decide) (by decide) (by simp [a100TF32F32, tf19Fp32Model]) (tf19_decode_zero 4 1 _) a100tf32In2 a100tf32In3
    a100tf32_table2 a100tf32_table3 t₁ t₂ hw₁ hw₂ n₁ n₂ hl

/-! ### H100 (tf32, wmma) -/

def h100tf32wIn2 : List (ℕ → {q : hopperTF32WmmaF32.Word × hopperTF32WmmaF32.Word // GridOK hopperTF32WmmaF32 q}) :=
  [gridInput hopperTF32WmmaF32 (tf19_decode_zero 4 2 _) [⟨(0x22f9c, 0x1fbff), by decide +kernel⟩, ⟨(0x6034b, 0x1d626), by decide +kernel⟩],
   gridInput hopperTF32WmmaF32 (tf19_decode_zero 4 2 _) [⟨(0x5d6d5, 0x1fd78), by decide +kernel⟩, ⟨(0x61121, 0x5f24c), by decide +kernel⟩]]

def h100tf32wIn3 : List (ℕ → {q : hopperTF32WmmaF32.Word × hopperTF32WmmaF32.Word // GridOK hopperTF32WmmaF32 q}) :=
  [gridInput hopperTF32WmmaF32 (tf19_decode_zero 4 2 _) [⟨(0x1f349, 0x607ff), by decide +kernel⟩, ⟨(0x613ff, 0x5ff7e), by decide +kernel⟩, ⟨(0x1fee9, 0x613ff), by decide +kernel⟩],
   gridInput hopperTF32WmmaF32 (tf19_decode_zero 4 2 _) [⟨(0x22f83, 0x1d60b), by decide +kernel⟩, ⟨(0x6022c, 0x203d7), by decide +kernel⟩, ⟨(0x22cc1, 0x5fe00), by decide +kernel⟩],
   gridInput hopperTF32WmmaF32 (tf19_decode_zero 4 2 _) [⟨(0x5d400, 0x5f801), by decide +kernel⟩, ⟨(0x62e0f, 0x2055a), by decide +kernel⟩, ⟨(0x15e00, 0x677ff), by decide +kernel⟩],
   gridInput hopperTF32WmmaF32 (tf19_decode_zero 4 2 _) [⟨(0x5fe36, 0x61365), by decide +kernel⟩, ⟨(0x62d1d, 0x1f3ff), by decide +kernel⟩, ⟨(0x675ca, 0x5fa00), by decide +kernel⟩],
   gridInput hopperTF32WmmaF32 (tf19_decode_zero 4 2 _) [⟨(0x1f001, 0x5f00c), by decide +kernel⟩, ⟨(0x5fc00, 0x1ffff), by decide +kernel⟩, ⟨(0x5fe60, 0x62dcb), by decide +kernel⟩],
   gridInput hopperTF32WmmaF32 (tf19_decode_zero 4 2 _) [⟨(0x62e00, 0x22dee), by decide +kernel⟩, ⟨(0x1f801, 0x1fe0a), by decide +kernel⟩, ⟨(0x1f00d, 0x1ffe3), by decide +kernel⟩],
   gridInput hopperTF32WmmaF32 (tf19_decode_zero 4 2 _) [⟨(0x1fd48, 0x21001), by decide +kernel⟩, ⟨(0x27590, 0x22e00), by decide +kernel⟩, ⟨(0x6764a, 0x20001), by decide +kernel⟩],
   gridInput hopperTF32WmmaF32 (tf19_decode_zero 4 2 _) [⟨(0x5f27a, 0x27589), by decide +kernel⟩, ⟨(0x5fc4b, 0x5ff90), by decide +kernel⟩, ⟨(0x1d400, 0x22fe0), by decide +kernel⟩]]

theorem h100tf32w_table2 : ((MMAlgebra.codes2All.filter fun κ =>
    MMAlgebra.rvalid (MMAlgebra.LTree.realize2 κ 0 1)).map fun κ => h100tf32wIn2.map fun q =>
      MMAlgebra.evR ((tcMachine hopperTF32WmmaF32).sub (GridOK hopperTF32WmmaF32)) hopperTF32WmmaF32.nfma q (MMAlgebra.LTree.realize2 κ 0 1)).Nodup := by
  decide +kernel

theorem h100tf32w_table3 : ((MMAlgebra.codes3All.filter fun κ => MMAlgebra.rvalid (κ.realize 0 1 2)).map
    fun κ => h100tf32wIn3.map fun q =>
      MMAlgebra.evR ((tcMachine hopperTF32WmmaF32).sub (GridOK hopperTF32WmmaF32)) hopperTF32WmmaF32.nfma q (κ.realize 0 1 2)).Nodup := by
  decide +kernel

/-- **H100 (tf32, wmma): on inputs with products on the binary32 grid, terms are equivalent exactly when their
normal forms agree.** -/
theorem h100tf32w_term_equiv_iff (t₁ t₂ : MMAlgebra.Term) (hw₁ : MMAlgebra.TermWF 4 t₁)
    (hw₂ : MMAlgebra.TermWF 4 t₂) (n₁ : t₁.leaves.Nodup) (n₂ : t₂.leaves.Nodup)
    (hl : ∀ i, i ∈ t₁.leaves ↔ i ∈ t₂.leaves) :
    (∀ q : ℕ → hopperTF32WmmaF32.Word × hopperTF32WmmaF32.Word, (∀ i, GridOK hopperTF32WmmaF32 (q i)) →
      MMAlgebra.eval (tcMachine hopperTF32WmmaF32) q 0 0 t₁ = MMAlgebra.eval (tcMachine hopperTF32WmmaF32) q 0 0 t₂) ↔
      MMAlgebra.nfR t₁ = MMAlgebra.nfR t₂ :=
  tc_sub_term_equiv_iff hopperTF32WmmaF32 (by decide) (by decide) (by simp [hopperTF32WmmaF32, tf19Fp32Model]) (tf19_decode_zero 4 2 _) h100tf32wIn2 h100tf32wIn3
    h100tf32w_table2 h100tf32w_table3 t₁ t₂ hw₁ hw₂ n₁ n₂ hl

/-! ### H100 (tf32, mma) -/

def h100tf32mIn2 : List (ℕ → {q : hopperTF32MmaF32.Word × hopperTF32MmaF32.Word // GridOK hopperTF32MmaF32 q}) :=
  [gridInput hopperTF32MmaF32 (tf19_decode_zero 8 2 _) [⟨(0x61200, 0x61370), by decide +kernel⟩, ⟨(0x677ff, 0x1ff4a), by decide +kernel⟩],
   gridInput hopperTF32MmaF32 (tf19_decode_zero 8 2 _) [⟨(0x27512, 0x5f3df), by decide +kernel⟩, ⟨(0x22ca3, 0x203d9), by decide +kernel⟩]]

def h100tf32mIn3 : List (ℕ → {q : hopperTF32MmaF32.Word × hopperTF32MmaF32.Word // GridOK hopperTF32MmaF32 q}) :=
  [gridInput hopperTF32MmaF32 (tf19_decode_zero 8 2 _) [⟨(0x5fa00, 0x5fe00), by decide +kernel⟩, ⟨(0x203a6, 0x5d755), by decide +kernel⟩, ⟨(0x20592, 0x5f235), by decide +kernel⟩],
   gridInput hopperTF32MmaF32 (tf19_decode_zero 8 2 _) [⟨(0x1d567, 0x605e0), by decide +kernel⟩, ⟨(0x1fe00, 0x5f801), by decide +kernel⟩, ⟨(0x5fd7d, 0x22ea0), by decide +kernel⟩],
   gridInput hopperTF32MmaF32 (tf19_decode_zero 8 2 _) [⟨(0x1d7c3, 0x61001), by decide +kernel⟩, ⟨(0x5d44f, 0x20001), by decide +kernel⟩, ⟨(0x1fe8d, 0x22f9d), by decide +kernel⟩],
   gridInput hopperTF32MmaF32 (tf19_decode_zero 8 2 _) [⟨(0x20609, 0x5fa34), by decide +kernel⟩, ⟨(0x276ec, 0x1f3ff), by decide +kernel⟩, ⟨(0x275f1, 0x5f33d), by decide +kernel⟩],
   gridInput hopperTF32MmaF32 (tf19_decode_zero 8 2 _) [⟨(0x22efd, 0x2012e), by decide +kernel⟩, ⟨(0x5f32e, 0x1d600), by decide +kernel⟩, ⟨(0x15d2f, 0x67709), by decide +kernel⟩],
   gridInput hopperTF32MmaF32 (tf19_decode_zero 8 2 _) [⟨(0x15e00, 0x5ff8e), by decide +kernel⟩, ⟨(0x60725, 0x27488), by decide +kernel⟩, ⟨(0x610ba, 0x6031a), by decide +kernel⟩]]

theorem h100tf32m_table2 : ((MMAlgebra.codes2All.filter fun κ =>
    MMAlgebra.rvalid (MMAlgebra.LTree.realize2 κ 0 1)).map fun κ => h100tf32mIn2.map fun q =>
      MMAlgebra.evR ((tcMachine hopperTF32MmaF32).sub (GridOK hopperTF32MmaF32)) hopperTF32MmaF32.nfma q (MMAlgebra.LTree.realize2 κ 0 1)).Nodup := by
  decide +kernel

theorem h100tf32m_table3 : ((MMAlgebra.codes3All.filter fun κ => MMAlgebra.rvalid (κ.realize 0 1 2)).map
    fun κ => h100tf32mIn3.map fun q =>
      MMAlgebra.evR ((tcMachine hopperTF32MmaF32).sub (GridOK hopperTF32MmaF32)) hopperTF32MmaF32.nfma q (κ.realize 0 1 2)).Nodup := by
  decide +kernel

/-- **H100 (tf32, mma): on inputs with products on the binary32 grid, terms are equivalent exactly when their
normal forms agree.** -/
theorem h100tf32m_term_equiv_iff (t₁ t₂ : MMAlgebra.Term) (hw₁ : MMAlgebra.TermWF 8 t₁)
    (hw₂ : MMAlgebra.TermWF 8 t₂) (n₁ : t₁.leaves.Nodup) (n₂ : t₂.leaves.Nodup)
    (hl : ∀ i, i ∈ t₁.leaves ↔ i ∈ t₂.leaves) :
    (∀ q : ℕ → hopperTF32MmaF32.Word × hopperTF32MmaF32.Word, (∀ i, GridOK hopperTF32MmaF32 (q i)) →
      MMAlgebra.eval (tcMachine hopperTF32MmaF32) q 0 0 t₁ = MMAlgebra.eval (tcMachine hopperTF32MmaF32) q 0 0 t₂) ↔
      MMAlgebra.nfR t₁ = MMAlgebra.nfR t₂ :=
  tc_sub_term_equiv_iff hopperTF32MmaF32 (by decide) (by decide) (by simp [hopperTF32MmaF32, tf19Fp32Model]) (tf19_decode_zero 8 2 _) h100tf32mIn2 h100tf32mIn3
    h100tf32m_table2 h100tf32m_table3 t₁ t₂ hw₁ hw₂ n₁ n₂ hl

end MMAlgebra.TC
