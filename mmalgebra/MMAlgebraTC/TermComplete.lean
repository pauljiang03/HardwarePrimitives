import MMAlgebra.Rigid
import MMAlgebraTC.ChainComplete

/-! # Completeness for terms on the Tensor Core models

The fp16 Tensor Core models satisfy every law of a rigid multiplier (`fp16Alg`): besides the block
laws used for chains, binary32 round-to-nearest addition is commutative, `+0` is its unit on
finite values other than `−0`, and it never returns `−0` (the sum of two binary32 values is a
multiple of `2^-149`, so it is zero or rounds to a nonzero value). By `MMAlgebra.rigid_sound` every
term evaluates as its rigid normal form, and kernel-checked fingerprint tables separate the four
valid normal forms on two products and the 28 on three products. By `MMAlgebra.rigid_term_complete`
two terms (any chains, split-K, stream-K, groupings and orders of block FMAs and binary32
additions, from `+0`) are equivalent on V100, A100 and H100 exactly when their normal forms agree
(`v100_term_equiv_iff`, `a100_term_equiv_iff`, `h100_term_equiv_iff`). -/

open TensorCore Ozaki.TC

namespace MMAlgebra.TC

/-! ## Binary32 addition on the Tensor Core machine -/

theorem tc_add_comm (p : Model) (x y : F32) : (tcMachine p).add x y = (tcMachine p).add y x := by
  show round32 .nearestEven (value32D x + value32D y) = round32 .nearestEven (value32D y + value32D x)
  rw [Rat.add_comm]

theorem value32D_zero : value32D (0 : F32) = 0 := by decide +kernel

theorem tc_add_zero (p : Model) (x : F32) (hx : Good x) : (tcMachine p).add x 0 = some x := by
  show round32 .nearestEven (value32D x + value32D 0) = some x
  rw [value32D_zero, Rat.add_zero]
  obtain ⟨hfs, hneg⟩ := hx
  obtain ⟨f, hf⟩ := Option.isSome_iff_exists.mp hfs
  have hv : value32 x = some f.value := by
    unfold value32; rw [← finite32_bits hf, f.valid]; rfl
  have hd : value32D x = f.value := by simp [value32D, hv]
  rw [hd]
  by_cases hz : f.value = 0
  · have hsig : f.decoded.significand = 0 := by
      apply Classical.byContradiction; intro h
      exact Decoded.value_ne_zero f.decoded h hz
    have h0 : x = 0 := zero_value_bits x f.decoded (by rw [← finite32_bits hf]; exact f.valid) hsig hneg
    rw [hz, h0]; decide +kernel
  · exact value32_round32 .nearestEven x f.value hv hz

/-- The sum of two binary32 values, rounded to nearest, is never `−0`. -/
theorem round32_rne_good {y : ℚ} (hg : OnGridQ y (-149)) {o : F32}
    (h : round32 .nearestEven y = some o) : Good o := by
  by_cases hy : y = 0
  · subst hy
    have h0 : round32 .nearestEven 0 = some (0 : F32) := by decide +kernel
    rw [h0] at h; cases h; decide
  · obtain ⟨b', hb', hv, _, _⟩ := round32_nonzero_spec .nearestEven y hy (round32_range h)
    rw [h] at hb'; cases hb'
    refine ⟨?_, ?_⟩
    · obtain ⟨f, hf, _, _⟩ := finite32_of_value32 _ _ hv
      rw [hf]; rfl
    · intro hneg
      rw [hneg] at hv
      have hv0 : value32 (0x80000000 : F32) = some 0 := by decide +kernel
      rw [hv0] at hv
      have hz : signedRounded .nearestEven y = 0 := (Option.some.inj hv).symm
      obtain ⟨k, rfl⟩ := hg
      have hk : k ≠ 0 := by intro h; subst h; simp at hy
      have hp := pow2_pos (-149)
      have hr := round32_range h
      rcases (by omega : 1 ≤ k ∨ k ≤ -1) with h1 | h1
      · have hn := signedRounded_nearest _ (pow2 (-149)) hy hr finiteValue32_pow2
        rw [hz, show ∀ q : ℚ, q - 0 = q from fun q => by grind] at hn
        have hk1 : (1 : ℚ) ≤ (k : ℚ) := by exact_mod_cast h1
        have e1 : absQ ((k : ℚ) * pow2 (-149)) = (k : ℚ) * pow2 (-149) :=
          absQ_of_nonneg (Rat.mul_nonneg (by grind) (Rat.le_of_lt hp))
        have e2 : absQ ((k : ℚ) * pow2 (-149) - pow2 (-149)) = ((k : ℚ) - 1) * pow2 (-149) := by
          rw [show (k : ℚ) * pow2 (-149) - pow2 (-149) = ((k : ℚ) - 1) * pow2 (-149) by grind]
          exact absQ_of_nonneg (Rat.mul_nonneg (by grind) (Rat.le_of_lt hp))
        rw [e1, e2] at hn
        grind
      · have hfin : FiniteValue32 (-pow2 (-149)) :=
          ⟨-1, -126, by decide, by decide, by decide, by simp; grind⟩
        have hn := signedRounded_nearest _ (-pow2 (-149)) hy hr hfin
        rw [hz, show ∀ q : ℚ, q - 0 = q from fun q => by grind] at hn
        have hk1 : (k : ℚ) ≤ -1 := by
          have : (k : ℚ) ≤ ((-1 : ℤ) : ℚ) := Rat.intCast_le_intCast.mpr h1
          simpa using this
        have e1 : absQ ((k : ℚ) * pow2 (-149)) = -((k : ℚ) * pow2 (-149)) := by
          rw [← absQ_neg]
          exact absQ_of_nonneg (by
            rw [show -((k : ℚ) * pow2 (-149)) = (-(k : ℚ)) * pow2 (-149) by grind]
            exact Rat.mul_nonneg (by grind) (Rat.le_of_lt hp))
        have e2 : absQ ((k : ℚ) * pow2 (-149) - -pow2 (-149)) = -(((k : ℚ) + 1) * pow2 (-149)) := by
          rw [← absQ_neg]
          rw [show -((k : ℚ) * pow2 (-149) - -pow2 (-149)) = (-((k : ℚ) + 1)) * pow2 (-149) by grind]
          rw [absQ_of_nonneg (Rat.mul_nonneg (by grind) (Rat.le_of_lt hp))]
          grind
        rw [e1, e2] at hn
        grind

theorem value32D_onGridQ (x : F32) : OnGridQ (value32D x) (-149) := by
  unfold value32D
  cases h : value32 x with
  | none => exact onGridQ_zero _
  | some v =>
    simp only [Option.getD_some]
    unfold value32 at h
    cases hd : decode32 x with
    | none => rw [hd] at h; cases h
    | some d =>
      rw [hd] at h; simp only [Option.map_some, Option.some.injEq] at h
      rw [← h]; exact decode32_onGridQ hd

theorem tc_add_good (p : Model) (x y o : F32) (h : (tcMachine p).add x y = some o) : Good o :=
  round32_rne_good (onGridQ_add (value32D_onGridQ x) (value32D_onGridQ y)) h

/-- The laws of a rigid multiplier, for the fp16 Tensor Core models. -/
def fp16Alg (K padding : ℕ) (eAlignMin : Option ℤ) (hfl : ∀ f ∈ eAlignMin, f ≤ -126) :
    MMAlgebra.RigidAlg (tcMachine (fp16Fp32Model K padding eAlignMin)) K :=
  { fp16Laws K padding eAlignMin hfl with
    add_comm := tc_add_comm _
    add_zero := fun x hx => tc_add_zero _ x hx
    block_good := fp16_block_good K padding eAlignMin
    add_good := tc_add_good _ }

/-! ## Fingerprint tables -/

/-- An input with the operand pairs of a list at `0, 1, 2, …` and zero pairs elsewhere. -/
def wordsInput (ws : List (F16 × F16)) : ℕ → F16 × F16 := fun j => ws.getD j (0, 0)

/-- V100: inputs on two products that separate the four valid normal forms. -/
def v100In2 : List (ℕ → F16 × F16) :=
  [wordsInput [(0x3a00, 0xc736), (0x5600, 0x5f00)], wordsInput [(0x3749, 0x9436), (0x4bc1, 0x91c7)],
   wordsInput [(0x65e1, 0xcbd0), (0x9006, 0xc99a)]]

/-- V100: inputs on three products that separate the 28 valid normal forms. -/
def v100In3 : List (ℕ → F16 × F16) :=
  [wordsInput [(0x84ce, 0xb7c5), (0x814e, 0xd12d), (0x95cf, 0x379e)],
   wordsInput [(0xced7, 0xbbe3), (0xd329, 0x92af), (0xcb8f, 0xe795)],
   wordsInput [(0x86d6, 0xb7c5), (0x33a6, 0x8022), (0x8272, 0x6818)],
   wordsInput [(0x3f98, 0xeba6), (0xbf81, 0xb782), (0x60b7, 0x1719)],
   wordsInput [(0xa295, 0x4b2e), (0x47d8, 0xcd1c), (0xa5e8, 0xc171)],
   wordsInput [(0x1098, 0xe4ce), (0x3fa0, 0x8b79), (0xd3a6, 0xc3d4)]]

theorem v100_table2 : ((MMAlgebra.codes2All.filter fun κ => MMAlgebra.rvalid (MMAlgebra.LTree.realize2 κ 0 1)).map
    fun κ => v100In2.map fun q => MMAlgebra.evR (tcMachine v100F16F32) 4 q (MMAlgebra.LTree.realize2 κ 0 1)).Nodup := by
  decide +kernel

theorem v100_table3 : ((MMAlgebra.codes3All.filter fun κ => MMAlgebra.rvalid (κ.realize 0 1 2)).map
    fun κ => v100In3.map fun q => MMAlgebra.evR (tcMachine v100F16F32) 4 q (κ.realize 0 1 2)).Nodup := by
  decide +kernel

/-- A100: inputs on two products. -/
def a100In2 : List (ℕ → F16 × F16) :=
  [wordsInput [(0x6210, 0x26e6), (0xba62, 0x2829)], wordsInput [(0x9102, 0x3ff2), (0x78e1, 0x07c5)]]

/-- A100: inputs on three products. -/
def a100In3 : List (ℕ → F16 × F16) :=
  [wordsInput [(0x2c96, 0x3bca), (0xbb85, 0x8a91), (0xdca8, 0x0b18)],
   wordsInput [(0x88af, 0xb619), (0xc302, 0x885d), (0x3bab, 0x3fad)],
   wordsInput [(0x977e, 0xb7f0), (0x869f, 0x4bec), (0x097e, 0x8496)],
   wordsInput [(0xb3f6, 0x7a4b), (0x498f, 0x019b), (0x3848, 0x8d32)],
   wordsInput [(0x2ca8, 0x33e4), (0x33ab, 0xb3f7), (0xb0dd, 0xc3bb)],
   wordsInput [(0x0d18, 0xc706), (0xe7ad, 0xc100), (0xa263, 0x9951)],
   wordsInput [(0x8523, 0x7a22), (0x0a63, 0x66eb), (0xbcb6, 0xe79d)],
   wordsInput [(0x0a6e, 0x7a45), (0xfa60, 0xbbbb), (0xcb91, 0x0ddb)]]

/-- H100: inputs on two products. -/
def h100In2 : List (ℕ → F16 × F16) :=
  [wordsInput [(0x7977, 0x8f7a), (0xbbd1, 0xaa05)], wordsInput [(0x2ecc, 0x8600), (0xb600, 0xbe00)]]

/-- H100: inputs on three products. -/
def h100In3 : List (ℕ → F16 × F16) :=
  [wordsInput [(0x8019, 0xe2b5), (0xb389, 0x8f28), (0x059b, 0x8288)],
   wordsInput [(0x0a7e, 0xbb3f), (0x78c3, 0x802b), (0xc42a, 0x9bee)],
   wordsInput [(0x3fd4, 0xc445), (0x80e7, 0x4cdb), (0x7827, 0x27be)],
   wordsInput [(0x0200, 0x241c), (0xc2e7, 0xc658), (0x19bc, 0x2c3e)]]

theorem a100_table2 : ((MMAlgebra.codes2All.filter fun κ => MMAlgebra.rvalid (MMAlgebra.LTree.realize2 κ 0 1)).map
    fun κ => a100In2.map fun q => MMAlgebra.evR (tcMachine ampereF16F32) 8 q (MMAlgebra.LTree.realize2 κ 0 1)).Nodup := by
  decide +kernel

theorem a100_table3 : ((MMAlgebra.codes3All.filter fun κ => MMAlgebra.rvalid (κ.realize 0 1 2)).map
    fun κ => a100In3.map fun q => MMAlgebra.evR (tcMachine ampereF16F32) 8 q (κ.realize 0 1 2)).Nodup := by
  decide +kernel

theorem h100_table2 : ((MMAlgebra.codes2All.filter fun κ => MMAlgebra.rvalid (MMAlgebra.LTree.realize2 κ 0 1)).map
    fun κ => h100In2.map fun q => MMAlgebra.evR (tcMachine hopperF16F32) 16 q (MMAlgebra.LTree.realize2 κ 0 1)).Nodup := by
  decide +kernel

theorem h100_table3 : ((MMAlgebra.codes3All.filter fun κ => MMAlgebra.rvalid (κ.realize 0 1 2)).map
    fun κ => h100In3.map fun q => MMAlgebra.evR (tcMachine hopperF16F32) 16 q (κ.realize 0 1 2)).Nodup := by
  decide +kernel

/-! ## Terms are equivalent exactly when their normal forms agree -/

/-- **V100 (fp16), completeness for terms.** Two terms from `+0` with blocks of 4 slots (any chain,
split-K, stream-K, grouping and order of block FMAs and binary32 additions) over the same products,
each once, with different normal forms differ on an input that is zero outside at most three of
the products. -/
theorem v100_term_complete (t₁ t₂ : MMAlgebra.Term) (hw₁ : MMAlgebra.TermWF 4 t₁)
    (hw₂ : MMAlgebra.TermWF 4 t₂) (n₁ : t₁.leaves.Nodup) (n₂ : t₂.leaves.Nodup)
    (hl : ∀ i, i ∈ t₁.leaves ↔ i ∈ t₂.leaves) (hne : MMAlgebra.nfR t₁ ≠ MMAlgebra.nfR t₂) :
    ∃ (s : List ℕ) (q : ℕ → F16 × F16), s.length ≤ 3 ∧ (∀ i, i ∉ s → q i = (0, 0)) ∧
      MMAlgebra.eval (tcMachine v100F16F32) q 0 0 t₁ ≠ MMAlgebra.eval (tcMachine v100F16F32) q 0 0 t₂ :=
  MMAlgebra.rigid_term_complete (fp16Alg 4 0 none (by simp)) v100In2 v100In3 v100_table2 v100_table3
    t₁ t₂ hw₁ hw₂ n₁ n₂ hl hne

/-- **A100 (fp16), completeness for terms**, with blocks of 8 slots. -/
theorem a100_term_complete (t₁ t₂ : MMAlgebra.Term) (hw₁ : MMAlgebra.TermWF 8 t₁)
    (hw₂ : MMAlgebra.TermWF 8 t₂) (n₁ : t₁.leaves.Nodup) (n₂ : t₂.leaves.Nodup)
    (hl : ∀ i, i ∈ t₁.leaves ↔ i ∈ t₂.leaves) (hne : MMAlgebra.nfR t₁ ≠ MMAlgebra.nfR t₂) :
    ∃ (s : List ℕ) (q : ℕ → F16 × F16), s.length ≤ 3 ∧ (∀ i, i ∉ s → q i = (0, 0)) ∧
      MMAlgebra.eval (tcMachine ampereF16F32) q 0 0 t₁ ≠
        MMAlgebra.eval (tcMachine ampereF16F32) q 0 0 t₂ :=
  MMAlgebra.rigid_term_complete (fp16Alg 8 1 (some (-132)) (by simp)) a100In2 a100In3 a100_table2
    a100_table3 t₁ t₂ hw₁ hw₂ n₁ n₂ hl hne

/-- **H100 (fp16), completeness for terms**, with blocks of 16 slots. -/
theorem h100_term_complete (t₁ t₂ : MMAlgebra.Term) (hw₁ : MMAlgebra.TermWF 16 t₁)
    (hw₂ : MMAlgebra.TermWF 16 t₂) (n₁ : t₁.leaves.Nodup) (n₂ : t₂.leaves.Nodup)
    (hl : ∀ i, i ∈ t₁.leaves ↔ i ∈ t₂.leaves) (hne : MMAlgebra.nfR t₁ ≠ MMAlgebra.nfR t₂) :
    ∃ (s : List ℕ) (q : ℕ → F16 × F16), s.length ≤ 3 ∧ (∀ i, i ∉ s → q i = (0, 0)) ∧
      MMAlgebra.eval (tcMachine hopperF16F32) q 0 0 t₁ ≠
        MMAlgebra.eval (tcMachine hopperF16F32) q 0 0 t₂ :=
  MMAlgebra.rigid_term_complete (fp16Alg 16 2 (some (-133)) (by simp)) h100In2 h100In3 h100_table2
    h100_table3 t₁ t₂ hw₁ hw₂ n₁ n₂ hl hne

/-- **V100 (fp16): terms are equivalent exactly when their normal forms agree.** -/
theorem v100_term_equiv_iff (t₁ t₂ : MMAlgebra.Term) (hw₁ : MMAlgebra.TermWF 4 t₁)
    (hw₂ : MMAlgebra.TermWF 4 t₂) (n₁ : t₁.leaves.Nodup) (n₂ : t₂.leaves.Nodup)
    (hl : ∀ i, i ∈ t₁.leaves ↔ i ∈ t₂.leaves) :
    (∀ q, MMAlgebra.eval (tcMachine v100F16F32) q 0 0 t₁ = MMAlgebra.eval (tcMachine v100F16F32) q 0 0 t₂) ↔
      MMAlgebra.nfR t₁ = MMAlgebra.nfR t₂ := by
  constructor
  · intro h
    apply Classical.byContradiction; intro hne
    obtain ⟨_, q, _, _, hq⟩ := v100_term_complete t₁ t₂ hw₁ hw₂ n₁ n₂ hl hne
    exact hq (h q)
  · intro h q
    have e₁ := MMAlgebra.rigid_sound (fp16Alg 4 0 none (by simp)) q t₁ hw₁ n₁
    have e₂ := MMAlgebra.rigid_sound (fp16Alg 4 0 none (by simp)) q t₂ hw₂ n₂
    rw [h] at e₁
    exact e₁.trans e₂.symm

/-- **A100 (fp16): terms are equivalent exactly when their normal forms agree.** -/
theorem a100_term_equiv_iff (t₁ t₂ : MMAlgebra.Term) (hw₁ : MMAlgebra.TermWF 8 t₁)
    (hw₂ : MMAlgebra.TermWF 8 t₂) (n₁ : t₁.leaves.Nodup) (n₂ : t₂.leaves.Nodup)
    (hl : ∀ i, i ∈ t₁.leaves ↔ i ∈ t₂.leaves) :
    (∀ q, MMAlgebra.eval (tcMachine ampereF16F32) q 0 0 t₁ =
        MMAlgebra.eval (tcMachine ampereF16F32) q 0 0 t₂) ↔ MMAlgebra.nfR t₁ = MMAlgebra.nfR t₂ := by
  constructor
  · intro h
    apply Classical.byContradiction; intro hne
    obtain ⟨_, q, _, _, hq⟩ := a100_term_complete t₁ t₂ hw₁ hw₂ n₁ n₂ hl hne
    exact hq (h q)
  · intro h q
    have e₁ := MMAlgebra.rigid_sound (fp16Alg 8 1 (some (-132)) (by simp)) q t₁ hw₁ n₁
    have e₂ := MMAlgebra.rigid_sound (fp16Alg 8 1 (some (-132)) (by simp)) q t₂ hw₂ n₂
    rw [h] at e₁
    exact e₁.trans e₂.symm

/-- **H100 (fp16): terms are equivalent exactly when their normal forms agree.** -/
theorem h100_term_equiv_iff (t₁ t₂ : MMAlgebra.Term) (hw₁ : MMAlgebra.TermWF 16 t₁)
    (hw₂ : MMAlgebra.TermWF 16 t₂) (n₁ : t₁.leaves.Nodup) (n₂ : t₂.leaves.Nodup)
    (hl : ∀ i, i ∈ t₁.leaves ↔ i ∈ t₂.leaves) :
    (∀ q, MMAlgebra.eval (tcMachine hopperF16F32) q 0 0 t₁ =
        MMAlgebra.eval (tcMachine hopperF16F32) q 0 0 t₂) ↔ MMAlgebra.nfR t₁ = MMAlgebra.nfR t₂ := by
  constructor
  · intro h
    apply Classical.byContradiction; intro hne
    obtain ⟨_, q, _, _, hq⟩ := h100_term_complete t₁ t₂ hw₁ hw₂ n₁ n₂ hl hne
    exact hq (h q)
  · intro h q
    have e₁ := MMAlgebra.rigid_sound (fp16Alg 16 2 (some (-133)) (by simp)) q t₁ hw₁ n₁
    have e₂ := MMAlgebra.rigid_sound (fp16Alg 16 2 (some (-133)) (by simp)) q t₂ hw₂ n₂
    rw [h] at e₁
    exact e₁.trans e₂.symm

end MMAlgebra.TC
