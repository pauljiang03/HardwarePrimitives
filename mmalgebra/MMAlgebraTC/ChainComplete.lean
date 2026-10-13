import MMAlgebra.ChainComplete
import MMAlgebraTC.NegZero
import MMAlgebraTC.Completeness
import MMAlgebraTC.Exact

/-! # Completeness for chains on the Tensor Core models

The laws of `MMAlgebra.RigidLaws` hold for the Tensor Core model as a machine (`tcMachine`): an
empty slot is the zero pair, a block depends on its products as a multiset (`evalBlock_bits_perm`),
and an empty block passes a finite accumulator other than `−0` through
(`zero_products_passthrough`). On the fp16 models every block output is such a value
(`blockOut_ne_negZero`), so the generic theorems of `MMAlgebra.ChainComplete` apply: with the
kernel-checked base witnesses of `v100_complete_pair`, `a100_complete_pair` and
`h100_complete_pair`, two chains from `+0` over the same products are equivalent on V100, A100 and
H100 exactly when they have the same ordered partition (`v100_chain_equiv_iff`,
`a100_chain_equiv_iff`, `h100_chain_equiv_iff`). -/

open TensorCore

namespace MMAlgebra.TC

theorem tc_slotZero (p : Model) : MMAlgebra.SlotZero (tcMachine p) (0, 0) := by
  intro d ps qs h
  show (blockOut (p := p) ⟨slotPairs p ps, d⟩).toOption = (blockOut ⟨slotPairs p qs, d⟩).toOption
  unfold slotPairs; rw [h]

theorem tc_perm (p : Model) (d : F32) {ps qs : List (Option (p.Word × p.Word))} (h : ps.Perm qs) :
    (tcMachine p).block d ps = (tcMachine p).block d qs := by
  show (blockOut (p := p) ⟨slotPairs p ps, d⟩).toOption = (blockOut ⟨slotPairs p qs, d⟩).toOption
  unfold slotPairs
  rw [evalBlock_bits_perm (h.map _)]

theorem tc_pass (K neab : ℕ) (eAlignMin : Option ℤ) (hfl : ∀ f ∈ eAlignMin, f ≤ -126) (d : F32)
    (hd : Good d) :
    (tcMachine (fp16Fp32Model K neab eAlignMin)).block d (List.replicate K none) = some d := by
  obtain ⟨hfs, hneg⟩ := hd
  obtain ⟨f, hf⟩ := Option.isSome_iff_exists.mp hfs
  obtain ⟨t, ht, hbits⟩ := zero_products_passthrough K neab eAlignMin hfl d f hf hneg
  show (blockOut (p := fp16Fp32Model K neab eAlignMin)
    ⟨slotPairs _ (List.replicate K none), d⟩).toOption = some d
  have : slotPairs (fp16Fp32Model K neab eAlignMin) (List.replicate K none) =
      List.replicate K (0, 0) := by
    simp [slotPairs, List.map_replicate]
  rw [this]
  unfold blockOut
  rw [ht]
  show (Except.ok t.output.bits : Except ModelError F32).toOption = some d
  rw [hbits]; rfl

/-- The laws of a rigid matrix multiplier, for the fp16 Tensor Core models. -/
def fp16Laws (K neab : ℕ) (eAlignMin : Option ℤ) (hfl : ∀ f ∈ eAlignMin, f ≤ -126) :
    MMAlgebra.RigidLaws (tcMachine (fp16Fp32Model K neab eAlignMin)) K where
  z := (0, 0)
  good := Good
  slot := tc_slotZero _
  perm := tc_perm _
  zero_good := by show Good 0; decide
  pass := tc_pass K neab eAlignMin hfl

/-- Every fp16 block output is a finite value other than `−0`. -/
theorem blockOut_good {K neab : ℕ} {eAlignMin : Option ℤ}
    {x : BlockInput (fp16Fp32Model K neab eAlignMin)} {d : F32} (h : blockOut x = .ok d) :
    Good d := by
  refine ⟨?_, blockOut_ne_negZero h⟩
  unfold blockOut at h
  cases ht : evalBlock x with
  | error e => rw [ht] at h; simp [Except.map] at h
  | ok t =>
    rw [ht] at h
    simp only [Except.map, Except.ok.injEq] at h
    subst h
    rw [finite32_self]; rfl

theorem fp16_block_good (K neab : ℕ) (eAlignMin : Option ℤ) (d : F32)
    (ps : List (Option ((fp16Fp32Model K neab eAlignMin).Word × (fp16Fp32Model K neab eAlignMin).Word)))
    (o : F32) (h : (tcMachine (fp16Fp32Model K neab eAlignMin)).block d ps = some o) : Good o := by
  have h' : (blockOut (p := fp16Fp32Model K neab eAlignMin) ⟨slotPairs _ ps, d⟩).toOption = some o := h
  cases hb : blockOut (p := fp16Fp32Model K neab eAlignMin) ⟨slotPairs _ ps, d⟩ with
  | error e => rw [hb] at h'; simp [Except.toOption] at h'
  | ok o' =>
    rw [hb] at h'
    simp only [Except.toOption, Option.some.injEq] at h'
    subst h'
    exact blockOut_good hb

/-! ## Base witnesses -/

/-- V100: the products `x = 0.0066986… × 0.0047111…` and `y = 56224 × (105 · 2^-24)` of
`v100_complete_pair`: `[x] [y]` and `[x y]` give `0x3eb42d60`, `[y] [x]` gives `0x3eb42d62`. -/
def v100Witness : MMAlgebra.PairWitness (fp16Laws 4 0 none (by simp)) where
  a := (0x1edc, 0x1cd3)
  b := (0x7add, 0x69)
  vx := 0x38045d50
  vy := 0x3eb42940
  vxy := 0x3eb42d60
  vlt := 0x3eb42d60
  vgt := 0x3eb42d62
  e₁ := by decide +kernel
  e₂ := by decide +kernel
  e₃ := by decide +kernel
  e₄ := by decide +kernel
  e₅ := by decide +kernel
  g₁ := by show Good _; decide
  g₂ := by show Good _; decide
  g₃ := by show Good _; decide
  g₄ := by show Good _; decide
  g₅ := by show Good _; decide
  sep := by decide

/-- A100: the same words as on V100. -/
def a100Witness : MMAlgebra.PairWitness (fp16Laws 8 1 (some (-132)) (by simp)) where
  a := (0x1edc, 0x1cd3)
  b := (0x7add, 0x69)
  vx := 0x38045d50
  vy := 0x3eb42940
  vxy := 0x3eb42d60
  vlt := 0x3eb42d60
  vgt := 0x3eb42d62
  e₁ := by decide +kernel
  e₂ := by decide +kernel
  e₃ := by decide +kernel
  e₄ := by decide +kernel
  e₅ := by decide +kernel
  g₁ := by show Good _; decide
  g₂ := by show Good _; decide
  g₃ := by show Good _; decide
  g₄ := by show Good _; decide
  g₅ := by show Good _; decide
  sep := by decide

/-- H100: `x = 0x0052 × 0x6587`, `y = 0x0ba7 × 0x3ff9`; `[x] [y]` is three units in the last place
above `[x y] = [y] [x]`. -/
def h100Witness : MMAlgebra.PairWitness (fp16Laws 16 2 (some (-133)) (by simp)) where
  a := (0x52, 0x6587)
  b := (0xba7, 0x3ff9)
  vx := 0x3be29f00
  vy := 0x39f409bc
  vxy := 0x3bf1df98
  vlt := 0x3bf1df9b
  vgt := 0x3bf1df98
  e₁ := by decide +kernel
  e₂ := by decide +kernel
  e₃ := by decide +kernel
  e₄ := by decide +kernel
  e₅ := by decide +kernel
  g₁ := by show Good _; decide
  g₂ := by show Good _; decide
  g₃ := by show Good _; decide
  g₄ := by show Good _; decide
  g₅ := by show Good _; decide
  sep := by decide

/-! ## Chains are equivalent exactly when their ordered partitions agree -/

/-- **V100 (fp16).** Two chains from `+0` with blocks of 4 slots over the same products, each
product once, give the same output word on every input if and only if they have the same ordered
partition. -/
theorem v100_chain_equiv_iff (σ τ : MMAlgebra.Chain) (hσ : ∀ B ∈ σ, B.length = 4)
    (hτ : ∀ B ∈ τ, B.length = 4) (nσ : σ.leaves.Nodup) (nτ : τ.leaves.Nodup)
    (hl : ∀ i, i ∈ σ.leaves ↔ i ∈ τ.leaves) :
    (∀ p, MMAlgebra.runChain (tcMachine v100F16F32) p 0 σ =
        MMAlgebra.runChain (tcMachine v100F16F32) p 0 τ) ↔ σ.nf = τ.nf :=
  MMAlgebra.chain_equiv_iff (fp16Laws 4 0 none (by simp)) (by decide) v100Witness
    (fp16_block_good 4 0 none) σ τ hσ hτ nσ nτ hl

/-- **A100 (fp16).** The same with blocks of 8 slots. -/
theorem a100_chain_equiv_iff (σ τ : MMAlgebra.Chain) (hσ : ∀ B ∈ σ, B.length = 8)
    (hτ : ∀ B ∈ τ, B.length = 8) (nσ : σ.leaves.Nodup) (nτ : τ.leaves.Nodup)
    (hl : ∀ i, i ∈ σ.leaves ↔ i ∈ τ.leaves) :
    (∀ p, MMAlgebra.runChain (tcMachine ampereF16F32) p 0 σ =
        MMAlgebra.runChain (tcMachine ampereF16F32) p 0 τ) ↔ σ.nf = τ.nf :=
  MMAlgebra.chain_equiv_iff (fp16Laws 8 1 (some (-132)) (by simp)) (by decide) a100Witness
    (fp16_block_good 8 1 (some (-132))) σ τ hσ hτ nσ nτ hl

/-- **H100 (fp16).** The same with blocks of 16 slots. -/
theorem h100_chain_equiv_iff (σ τ : MMAlgebra.Chain) (hσ : ∀ B ∈ σ, B.length = 16)
    (hτ : ∀ B ∈ τ, B.length = 16) (nσ : σ.leaves.Nodup) (nτ : τ.leaves.Nodup)
    (hl : ∀ i, i ∈ σ.leaves ↔ i ∈ τ.leaves) :
    (∀ p, MMAlgebra.runChain (tcMachine hopperF16F32) p 0 σ =
        MMAlgebra.runChain (tcMachine hopperF16F32) p 0 τ) ↔ σ.nf = τ.nf :=
  MMAlgebra.chain_equiv_iff (fp16Laws 16 2 (some (-133)) (by simp)) (by decide) h100Witness
    (fp16_block_good 16 2 (some (-133))) σ τ hσ hτ nσ nτ hl

end MMAlgebra.TC
