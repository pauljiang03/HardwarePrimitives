import MMAlgebraTC.ChainComplete
import MMAlgebraTC.Pinned

/-! # Completeness for chains on the bf16 and tf32 Tensor Core models

An empty block FMA passes a finite accumulator other than `−0` through on every Tensor Core model
with at least 23 fractional alignment bits, a binary32 block output and a minimum alignment exponent
at most `−126` whose zero word decodes to zero (`tc_pass_any`): the accumulator is the only nonzero term, it sets the
alignment exponent, and it lies on the alignment grid. With the multiset law, these are the laws
that chain completeness uses (`tcLaws`), and kernel-checked base witnesses give completeness for
chains on A100 and H100 bf16 and on A100 and H100 tf32 (`a100bf16_chain_complete`, …). On these
formats a block can return `−0` (a tiny negative product truncated to zero), so an empty block is
not invisible after such a block; completeness does not need it. -/

open TensorCore Ozaki Ozaki.TC

namespace MMAlgebra.TC

/-- **An empty block passes a good accumulator through**, on any Tensor Core model with
`F ≥ 23`, a binary32 block output, a minimum alignment exponent at most `−126`, and a zero word that
decodes to zero. -/
theorem tc_pass_any (p : Model) (hF : 23 ≤ p.alignFracBits)
    (hout : 23 ≤ p.outputFracBits) (hmin : ∀ f ∈ p.eAlignMin, f ≤ -126)
    (hz : p.decode 0 = some ⟨0, 0, 0⟩) (d : F32) (hd : Good d) :
    (tcMachine p).block d (List.replicate p.nfma none) = some d := by
  obtain ⟨hfs, hneg⟩ := hd
  obtain ⟨f, hf⟩ := Option.isSome_iff_exists.mp hfs
  have hc : decode32 d = some f.decoded := by rw [← finite32_bits hf]; exact f.valid
  have hslot : slotPairs p (List.replicate p.nfma none) = List.replicate p.nfma (0, 0) := by
    simp [slotPairs]
  have hps := prepareProducts_replicate p 0 0 ⟨0, 0, 0⟩ ⟨0, 0, 0⟩ p.nfma hz hz
  have hterms : (PreparedBlock.mk p (List.replicate p.nfma (⟨0, 0, 0⟩, ⟨0, 0, 0⟩)) f.decoded).terms =
      ⟨f.decoded.significand, f.decoded.exponent, f.decoded.mantissaBits⟩ ::
        List.replicate p.nfma ⟨0, 0, 0⟩ := by
    simp [PreparedBlock.terms, List.map_replicate, denormalizedMul]
  have hacc : (PreparedBlock.mk p (List.replicate p.nfma (⟨0, 0, 0⟩, ⟨0, 0, 0⟩)) f.decoded).accumulator =
      f.value := by
    rw [accumulator_value, hterms, sumQ_eq]
    simp only [List.map_cons, List.map_replicate, List.sum_cons]
    have h0 : ∀ g : ℤ, truncGrid (DenormalizedProduct.value ⟨0, 0, 0⟩) g = 0 := by
      intro g
      have : DenormalizedProduct.value ⟨0, 0, 0⟩ = 0 := by simp [DenormalizedProduct.value]
      rw [this, truncGrid_zero]
    have hr : ∀ n : ℕ, (List.replicate n (0 : ℚ)).sum = 0 := by
      intro n; induction n with
      | zero => rfl
      | succ n ih => rw [List.replicate_succ, List.sum_cons, ih, Rat.add_zero]
    rw [h0, hr, Rat.add_zero]
    show truncGrid f.decoded.value _ = f.decoded.value
    by_cases hsig : f.decoded.significand = 0
    · have hv : f.decoded.value = 0 := by simp [Decoded.value, hsig]
      rw [hv, truncGrid_zero]
    · obtain ⟨hmb, hlow⟩ : f.decoded.mantissaBits = 23 ∧ -126 ≤ f.decoded.exponent := by
        rcases decode32_fields d f.decoded hc with ⟨_, _, h0⟩ | ⟨_, _, h0⟩ | ⟨hE1, _, h0⟩
        · rw [h0] at hsig; exact absurd rfl hsig
        · rw [h0]; exact ⟨rfl, Int.le_refl _⟩
        · rw [h0]; exact ⟨rfl, by simp; omega⟩
      have hexp : (PreparedBlock.mk p (List.replicate p.nfma (⟨0, 0, 0⟩, ⟨0, 0, 0⟩)) f.decoded).alignExp =
          some f.decoded.exponent := by
        apply alignExp_eq _ _ (fun g hg => by have := hmin g hg; omega)
        · intro u hu hnz
          rw [hterms] at hu
          rcases List.mem_cons.mp hu with rfl | hu
          · exact Int.le_refl _
          · rw [List.mem_replicate] at hu; rw [hu.2] at hnz; exact absurd rfl hnz
        · exact ⟨_, by rw [hterms]; exact List.mem_cons_self, hsig, rfl⟩
      unfold PreparedBlock.alignGridExponent
      rw [hexp]
      simp only [Option.getD_some]
      obtain ⟨n, hn⟩ : ∃ n : ℕ, p.alignFracBits = 23 + n := ⟨(p.alignFracBits - 23).toNat, by omega⟩
      have hval : f.decoded.value = ((f.decoded.significand * ((2 ^ n : ℕ) : ℤ) : ℤ) : ℚ) *
          pow2 (f.decoded.exponent - p.alignFracBits) := by
        unfold Decoded.value
        rw [hmb, Rat.intCast_mul, Rat.intCast_natCast, ← pow2_natCast, Rat.mul_assoc, ← pow2_add]
        congr 2; omega
      rw [hval, truncGrid_fixed]
  have hrun : evalPrepared (PreparedBlock.mk p (List.replicate p.nfma (⟨0, 0, 0⟩, ⟨0, 0, 0⟩)) f.decoded) =
      .ok ⟨PreparedBlock.mk p (List.replicate p.nfma (⟨0, 0, 0⟩, ⟨0, 0, 0⟩)) f.decoded, f⟩ := by
    by_cases hsig : f.decoded.significand = 0
    · have hc0 : d = 0 := zero_value_bits d f.decoded hc hsig hneg
      have hv : f.value = 0 := by simp [Finite32.value, Decoded.value, hsig]
      have hr : round32 .truncate 0 = some (0 : F32) := by decide +kernel
      have hf0 : finite32 (0 : F32) = some f := by rw [← hc0]; exact hf
      simp only [evalPrepared, hacc, hv, hr, truncateFraction32_of_le hout, hf0]
    · have hv : f.value ≠ 0 := Decoded.value_ne_zero f.decoded hsig
      have hval32 : value32 d = some f.value := by unfold value32; rw [hc]; rfl
      have hr := value32_round32 .truncate d f.value hval32 hv
      simp only [evalPrepared, hacc, hr, truncateFraction32_of_le hout, hf]
  show (blockOut (p := p) ⟨slotPairs p (List.replicate p.nfma none), d⟩).toOption = some d
  rw [hslot]
  unfold blockOut evalBlock
  rw [if_neg (by simp)]
  simp only [prepare, hc, hps, hrun]
  show some f.bits = some d
  rw [finite32_bits hf]

/-- The laws of a rigid multiplier for chains, on a Tensor Core model with the conditions of
`tc_pass_any`. -/
def tcLaws (p : Model) (hF : 23 ≤ p.alignFracBits)
    (hout : 23 ≤ p.outputFracBits) (hmin : ∀ f ∈ p.eAlignMin, f ≤ -126)
    (hz : p.decode 0 = some ⟨0, 0, 0⟩) : MMAlgebra.RigidLaws (tcMachine p) p.nfma where
  z := (0, 0)
  good := Good
  slot := tc_slotZero p
  perm := tc_perm p
  zero_good := by show Good 0; decide
  pass := tc_pass_any p hF hout hmin hz

/-! ## Base witnesses -/

theorem bf16_decode_zero (K neab : ℕ) (e : Option ℤ) :
    (bf16Fp32Model K neab e).decode 0 = some ⟨0, 0, 0⟩ := by
  show (classify bf16 0).finite = some _; decide +kernel

theorem tf19_decode_zero (K neab : ℕ) (e : Option ℤ) :
    (tf19Fp32Model K neab e).decode 0 = some ⟨0, 0, 0⟩ := by
  show (classify tf19 0).finite = some _; decide +kernel

def a100bf16Laws := tcLaws a100BF16F32 (by decide) (by decide) (by simp [a100BF16F32, bf16Fp32Model]) (bf16_decode_zero 8 1 _)
def h100bf16Laws := tcLaws hopperBF16F32 (by decide) (by decide) (by simp [hopperBF16F32, bf16Fp32Model]) (bf16_decode_zero 16 2 _)
def a100tf32Laws := tcLaws a100TF32F32 (by decide) (by decide) (by simp [a100TF32F32, tf19Fp32Model]) (tf19_decode_zero 4 1 _)
def h100tf32wLaws := tcLaws hopperTF32WmmaF32 (by decide) (by decide) (by simp [hopperTF32WmmaF32, tf19Fp32Model])
  (tf19_decode_zero 4 2 _)
def h100tf32mLaws := tcLaws hopperTF32MmaF32 (by decide) (by decide) (by simp [hopperTF32MmaF32, tf19Fp32Model])
  (tf19_decode_zero 8 2 _)

def a100bf16Witness : MMAlgebra.PairWitness a100bf16Laws where
  a := (0xb830, 0xcfe5)
  b := (0x3b8f, 0xc00d)
  vx := 0x489d7000
  vy := 0xbc1d8600
  vxy := 0x489d6fff
  vlt := 0x489d7000
  vgt := 0x489d6fff
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

def h100bf16Witness : MMAlgebra.PairWitness h100bf16Laws where
  a := (0xbe73, 0xbd25)
  b := (0x43e0, 0xc0d2)
  vx := 0x3c1c9f00
  vy := 0xc537c000
  vxy := 0xc537bfd8
  vlt := 0xc537bfd8
  vgt := 0xc537bfd9
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

def a100tf32Witness : MMAlgebra.PairWitness a100tf32Laws where
  a := (0x1fa00, 0x5fb48)
  b := (0x18bd0, 0x22da3)
  vx := 0xbf2ec000
  vy := 0x37b025c0
  vxy := 0xbf2ebe9f
  vlt := 0xbf2ebea0
  vgt := 0xbf2ebe9f
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

def h100tf32wWitness : MMAlgebra.PairWitness h100tf32wLaws where
  a := (0x607d8, 0x20bd7)
  b := (0x5ccb5, 0x5f7ba)
  vx := 0xc2f5f9a0
  vy := 0x39117a08
  vxy := 0xc2f5f98d
  vlt := 0xc2f5f98e
  vgt := 0xc2f5f98d
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

def h100tf32mWitness : MMAlgebra.PairWitness h100tf32mLaws where
  a := (0x65d77, 0x5df62)
  b := (0x1e8ce, 0x5ec1e)
  vx := 0x48216238
  vy := 0xbb1e4120
  vxy := 0x48216237
  vlt := 0x48216238
  vgt := 0x48216237
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

/-! ## Completeness for chains -/

/-- **A100 bf16, completeness for chains.** -/
theorem a100bf16_chain_complete (σ τ : MMAlgebra.Chain) (hσ : ∀ B ∈ σ, B.length = 8)
    (hτ : ∀ B ∈ τ, B.length = 8) (nσ : σ.leaves.Nodup) (nτ : τ.leaves.Nodup)
    (hl : ∀ i, i ∈ σ.leaves ↔ i ∈ τ.leaves) (hne : σ.nf ≠ τ.nf) :
    ∃ (x y : ℕ) (q : ℕ → a100BF16F32.Word × a100BF16F32.Word), x ≠ y ∧
      (∀ i, i ≠ x → i ≠ y → q i = (0, 0)) ∧
      MMAlgebra.runChain (tcMachine a100BF16F32) q 0 σ ≠ MMAlgebra.runChain (tcMachine a100BF16F32) q 0 τ :=
  MMAlgebra.chain_complete a100bf16Laws (by decide) a100bf16Witness σ τ hσ hτ nσ nτ hl hne

/-- **H100 bf16, completeness for chains.** -/
theorem h100bf16_chain_complete (σ τ : MMAlgebra.Chain) (hσ : ∀ B ∈ σ, B.length = 16)
    (hτ : ∀ B ∈ τ, B.length = 16) (nσ : σ.leaves.Nodup) (nτ : τ.leaves.Nodup)
    (hl : ∀ i, i ∈ σ.leaves ↔ i ∈ τ.leaves) (hne : σ.nf ≠ τ.nf) :
    ∃ (x y : ℕ) (q : ℕ → hopperBF16F32.Word × hopperBF16F32.Word), x ≠ y ∧
      (∀ i, i ≠ x → i ≠ y → q i = (0, 0)) ∧
      MMAlgebra.runChain (tcMachine hopperBF16F32) q 0 σ ≠ MMAlgebra.runChain (tcMachine hopperBF16F32) q 0 τ :=
  MMAlgebra.chain_complete h100bf16Laws (by decide) h100bf16Witness σ τ hσ hτ nσ nτ hl hne

/-- **A100 tf32, completeness for chains.** -/
theorem a100tf32_chain_complete (σ τ : MMAlgebra.Chain) (hσ : ∀ B ∈ σ, B.length = 4)
    (hτ : ∀ B ∈ τ, B.length = 4) (nσ : σ.leaves.Nodup) (nτ : τ.leaves.Nodup)
    (hl : ∀ i, i ∈ σ.leaves ↔ i ∈ τ.leaves) (hne : σ.nf ≠ τ.nf) :
    ∃ (x y : ℕ) (q : ℕ → a100TF32F32.Word × a100TF32F32.Word), x ≠ y ∧
      (∀ i, i ≠ x → i ≠ y → q i = (0, 0)) ∧
      MMAlgebra.runChain (tcMachine a100TF32F32) q 0 σ ≠ MMAlgebra.runChain (tcMachine a100TF32F32) q 0 τ :=
  MMAlgebra.chain_complete a100tf32Laws (by decide) a100tf32Witness σ τ hσ hτ nσ nτ hl hne

/-- **H100 tf32 (WMMA, `K = 4`), completeness for chains.** -/
theorem h100tf32wmma_chain_complete (σ τ : MMAlgebra.Chain) (hσ : ∀ B ∈ σ, B.length = 4)
    (hτ : ∀ B ∈ τ, B.length = 4) (nσ : σ.leaves.Nodup) (nτ : τ.leaves.Nodup)
    (hl : ∀ i, i ∈ σ.leaves ↔ i ∈ τ.leaves) (hne : σ.nf ≠ τ.nf) :
    ∃ (x y : ℕ) (q : ℕ → hopperTF32WmmaF32.Word × hopperTF32WmmaF32.Word), x ≠ y ∧
      (∀ i, i ≠ x → i ≠ y → q i = (0, 0)) ∧
      MMAlgebra.runChain (tcMachine hopperTF32WmmaF32) q 0 σ ≠
        MMAlgebra.runChain (tcMachine hopperTF32WmmaF32) q 0 τ :=
  MMAlgebra.chain_complete h100tf32wLaws (by decide) h100tf32wWitness σ τ hσ hτ nσ nτ hl hne

/-- **H100 tf32 (MMA, `K = 8`), completeness for chains.** -/
theorem h100tf32mma_chain_complete (σ τ : MMAlgebra.Chain) (hσ : ∀ B ∈ σ, B.length = 8)
    (hτ : ∀ B ∈ τ, B.length = 8) (nσ : σ.leaves.Nodup) (nτ : τ.leaves.Nodup)
    (hl : ∀ i, i ∈ σ.leaves ↔ i ∈ τ.leaves) (hne : σ.nf ≠ τ.nf) :
    ∃ (x y : ℕ) (q : ℕ → hopperTF32MmaF32.Word × hopperTF32MmaF32.Word), x ≠ y ∧
      (∀ i, i ≠ x → i ≠ y → q i = (0, 0)) ∧
      MMAlgebra.runChain (tcMachine hopperTF32MmaF32) q 0 σ ≠
        MMAlgebra.runChain (tcMachine hopperTF32MmaF32) q 0 τ :=
  MMAlgebra.chain_complete h100tf32mLaws (by decide) h100tf32mWitness σ τ hσ hτ nσ nτ hl hne

end MMAlgebra.TC
