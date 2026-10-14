import MMAlgebraTC.FP8
import MMAlgebraTC.TermVariants
import TensorCore.TC.OutputWidth
import TensorCore.TC.Specification.Rounding

/-! # Completeness for the FP8 Tensor Cores

**Ada and Hopper FP8, chains.** An empty block FMA truncates its accumulator input to a 13-bit
mantissa (`tc_empty_block_trunc13`), so it passes through every finite value other than `−0` whose
ten low mantissa bits are zero, and every block output is such a value (`narrow_block_good`: the
accumulator is a multiple of `2^-139`, so the truncated output is never `−0`). These are the laws of
a rigid multiplier for chains with 13-bit values as the good accumulators (`narrowLaws`), and with
kernel-checked base witnesses two chains from `+0` over the same products are equivalent exactly
when their ordered partitions agree (`adaE4M3_chain_equiv_iff`, `adaE5M2_chain_equiv_iff`,
`hopperE4M3_chain_equiv_iff`, `hopperE5M2_chain_equiv_iff`). Terms with additions are not covered:
an addition can produce a value with more than 13 mantissa bits, which a following empty block
truncates (a truncation node).

**B200 FP8, chains and terms, every input.** B200's FP8 block FMAs are rigid (`tcLaws`). Every FP8 value is a multiple of `2^-16`, so every FP8 product lies on the binary32 grid
(`gridOK_bwE4M3`, `gridOK_bwE5M2`), and the term theorem for inputs on that grid
(`tc_sub_term_equiv_iff`) holds on every input: with kernel-checked fingerprint tables, two terms
over the same products are equivalent exactly when their rigid normal forms agree
(`bwE4M3_term_equiv_iff`, `bwE5M2_term_equiv_iff`), and likewise chains
(`bwE4M3_chain_equiv_iff`, `bwE5M2_chain_equiv_iff`).

The base witnesses and the fingerprint tables were found by searching random and structured FP8
inputs with an exact Python port of the block FMA, and are checked here by kernel evaluation. -/

open TensorCore Ozaki Ozaki.TC

namespace MMAlgebra.TC.FP8

theorem truncateMantissa32_self {m : ℕ} {d : F32} (h : d.toNat % 2 ^ (23 - m) = 0) :
    truncateMantissa32 m d = d := by
  apply BitVec.eq_of_toNat_eq
  rw [truncateMantissa32_toNat]
  have := Nat.div_add_mod d.toNat (2 ^ (23 - m))
  rw [h, Nat.add_zero] at this
  rw [Nat.mul_comm]; exact this

/-! ## The rigid laws for chains on Ada and Hopper FP8 -/

/-- A finite accumulator other than `−0` with a 13-bit mantissa. -/
def Good13 (d : F32) : Prop := Good d ∧ d.toNat % 2 ^ 10 = 0

instance (d : F32) : Decidable (Good13 d) := by unfold Good13; infer_instance

/-- The laws of a rigid multiplier for chains on Ada and Hopper FP8, with 13-bit values as the good
accumulators: every block output has a 13-bit mantissa, and an empty block passes such a value
through. -/
def narrowLaws (p : Model) (hF : p.alignMantissaBits = 13) (hm : p.outputMantissaBits = 13)
    (hmin : ∀ f ∈ p.eAlignMin, f ≤ -126) (hz : p.decode 0 = some ⟨0, 0, 0⟩) :
    MMAlgebra.RigidLaws (tcMachine p) p.nfma where
  z := (0, 0)
  good := Good13
  slot := tc_slotZero p
  perm := tc_perm p
  zero_good := by show Good13 0; decide
  pass := fun d hd => by
    rw [tc_empty_block_trunc13 p hF hm hmin hz d hd.1.1]
    congr 1
    unfold trunc13
    rw [truncateMantissa32_self (m := 13) hd.2, if_neg hd.1.2]

theorem e4m3x_zero : (classify e4m3x 0).finite = some ⟨0, 0, 0⟩ := by decide +kernel
theorem e5m2_zero : (classify e5m2 0).finite = some ⟨0, 0, 0⟩ := by decide +kernel

def adaE4M3Laws := narrowLaws adaE4M3F32 rfl rfl (by simp [adaE4M3F32]) e4m3x_zero
def adaE5M2Laws := narrowLaws adaE5M2F32 rfl rfl (by simp [adaE5M2F32]) e5m2_zero
def hopperE4M3Laws := narrowLaws hopperE4M3F32 rfl rfl (by simp [hopperE4M3F32]) e4m3x_zero
def hopperE5M2Laws := narrowLaws hopperE5M2F32 rfl rfl (by simp [hopperE5M2F32]) e5m2_zero

/-- B200 FP8 keeps `F = 25` and a binary32 block output: the snapshot's laws apply. -/
def blackwellE4M3Laws := tcLaws blackwellE4M3F32 (by decide) (by decide) (by simp [blackwellE4M3F32])
  e4m3x_zero
def blackwellE5M2Laws := tcLaws blackwellE5M2F32 (by decide) (by decide) (by simp [blackwellE5M2F32])
  e5m2_zero

/-! ## Base witnesses (found with the Python port, checked here by kernel evaluation) -/

def adaE4M3Witness : MMAlgebra.PairWitness adaE4M3Laws where
  a := (0x122, 0x11b)
  b := (0x7d, 0x12b)
  vx := 0x3c5c0000
  vy := 0xc30f0000
  vxy := 0xc30efc00
  vlt := 0xc30efc00
  vgt := 0xc30f0000
  e₁ := by decide +kernel
  e₂ := by decide +kernel
  e₃ := by decide +kernel
  e₄ := by decide +kernel
  e₅ := by decide +kernel
  g₁ := by show Good13 _; decide
  g₂ := by show Good13 _; decide
  g₃ := by show Good13 _; decide
  g₄ := by show Good13 _; decide
  g₅ := by show Good13 _; decide
  sep := by decide

def adaE5M2Witness : MMAlgebra.PairWitness adaE5M2Laws where
  a := (0x84, 0x37)
  b := (0x81, 0x6b)
  vx := 0xb7e00000
  vy := 0xbd600000
  vxy := 0xbd601000
  vlt := 0xbd601000
  vgt := 0xbd601c00
  e₁ := by decide +kernel
  e₂ := by decide +kernel
  e₃ := by decide +kernel
  e₄ := by decide +kernel
  e₅ := by decide +kernel
  g₁ := by show Good13 _; decide
  g₂ := by show Good13 _; decide
  g₃ := by show Good13 _; decide
  g₄ := by show Good13 _; decide
  g₅ := by show Good13 _; decide
  sep := by decide

def hopperE4M3Witness : MMAlgebra.PairWitness hopperE4M3Laws where
  a := (0x122, 0x11b)
  b := (0x7d, 0x12b)
  vx := 0x3c5c0000
  vy := 0xc30f0000
  vxy := 0xc30efc00
  vlt := 0xc30efc00
  vgt := 0xc30f0000
  e₁ := by decide +kernel
  e₂ := by decide +kernel
  e₃ := by decide +kernel
  e₄ := by decide +kernel
  e₅ := by decide +kernel
  g₁ := by show Good13 _; decide
  g₂ := by show Good13 _; decide
  g₃ := by show Good13 _; decide
  g₄ := by show Good13 _; decide
  g₅ := by show Good13 _; decide
  sep := by decide

def hopperE5M2Witness : MMAlgebra.PairWitness hopperE5M2Laws where
  a := (0x84, 0x37)
  b := (0x81, 0x6b)
  vx := 0xb7e00000
  vy := 0xbd600000
  vxy := 0xbd601000
  vlt := 0xbd601000
  vgt := 0xbd601c00
  e₁ := by decide +kernel
  e₂ := by decide +kernel
  e₃ := by decide +kernel
  e₄ := by decide +kernel
  e₅ := by decide +kernel
  g₁ := by show Good13 _; decide
  g₂ := by show Good13 _; decide
  g₃ := by show Good13 _; decide
  g₄ := by show Good13 _; decide
  g₅ := by show Good13 _; decide
  sep := by decide

def blackwellE4M3Witness : MMAlgebra.PairWitness blackwellE4M3Laws where
  a := (0x15c, 0x7d)
  b := (0x109, 0x131)
  vx := 0xc61c0000
  vy := 0x3c220000
  vxy := 0xc61bfff5
  vlt := 0xc61bfff6
  vgt := 0xc61bfff5
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

def blackwellE5M2Witness : MMAlgebra.PairWitness blackwellE5M2Laws where
  a := (0x33, 0x6a)
  b := (0xa2, 0x14)
  vx := 0x44280000
  vy := 0xb7400000
  vxy := 0x4427ffff
  vlt := 0x44280000
  vgt := 0x4427ffff
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

/-- **Ada (L40S, RTX 1000 Ada) E4M3, completeness for chains**: two chains from `+0` over the same
products with different ordered partitions differ on an input supported on two products. -/
theorem adaE4M3_chain_complete (σ τ : MMAlgebra.Chain) (hσ : ∀ B ∈ σ, B.length = 16)
    (hτ : ∀ B ∈ τ, B.length = 16) (nσ : σ.leaves.Nodup) (nτ : τ.leaves.Nodup)
    (hl : ∀ i, i ∈ σ.leaves ↔ i ∈ τ.leaves) (hne : σ.nf ≠ τ.nf) :
    ∃ (x y : ℕ) (q : ℕ → adaE4M3F32.Word × adaE4M3F32.Word), x ≠ y ∧
      (∀ i, i ≠ x → i ≠ y → q i = (0, 0)) ∧
      MMAlgebra.runChain (tcMachine adaE4M3F32) q 0 σ ≠ MMAlgebra.runChain (tcMachine adaE4M3F32) q 0 τ :=
  MMAlgebra.chain_complete adaE4M3Laws (by decide) adaE4M3Witness σ τ hσ hτ nσ nτ hl hne

theorem adaE5M2_chain_complete (σ τ : MMAlgebra.Chain) (hσ : ∀ B ∈ σ, B.length = 16)
    (hτ : ∀ B ∈ τ, B.length = 16) (nσ : σ.leaves.Nodup) (nτ : τ.leaves.Nodup)
    (hl : ∀ i, i ∈ σ.leaves ↔ i ∈ τ.leaves) (hne : σ.nf ≠ τ.nf) :
    ∃ (x y : ℕ) (q : ℕ → adaE5M2F32.Word × adaE5M2F32.Word), x ≠ y ∧
      (∀ i, i ≠ x → i ≠ y → q i = (0, 0)) ∧
      MMAlgebra.runChain (tcMachine adaE5M2F32) q 0 σ ≠ MMAlgebra.runChain (tcMachine adaE5M2F32) q 0 τ :=
  MMAlgebra.chain_complete adaE5M2Laws (by decide) adaE5M2Witness σ τ hσ hτ nσ nτ hl hne

theorem hopperE4M3_chain_complete (σ τ : MMAlgebra.Chain) (hσ : ∀ B ∈ σ, B.length = 32)
    (hτ : ∀ B ∈ τ, B.length = 32) (nσ : σ.leaves.Nodup) (nτ : τ.leaves.Nodup)
    (hl : ∀ i, i ∈ σ.leaves ↔ i ∈ τ.leaves) (hne : σ.nf ≠ τ.nf) :
    ∃ (x y : ℕ) (q : ℕ → hopperE4M3F32.Word × hopperE4M3F32.Word), x ≠ y ∧
      (∀ i, i ≠ x → i ≠ y → q i = (0, 0)) ∧
      MMAlgebra.runChain (tcMachine hopperE4M3F32) q 0 σ ≠
        MMAlgebra.runChain (tcMachine hopperE4M3F32) q 0 τ :=
  MMAlgebra.chain_complete hopperE4M3Laws (by decide) hopperE4M3Witness σ τ hσ hτ nσ nτ hl hne

theorem hopperE5M2_chain_complete (σ τ : MMAlgebra.Chain) (hσ : ∀ B ∈ σ, B.length = 32)
    (hτ : ∀ B ∈ τ, B.length = 32) (nσ : σ.leaves.Nodup) (nτ : τ.leaves.Nodup)
    (hl : ∀ i, i ∈ σ.leaves ↔ i ∈ τ.leaves) (hne : σ.nf ≠ τ.nf) :
    ∃ (x y : ℕ) (q : ℕ → hopperE5M2F32.Word × hopperE5M2F32.Word), x ≠ y ∧
      (∀ i, i ≠ x → i ≠ y → q i = (0, 0)) ∧
      MMAlgebra.runChain (tcMachine hopperE5M2F32) q 0 σ ≠
        MMAlgebra.runChain (tcMachine hopperE5M2F32) q 0 τ :=
  MMAlgebra.chain_complete hopperE5M2Laws (by decide) hopperE5M2Witness σ τ hσ hτ nσ nτ hl hne

theorem blackwellE4M3_chain_complete (σ τ : MMAlgebra.Chain) (hσ : ∀ B ∈ σ, B.length = 32)
    (hτ : ∀ B ∈ τ, B.length = 32) (nσ : σ.leaves.Nodup) (nτ : τ.leaves.Nodup)
    (hl : ∀ i, i ∈ σ.leaves ↔ i ∈ τ.leaves) (hne : σ.nf ≠ τ.nf) :
    ∃ (x y : ℕ) (q : ℕ → blackwellE4M3F32.Word × blackwellE4M3F32.Word), x ≠ y ∧
      (∀ i, i ≠ x → i ≠ y → q i = (0, 0)) ∧
      MMAlgebra.runChain (tcMachine blackwellE4M3F32) q 0 σ ≠
        MMAlgebra.runChain (tcMachine blackwellE4M3F32) q 0 τ :=
  MMAlgebra.chain_complete blackwellE4M3Laws (by decide) blackwellE4M3Witness σ τ hσ hτ nσ nτ hl hne

theorem blackwellE5M2_chain_complete (σ τ : MMAlgebra.Chain) (hσ : ∀ B ∈ σ, B.length = 32)
    (hτ : ∀ B ∈ τ, B.length = 32) (nσ : σ.leaves.Nodup) (nτ : τ.leaves.Nodup)
    (hl : ∀ i, i ∈ σ.leaves ↔ i ∈ τ.leaves) (hne : σ.nf ≠ τ.nf) :
    ∃ (x y : ℕ) (q : ℕ → blackwellE5M2F32.Word × blackwellE5M2F32.Word), x ≠ y ∧
      (∀ i, i ≠ x → i ≠ y → q i = (0, 0)) ∧
      MMAlgebra.runChain (tcMachine blackwellE5M2F32) q 0 σ ≠
        MMAlgebra.runChain (tcMachine blackwellE5M2F32) q 0 τ :=
  MMAlgebra.chain_complete blackwellE5M2Laws (by decide) blackwellE5M2Witness σ τ hσ hτ nσ nτ hl hne

/-! ## Every block output of Ada and Hopper FP8 is a 13-bit value other than `−0` -/

/-- A nonzero accumulator on the grid `2^-139` truncates to a word whose magnitude bits are at least
`2^10` (that is, at least `2^-139`). -/
theorem round32_magnitude_ge (x : ℚ) (bits : F32) (hx : x ≠ 0) (k : ℤ) (hk : x = (k : ℚ) * pow2 (-139))
    (h : round32 .truncate x = some bits) : 1024 ≤ bits.toNat % 2 ^ 31 := by
  obtain ⟨_, d, hd, hbet, hmax⟩ := IndependentSpec.round32_rounds x bits h
  rw [IndependentSpec.value32_eq] at hd
  -- the binary32 value ±2^-139 lies between 0 and x
  have hp := pow2_pos (-139)
  have hk0 : k ≠ 0 := by intro h0; rw [h0] at hk; simp at hk; exact hx hk
  have hge : pow2 (-139) ≤ IndependentSpec.magnitude d := by
    rcases (show 1 ≤ k ∨ k ≤ -1 by omega) with hk1 | hk1
    · have hk1' : ((1 : ℤ) : ℚ) ≤ (k : ℚ) := Rat.intCast_le_intCast.mpr hk1
      rw [Rat.intCast_one] at hk1'
      have hx1 : pow2 (-139) ≤ x := by
        rw [hk]
        have := Rat.mul_le_mul_of_nonneg_right hk1' (Rat.le_of_lt hp)
        rwa [Rat.one_mul] at this
      have hle := hmax (0x00000400 : F32) (pow2 (-139)) (by rw [IndependentSpec.value32_eq]; decide +kernel)
        (by
          unfold IndependentSpec.Between
          left
          exact ⟨by grind, Rat.le_of_lt hp, hx1⟩)
      unfold IndependentSpec.magnitude at hle ⊢
      grind
    · have hk1' : (k : ℚ) ≤ ((-1 : ℤ) : ℚ) := Rat.intCast_le_intCast.mpr hk1
      rw [Rat.intCast_neg, Rat.intCast_one] at hk1'
      have hx1 : x ≤ -pow2 (-139) := by
        rw [hk]
        have := Rat.mul_le_mul_of_nonneg_right hk1' (Rat.le_of_lt hp)
        rwa [Rat.neg_mul, Rat.one_mul] at this
      have hle := hmax (0x80000400 : F32) (-pow2 (-139)) (by rw [IndependentSpec.value32_eq]; decide +kernel)
        (by
          unfold IndependentSpec.Between
          right
          refine ⟨by grind, hx1, by grind⟩)
      unfold IndependentSpec.magnitude at hle ⊢
      grind
  -- in coefficients
  cases hdd : decode32 bits with
  | none => simp [value32, hdd] at hd
  | some dd =>
    have hv : d = dd.value := by simpa [value32, hdd] using hd.symm
    rw [hv, decode32_value_coeff hdd] at hge
    unfold IndependentSpec.magnitude at hge
    have habs := sign32_abs bits.toNat (coeff32 (bits.toNat % 2 ^ 31)) (pow2 (-149)) (pow2_pos _)
    unfold absQ at habs
    have hc : (1024 : ℚ) * pow2 (-149) ≤ (coeff32 (bits.toNat % 2 ^ 31) : ℚ) * pow2 (-149) := by
      have e : pow2 (-139) = (1024 : ℚ) * pow2 (-149) := by
        rw [show (1024 : ℚ) = pow2 10 by decide +kernel, ← pow2_add]; rfl
      rw [e] at hge
      grind
    have hc' : 1024 ≤ coeff32 (bits.toNat % 2 ^ 31) := by
      have := Rat.le_of_mul_le_mul_right hc (pow2_pos _)
      exact_mod_cast this
    have h1024 : coeff32 1024 = 1024 := by decide
    rw [← h1024] at hc'
    exact le_of_coeff32_le hc'

/-- On a Tensor Core model with 13 mantissa bits after alignment, a 13-bit block output and an
input format of bias at most 64 (Ada and Hopper FP8), every block output is finite, has a 13-bit
mantissa, and is not `−0`. -/
theorem narrow_block_good (p : Model) (hF : p.alignMantissaBits = 13) (hm : p.outputMantissaBits = 13)
    (hbias : p.input.bias ≤ 64) (d : F32) (ps : List (Option (p.Word × p.Word))) (o : F32)
    (h : (tcMachine p).block d ps = some o) : Good13 o := by
  have h' : (blockOut (p := p) ⟨slotPairs p ps, d⟩).toOption = some o := h
  cases hb : evalBlock (p := p) ⟨slotPairs p ps, d⟩ with
  | error e => simp [blockOut, hb, Except.map, Except.toOption] at h'
  | ok t =>
    simp only [blockOut, hb, Except.map, Except.toOption, Option.some.injEq] at h'
    subst h'
    have hp := evalBlock_prepared hb
    have hev := evalBlock_evalPrepared hb
    obtain ⟨bits, hr, ht⟩ := evalPrepared_output_mantissa hev
    have hmod : t.block.model.outputMantissaBits = 13 := by rw [evalBlock_model hb]; exact hm
    rw [hmod] at ht
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · rw [finite32_self]; rfl
    · rw [ht]
      intro hneg
      by_cases hz : t.block.accumulator = 0
      · rw [hz] at hr
        have h0 : round32 .truncate 0 = some (0 : F32) := by decide +kernel
        rw [h0] at hr
        cases Option.some.inj hr
        exact absurd hneg (by decide)
      · -- the accumulator is a multiple of 2^-139
        have hgrid : ∃ k : ℤ, t.block.accumulator = (k : ℚ) * pow2 (-139) := by
          unfold PreparedBlock.accumulator
          have hlow := prepare_terms_lower p hbias ⟨slotPairs p ps, d⟩ t.block hp
          have hge : -139 ≤ t.block.alignGridExponent := by
            unfold PreparedBlock.alignGridExponent PreparedBlock.alignExp
            rw [prepare_model hp, hF]
            cases hmx : maxTermExp t.block.terms with
            | none =>
              exfalso; apply hz
              unfold PreparedBlock.accumulator PreparedBlock.alignedBits
              have hall : ∀ u ∈ t.block.terms, u.significand = 0 := by
                intro u hu
                apply Classical.byContradiction; intro hnz
                obtain ⟨e, he, _⟩ := maxTermExp_term _ u hu hnz
                rw [hmx] at he; cases he
              rw [TensorCore.Datapath.sumZ_map_zero _ _ (fun u hu => by
                rw [show u.value = 0 by simp [DenormalizedProduct.value, hall u hu], TensorCore.Datapath.truncBits_zero])]
              simp
            | some e =>
              have := maxTermExp_lower _ (-126) e hlow hmx
              simp only [Model.applyEAlignMin, Option.getD_some]
              split <;> omega
          refine ⟨sumZ t.block.alignedBits * 2 ^ (t.block.alignGridExponent + 139).toNat, ?_⟩
          rw [Rat.intCast_mul, Rat.mul_assoc]
          congr 1
          rw [show ((2 ^ (t.block.alignGridExponent + 139).toNat : ℤ) : ℚ) =
              (((2 ^ (t.block.alignGridExponent + 139).toNat : ℕ) : ℤ) : ℚ) by simp,
            Rat.intCast_natCast, ← pow2_natCast, ← pow2_add]
          congr 1; omega
        obtain ⟨k, hk⟩ := hgrid
        have hmag := round32_magnitude_ge _ bits hz k hk hr
        have hparts := (truncateMantissa32_parts 13 bits).2
        rw [hneg] at hparts
        have : (bits.toNat % 2 ^ 31) / 2 ^ 10 * 2 ^ 10 ≥ 1024 := by
          have := Nat.div_mul_le_self (bits.toNat % 2 ^ 31) (2 ^ 10)
          have h2 := Nat.div_add_mod (bits.toNat % 2 ^ 31) (2 ^ 10)
          have h3 := Nat.mod_lt (bits.toNat % 2 ^ 31) (show 0 < 2 ^ 10 by decide)
          rw [Nat.mul_comm] at h2
          omega
        simp at hparts
        omega
    · rw [ht, truncateMantissa32_toNat]; exact Nat.mul_mod_left _ _

/-! ## Chains are equivalent exactly when their ordered partitions agree -/

theorem adaE4M3_chain_equiv_iff (σ τ : MMAlgebra.Chain) (hσ : ∀ B ∈ σ, B.length = 16)
    (hτ : ∀ B ∈ τ, B.length = 16) (nσ : σ.leaves.Nodup) (nτ : τ.leaves.Nodup)
    (hl : ∀ i, i ∈ σ.leaves ↔ i ∈ τ.leaves) :
    (∀ q, MMAlgebra.runChain (tcMachine adaE4M3F32) q 0 σ =
        MMAlgebra.runChain (tcMachine adaE4M3F32) q 0 τ) ↔ σ.nf = τ.nf :=
  MMAlgebra.chain_equiv_iff adaE4M3Laws (by decide) adaE4M3Witness
    (narrow_block_good _ rfl rfl (by decide)) σ τ hσ hτ nσ nτ hl

theorem adaE5M2_chain_equiv_iff (σ τ : MMAlgebra.Chain) (hσ : ∀ B ∈ σ, B.length = 16)
    (hτ : ∀ B ∈ τ, B.length = 16) (nσ : σ.leaves.Nodup) (nτ : τ.leaves.Nodup)
    (hl : ∀ i, i ∈ σ.leaves ↔ i ∈ τ.leaves) :
    (∀ q, MMAlgebra.runChain (tcMachine adaE5M2F32) q 0 σ =
        MMAlgebra.runChain (tcMachine adaE5M2F32) q 0 τ) ↔ σ.nf = τ.nf :=
  MMAlgebra.chain_equiv_iff adaE5M2Laws (by decide) adaE5M2Witness
    (narrow_block_good _ rfl rfl (by decide)) σ τ hσ hτ nσ nτ hl

theorem hopperE4M3_chain_equiv_iff (σ τ : MMAlgebra.Chain) (hσ : ∀ B ∈ σ, B.length = 32)
    (hτ : ∀ B ∈ τ, B.length = 32) (nσ : σ.leaves.Nodup) (nτ : τ.leaves.Nodup)
    (hl : ∀ i, i ∈ σ.leaves ↔ i ∈ τ.leaves) :
    (∀ q, MMAlgebra.runChain (tcMachine hopperE4M3F32) q 0 σ =
        MMAlgebra.runChain (tcMachine hopperE4M3F32) q 0 τ) ↔ σ.nf = τ.nf :=
  MMAlgebra.chain_equiv_iff hopperE4M3Laws (by decide) hopperE4M3Witness
    (narrow_block_good _ rfl rfl (by decide)) σ τ hσ hτ nσ nτ hl

theorem hopperE5M2_chain_equiv_iff (σ τ : MMAlgebra.Chain) (hσ : ∀ B ∈ σ, B.length = 32)
    (hτ : ∀ B ∈ τ, B.length = 32) (nσ : σ.leaves.Nodup) (nτ : τ.leaves.Nodup)
    (hl : ∀ i, i ∈ σ.leaves ↔ i ∈ τ.leaves) :
    (∀ q, MMAlgebra.runChain (tcMachine hopperE5M2F32) q 0 σ =
        MMAlgebra.runChain (tcMachine hopperE5M2F32) q 0 τ) ↔ σ.nf = τ.nf :=
  MMAlgebra.chain_equiv_iff hopperE5M2Laws (by decide) hopperE5M2Witness
    (narrow_block_good _ rfl rfl (by decide)) σ τ hσ hτ nσ nτ hl

theorem e4m3x_value_grid : ∀ n : ℕ, n < 512 →
    ((decodeD blackwellE4M3F32 (BitVec.ofNat 9 n)).value * pow2 16).den = 1 := by
  decide +kernel

theorem e5m2_value_grid : ∀ n : ℕ, n < 256 →
    ((decodeD blackwellE5M2F32 (BitVec.ofNat 8 n)).value * pow2 16).den = 1 := by
  decide +kernel

theorem den_one_eq {x : ℚ} (h : x.den = 1) : x = (x.num : ℚ) :=
  Rat.ext (by simp) (by rw [Rat.den_intCast]; exact h)

/-- Products of two values on the grid `2^-16` lie on the grid `2^-149`. -/
theorem gridOK_of_values (p : Model) (q : p.Word × p.Word)
    (ha : (wordValue p q.1 * pow2 16).den = 1) (hb : (wordValue p q.2 * pow2 16).den = 1) :
    GridOK p q := by
  unfold GridOK
  show (wordValue p q.1 * wordValue p q.2 * pow2 149).den = 1
  have ea := den_one_eq ha
  have eb := den_one_eq hb
  have hp : pow2 149 = pow2 16 * pow2 16 * pow2 117 := by rw [← pow2_add, ← pow2_add]; rfl
  have e : wordValue p q.1 * wordValue p q.2 * pow2 149 =
      (((wordValue p q.1 * pow2 16).num * (wordValue p q.2 * pow2 16).num * (2 ^ 117 : ℕ) : ℤ) : ℚ) := by
    rw [Rat.intCast_mul, Rat.intCast_mul, ← ea, ← eb, Rat.intCast_natCast, ← pow2_natCast, hp]
    grind
  rw [e, Rat.den_intCast]

theorem gridOK_bwE4M3 (q : blackwellE4M3F32.Word × blackwellE4M3F32.Word) :
    GridOK blackwellE4M3F32 q := by
  apply gridOK_of_values
  · have := e4m3x_value_grid q.1.toNat q.1.isLt
    have e : (BitVec.ofNat 9 q.1.toNat : blackwellE4M3F32.Word) = q.1 := by
      apply BitVec.eq_of_toNat_eq; simp; exact BitVec.isLt _
    rw [e] at this; exact this
  · have := e4m3x_value_grid q.2.toNat q.2.isLt
    have e : (BitVec.ofNat 9 q.2.toNat : blackwellE4M3F32.Word) = q.2 := by
      apply BitVec.eq_of_toNat_eq; simp; exact BitVec.isLt _
    rw [e] at this; exact this

theorem gridOK_bwE5M2 (q : blackwellE5M2F32.Word × blackwellE5M2F32.Word) :
    GridOK blackwellE5M2F32 q := by
  apply gridOK_of_values
  · have := e5m2_value_grid q.1.toNat q.1.isLt
    have e : (BitVec.ofNat 8 q.1.toNat : blackwellE5M2F32.Word) = q.1 := by
      apply BitVec.eq_of_toNat_eq; simp; exact BitVec.isLt _
    rw [e] at this; exact this
  · have := e5m2_value_grid q.2.toNat q.2.isLt
    have e : (BitVec.ofNat 8 q.2.toNat : blackwellE5M2F32.Word) = q.2 := by
      apply BitVec.eq_of_toNat_eq; simp; exact BitVec.isLt _
    rw [e] at this; exact this

def bwE4M3In2 : List (ℕ → {q : blackwellE4M3F32.Word × blackwellE4M3F32.Word // GridOK blackwellE4M3F32 q}) :=
  [gridInput blackwellE4M3F32 e4m3x_zero [⟨(0x10c, 0x16), gridOK_bwE4M3 _⟩, ⟨(0x66, 0x60), gridOK_bwE4M3 _⟩],
   gridInput blackwellE4M3F32 e4m3x_zero [⟨(0x176, 0x16c), gridOK_bwE4M3 _⟩, ⟨(0x109, 0xa), gridOK_bwE4M3 _⟩],
   gridInput blackwellE4M3F32 e4m3x_zero [⟨(0x13d, 0x13e), gridOK_bwE4M3 _⟩, ⟨(0x132, 0x41), gridOK_bwE4M3 _⟩],
   gridInput blackwellE4M3F32 e4m3x_zero [⟨(0x71, 0x15e), gridOK_bwE4M3 _⟩, ⟨(0x175, 0xa), gridOK_bwE4M3 _⟩],
   gridInput blackwellE4M3F32 e4m3x_zero [⟨(0x16e, 0x6d), gridOK_bwE4M3 _⟩, ⟨(0x135, 0x34), gridOK_bwE4M3 _⟩],
   gridInput blackwellE4M3F32 e4m3x_zero [⟨(0x11d, 0x1b), gridOK_bwE4M3 _⟩, ⟨(0x115, 0x11), gridOK_bwE4M3 _⟩],
   gridInput blackwellE4M3F32 e4m3x_zero [⟨(0x16, 0xb), gridOK_bwE4M3 _⟩, ⟨(0x6c, 0x16f), gridOK_bwE4M3 _⟩]]

def bwE4M3In3 : List (ℕ → {q : blackwellE4M3F32.Word × blackwellE4M3F32.Word // GridOK blackwellE4M3F32 q}) :=
  [gridInput blackwellE4M3F32 e4m3x_zero [⟨(0x10f, 0x10), gridOK_bwE4M3 _⟩, ⟨(0x63, 0x77), gridOK_bwE4M3 _⟩, ⟨(0x6b, 0x16f), gridOK_bwE4M3 _⟩],
   gridInput blackwellE4M3F32 e4m3x_zero [⟨(0x10f, 0x108), gridOK_bwE4M3 _⟩, ⟨(0x109, 0x11), gridOK_bwE4M3 _⟩, ⟨(0x76, 0x169), gridOK_bwE4M3 _⟩],
   gridInput blackwellE4M3F32 e4m3x_zero [⟨(0x16b, 0x16d), gridOK_bwE4M3 _⟩, ⟨(0x42, 0x146), gridOK_bwE4M3 _⟩, ⟨(0x10e, 0x13), gridOK_bwE4M3 _⟩],
   gridInput blackwellE4M3F32 e4m3x_zero [⟨(0x113, 0x11), gridOK_bwE4M3 _⟩, ⟨(0x13b, 0x35), gridOK_bwE4M3 _⟩, ⟨(0x166, 0x163), gridOK_bwE4M3 _⟩],
   gridInput blackwellE4M3F32 e4m3x_zero [⟨(0x1a, 0xa), gridOK_bwE4M3 _⟩, ⟨(0x16f, 0x16b), gridOK_bwE4M3 _⟩, ⟨(0x11b, 0x17), gridOK_bwE4M3 _⟩],
   gridInput blackwellE4M3F32 e4m3x_zero [⟨(0x64, 0x67), gridOK_bwE4M3 _⟩, ⟨(0x115, 0x12), gridOK_bwE4M3 _⟩, ⟨(0x10d, 0x9), gridOK_bwE4M3 _⟩],
   gridInput blackwellE4M3F32 e4m3x_zero [⟨(0x10a, 0xa), gridOK_bwE4M3 _⟩, ⟨(0x173, 0x16e), gridOK_bwE4M3 _⟩, ⟨(0x1f, 0x11e), gridOK_bwE4M3 _⟩],
   gridInput blackwellE4M3F32 e4m3x_zero [⟨(0x13d, 0x31), gridOK_bwE4M3 _⟩, ⟨(0x10, 0x111), gridOK_bwE4M3 _⟩, ⟨(0x6d, 0x6f), gridOK_bwE4M3 _⟩]]

theorem bwE4M3_table2 : ((MMAlgebra.codes2All.filter fun κ =>
    MMAlgebra.rvalid (MMAlgebra.LTree.realize2 κ 0 1)).map fun κ => bwE4M3In2.map fun q =>
      MMAlgebra.evR ((tcMachine blackwellE4M3F32).sub (GridOK blackwellE4M3F32)) blackwellE4M3F32.nfma q
        (MMAlgebra.LTree.realize2 κ 0 1)).Nodup := by
  decide +kernel

theorem bwE4M3_table3 : ((MMAlgebra.codes3All.filter fun κ => MMAlgebra.rvalid (κ.realize 0 1 2)).map
    fun κ => bwE4M3In3.map fun q =>
      MMAlgebra.evR ((tcMachine blackwellE4M3F32).sub (GridOK blackwellE4M3F32)) blackwellE4M3F32.nfma q (κ.realize 0 1 2)).Nodup := by
  decide +kernel


def bwE5M2In2 : List (ℕ → {q : blackwellE5M2F32.Word × blackwellE5M2F32.Word // GridOK blackwellE5M2F32 q}) :=
  [gridInput blackwellE5M2F32 e5m2_zero [⟨(0xb, 0x89), gridOK_bwE5M2 _⟩, ⟨(0x42, 0x38), gridOK_bwE5M2 _⟩],
   gridInput blackwellE5M2F32 e5m2_zero [⟨(0x8e, 0x4), gridOK_bwE5M2 _⟩, ⟨(0xbb, 0xbf), gridOK_bwE5M2 _⟩],
   gridInput blackwellE5M2F32 e5m2_zero [⟨(0x43, 0x3a), gridOK_bwE5M2 _⟩, ⟨(0x89, 0xb), gridOK_bwE5M2 _⟩]]

def bwE5M2In3 : List (ℕ → {q : blackwellE5M2F32.Word × blackwellE5M2F32.Word // GridOK blackwellE5M2F32 q}) :=
  [gridInput blackwellE5M2F32 e5m2_zero [⟨(0xc2, 0xc2), gridOK_bwE5M2 _⟩, ⟨(0xf2, 0x70), gridOK_bwE5M2 _⟩, ⟨(0x70, 0x76), gridOK_bwE5M2 _⟩],
   gridInput blackwellE5M2F32 e5m2_zero [⟨(0x87, 0x14), gridOK_bwE5M2 _⟩, ⟨(0x94, 0x8a), gridOK_bwE5M2 _⟩, ⟨(0xf9, 0x86), gridOK_bwE5M2 _⟩],
   gridInput blackwellE5M2F32 e5m2_zero [⟨(0xf, 0x8f), gridOK_bwE5M2 _⟩, ⟨(0xc3, 0xc0), gridOK_bwE5M2 _⟩, ⟨(0xc1, 0xc3), gridOK_bwE5M2 _⟩],
   gridInput blackwellE5M2F32 e5m2_zero [⟨(0xbf, 0xbe), gridOK_bwE5M2 _⟩, ⟨(0x85, 0x87), gridOK_bwE5M2 _⟩, ⟨(0x8c, 0x9), gridOK_bwE5M2 _⟩],
   gridInput blackwellE5M2F32 e5m2_zero [⟨(0x55, 0x85), gridOK_bwE5M2 _⟩, ⟨(0xda, 0xd6), gridOK_bwE5M2 _⟩, ⟨(0xba, 0x55), gridOK_bwE5M2 _⟩],
   gridInput blackwellE5M2F32 e5m2_zero [⟨(0xba, 0xbe), gridOK_bwE5M2 _⟩, ⟨(0xe, 0xa), gridOK_bwE5M2 _⟩, ⟨(0xc3, 0x3a), gridOK_bwE5M2 _⟩],
   gridInput blackwellE5M2F32 e5m2_zero [⟨(0x2b, 0x84), gridOK_bwE5M2 _⟩, ⟨(0x19, 0xa2), gridOK_bwE5M2 _⟩, ⟨(0x62, 0x3e), gridOK_bwE5M2 _⟩],
   gridInput blackwellE5M2F32 e5m2_zero [⟨(0xf3, 0xf5), gridOK_bwE5M2 _⟩, ⟨(0x3d, 0xc3), gridOK_bwE5M2 _⟩, ⟨(0x84, 0x9), gridOK_bwE5M2 _⟩],
   gridInput blackwellE5M2F32 e5m2_zero [⟨(0xbd, 0xb8), gridOK_bwE5M2 _⟩, ⟨(0x3f, 0xc3), gridOK_bwE5M2 _⟩, ⟨(0xd, 0xb), gridOK_bwE5M2 _⟩],
   gridInput blackwellE5M2F32 e5m2_zero [⟨(0x53, 0xf1), gridOK_bwE5M2 _⟩, ⟨(0x42, 0x33), gridOK_bwE5M2 _⟩, ⟨(0x66, 0x52), gridOK_bwE5M2 _⟩]]

theorem bwE5M2_table2 : ((MMAlgebra.codes2All.filter fun κ =>
    MMAlgebra.rvalid (MMAlgebra.LTree.realize2 κ 0 1)).map fun κ => bwE5M2In2.map fun q =>
      MMAlgebra.evR ((tcMachine blackwellE5M2F32).sub (GridOK blackwellE5M2F32)) blackwellE5M2F32.nfma q
        (MMAlgebra.LTree.realize2 κ 0 1)).Nodup := by
  decide +kernel

theorem bwE5M2_table3 : ((MMAlgebra.codes3All.filter fun κ => MMAlgebra.rvalid (κ.realize 0 1 2)).map
    fun κ => bwE5M2In3.map fun q =>
      MMAlgebra.evR ((tcMachine blackwellE5M2F32).sub (GridOK blackwellE5M2F32)) blackwellE5M2F32.nfma q (κ.realize 0 1 2)).Nodup := by
  decide +kernel

/-- **B200 E4M3: two terms over the same products give the same output word on every input exactly
when their rigid normal forms agree.** -/
theorem bwE4M3_term_equiv_iff (t₁ t₂ : MMAlgebra.Term) (hw₁ : MMAlgebra.TermWF 32 t₁)
    (hw₂ : MMAlgebra.TermWF 32 t₂) (n₁ : t₁.leaves.Nodup) (n₂ : t₂.leaves.Nodup)
    (hl : ∀ i, i ∈ t₁.leaves ↔ i ∈ t₂.leaves) :
    (∀ q : ℕ → blackwellE4M3F32.Word × blackwellE4M3F32.Word,
      MMAlgebra.eval (tcMachine blackwellE4M3F32) q 0 0 t₁ =
        MMAlgebra.eval (tcMachine blackwellE4M3F32) q 0 0 t₂) ↔
      MMAlgebra.nfR t₁ = MMAlgebra.nfR t₂ := by
  have h := tc_sub_term_equiv_iff blackwellE4M3F32 (by decide) (by decide)
    (by simp [blackwellE4M3F32]) e4m3x_zero bwE4M3In2 bwE4M3In3 bwE4M3_table2 bwE4M3_table3
    t₁ t₂ hw₁ hw₂ n₁ n₂ hl
  constructor
  · intro hq; exact h.mp (fun q _ => hq q)
  · intro he q; exact h.mpr he q (fun i => gridOK_bwE4M3 (q i))

/-- **B200 E5M2: the same.** -/
theorem bwE5M2_term_equiv_iff (t₁ t₂ : MMAlgebra.Term) (hw₁ : MMAlgebra.TermWF 32 t₁)
    (hw₂ : MMAlgebra.TermWF 32 t₂) (n₁ : t₁.leaves.Nodup) (n₂ : t₂.leaves.Nodup)
    (hl : ∀ i, i ∈ t₁.leaves ↔ i ∈ t₂.leaves) :
    (∀ q : ℕ → blackwellE5M2F32.Word × blackwellE5M2F32.Word,
      MMAlgebra.eval (tcMachine blackwellE5M2F32) q 0 0 t₁ =
        MMAlgebra.eval (tcMachine blackwellE5M2F32) q 0 0 t₂) ↔
      MMAlgebra.nfR t₁ = MMAlgebra.nfR t₂ := by
  have h := tc_sub_term_equiv_iff blackwellE5M2F32 (by decide) (by decide)
    (by simp [blackwellE5M2F32]) e5m2_zero bwE5M2In2 bwE5M2In3 bwE5M2_table2 bwE5M2_table3
    t₁ t₂ hw₁ hw₂ n₁ n₂ hl
  constructor
  · intro hq; exact h.mp (fun q _ => hq q)
  · intro he q; exact h.mpr he q (fun i => gridOK_bwE5M2 (q i))

/-! ## Chains on B200 FP8: equivalence -/

theorem bw_block_good (p : Model) (hz : p.decode 0 = some ⟨0, 0, 0⟩) (hw : 23 ≤ p.outputMantissaBits)
    (hg : ∀ q, GridOK p q) (d : F32) (ps : List (Option (p.Word × p.Word))) (o : F32)
    (h : (tcMachine p).block d ps = some o) : Good o := by
  apply tc_sub_block_good p hz hw d (ps.map (Option.map fun q => ⟨q, hg q⟩)) o
  have e : (ps.map (Option.map fun q => (⟨q, hg q⟩ : {q // GridOK p q}))).map (Option.map Subtype.val) = ps := by
    simp [List.map_map, Function.comp_def]
  rw [e]; exact h

theorem bwE4M3_chain_equiv_iff (σ τ : MMAlgebra.Chain) (hσ : ∀ B ∈ σ, B.length = 32)
    (hτ : ∀ B ∈ τ, B.length = 32) (nσ : σ.leaves.Nodup) (nτ : τ.leaves.Nodup)
    (hl : ∀ i, i ∈ σ.leaves ↔ i ∈ τ.leaves) :
    (∀ q, MMAlgebra.runChain (tcMachine blackwellE4M3F32) q 0 σ =
        MMAlgebra.runChain (tcMachine blackwellE4M3F32) q 0 τ) ↔ σ.nf = τ.nf :=
  MMAlgebra.chain_equiv_iff blackwellE4M3Laws (by decide) blackwellE4M3Witness
    (bw_block_good _ e4m3x_zero (by decide) gridOK_bwE4M3) σ τ hσ hτ nσ nτ hl

theorem bwE5M2_chain_equiv_iff (σ τ : MMAlgebra.Chain) (hσ : ∀ B ∈ σ, B.length = 32)
    (hτ : ∀ B ∈ τ, B.length = 32) (nσ : σ.leaves.Nodup) (nτ : τ.leaves.Nodup)
    (hl : ∀ i, i ∈ σ.leaves ↔ i ∈ τ.leaves) :
    (∀ q, MMAlgebra.runChain (tcMachine blackwellE5M2F32) q 0 σ =
        MMAlgebra.runChain (tcMachine blackwellE5M2F32) q 0 τ) ↔ σ.nf = τ.nf :=
  MMAlgebra.chain_equiv_iff blackwellE5M2Laws (by decide) blackwellE5M2Witness
    (bw_block_good _ e5m2_zero (by decide) gridOK_bwE5M2) σ τ hσ hτ nσ nτ hl

end MMAlgebra.TC.FP8
