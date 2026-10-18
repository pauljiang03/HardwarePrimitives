import MMAlgebraMC.RoundedMC

/-! # Completeness for chains on CDNA 1 bf16

CDNA 1 bf16 blocks are correctly rounded too, but a bf16 product can fall below binary32's range,
and then a one-product block rounds it: the merge law of CDNA 1 fp16 fails, and over all inputs the
chains of CDNA 1 bf16 are rigid. With the laws of a rigid multiplier for chains (the multiset law,
and an empty block passing a finite value other than `−0` through, `cdna1BF16_pass`) and the tie
witness of `MMAlgebraMCTests.cdna1BF16_tie` as base witness, two chains over the same products
with different ordered partitions differ on some input (`cdna1BF16_chain_complete`). -/

open MatrixCore Ozaki.MC

namespace MMAlgebra.MC

/-- **An empty CDNA 1 bf16 block passes a good accumulator through.** -/
theorem cdna1BF16_pass (d : F32) (hd : GoodW d) :
    (mcMachine cdna1BF16).block d (List.replicate 2 none) = some d := by
  obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp hd.1
  obtain ⟨C, hC, rfl⟩ : ∃ C, (fp32.decode d).toFinite = some C ∧ C.value = v := by
    unfold value32 at hv
    cases hc : (fp32.decode d).toFinite with
    | none => rw [hc] at hv; cases hv
    | some C => rw [hc] at hv; exact ⟨C, rfl, Option.some.inj hv⟩
  show (blockBits (P := cdna1BF16) ⟨(slotPairs cdna1BF16 (List.replicate 2 none)).map Prod.fst,
    (slotPairs cdna1BF16 (List.replicate 2 none)).map Prod.snd, d⟩).toOption = some d
  have hz : decPair cdna1BF16 (0, 0) = some (⟨false, 0, -126, 7⟩, ⟨false, 0, -126, 7⟩) := by
    decide +kernel
  have hslot : slotPairs cdna1BF16 (List.replicate 2 none) = List.replicate 2 (0, 0) := by
    simp [slotPairs]
  have hL : (List.replicate 2 ((0, 0) : cdna1BF16.a.Word × cdna1BF16.b.Word)).mapM (decPair cdna1BF16) =
      some (List.replicate 2 (⟨false, 0, -126, 7⟩, ⟨false, 0, -126, 7⟩)) := by
    simp only [List.replicate, List.mapM_cons, List.mapM_nil, hz]; rfl
  have hprep : prepare (P := cdna1BF16) ⟨(slotPairs cdna1BF16 (List.replicate 2 none)).map Prod.fst,
      (slotPairs cdna1BF16 (List.replicate 2 none)).map Prod.snd, d⟩ =
      some ⟨List.replicate 2 ⟨false, 0, -126, 7⟩, List.replicate 2 ⟨false, 0, -126, 7⟩, C⟩ := by
    rw [hslot, prepare_pairs, hL, Option.bind_some, hC]; rfl
  have hexact : (Prepared.mk (List.replicate 2 ⟨false, 0, -126, 7⟩)
      (List.replicate 2 ⟨false, 0, -126, 7⟩) C).exact = C.value := by
    rw [Prepared.exact_eq]
    show sumQ [_, _] + C.value = C.value
    have : sumQ [(0 : ℚ) * 0, 0 * 0] = 0 := by decide +kernel
    simp only [Unpacked.value] at this ⊢
    grind
  unfold blockBits evalBlock
  simp only [List.length_map, List.length_replicate, hslot]
  rw [if_neg (by decide)]
  rw [hslot] at hprep
  rw [hprep]
  simp only
  rw [accumulate_correctRounding rfl rfl, hexact]
  simp only
  have hval : value32 d = some C.value := by unfold value32; rw [hC]; rfl
  rw [show (!cdna1BF16.subnormals) = false from rfl, fl32_value_self hval hd.2]
  rfl

/-- The laws of a rigid multiplier for chains, on CDNA 1 bf16. -/
def cdna1BF16Laws : MMAlgebra.RigidLaws (mcMachine cdna1BF16) 2 where
  z := (0, 0)
  good := GoodW
  slot := fun d ps qs h => by
    show (blockBits (P := cdna1BF16) ⟨(slotPairs cdna1BF16 ps).map Prod.fst,
      (slotPairs cdna1BF16 ps).map Prod.snd, d⟩).toOption =
      (blockBits (P := cdna1BF16) ⟨(slotPairs cdna1BF16 qs).map Prod.fst,
      (slotPairs cdna1BF16 qs).map Prod.snd, d⟩).toOption
    unfold slotPairs; rw [h]
  perm := fun d _ _ h => mc_perm (Or.inl rfl) d h
  zero_good := mc_zero_good
  pass := cdna1BF16_pass

/-- The tie witness: `x = 2^-75 × 2^-74 = 2^-149` and `y = 2^-75 × 2^-75 = 2^-150`. The block holding
`y` alone rounds the tie `2^-150` to `+0`, so `[y] [x]` gives `2^-149`, while `[x] [y]` and `[x y]`
round the tie `1.5 · 2^-149` to even, `2^-148`. -/
def cdna1BF16Witness : MMAlgebra.PairWitness cdna1BF16Laws where
  a := (0x1A00, 0x1A80)
  b := (0x1A00, 0x1A00)
  vx := 0x1
  vy := 0x0
  vxy := 0x2
  vlt := 0x2
  vgt := 0x1
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

/-- **CDNA 1 (bf16), completeness for chains.** Two chains from `+0` with blocks of 2 slots over
the same products, each once, with different ordered partitions differ on an input that is zero
outside two of the products. -/
theorem cdna1BF16_chain_complete (σ τ : MMAlgebra.Chain) (hσ : ∀ B ∈ σ, B.length = 2)
    (hτ : ∀ B ∈ τ, B.length = 2) (nσ : σ.leaves.Nodup) (nτ : τ.leaves.Nodup)
    (hl : ∀ i, i ∈ σ.leaves ↔ i ∈ τ.leaves) (hne : σ.nf ≠ τ.nf) :
    ∃ (x y : ℕ) (p : ℕ → cdna1BF16.a.Word × cdna1BF16.b.Word), x ≠ y ∧
      (∀ i, i ≠ x → i ≠ y → p i = (0, 0)) ∧
      MMAlgebra.runChain (mcMachine cdna1BF16) p 0 σ ≠ MMAlgebra.runChain (mcMachine cdna1BF16) p 0 τ :=
  MMAlgebra.chain_complete cdna1BF16Laws (by decide) cdna1BF16Witness σ τ hσ hτ nσ nτ hl hne

end MMAlgebra.MC
