import MMAlgebraTC.Pinned

/-! # Anchored accumulation on the Tensor Core model

Start a chain at an anchor `c₀ = 1.5·2^α` instead of `0`. While every running value stays in the
binade `[2^α, 2^(α+1))` and no product exponent exceeds `α`, every block aligns to `α` (the exponent
of `c`), truncates each product toward zero to `2^(α−F)`, and its final truncation is a floor on
`2^(α−23)`, which commutes with adding the on-grid `c`. So each block adds the increment
`⌊Σ trunc_{α−F}(aᵢbᵢ)⌋_{2^(α−23)}`, which depends on the block's products alone
(`evalBlock_anchored`), and a chain returns `c₀` plus the sum of its blocks' increments
(`runBlocks_anchored`): a function of the multiset of blocks (`anchored_blocks_perm`). No product
slot is spent. On V100 (`F = 23`) the floor is the identity, and the increment is a sum over
products. -/

open TensorCore
open Ozaki
open Ozaki.TC

namespace MMAlgebra.TC


/-- Floor onto multiples of `2^u`. -/
def floorGrid (x : ℚ) (u : ℤ) : ℚ := ((x / pow2 u).floor : ℚ) * pow2 u

/-- The increment of one anchored block. -/
def anchorIncrement (p : Model) (α : ℤ) (ps : List (p.Word × p.Word)) : ℚ :=
  floorGrid (truncSum p (α - p.alignMantissaBits) ps) (α - 23)

theorem floorGrid_shift (K : ℤ) (X : ℚ) (u : ℤ) :
    floorGrid ((K : ℚ) * pow2 u + X) u = (K : ℚ) * pow2 u + floorGrid X u := by
  unfold floorGrid
  have hu : pow2 u ≠ 0 := Rat.ne_of_gt (pow2_pos u)
  have h : ((K : ℚ) * pow2 u + X) / pow2 u = X / pow2 u + (K : ℚ) := by
    rw [Rat.div_def, Rat.div_def, Rat.add_mul, Rat.mul_assoc, Rat.mul_inv_cancel _ hu]; grind
  rw [h, Rat.floor_add_intCast, Rat.intCast_add]; grind

/-- Truncation of a value in the binade `[2^α, 2^(α+1))` is the floor on `2^(α−23)`. -/
theorem trunc_binade {y : ℚ} {α : ℤ} (hα : -126 ≤ α) (h1 : pow2 α ≤ y) (h2 : y < pow2 (α + 1)) :
    signedRounded .truncate y = floorGrid y (α - 23) := by
  have hy : 0 ≤ y := Rat.le_trans (Rat.le_of_lt (pow2_pos α)) h1
  unfold signedRounded
  rw [if_neg (by grind), absQ_of_nonneg hy]
  unfold magnitudeRounded roundedSignificand normExp
  rw [magnitudeExponent_eq_of_bounds y α h1 h2]
  have hm : max α emin32 = α := by unfold emin32; omega
  rw [hm]; rfl

/-- Model and range conditions of an anchored chain at `α`, with a binary32 block output. -/
structure AnchorModel (p : Model) (α : ℤ) : Prop where
  wide : 23 ≤ p.alignMantissaBits
  eAlignMin : ∀ f ∈ p.eAlignMin, f ≤ α
  lo : -126 ≤ α
  hi : α ≤ 127
  output : 23 ≤ p.outputMantissaBits

/-- Products of a block: finite words, none with exponent above `α`. -/
structure AnchorBlock (p : Model) (α : ℤ) (ps : List (p.Word × p.Word)) : Prop where
  finite : ∀ q ∈ ps, (p.decode q.1).isSome ∧ (p.decode q.2).isSome
  le : ∀ q ∈ ps, (prodTerm p q).significand ≠ 0 → (prodTerm p q).exponent ≤ α

/-- **Anchored block.** `c` in the binade `[2^α, 2^(α+1))` on the grid `2^(α−23)`, products of
exponent at most `α`, and `c + Σ trunc_{α−F}(aᵢbᵢ)` still in the binade: the output is
`c + ⌊Σ trunc_{α−F}(aᵢbᵢ)⌋_{2^(α−23)}`. -/
theorem evalBlock_anchored {p : Model} {α : ℤ} (hm : AnchorModel p α) {x : BlockInput p}
    (hb : AnchorBlock p α x.products) {v : ℚ} (hc : value32 x.c = some v)
    (hcg : ∃ K : ℤ, v = K * pow2 (α - 23)) (hc1 : pow2 α ≤ v) (hc2 : v < pow2 (α + 1))
    (hs1 : pow2 α ≤ v + truncSum p (α - p.alignMantissaBits) x.products)
    (hs2 : v + truncSum p (α - p.alignMantissaBits) x.products < pow2 (α + 1))
    {t : BlockTrace} (ht : evalBlock x = .ok t) :
    t.output.value = v + anchorIncrement p α x.products := by
  obtain ⟨dc, hdc, hdcv⟩ := decode32_isSome_of_value32 hc
  have hfin := hb.finite
  have hprep : prepare x = some ⟨p, x.products.map fun q => (decodeD p q.1, decodeD p q.2), dc⟩ := by
    unfold prepare; rw [hdc, prepareProducts_eq p x.products hfin]
  generalize hblk : (⟨p, x.products.map fun q => (decodeD p q.1, decodeD p q.2), dc⟩ :
    PreparedBlock) = blk at hprep
  have hev := evalPrepared_of_evalBlock hprep ht
  have hmodel : blk.model = p := by rw [← hblk]
  have hterms : blk.terms = ⟨dc.significand, dc.exponent, dc.mantissaBits⟩ ::
      x.products.map (prodTerm p) := by rw [← hblk]; exact terms_eq _ _
  have hvpos : 0 < v := by have := pow2_pos α; grind
  -- c is nonzero with exponent exactly α
  have hcnz : dc.significand ≠ 0 := by
    intro h0
    have : dc.value = 0 := by simp [Decoded.value, h0]
    rw [hdcv] at this; grind
  have hbias : (1 : ℤ) - fp32.bias ≤ α := by
    have : fp32.bias = 127 := rfl
    have := hm.lo; omega
  have hcle : dc.exponent ≤ α :=
    decode_exp_le (f := fp32) (w := x.c) (d := dc) hdc hbias
      (by rw [hdcv, ← absQ_eq, absQ_of_nonneg (Rat.le_of_lt hvpos)]; exact hc2) hcnz
  have hcge : α ≤ dc.exponent := by
    apply Classical.byContradiction; intro hlt
    have hbd := classifyNat_bounded fp32 x.c.toNat dc hdc
    unfold Decoded.Bounded at hbd
    rw [hdcv, absQ_of_nonneg (Rat.le_of_lt hvpos)] at hbd
    have h2 : 2 * pow2 dc.exponent ≤ pow2 α := by
      have := pow2_le_of_le (show dc.exponent + 1 ≤ α by omega)
      rw [pow2_add, pow2_one] at this; grind
    grind
  have hle : ∀ u ∈ blk.terms, u.significand ≠ 0 → u.exponent ≤ α := by
    intro u hu hnz
    rw [hterms] at hu
    rcases List.mem_cons.mp hu with rfl | hu
    · exact hcle
    · obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hu
      exact hb.le q hq hnz
  have hg : blk.alignGridExponent = α - p.alignMantissaBits := by
    unfold PreparedBlock.alignGridExponent
    have hpin : ∃ u ∈ blk.terms, u.significand ≠ 0 ∧ u.exponent = α :=
      ⟨_, by rw [hterms]; exact List.mem_cons_self .., hcnz, by show dc.exponent = α; omega⟩
    obtain ⟨u, hu, hnz, he⟩ := hpin
    obtain ⟨e, hbe, hle'⟩ := alignExp_term blk u hu hnz
    have hup := alignExp_upper blk α (by rw [hmodel]; exact hm.eAlignMin) hle e (by simp [hbe])
    rw [hbe, hmodel]; simp only [Option.getD_some]; omega
  -- the accumulator is c plus the truncated products
  have hacc : blk.accumulator = v + truncSum p (α - p.alignMantissaBits) x.products := by
    rw [accumulator_value, hg, hterms, sumQ_eq]
    simp only [List.map_cons, List.sum_cons, List.map_map, Function.comp_def]
    obtain ⟨K, hK⟩ := hcg
    have hcv : (⟨dc.significand, dc.exponent, dc.mantissaBits⟩ : DenormalizedProduct).value = v := by
      change dc.value = v; exact hdcv
    rw [hcv, hK, truncGrid_exact_of_grid K (α - 23) (α - p.alignMantissaBits) (by have := hm.wide; omega)]
    rfl
  have hout := evalPrepared_output_value hev (by rw [hmodel]; exact hm.output)
  rw [hacc, trunc_binade hm.lo hs1 hs2] at hout
  rw [hout]
  obtain ⟨K, hK⟩ := hcg
  rw [hK, floorGrid_shift]
  rfl

/-- The value of an anchored chain: the anchor plus the increments of its blocks. -/
def anchoredChainValue (p : Model) (α : ℤ) (v : ℚ) (blocks : List (List (p.Word × p.Word))) : ℚ :=
  v + (blocks.map (anchorIncrement p α)).sum

/-- Every running value of the chain, and every pre-floor sum, stays in the binade. -/
def InBinade (p : Model) (α : ℤ) (v : ℚ) : List (List (p.Word × p.Word)) → Prop
  | [] => pow2 α ≤ v ∧ v < pow2 (α + 1)
  | g :: rest => pow2 α ≤ v ∧ v < pow2 (α + 1) ∧
      pow2 α ≤ v + truncSum p (α - p.alignMantissaBits) g ∧
      v + truncSum p (α - p.alignMantissaBits) g < pow2 (α + 1) ∧
      InBinade p α (v + anchorIncrement p α g) rest

theorem anchorIncrement_grid (p : Model) (α : ℤ) (ps : List (p.Word × p.Word)) :
    ∃ K : ℤ, anchorIncrement p α ps = K * pow2 (α - 23) :=
  ⟨_, rfl⟩

/-- **Anchored chain.** From an anchor in the binade on the grid `2^(α−23)`, with every running
value in the binade, the chain returns the anchor plus the sum of its blocks' increments. -/
theorem runBlocks_anchored {p : Model} {α : ℤ} (hm : AnchorModel p α) :
    ∀ (blocks : List (List (p.Word × p.Word))) (c : F32) (v : ℚ) (ts : List BlockTrace),
      value32 c = some v → (∃ K : ℤ, v = K * pow2 (α - 23)) →
      (∀ g ∈ blocks, AnchorBlock p α g) → InBinade p α v blocks →
      runBlocks p c blocks = .ok ts → runValue c ts = anchoredChainValue p α v blocks
  | [], c, v, ts, hc, _, _, _, hrun => by
    simp only [runBlocks, Except.ok.injEq] at hrun; subst hrun
    simp [runValue, value32D, hc, anchoredChainValue]
    grind
  | g :: rest, c, v, ts, hc, hcg, hg, hbin, hrun => by
    obtain ⟨h1, h2, h3, h4, hrest⟩ := hbin
    simp only [runBlocks] at hrun
    split at hrun
    · cases hrun
    · rename_i t ht
      split at hrun
      · cases hrun
      · rename_i ts' hts'
        cases hrun
        rw [runValue_cons]
        have hval := evalBlock_anchored (x := ⟨g, c⟩) hm (hg g (by simp)) hc hcg h1 h2 h3 h4 ht
        have hc' : value32 t.output.bits = some (v + anchorIncrement p α g) := by rw [value32_output, hval]
        have hcg' : ∃ K : ℤ, v + anchorIncrement p α g = K * pow2 (α - 23) := by
          obtain ⟨K, hK⟩ := hcg
          obtain ⟨L, hL⟩ := anchorIncrement_grid p α g
          exact ⟨K + L, by rw [hK, hL, Rat.intCast_add]; grind⟩
        rw [runBlocks_anchored hm rest t.output.bits _ ts' hc' hcg' (fun g' h' => hg g' (by simp [h'])) hrest hts']
        simp only [anchoredChainValue, List.map_cons, List.sum_cons]
        grind

/-- **Block-granular schedule freedom.** Two anchored chains over permutations of the same blocks
return the same value. -/
theorem anchored_blocks_perm {p : Model} {α : ℤ} (hm : AnchorModel p α)
    (b₁ b₂ : List (List (p.Word × p.Word))) (hperm : b₁.Perm b₂) (c : F32) (v : ℚ)
    (hc : value32 c = some v) (hcg : ∃ K : ℤ, v = K * pow2 (α - 23))
    (hg₁ : ∀ g ∈ b₁, AnchorBlock p α g) (hg₂ : ∀ g ∈ b₂, AnchorBlock p α g)
    (hr₁ : InBinade p α v b₁) (hr₂ : InBinade p α v b₂)
    {ts₁ ts₂ : List BlockTrace} (h₁ : runBlocks p c b₁ = .ok ts₁) (h₂ : runBlocks p c b₂ = .ok ts₂) :
    runValue c ts₁ = runValue c ts₂ := by
  rw [runBlocks_anchored hm b₁ c v ts₁ hc hcg hg₁ hr₁ h₁, runBlocks_anchored hm b₂ c v ts₂ hc hcg hg₂ hr₂ h₂]
  unfold anchoredChainValue; rw [sum_perm_q (hperm.map _)]

end MMAlgebra.TC
