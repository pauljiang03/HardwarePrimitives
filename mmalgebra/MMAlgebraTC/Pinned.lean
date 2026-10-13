import OzakiTC

/-! # Pinned accumulation on the Tensor Core model

A Tensor Core block FMA aligns `c` and its products to the largest exponent `α` of a nonzero term
and truncates every term toward zero to the grid `2^(α − F)`. Fix that exponent: put in every block
one product of exponent exactly `α` (a *pin*, for example the cancelling pair `+2^α, −2^α`), keep
every other product at or below it, and keep the running value on the grid. Then the block adds
`Σ trunc_{α−F}(aᵢbᵢ)` to `c` exactly, as long as the result stays below `2^(α−F+24)` in magnitude
(`evalBlock_pinned`), and the pin pair contributes nothing (`truncSum_pair`).

A chain of pinned blocks from `c₀` therefore returns `c₀ + Σ trunc_{α−F}(aᵢbᵢ)` over all its
products (`runBlocks_pinned`): a function of the multiset of products alone. Every order, every
assignment of products to blocks (`pinned_schedule_free`), and every split-K whose partial results
are added in binary32 (`pinned_splitK`) gives the same value. With the grid `g = α − F` fixed,
V100, A100 and H100 compute the same function. The development builds on the exactness lemmas of
`OzakiTC`. -/

open TensorCore
open Ozaki
open Ozaki.TC

namespace MMAlgebra.TC


/-- The denormalized product of an encoded operand pair, as the block FMA sees it. -/
def prodTerm (p : Model) (q : p.Word × p.Word) : DenormalizedProduct :=
  denormalizedMul (decodeD p q.1) (decodeD p q.2)

/-- `Σ trunc_g(aᵢbᵢ)`: each product truncated toward zero to a multiple of `2^g`. -/
def truncSum (p : Model) (g : ℤ) (ps : List (p.Word × p.Word)) : ℚ :=
  (ps.map fun q => truncGrid (prodTerm p q).value g).sum

theorem truncSum_nil (p : Model) (g : ℤ) : truncSum p g [] = 0 := rfl

theorem truncSum_append (p : Model) (g : ℤ) (xs ys : List (p.Word × p.Word)) :
    truncSum p g (xs ++ ys) = truncSum p g xs + truncSum p g ys := by
  unfold truncSum; rw [sum_map_append]

theorem truncSum_perm (p : Model) (g : ℤ) {xs ys : List (p.Word × p.Word)} (h : xs.Perm ys) :
    truncSum p g xs = truncSum p g ys := by
  unfold truncSum; exact sum_perm_q (h.map _)

/-- A truncated sum is an integer multiple of `2^g`. -/
theorem truncSum_grid (p : Model) (g : ℤ) :
    ∀ ps : List (p.Word × p.Word), ∃ z : ℤ, truncSum p g ps = z * pow2 g
  | [] => ⟨0, by simp [truncSum]⟩
  | q :: ps => by
    obtain ⟨z, hz⟩ := truncSum_grid p g ps
    refine ⟨truncBits (prodTerm p q).value g + z, ?_⟩
    have h : truncSum p g (q :: ps) = truncGrid (prodTerm p q).value g + truncSum p g ps := by
      simp [truncSum, List.map_cons, List.sum_cons]
    rw [h, hz]; unfold truncGrid; rw [Rat.intCast_add]; grind

/-- A cancelling pin pair contributes nothing. -/
theorem truncSum_pair (p : Model) (g : ℤ) (q q' : p.Word × p.Word)
    (h : (prodTerm p q').value = -(prodTerm p q).value) : truncSum p g [q, q'] = 0 := by
  simp only [truncSum, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, h, truncGrid_neg]
  grind

/-! ## One block -/

/-- The alignment exponent is `α` when some nonzero term has exponent `α`, no nonzero term exceeds
it, and the minimum alignment exponent does not exceed it. -/
theorem alignExp_eq (b : PreparedBlock) (α : ℤ) (hf : ∀ f ∈ b.model.eAlignMin, f ≤ α)
    (ht : ∀ t ∈ b.terms, t.significand ≠ 0 → t.exponent ≤ α)
    (hpin : ∃ t ∈ b.terms, t.significand ≠ 0 ∧ t.exponent = α) : b.alignExp = some α := by
  obtain ⟨t, htm, hnz, he⟩ := hpin
  obtain ⟨e, hb, hle⟩ := alignExp_term b t htm hnz
  have hup := alignExp_upper b α hf ht e (by simp [hb])
  rw [hb]; congr 1; omega

theorem abs_grid_natAbs {k g : ℤ} (h : Rat.abs ((k : ℚ) * pow2 g) < 2 ^ (g + 24)) :
    k.natAbs < 2 ^ 24 := by
  have hp : (0 : ℚ) < pow2 g := pow2_pos g
  have habs : Rat.abs ((k : ℚ) * pow2 g) = Rat.abs (k : ℚ) * pow2 g := by
    rw [Ozaki.abs_mul]; congr 1; exact abs_of_nonneg (Rat.le_of_lt hp)
  have e24 : (2 : ℚ) ^ (g + 24) = pow2 24 * pow2 g := by
    rw [← pow2_eq, pow2_add, Rat.mul_comm]
  rw [habs, e24] at h
  have h' : Rat.abs (k : ℚ) < pow2 24 := by
    apply Classical.byContradiction; intro hn
    have : pow2 24 * pow2 g ≤ Rat.abs (k : ℚ) * pow2 g :=
      Rat.mul_le_mul_of_nonneg_right (by grind) (Rat.le_of_lt hp)
    grind
  rw [abs_intCast, show (24 : ℤ) = ((24 : ℕ) : ℤ) from rfl, pow2_eq, two_pow_natCast] at h'
  exact Rat.natCast_lt_natCast.mp h'

/-- **Pinned prepared block.** The output is the sum of the terms truncated to `2^(α−F)`. -/
theorem evalPrepared_pinned (blk : PreparedBlock) {t : BlockTrace} (hev : evalPrepared blk = .ok t)
    (α : ℤ) (hf : ∀ f ∈ blk.model.eAlignMin, f ≤ α)
    (hle : ∀ u ∈ blk.terms, u.significand ≠ 0 → u.exponent ≤ α)
    (hpin : ∃ u ∈ blk.terms, u.significand ≠ 0 ∧ u.exponent = α)
    (hlo : -149 ≤ α - blk.model.alignFracBits) (hhi : α - blk.model.alignFracBits ≤ 104)
    (hrange : Rat.abs blk.accumulator < 2 ^ (α - blk.model.alignFracBits + 24)) :
    t.output.value = blk.accumulator ∧
      blk.accumulator = sumQ (blk.terms.map fun u => truncGrid u.value (α - blk.model.alignFracBits)) := by
  have hg : blk.alignGridExponent = α - blk.model.alignFracBits := by
    unfold PreparedBlock.alignGridExponent; rw [alignExp_eq blk α hf hle hpin]; rfl
  have hacc := accumulator_value blk
  rw [hg] at hacc
  refine ⟨?_, hacc⟩
  have hk : blk.accumulator = (sumZ blk.alignedBits : ℚ) * pow2 (α - blk.model.alignFracBits) := by
    unfold PreparedBlock.accumulator; rw [hg]
  have hnat : (sumZ blk.alignedBits).natAbs < 2 ^ 24 := by
    rw [hk] at hrange; exact abs_grid_natAbs hrange
  have hfin : FiniteValue32 blk.accumulator := by
    rw [hk]; exact grid_finiteValue32 _ _ hlo hhi hnat
  rw [evalPrepared_output_value hev, signedRounded_trunc_of_finite _ hfin]

theorem terms_eq {p : Model} (ps : List (p.Word × p.Word)) (dc : Decoded) :
    (⟨p, ps.map fun q => (decodeD p q.1, decodeD p q.2), dc⟩ : PreparedBlock).terms =
      ⟨dc.significand, dc.exponent, dc.mantissaBits⟩ :: ps.map (prodTerm p) := by
  simp [PreparedBlock.terms, List.map_map, Function.comp_def, prodTerm]

theorem evalPrepared_of_evalBlock {p : Model} {x : BlockInput p} {blk : PreparedBlock}
    (hprep : prepare x = some blk) {t : BlockTrace} (ht : evalBlock x = .ok t) :
    evalPrepared blk = .ok t := by
  unfold evalBlock at ht
  split at ht
  · cases ht
  · rw [hprep] at ht; exact ht

theorem prepare_of_finite {p : Model} {x : BlockInput p}
    (hfin : ∀ q ∈ x.products, (p.decode q.1).isSome ∧ (p.decode q.2).isSome) {dc : Decoded}
    (hdc : decode32 x.c = some dc) :
    prepare x = some ⟨p, x.products.map fun q => (decodeD p q.1, decodeD p q.2), dc⟩ := by
  unfold prepare; rw [hdc, prepareProducts_eq p x.products hfin]

/-- Conditions for a pinned block of a model at alignment exponent `α`: finite words, no nonzero
product above `α`, and one nonzero product at exactly `α`. -/
structure PinnedBlock (p : Model) (α : ℤ) (ps : List (p.Word × p.Word)) : Prop where
  finite : ∀ q ∈ ps, (p.decode q.1).isSome ∧ (p.decode q.2).isSome
  le : ∀ q ∈ ps, (prodTerm p q).significand ≠ 0 → (prodTerm p q).exponent ≤ α
  pin : ∃ q ∈ ps, (prodTerm p q).significand ≠ 0 ∧ (prodTerm p q).exponent = α

/-- Model conditions: `F ≥ 23`, the minimum alignment exponent at most `α`, and the grid
`2^(α−F)` within binary32's range of exact multiples. -/
structure PinnedModel (p : Model) (α : ℤ) : Prop where
  wide : 23 ≤ p.alignFracBits
  eAlignMin : ∀ f ∈ p.eAlignMin, f ≤ α
  lo : -149 ≤ α - p.alignFracBits
  hi : α - p.alignFracBits ≤ 104

/-- **Pinned block.** `c` on the grid `2^(α−F)`, a pinned block, and a result below `2^(α−F+24)`:
the output is `c + Σ trunc_{α−F}(aᵢbᵢ)` exactly. -/
theorem evalBlock_pinned {p : Model} {α : ℤ} (hm : PinnedModel p α) {x : BlockInput p}
    (hb : PinnedBlock p α x.products) {v : ℚ} (hc : value32 x.c = some v)
    (hcg : ∃ z : ℤ, v = z * pow2 (α - p.alignFracBits))
    (hrange : Rat.abs (v + truncSum p (α - p.alignFracBits) x.products) <
      2 ^ (α - p.alignFracBits + 24))
    (hcr : Rat.abs v < 2 ^ (α - p.alignFracBits + 24))
    {t : BlockTrace} (ht : evalBlock x = .ok t) :
    t.output.value = v + truncSum p (α - p.alignFracBits) x.products := by
  obtain ⟨dc, hdc, hdcv⟩ := decode32_isSome_of_value32 hc
  have hprep := prepare_of_finite hb.finite hdc
  generalize hblk : (⟨p, x.products.map fun q => (decodeD p q.1, decodeD p q.2), dc⟩ :
    PreparedBlock) = blk at hprep
  have hev := evalPrepared_of_evalBlock hprep ht
  have hmodel : blk.model = p := by rw [← hblk]
  have hterms : blk.terms = ⟨dc.significand, dc.exponent, dc.mantissaBits⟩ ::
      x.products.map (prodTerm p) := by rw [← hblk]; exact terms_eq _ _
  -- c's exponent is at most α
  have hcexp : dc.significand ≠ 0 → dc.exponent ≤ α := by
    intro hnz
    have hlt : Rat.abs dc.value < 2 ^ (α + 1) := by
      rw [hdcv]
      have : (2 : ℚ) ^ (α - p.alignFracBits + 24) ≤ 2 ^ (α + 1) := by
        rw [← pow2_eq, ← pow2_eq]; exact pow2_le_of_le (by have := hm.wide; omega)
      grind
    have hbias : (1 : ℤ) - fp32.bias ≤ α := by
      have : fp32.bias = 127 := rfl
      have := hm.lo; have := hm.wide; omega
    exact decode_exp_le (f := fp32) (w := x.c) (d := dc) hdc hbias hlt hnz
  have hle : ∀ u ∈ blk.terms, u.significand ≠ 0 → u.exponent ≤ α := by
    intro u hu hnz
    rw [hterms] at hu
    rcases List.mem_cons.mp hu with rfl | hu
    · exact hcexp hnz
    · obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hu
      exact hb.le q hq hnz
  have hpin : ∃ u ∈ blk.terms, u.significand ≠ 0 ∧ u.exponent = α := by
    obtain ⟨q, hq, hnz, he⟩ := hb.pin
    exact ⟨prodTerm p q, by rw [hterms]; exact List.mem_cons_of_mem _ (List.mem_map.mpr ⟨q, hq, rfl⟩),
      hnz, he⟩
  have hsum : sumQ (blk.terms.map fun u => truncGrid u.value (α - blk.model.alignFracBits)) =
      v + truncSum p (α - p.alignFracBits) x.products := by
    rw [hterms, hmodel, sumQ_eq]
    simp only [List.map_cons, List.sum_cons, List.map_map, Function.comp_def]
    obtain ⟨z, hz⟩ := hcg
    have hcv : (⟨dc.significand, dc.exponent, dc.mantissaBits⟩ : DenormalizedProduct).value = v := by
      change dc.value = v; exact hdcv
    rw [hcv, hz, truncGrid_fixed]
    rfl
  have hacc_eq : blk.accumulator = v + truncSum p (α - p.alignFracBits) x.products := by
    rw [accumulator_value]
    have hg : blk.alignGridExponent = α - blk.model.alignFracBits := by
      unfold PreparedBlock.alignGridExponent
      rw [alignExp_eq blk α (by rw [hmodel]; exact hm.eAlignMin) hle hpin]; rfl
    rw [hg, hsum]
  obtain ⟨hout, _⟩ := evalPrepared_pinned blk hev α (by rw [hmodel]; exact hm.eAlignMin) hle hpin
    (by rw [hmodel]; exact hm.lo) (by rw [hmodel]; exact hm.hi)
    (by rw [hacc_eq, hmodel]; exact hrange)
  rw [hout, hacc_eq]

/-! ## Chains -/

/-- Every prefix of the chain, at a block boundary, stays below `2^(g+24)`. -/
def PrefixesInRange (p : Model) (g : ℤ) (v : ℚ) (blocks : List (List (p.Word × p.Word))) : Prop :=
  ∀ n : ℕ, n ≤ blocks.length → Rat.abs (v + truncSum p g (blocks.take n).flatten) < 2 ^ (g + 24)

/-- **Pinned chain.** From `c` on the grid with every block pinned at `α` and every prefix in
range, the chain returns `c + Σ trunc_{α−F}(aᵢbᵢ)` over all products of all blocks. -/
theorem runBlocks_pinned {p : Model} {α : ℤ} (hm : PinnedModel p α) :
    ∀ (blocks : List (List (p.Word × p.Word))) (c : F32) (v : ℚ) (ts : List BlockTrace),
      value32 c = some v → (∃ z : ℤ, v = z * pow2 (α - p.alignFracBits)) →
      (∀ gr ∈ blocks, PinnedBlock p α gr) →
      PrefixesInRange p (α - p.alignFracBits) v blocks →
      runBlocks p c blocks = .ok ts →
      runValue c ts = v + truncSum p (α - p.alignFracBits) blocks.flatten
  | [], c, v, ts, hc, _, _, _, hrun => by
    simp only [runBlocks, Except.ok.injEq] at hrun; subst hrun
    simp [runValue, value32D, hc, truncSum]
    grind
  | gr :: rest, c, v, ts, hc, hcg, hg, hpre, hrun => by
    simp only [runBlocks] at hrun
    split at hrun
    · cases hrun
    · rename_i t ht
      split at hrun
      · cases hrun
      · rename_i ts' hts'
        cases hrun
        rw [runValue_cons]
        have h0 := hpre 0 (by simp)
        have h1 := hpre 1 (by simp)
        simp only [List.take_zero, List.flatten_nil, truncSum_nil, Rat.add_zero, List.take_succ_cons,
          List.flatten_cons, List.flatten_nil, List.append_nil] at h0 h1
        have hval := evalBlock_pinned (x := ⟨gr, c⟩) hm (hg gr (by simp)) hc hcg h1 h0 ht
        have hc' : value32 t.output.bits = some (v + truncSum p (α - p.alignFracBits) gr) := by
          rw [value32_output, hval]
        have hcg' : ∃ z : ℤ, v + truncSum p (α - p.alignFracBits) gr =
            z * pow2 (α - p.alignFracBits) := by
          obtain ⟨z, hz⟩ := hcg
          obtain ⟨w, hw⟩ := truncSum_grid p (α - p.alignFracBits) gr
          exact ⟨z + w, by rw [hz, hw, Rat.intCast_add]; grind⟩
        have hpre' : PrefixesInRange p (α - p.alignFracBits)
            (v + truncSum p (α - p.alignFracBits) gr) rest := by
          intro n hn
          have := hpre (n + 1) (by simp; omega)
          simp only [List.take_succ_cons, List.flatten_cons, truncSum_append] at this
          grind
        rw [runBlocks_pinned hm rest t.output.bits _ ts' hc' hcg'
          (fun g' hg' => hg g' (by simp [hg'])) hpre' hts', List.flatten_cons, truncSum_append]
        grind

/-- **Schedule freedom.** Two pinned chains from the same `c` whose blocks hold the same multiset
of products (in any order, grouped into blocks in any way) return the same value. -/
theorem pinned_schedule_free {p : Model} {α : ℤ} (hm : PinnedModel p α)
    (b₁ b₂ : List (List (p.Word × p.Word))) (hperm : b₁.flatten.Perm b₂.flatten)
    (c : F32) (v : ℚ) (hc : value32 c = some v) (hcg : ∃ z : ℤ, v = z * pow2 (α - p.alignFracBits))
    (hg₁ : ∀ gr ∈ b₁, PinnedBlock p α gr) (hg₂ : ∀ gr ∈ b₂, PinnedBlock p α gr)
    (hr₁ : PrefixesInRange p (α - p.alignFracBits) v b₁)
    (hr₂ : PrefixesInRange p (α - p.alignFracBits) v b₂)
    {ts₁ ts₂ : List BlockTrace} (h₁ : runBlocks p c b₁ = .ok ts₁) (h₂ : runBlocks p c b₂ = .ok ts₂) :
    runValue c ts₁ = runValue c ts₂ := by
  rw [runBlocks_pinned hm b₁ c v ts₁ hc hcg hg₁ hr₁ h₁,
    runBlocks_pinned hm b₂ c v ts₂ hc hcg hg₂ hr₂ h₂, truncSum_perm p _ hperm]

/-- **Split-K.** Chains from `0` over two parts return values that add up to the value of one chain
over both parts. Their sum is a binary32 value on the grid, so a binary32 addition of the two
partial results returns it unchanged (`int`-grid argument of `grid_finiteValue32`). -/
theorem pinned_splitK {p : Model} {α : ℤ} (hm : PinnedModel p α)
    (b₁ b₂ : List (List (p.Word × p.Word)))
    (hg : ∀ gr ∈ b₁ ++ b₂, PinnedBlock p α gr)
    (hr₁ : PrefixesInRange p (α - p.alignFracBits) 0 b₁)
    (hr₂ : PrefixesInRange p (α - p.alignFracBits) 0 b₂)
    (hr : PrefixesInRange p (α - p.alignFracBits) 0 (b₁ ++ b₂))
    {ts₁ ts₂ ts : List BlockTrace} (h₁ : runBlocks p 0 b₁ = .ok ts₁)
    (h₂ : runBlocks p 0 b₂ = .ok ts₂) (h : runBlocks p 0 (b₁ ++ b₂) = .ok ts) :
    runValue 0 ts₁ + runValue 0 ts₂ = runValue 0 ts ∧
      FiniteValue32 (runValue 0 ts₁ + runValue 0 ts₂) := by
  have hz : value32 (0 : F32) = some 0 := by decide +kernel
  have hcg : ∃ z : ℤ, (0 : ℚ) = z * pow2 (α - p.alignFracBits) := ⟨0, by simp⟩
  have e₁ := runBlocks_pinned hm b₁ 0 0 ts₁ hz hcg (fun g' h' => hg g' (List.mem_append_left _ h')) hr₁ h₁
  have e₂ := runBlocks_pinned hm b₂ 0 0 ts₂ hz hcg (fun g' h' => hg g' (List.mem_append_right _ h')) hr₂ h₂
  have e := runBlocks_pinned hm (b₁ ++ b₂) 0 0 ts hz hcg hg hr h
  have hsum : runValue 0 ts₁ + runValue 0 ts₂ = runValue 0 ts := by
    rw [e₁, e₂, e, List.flatten_append, truncSum_append]; grind
  refine ⟨hsum, ?_⟩
  rw [hsum, e]
  obtain ⟨w, hw⟩ := truncSum_grid p (α - p.alignFracBits) (b₁ ++ b₂).flatten
  have hfull := hr (b₁ ++ b₂).length (by omega)
  rw [List.take_length] at hfull
  rw [Rat.zero_add] at hfull ⊢
  rw [hw] at hfull ⊢
  exact grid_finiteValue32 _ _ hm.lo hm.hi (abs_grid_natAbs hfull)

end MMAlgebra.TC
