import OzakiMC.Models

/-! # Exact Matrix Core blocks with cancellation

The AMD analogue of `OzakiTC.Cancellation`. `evalBlock_int` asks `|c| + Σ|aᵢbᵢ| ≤ 2^24`; what each
configuration of the Matrix Core model needs is weaker, and differs by architecture. With integer
operands, an integer `c` and every product at most `2^24` in magnitude (true for slices of at most
`12` bits):

* **SFMA, CDNA 1** (`correct_rounding`): `S_acc` is the exact sum, so the block is exact whenever
  the exact sum `c + Σ aᵢbᵢ` is within `2^24`, whatever the products' total magnitude;
* **CDNA 3** (`global_alignment`): products of exponent at most `24` align to `24` mantissa bits
  without loss, and the late addition of `c` rounds an integer down to an integer; exact whenever
  `|c| ≤ 2^24` and the exact sum is within `2^24`;
* **CDNA 2** (`pair_wise_sum`): every pairwise sum is rounded to binary32, so every pairwise sum
  must be within `2^24` as well (`PairwiseSumsBounded`), not only the total; cancellation inside a
  pairwise sum is free, cancellation across pairwise sums is not.

`accumulate_cancel` states this for prepared blocks and `evalBlock_cancel` for encoded ones. As on
the Tensor Core, this is the exact condition, not a scheduling rule: the sums are known only after
the products are computed. -/

open MatrixCore

namespace Ozaki.MC

/-! ## The pairwise sum -/

/-- Every pairwise sum of CDNA 2 on `zs`, with `depth` levels, is at most `2^24` in magnitude. -/
def PairwiseSumsBounded : ℕ → List ℤ → Prop
  | _, [] => True
  | _, [_] => True
  | 0, _ :: _ :: _ => False
  | depth + 1, z1 :: z2 :: rest =>
    PairwiseSumsBounded depth ((z1 :: z2 :: rest).take ((z1 :: z2 :: rest).length / 2)) ∧
      PairwiseSumsBounded depth ((z1 :: z2 :: rest).drop ((z1 :: z2 :: rest).length / 2)) ∧
      (z1 :: z2 :: rest).sum.natAbs ≤ 2 ^ 24

/-- **The pairwise sum with cancellation.** When every pairwise sum is at most `2^24` in magnitude,
the pairwise sum of integers is their exact sum. -/
theorem pairwiseGroupSum_cancel (ftz : Bool) : ∀ (depth : ℕ) (zs : List ℤ), PairwiseSumsBounded depth zs →
    pairwiseGroupSum ftz depth (zs.map fun z : ℤ => (z : ℚ)) = some ((zs.sum : ℤ) : ℚ)
  | _, [], _ => by simp [pairwiseGroupSum]
  | _, [z], _ => by simp [pairwiseGroupSum]
  | 0, _ :: _ :: _, h => absurd h (by simp [PairwiseSumsBounded])
  | depth + 1, z1 :: z2 :: rest, ⟨hl, hr, hs⟩ => by
    generalize hzs : z1 :: z2 :: rest = zs at hl hr hs
    have hunfold : pairwiseGroupSum ftz (depth + 1) (zs.map fun z : ℤ => (z : ℚ)) =
        (pairwiseGroupSum ftz depth ((zs.take (zs.length / 2)).map fun z : ℤ => (z : ℚ))).bind fun u =>
          (pairwiseGroupSum ftz depth ((zs.drop (zs.length / 2)).map fun z : ℤ => (z : ℚ))).bind fun v =>
            flValue ftz (u + v) := by
      rw [← hzs, List.map_cons, List.map_cons, pairwiseGroupSum]
      simp only [List.length_cons, List.map_take, List.map_drop, List.map_cons, List.length_map,
        Option.bind_eq_bind]
      all_goals simp
    have htd := List.take_append_drop (zs.length / 2) zs
    have hsum : zs.sum = (zs.take (zs.length / 2)).sum + (zs.drop (zs.length / 2)).sum := by
      conv => lhs; rw [← htd]
      rw [List.sum_append]
    rw [hunfold, pairwiseGroupSum_cancel ftz depth _ hl, pairwiseGroupSum_cancel ftz depth _ hr]
    simp only [Option.bind_some]
    rw [← Rat.intCast_add, ← hsum]
    exact flValue_int ftz _ hs

/-- Magnitudes within `2^24` give pairwise sums that are all within `2^24`. -/
theorem pairwiseSumsBounded_of_bound : ∀ (depth : ℕ) (zs : List ℤ), zs.length ≤ depth + 1 →
    (zs.map Int.natAbs).sum ≤ 2 ^ 24 → PairwiseSumsBounded depth zs
  | _, [], _, _ => by simp [PairwiseSumsBounded]
  | _, [_], _, _ => by simp [PairwiseSumsBounded]
  | 0, _ :: _ :: _, hl, _ => by simp at hl
  | depth + 1, z1 :: z2 :: rest, hl, hb => by
    generalize hzs : z1 :: z2 :: rest = zs at hl hb
    have h2 : 2 ≤ zs.length := by rw [← hzs]; simp
    have htd := List.take_append_drop (zs.length / 2) zs
    have hsplit : (zs.map Int.natAbs).sum = ((zs.take (zs.length / 2)).map Int.natAbs).sum +
        ((zs.drop (zs.length / 2)).map Int.natAbs).sum := by
      conv => lhs; rw [← htd]
      rw [List.map_append, List.sum_append]
    have h1 := pairwiseSumsBounded_of_bound depth (zs.take (zs.length / 2)) (by simp; omega) (by omega)
    have h3 := pairwiseSumsBounded_of_bound depth (zs.drop (zs.length / 2)) (by simp; omega) (by omega)
    have h4 := Nat.le_trans (natAbs_sum_le zs) hb
    rw [← hzs] at h1 h3 h4 ⊢
    exact ⟨h1, h3, h4⟩

/-! ## Prepared blocks -/

/-- A prepared block of integer operands and an integer `c`, every product and `c` within `2^24`,
and the exact sum `Σ p_ℓ + c` within `2^24`; no bound on `Σ|p_ℓ|`. -/
structure IntPreparedC (x : Prepared) : Prop where
  a : ∀ u ∈ x.a, IntOperand u
  b : ∀ u ∈ x.b, IntOperand u
  c : IntOperand x.c
  p_le : ∀ q ∈ x.p, absQ q.value ≤ pow2 24
  c_le : absQ x.c.value ≤ pow2 24
  sum_le : absQ x.exact ≤ pow2 24

namespace IntPreparedC

variable {x : Prepared} (h : IntPreparedC x)
include h

theorem p : ∀ q ∈ x.p, IntOperand q := by
  intro q hq
  obtain ⟨a, ha, b, hb, rfl⟩ := mem_zipWith' hq
  exact (h.a a ha).mul (h.b b hb)

theorem flushed : x.flushed = x := by
  obtain ⟨a, b, c⟩ := x
  simp only [Prepared.flushed, Prepared.mk.injEq]
  refine ⟨?_, ?_, h.c.flush⟩
  · conv => rhs; rw [← List.map_id a]
    exact List.map_congr_left fun u hu => (h.a u hu).flush
  · conv => rhs; rw [← List.map_id b]
    exact List.map_congr_left fun u hu => (h.b u hu).flush

theorem productOverflows : x.productOverflows = false := by
  unfold Prepared.productOverflows
  apply List.any_eq_false.mpr
  intro q hq hle
  have h1 := h.p_le q hq
  have h2 : pow2 24 < pow2 128 := pow2_lt_of_lt (by decide)
  have := of_decide_eq_true hle
  grind

/-- The products as a list of integers. -/
theorem ints : ∃ zs : List ℤ, x.p.map Unpacked.value = zs.map (fun z : ℤ => (z : ℚ)) :=
  intList (x.p.map Unpacked.value) (by
    intro q hq
    obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hq
    obtain ⟨⟨z, hz⟩, _⟩ := h.p r hr
    exact ⟨z, hz⟩)

theorem c_int : ∃ z : ℤ, x.c.value = z := h.c.1

end IntPreparedC

/-- **CDNA 2 with cancellation**: the pairwise sums of integer products, each within `2^24`,
plus `c`, is the exact sum. -/
theorem pairwiseSum_cancel (P : Model) {x : Prepared} (h : IntPreparedC x)
    (htree : ∀ zs : List ℤ, x.p.map Unpacked.value = zs.map (fun z : ℤ => (z : ℚ)) →
      PairwiseSumsBounded zs.length zs) :
    pairwiseSum P x = some x.exact := by
  have hx' : (if P.subnormals then x else x.flushed) = x := by
    split
    · rfl
    · exact h.flushed
  obtain ⟨zs, hzs⟩ := h.ints
  have hps : x.p.mapM (fun p => flValue (!P.subnormals) p.value) =
      some (zs.map fun z : ℤ => (z : ℚ)) := by
    rw [← hzs]
    refine Ozaki.mapM_eq_some_map fun q hq => ?_
    obtain ⟨⟨z, hz⟩, _⟩ := h.p q hq
    rw [hz]
    exact flValue_int _ z (natAbs_le_of_absQ (by rw [← hz]; exact h.p_le q hq))
  have htree' := pairwiseGroupSum_cancel (!P.subnormals) zs.length zs (htree zs hzs)
  unfold pairwiseSum
  simp only [hx', hps, Option.bind_eq_bind, Option.bind_some, List.length_map, htree']
  unfold Prepared.exact
  rw [hzs, sumQ_cast]
  congr 1
  grind

/-- **CDNA 3 with cancellation**: global alignment of integer products within `2^24` and an integer
`c` within `2^24` is exact whenever the exact sum is within `2^24`. -/
theorem alignedAccumulation_cancel {P : Model} (hacc : P.accumulation = .globalAlignment)
    (hpadding : 1 ≤ P.padding) (hlate : P.late = {}) (hcz : P.cZeroExp = some (-126)) {x : Prepared}
    (h : IntPreparedC x) : alignedAccumulation P x = x.exact := by
  have hprod := h.p
  have he24 : ∀ q ∈ x.p, q.m ≠ 0 → q.e ≤ 24 := fun q hq hm => (hprod q hq).exp_le hm (h.p_le q hq)
  obtain ⟨zs, hzs⟩ := h.ints
  have hS : sumQ (x.p.map Unpacked.value) = ((zs.sum : ℤ) : ℚ) := by rw [hzs, sumQ_cast]
  -- the product sum: truncation to `23 + padding ≥ 24` mantissa bits is exact
  have hal : productSum P x.p = alignedSum P.padding x.p := by unfold productSum; rw [hacc]
  have hps : productSum P x.p = (maxExp x.p, sumQ (x.p.map Unpacked.value)) := by
    rw [hal]
    unfold alignedSum
    split
    · rename_i hm; rw [hm, sum_of_zero (maxExp_none hm)]
    · rename_i e hm
      rw [hm]
      congr 1
      congr 1
      apply List.map_congr_left
      intro q hq
      have he := maxExp_upper he24 e hm
      exact truncGrid_of_onGrid ((hprod q hq).onGrid (by omega))
  have heMax : ∀ e, (productSum P x.p).1 = some e → e ≤ 24 := by
    rw [hps]; exact maxExp_upper he24
  have hcE : ∀ eC, cExp P x.c = some eC → eC ≤ 24 := by
    intro eC he
    unfold cExp at he
    split at he
    · rw [hcz] at he; cases he; omega
    · rename_i hm; cases he; exact h.c.exp_le hm h.c_le
  obtain ⟨zc, hzc⟩ := h.c_int
  have hT : ∀ T : ℤ, absQ (T : ℚ) ≤ pow2 24 → normalizeRD P.late.accMantissaBits (T : ℚ) = T := by
    intro T hT
    unfold normalizeRD
    split
    · rename_i h0; rw [h0]
    · rename_i h0
      have hpos := absQ_pos h0
      have hlog : log2Floor (absQ (T : ℚ)) ≤ 24 :=
        pow2_le_iff.mp (Rat.le_trans (log2Floor_spec hpos).1 hT)
      have hn : normExp (absQ (T : ℚ)) ≤ 24 := by unfold normExp; omega
      have hacc31 : P.late.accMantissaBits = 31 := by rw [hlate]
      exact rdGrid_of_onGrid (OnGrid.mono ⟨T, by rw [pow2_zero, Rat.mul_one]⟩ (by omega))
  have hsumbound : absQ ((zs.sum + zc : ℤ) : ℚ) ≤ pow2 24 := by
    have := h.sum_le
    unfold Prepared.exact at this
    rw [hS, hzc, ← Rat.intCast_add] at this
    exact this
  unfold alignedAccumulation
  simp only
  rcases lateSum_cases P (productSum P x.p).1 (productSum P x.p).2 x.c with
    ⟨hc0, hl⟩ | ⟨e, eC, he, hce, _, hl⟩ | ⟨eC, hce, _, hl⟩
  · rw [hl, hps]; unfold Prepared.exact; rw [cExp_none hc0]; grind
  · rw [hl, hps]
    have hsc : shiftedC P e eC x.c = x.c.value := by
      unfold shiftedC
      rw [hlate]
      simp only
      have := heMax e he
      exact rdGrid_of_onGrid (h.c.onGrid (by omega))
    rw [hsc]; rfl
  · rw [hl, hps]
    have hle := hcE eC hce
    unfold shiftedSum
    rw [hS, hlate]
    simp only [rdMantissa]
    rw [rdGrid_of_onGrid (OnGrid.mono ⟨zs.sum, by rw [pow2_zero, Rat.mul_one]⟩ (by omega)), hzc,
      ← Rat.intCast_add]
    have := hT (zs.sum + zc) hsumbound
    rw [hlate] at this
    rw [this]
    unfold Prepared.exact
    rw [hS, hzc, Rat.intCast_add]


/-- **Exact accumulation with cancellation.** On an exact configuration, `S_acc` of a block of
integer operands whose products and `c` are within `2^24` and whose exact sum is within `2^24` is
that sum; on CDNA 2 every pairwise sum must be within `2^24` too. -/
theorem accumulate_cancel {P : Model} (hP : ExactConfig P) {x : Prepared} (h : IntPreparedC x)
    (htree : P.accumulation = .pairWiseSum → ∀ zs : List ℤ,
      x.p.map Unpacked.value = zs.map (fun z : ℤ => (z : ℚ)) → PairwiseSumsBounded zs.length zs) :
    accumulate P x = .ok x.exact := by
  unfold accumulate
  rw [h.productOverflows, Bool.and_false]
  simp only [Bool.false_eq_true, ↓reduceIte]
  rcases hP with hP | hP | ⟨hP, hn, hl, hc⟩
  · rw [hP]
  · rw [hP]; simp only [pairwiseSum_cancel P h (htree hP)]
  · rw [hP]; simp only [alignedAccumulation_cancel hP hn hl hc h]

/-! ## Encoded blocks -/

/-- **Exact Matrix Core block with cancellation.** On an exact configuration, integer operands
whose products are each within `2^24`, an integer `c` within `2^24`, and an exact sum
`c + Σ aᵢbᵢ` within `2^24` give the binary32 word of that sum, however large `Σ|aᵢbᵢ|` is; on
CDNA 2 every pairwise sum of the products must be within `2^24` as well. -/
theorem evalBlock_cancel {P : Model} (hP : ExactConfig P) (hfa : smallSubnormals P.a)
    (hfb : smallSubnormals P.b) {x : BlockInput P} (hla : x.a.length = P.nfma)
    (hlb : x.b.length = P.nfma) (ha : ∀ w ∈ x.a, IntWord P.a w) (hb : ∀ w ∈ x.b, IntWord P.b w)
    {zc : ℤ} (hc : value32 x.c = some (zc : ℚ)) (hc24 : absQ (zc : ℚ) ≤ pow2 24)
    (hprod : ∀ v ∈ List.zipWith (fun w w' => P.a.wordValue w * P.b.wordValue w') x.a x.b,
      absQ v ≤ pow2 24)
    (hsum : absQ ((zc : ℚ) + exactProducts P x.a x.b) ≤ pow2 24)
    (htree : P.accumulation = .pairWiseSum → ∀ zs : List ℤ,
      List.zipWith (fun w w' => P.a.wordValue w * P.b.wordValue w') x.a x.b =
        zs.map (fun z : ℤ => (z : ℚ)) → PairwiseSumsBounded zs.length zs) :
    ∃ t, evalBlock x = .ok t ∧ value32 t.d = some ((zc : ℚ) + exactProducts P x.a x.b) := by
  obtain ⟨A, hA⟩ := mapM_exists x.a fun w hw => by
    obtain ⟨u, hu, _⟩ := ha w hw; exact ⟨u, hu⟩
  obtain ⟨B, hB⟩ := mapM_exists x.b fun w hw => by
    obtain ⟨u, hu, _⟩ := hb w hw; exact ⟨u, hu⟩
  obtain ⟨uc, hC, hcv⟩ : ∃ uc, (fp32.decode x.c).toFinite = some uc ∧ uc.value = zc := by
    unfold value32 at hc
    cases hd : (fp32.decode x.c).toFinite with
    | none => rw [hd] at hc; simp at hc
    | some uc => rw [hd] at hc; simp at hc; exact ⟨uc, rfl, hc⟩
  have hprep : prepare x = some ⟨A, B, uc⟩ := by
    unfold prepare; simp only [hA, hB, hC]; rfl
  have hops : ∀ (i : InputFormat) (ws : List i.Word) (U : List Unpacked), smallSubnormals i →
      (∀ w ∈ ws, IntWord i w) → ws.mapM (fun w => (i.read w).toFinite) = some U →
      ∀ u ∈ U, IntOperand u := by
    intro i ws U hi hw hU u hu
    obtain ⟨w, hw', hr⟩ := mapM_mem_option hU u hu
    obtain ⟨u', hu', z, hz⟩ := hw w hw'
    rw [hr] at hu'; cases hu'
    exact ⟨⟨z, hz⟩, int_normal (fun hm => read_sub hi hr hm) hz⟩
  -- the products' values are the words' products
  have hpv : (Prepared.p ⟨A, B, uc⟩).map Unpacked.value =
      List.zipWith (fun w w' => P.a.wordValue w * P.b.wordValue w') x.a x.b := by
    unfold Prepared.p
    simp only [List.map_zipWith, Unpacked.value_mul]
    exact mapM_zipWith (fun a b => a * b) x.a x.b A B hA hB
  have hexact : (Prepared.exact ⟨A, B, uc⟩) = (zc : ℚ) + exactProducts P x.a x.b := by
    rw [Prepared.exact_eq]
    simp only
    rw [mapM_products x.a x.b A B hA hB, hcv]
    grind
  have hint : IntPreparedC ⟨A, B, uc⟩ := by
    refine ⟨hops _ _ _ hfa ha hA, hops _ _ _ hfb hb hB,
      ⟨⟨zc, hcv⟩, int_normal (binary32_sub hC) hcv⟩, ?_, by simp only [hcv]; exact hc24,
      by rw [hexact]; exact hsum⟩
    intro q hq
    exact hprod q.value (by rw [← hpv]; exact List.mem_map_of_mem hq)
  obtain ⟨Z, hZ, _⟩ := exactProducts_int x.a x.b ha hb
  have hbnd : (zc + Z).natAbs ≤ 2 ^ 24 := by
    apply natAbs_le_of_absQ
    rw [Rat.intCast_add, ← hZ]; exact hsum
  obtain ⟨w, hw, hv⟩ := fl32_int (!P.subnormals) (zc + Z) hbnd
  refine ⟨⟨⟨A, B, uc⟩, Prepared.exact ⟨A, B, uc⟩, w⟩, ?_, ?_⟩
  · unfold evalBlock
    rw [if_neg (by omega), hprep]
    simp only [accumulate_cancel hP hint (fun hacc zs hzs => htree hacc zs (by rw [← hpv]; exact hzs))]
    rw [hexact, hZ, ← Rat.intCast_add, hw]
  · simp only
    rw [hv, hZ, Rat.intCast_add]

/-! ## Witnesses

fp16 words: `0x6800 = 2048`, `0xE800 = −2048`; binary32 `0x4B000000 = 2^23`. -/

/-- **CDNA 3, cancellation to zero.** Four products `2^22` and four `−2^22` in one block of eight
total `2^25` in magnitude, twice the exactness bound; the block returns `+0`. -/
theorem cdna3_cancel_zero :
    (evalBlock (P := cdna3F16)
      ⟨List.replicate 4 (0x6800 : BitVec 16) ++ List.replicate 4 0xE800, List.replicate 8 0x6800,
        0⟩).map (fun t => t.d) = .ok 0 ∧
    wordDotAbs cdna3F16 (List.replicate 4 (0x6800 : BitVec 16) ++ List.replicate 4 0xE800)
      (List.replicate 8 0x6800) = pow2 25 := by
  decide +kernel

/-- **CDNA 1 and CDNA 2, cancellation against `c`.** `c = 2^23` and products
`2^22, −2^22, 2^22, −2^22`: `|c| + Σ|aᵢbᵢ| = 2^23 + 2^24` exceeds the exactness bound, and both
return the exact `2^23`; on CDNA 2 each pairwise sum (`2^22 − 2^22`) cancels. -/
theorem cdna12_cancel_c :
    (evalBlock (P := cdna1F16)
      ⟨[(0x6800 : BitVec 16), 0xE800, 0x6800, 0xE800], List.replicate 4 0x6800, 0x4B000000⟩).map
      (fun t => t.d) = .ok 0x4B000000 ∧
    (evalBlock (P := cdna2F16)
      ⟨[(0x6800 : BitVec 16), 0xE800, 0x6800, 0xE800], List.replicate 4 0x6800, 0x4B000000⟩).map
      (fun t => t.d) = .ok 0x4B000000 ∧
    value32 0x4B000000 = some (pow2 23) ∧
    wordDotAbs cdna1F16 [(0x6800 : BitVec 16), 0xE800, 0x6800, 0xE800] (List.replicate 4 0x6800) =
      pow2 24 := by
  decide +kernel

end Ozaki.MC
