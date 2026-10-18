import MatrixCore

/-! # Larger products: when the output can fall, by how much, and when it is correctly rounded -/

open MatrixCore

namespace MatrixCoreTests.ProductProperties

/-! ## CDNA 3: monotone while the alignment exponents stay the same -/

/-- Raising the lead product from `1` to `1 + 2^-10` keeps `e_max = 0`, and the output rises. -/
example : blockBits (P := cdna3F16)
      ⟨0x3C00 :: List.replicate 7 0x0C00, 0x3C00 :: List.replicate 7 0x0C00, 0x3F800000⟩ =
      .ok 0x40000002 ∧
    blockBits (P := cdna3F16)
      ⟨0x3C01 :: List.replicate 7 0x0C00, 0x3C00 :: List.replicate 7 0x0C00, 0x3F800000⟩ =
      .ok 0x40001002 := by decide +kernel

/-- Same `c` and `e_max`: larger products never lower a CDNA 3 FP16 output. -/
example {x x' : BlockInput cdna3F16} {t t' : BlockTrace cdna3F16} (h : evalBlock x = .ok t)
    (h' : evalBlock x' = .ok t') (hp : productsLE x x' = true) (hc : x.c = x'.c)
    (he : maxExp t.prepared.p = maxExp t'.prepared.p) : wordValue t.d ≤ wordValue t'.d :=
  cdna3F16_product_monotone h h' hp hc he

/-- Every FP8 combination, same `c` and group exponents: larger products never lower the output. -/
example (fa fb : Format) {x x' : BlockInput (cdna3FP8 fa fb)} {t t' : BlockTrace (cdna3FP8 fa fb)}
    (h : evalBlock x = .ok t) (h' : evalBlock x' = .ok t') (hp : productsLE x x' = true)
    (hc : x.c = x'.c)
    (ho : maxExp (oddIndexed t.prepared.p) = maxExp (oddIndexed t'.prepared.p))
    (he : maxExp (evenIndexed t.prepared.p) = maxExp (evenIndexed t'.prepared.p)) :
    wordValue t.d ≤ wordValue t'.d :=
  cdna3FP8_product_monotone fa fb h h' hp hc ho he

/-- The blocks of `cdna3F16_nonmonotonic`: `p₁ = 2^-9 − 2^-29` and seven products `2^-24`. -/
def xLow : BlockInput cdna3F16 :=
  ⟨0x3C01 :: List.replicate 7 0x0C00, 0x17FE :: List.replicate 7 0x0C00, 0⟩

/-- `p₁ = 2^-9 = 0x0001 · 0x7800` and the same seven products. -/
def xHigh : BlockInput cdna3F16 :=
  ⟨0x0001 :: List.replicate 7 0x0C00, 0x7800 :: List.replicate 7 0x0C00, 0⟩

/-- Where the hypothesis fails, the output falls: `e_max` rises from `−10` to `1`. -/
example : (evalBlock xLow).map (fun t => alignmentExponents cdna3F16 t.prepared.p) =
      .ok [some (-10)] ∧
    (evalBlock xHigh).map (fun t => alignmentExponents cdna3F16 t.prepared.p) = .ok [some 1] ∧
    blockBits xLow = .ok 0x3B0006F8 ∧ blockBits xHigh = .ok 0x3B000000 := by decide +kernel

/-- For every non-monotone pair, the alignment exponents differ. -/
example : ∃ t t', evalBlock xLow = .ok t ∧ evalBlock xHigh = .ok t' ∧
    alignmentExponents cdna3F16 t.prepared.p ≠ alignmentExponents cdna3F16 t'.prepared.p :=
  aligned_nonmonotone_alignment_changes (Or.inl rfl) cdna3F16_nonmonotonic

/-- FP8 E4M3: `cdna3E4M3_nonmonotonic` raises the odd group's exponent from `−3` to `0`. -/
example : (evalBlock (P := cdna3FP8 e4m3fnuz e4m3fnuz)
      ⟨0x2F :: List.replicate 15 0, 0x40 :: List.replicate 15 0, 0x33000000⟩).map
      (fun t => alignmentExponents (cdna3FP8 e4m3fnuz e4m3fnuz) t.prepared.p) =
      .ok [some (-3), none] ∧
    (evalBlock (P := cdna3FP8 e4m3fnuz e4m3fnuz)
      ⟨0x01 :: List.replicate 15 0, 0x7F :: List.replicate 15 0, 0x33000000⟩).map
      (fun t => alignmentExponents (cdna3FP8 e4m3fnuz e4m3fnuz) t.prepared.p) =
      .ok [some 0, none] := by decide +kernel

/-! ## CDNA 2: flushing is the only cause -/

/-- Without subnormal operands, raising `p₁` from `1 + 2^-10` to `1 + 2^-9` raises the output. -/
example : blockBits (P := cdna2F16)
      ⟨[0x3C00, 0x3C00, 0x1400, 0], [0x3C01, 0x1400, 0x1400, 0], 0x3F800000⟩ = .ok 0x40002004 ∧
    blockBits (P := cdna2F16)
      ⟨[0x3C00, 0x3C00, 0x1400, 0], [0x3C02, 0x1400, 0x1400, 0], 0x3F800000⟩ = .ok 0x40003004 := by
  decide +kernel

/-- For every input without subnormal operands: larger products never lower a CDNA 2 output. -/
example {x x' : BlockInput cdna2F16} {t t' : BlockTrace cdna2F16} (h : evalBlock x = .ok t)
    (h' : evalBlock x' = .ok t') (hp : productsLE x x' = true) (hc : x.c = x'.c)
    (hn : t.prepared.NormalOperands) (hn' : t'.prepared.NormalOperands) :
    wordValue t.d ≤ wordValue t'.d :=
  cdna2F16_product_monotone h h' hp hc hn hn'

/-- Where the hypothesis fails: `cdna2F16_nonmonotonic` flushes the subnormal operand `0x0200`. -/
example : (evalBlock (P := cdna2F16) ⟨[0x0200, 0, 0, 0], [0xD200, 0, 0, 0], 0⟩).map
      (fun t => decide (∀ u ∈ t.prepared.a ++ t.prepared.b, u.m = 0 ∨ 2 ^ u.t ≤ u.m)) =
      .ok false ∧
    blockBits (P := cdna2F16) ⟨[0x0200, 0, 0, 0], [0xD200, 0, 0, 0], 0⟩ = .ok 0x00000000 ∧
    blockBits (P := cdna2F16) ⟨[0x0400, 0, 0, 0], [0xC800, 0, 0, 0], 0⟩ = .ok 0xBA000000 := by
  decide +kernel

/-! ## The loss condition -/

/-- The gain `Δ` and the losses `R`, `R'` of a pair of blocks. -/
def gainAndLosses {P : Model} (x x' : BlockInput P) : Except ModelError (ℚ × ℚ × ℚ) := do
  let t ← evalBlock x
  let t' ← evalBlock x'
  return (t.gain t', t.accumulationLoss, t'.accumulationLoss)

/-- `cdna3F16_nonmonotonic`: `R' − R = 7·2^-24 > Δ = 2^-29`. -/
example : gainAndLosses xLow xHigh = .ok (pow2 (-29), 0, 7 * pow2 (-24)) := by decide +kernel

/-- Both `S_acc` are FP32 values, so the loss condition is necessary and sufficient here. -/
example {t t' : BlockTrace cdna3F16} (h : evalBlock xLow = .ok t) (h' : evalBlock xHigh = .ok t') :
    wordValue t'.d < wordValue t.d ∧ t.gain t' < t'.accumulationLoss - t.accumulationLoss := by
  have hs : (evalBlock xLow).map (·.sAcc) = .ok (((2097598 : ℕ) : ℚ) * pow2 (-30)) := by
    decide +kernel
  have hs' : (evalBlock xHigh).map (·.sAcc) = .ok (((2097152 : ℕ) : ℚ) * pow2 (-30)) := by
    decide +kernel
  have hg : gainAndLosses xLow xHigh = .ok (pow2 (-29), 0, 7 * pow2 (-24)) := by decide +kernel
  have hv := (finiteValue32_mul_pow2_neg30 (N := 2097598) (by decide)).1
  have hv' := (finiteValue32_mul_pow2_neg30 (N := 2097152) (by decide)).1
  rw [h] at hs; rw [h'] at hs'
  simp only [gainAndLosses, h, h'] at hg
  simp only [Except.map, Except.ok.injEq] at hs hs'
  have hgt : t.gain t' < t'.accumulationLoss - t.accumulationLoss := by
    have e : (t.gain t', t.accumulationLoss, t'.accumulationLoss) =
        (pow2 (-29), 0, 7 * pow2 (-24)) := by
      have := hg; simp only [bind, Except.bind, pure, Except.pure, Except.ok.injEq] at this
      exact this
    simp only [Prod.mk.injEq] at e
    rw [e.1, e.2.1, e.2.2]
    decide +kernel
  rw [← hs] at hv; rw [← hs'] at hv'
  exact ⟨(output_decrease_iff rfl h h' hv hv').mpr hgt, hgt⟩

/-- For every pair: an output decrease requires `R' − R > Δ`. -/
example {P : Model} {x x' : BlockInput P} {t t' : BlockTrace P} (h : evalBlock x = .ok t)
    (h' : evalBlock x' = .ok t') (hlt : wordValue t'.d < wordValue t.d) :
    t.gain t' < t'.accumulationLoss - t.accumulationLoss :=
  (output_decrease_requires_loss h h' hlt).2

/-- The drop of `cdna3F16_nonmonotonic` and the bound of `aligned_output_drop_le`. -/
example : (do
      let t ← evalBlock xLow
      let t' ← evalBlock xHigh
      return (wordValue t.d - wordValue t'.d,
        alignedBound cdna3F16 t.prepared + flBound false t.sAcc +
          (alignedBound cdna3F16 t'.prepared + flBound false t'.sAcc) - t.gain t') :
      Except ModelError (ℚ × ℚ)) = .ok (223 * pow2 (-29), 22511 * pow2 (-34)) := by
  decide +kernel

/-- For every pair of CDNA 3 FP16 blocks: the drop is within the two error bounds minus `Δ`. -/
example {x x' : BlockInput cdna3F16} {t t' : BlockTrace cdna3F16} (h : evalBlock x = .ok t)
    (h' : evalBlock x' = .ok t') :
    wordValue t.d - wordValue t'.d ≤
      (alignedBound cdna3F16 t.prepared + flBound false t.sAcc) +
        (alignedBound cdna3F16 t'.prepared + flBound false t'.sAcc) - t.gain t' :=
  aligned_output_drop_le (Or.inl rfl) (fun _ h => by simp [cdna3F16] at h) (by decide) h h'

/-! ## The family and its threshold -/

/-- `cdna3F16_nonmonotonic` is the member with lead `0x3C01 · 0x17FE` and `n = 7`. -/
example : cdna3F16LeadBlock 0x3C01 0x17FE 7 = xLow ∧ cdna3F16LeadBlock 0x0001 0x7800 7 = xHigh := by
  decide

/-- Lead `0x3C30 · 0x17A4` (threshold `64 n > 320`): equal outputs at `n = 5`, a drop at `n = 6`. -/
example : blockBits (cdna3F16LeadBlock 0x3C30 0x17A4 5) = .ok 0x3B000000 ∧
    blockBits (cdna3F16LeadBlock 0x0001 0x7800 5) = .ok 0x3B000000 ∧
    blockBits (cdna3F16LeadBlock 0x3C30 0x17A4 6) = .ok 0x3B000100 ∧
    blockBits (cdna3F16LeadBlock 0x0001 0x7800 6) = .ok 0x3B000000 := by decide +kernel

/-- The general theorem on both sides of that threshold. -/
example : ¬ ProductNonmonotone (cdna3F16LeadBlock 0x3C30 0x17A4 5)
      (cdna3F16LeadBlock 0x0001 0x7800 5) ∧
    ProductNonmonotone (cdna3F16LeadBlock 0x3C30 0x17A4 6) (cdna3F16LeadBlock 0x0001 0x7800 6) := by
  have hiff := fun n (hn : n ≤ 7) => cdna3F16LeadBlock_nonmonotone_iff
    (wa := 0x3C30) (wb := 0x17A4) (ua := ⟨false, 1072, 0, 10⟩) (ub := ⟨false, 1956, -10, 10⟩)
    (by decide) (by decide) rfl (by decide) rfl hn
  rw [hiff 5 (by decide), hiff 6 (by decide)]
  decide

/-- Lead `0x3DA8 · 0x15A8` (threshold `64 n > 448`): no member with `n ≤ 7` is non-monotone. -/
example : ∀ n ≤ 7, ¬ ProductNonmonotone (cdna3F16LeadBlock 0x3DA8 0x15A8 n)
    (cdna3F16LeadBlock 0x0001 0x7800 n) := by
  intro n hn
  rw [cdna3F16LeadBlock_nonmonotone_iff (ua := ⟨false, 1448, 0, 10⟩) (ub := ⟨false, 1448, -10, 10⟩)
    (by decide) (by decide) rfl (by decide) rfl hn]
  show ¬ (1448 * 1448 ≤ 2 ^ 21 ∧ (2 ^ 21 : ℤ) - ((1448 * 1448 : ℕ) : ℤ) < 64 * n)
  omega

/-- At `n = 7` both outputs of that lead are `2^-9`. -/
example : blockBits (cdna3F16LeadBlock 0x3DA8 0x15A8 7) = .ok 0x3B000000 ∧
    blockBits (cdna3F16LeadBlock 0x0001 0x7800 7) = .ok 0x3B000000 := by decide +kernel

/-- The lead of `cdna3F16_nonmonotonic`: non-monotone exactly when `n ≥ 1`. -/
example : ∀ n ≤ 7, (ProductNonmonotone (cdna3F16LeadBlock 0x3C01 0x17FE n)
    (cdna3F16LeadBlock 0x0001 0x7800 n) ↔ 1 ≤ n) := by
  intro n hn
  rw [cdna3F16LeadBlock_nonmonotone_iff (ua := ⟨false, 1025, 0, 10⟩) (ub := ⟨false, 2046, -10, 10⟩)
    (by decide) (by decide) rfl (by decide) rfl hn]
  show 1025 * 2046 ≤ 2 ^ 21 ∧ (2 ^ 21 : ℤ) - ((1025 * 2046 : ℕ) : ℤ) < 64 * n ↔ 1 ≤ n
  omega

/-! ## Correct rounding when the alignment loses nothing -/

/-- `e_max = 0`, every product on the grid `2^-24`, `c = 0`; the exact sum is an FP32 tie. -/
def xTie : BlockInput cdna3F16 :=
  ⟨0x3C00 :: List.replicate 7 0x3401, 0x3C00 :: List.replicate 7 0x3401, 0⟩

/-- `S_acc` is the exact sum, and the output is its RNE, the even neighbor. -/
example : (evalBlock xTie).map (fun t => (t.sAcc, t.prepared.exact)) =
      .ok (24131591 * pow2 (-24), 24131591 * pow2 (-24)) ∧
    rne32 (24131591 * pow2 (-24)) = some 0x3FB81C04 ∧ blockBits xTie = .ok 0x3FB81C04 := by
  decide +kernel

/-- The theorem: the output of `xTie` is correctly rounded, from `LosslessAlignment`. -/
example {t : BlockTrace cdna3F16} (h : evalBlock xTie = .ok t) :
    NearestEven32 t.prepared.exact t.d := by
  apply cdna3F16_nearestEven_of_lossless h
  have he : (evalBlock xTie).map (fun t => (productSum cdna3F16 t.prepared.p).1) = .ok (some 0) := by
    decide +kernel
  have hg : (evalBlock xTie).map
      (fun t => decide (∀ p ∈ t.prepared.p, p.m = 0 ∨ (0 : ℤ) - 24 ≤ p.e - p.t)) = .ok true := by
    decide +kernel
  have hc : (evalBlock xTie).map (fun t => t.prepared.c.m) = .ok 0 := by decide +kernel
  rw [h] at he hg hc
  simp only [Except.map, Except.ok.injEq, decide_eq_true_eq] at he hg hc
  exact LosslessAlignment.of_c_zero he hc (fun eZ hZ => by simp [cdna3F16] at hZ; omega)
    (fun p hp => Unpacked.onGrid_of_le (hg p hp))

/-- CDNA 2: every product and partial sum of `p = (1 + 2^-10, 2^-10, 2^-20, 0)` is an FP32 value. -/
def xPair : BlockInput cdna2F16 :=
  ⟨[0x3C00, 0x3C00, 0x1400, 0], [0x3C01, 0x1400, 0x1400, 0], 0x3F800000⟩

/-- The theorem: the output of `xPair` is `fl{Σ p_ℓ + c}`. -/
example {t : BlockTrace cdna2F16} (h : evalBlock xPair = .ok t) :
    fl32 true t.prepared.exact = some t.d := by
  have hconv : (evalBlock xPair).map (fun t => decide (t.prepared.p.mapM
      (fun p => flValue true p.value) = some (t.prepared.p.map Unpacked.value))) = .ok true := by
    decide +kernel
  have hsum : (evalBlock xPair).map (fun t => decide (pairwiseGroupSum true t.prepared.p.length
      (t.prepared.p.map Unpacked.value) = some (sumQ (t.prepared.p.map Unpacked.value)))) =
      .ok true := by decide +kernel
  have hf : (evalBlock xPair).map (fun t => decide (t.prepared.flushed = t.prepared)) = .ok true := by
    decide +kernel
  rw [h] at hconv hsum hf
  simp only [Except.map, Except.ok.injEq, decide_eq_true_eq] at hconv hsum hf
  exact (pairwise_fl_exact_of_lossless rfl h (Or.inr hf) hconv hsum).2

end MatrixCoreTests.ProductProperties
