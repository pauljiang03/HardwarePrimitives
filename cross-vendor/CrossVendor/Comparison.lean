import CrossVendor.Correction

/-! # NVIDIA Tensor Cores and AMD Matrix Cores, compared

One theorem per row of the comparison: the Tensor Core fact and the Matrix Core fact in a single
statement. -/

namespace CrossVendor

/-! ## Final rounding -/

/-- `c = 1` and the FP16 product `2^-12 · 1.5·2^-12 = 3·2^-25`, with seven zero products. -/
def roundingTC : TensorCore.BlockInput TensorCore.ampereF16F32 :=
  ⟨(0x0C00, 0x0E00) :: List.replicate 7 (0, 0), 0x3F800000⟩

/-- The same words on CDNA 3. -/
def roundingMC : MatrixCore.BlockInput MatrixCore.cdna3F16 :=
  ⟨0x0C00 :: List.replicate 7 0, 0x0E00 :: List.replicate 7 0, 0x3F800000⟩

/-- **Truncation and round to nearest.** On the same FP16 words, with exact sum `1 + 3·2^-25`, A100
truncates to `1` and CDNA 3 rounds to nearest, `1 + 2^-23`. From each block's own output, TC-EFT
and MC-EFT return the same word, `1 + 2^-23`. -/
theorem final_rounding :
    TensorCore.exactDot roundingTC = some (1 + 3 * TensorCore.pow2 (-25)) ∧
    (MatrixCore.prepare roundingMC).map MatrixCore.Prepared.exact =
      some (1 + 3 * MatrixCore.pow2 (-25)) ∧
    (TensorCore.evalBlock roundingTC).map (·.output.bits) = .ok 0x3F800000 ∧
    MatrixCore.blockBits roundingMC = .ok 0x3F800001 ∧
    (TensorCore.EFMachine.tcEft .ampereF16 roundingTC 0x3F800000).map (·.bits) =
      .ok (some 0x3F800001) ∧
    (MatrixCore.mcEft roundingMC 0x3F800001).map (·.bits) = .ok (some 0x3F800001) := by
  decide +kernel

/-! ## Monotonicity in the accumulator input -/

/-- Sixteen FP16 products `2^-13 · 2^-13 = 2^-26` and the accumulator input `c`. -/
def accumulatorTC (c : BitVec 32) : TensorCore.BlockInput TensorCore.hopperF16F32 :=
  ⟨List.replicate 16 (0x0800, 0x0800), c⟩

/-- **Monotonicity in `C` and `c`.** On H100, lowering `C` from `1` to the next FP32 value below
raises the output from `1` to `1 + 2^-23`: with `C = 1` the products fall below the alignment
grid, with the smaller `C` they stay on it. On every Matrix Core configuration of the paper, a
larger `c` never gives a smaller output. -/
theorem accumulator_monotonicity :
    ((TensorCore.evalBlock (accumulatorTC 0x3F800000)).map (·.output.bits) = .ok 0x3F800000 ∧
      (TensorCore.evalBlock (accumulatorTC 0x3F7FFFFF)).map (·.output.bits) = .ok 0x3F800001) ∧
    (MatrixCore.MonotoneModel MatrixCore.sfmaF32 ∧ MatrixCore.MonotoneModel MatrixCore.cdna1F16 ∧
      MatrixCore.MonotoneModel MatrixCore.cdna1BF16 ∧ MatrixCore.MonotoneModel MatrixCore.cdna2F16 ∧
      MatrixCore.MonotoneModel MatrixCore.cdna2BF16 ∧
      MatrixCore.MonotoneModel MatrixCore.cdna2BF16_1k ∧
      MatrixCore.MonotoneModel MatrixCore.cdna3F16 ∧ MatrixCore.MonotoneModel MatrixCore.cdna3BF16 ∧
      MatrixCore.MonotoneModel MatrixCore.cdna3XF32 ∧
      ∀ fa fb, MatrixCore.MonotoneModel (MatrixCore.cdna3FP8 fa fb)) ∧
    ∀ {P : MatrixCore.Model}, MatrixCore.MonotoneModel P →
      ∀ {a : List P.a.Word} {b : List P.b.Word} {c c' : BitVec 32}
        {t t' : MatrixCore.BlockTrace P},
        MatrixCore.evalBlock (P := P) ⟨a, b, c⟩ = .ok t →
        MatrixCore.evalBlock (P := P) ⟨a, b, c'⟩ = .ok t' →
        MatrixCore.wordValue c ≤ MatrixCore.wordValue c' →
        MatrixCore.wordValue t.d ≤ MatrixCore.wordValue t'.d :=
  ⟨by decide +kernel, MatrixCore.paper_models_monotone,
    fun hP _ _ _ _ _ _ h h' hc => MatrixCore.evalBlock_c_monotone hP h h' hc⟩

/-! ## Monotonicity in the products -/

/-- V100: a lead product and three products `2^-12 · 2^-12 = 2^-24`, `c = 0`. -/
def productTC (a b : BitVec 16) : TensorCore.BlockInput TensorCore.v100F16F32 :=
  ⟨(a, b) :: List.replicate 3 (0x0C00, 0x0C00), 0⟩

/-- CDNA 3: a lead product and seven products `2^-24`, `c = 0`. -/
def productMC3 (a b : BitVec 16) : MatrixCore.BlockInput MatrixCore.cdna3F16 :=
  ⟨a :: List.replicate 7 0x0C00, b :: List.replicate 7 0x0C00, 0⟩

/-- CDNA 2: one product and three zero products, `c = 0`. -/
def productMC2 (a b : BitVec 16) : MatrixCore.BlockInput MatrixCore.cdna2F16 :=
  ⟨a :: List.replicate 3 0, b :: List.replicate 3 0, 0⟩

/-- **Monotonicity in the products.** Raising one product can lower the output on V100, CDNA 2
and CDNA 3, and never on CDNA 1 or the SFMA.

* V100 and CDNA 3: the lead product rises from `2^-9 − 2^-29` (normal operands, exponent `−10`) to
  `2^-9` (`2^-24 · 2^15`, a subnormal operand, exponent `1`). The alignment grid coarsens and the
  products `2^-24` are lost, so the exact sum rises and the output falls.
* CDNA 2: the product rises from `2^-14` to `(1 − 2^-10)·2^-13`, whose subnormal operand is
  flushed to zero. -/
theorem product_monotonicity :
    (TensorCore.exactDot (productTC 0x3C01 0x17FE) =
        some (TensorCore.pow2 (-9) - TensorCore.pow2 (-29) + 3 * TensorCore.pow2 (-24)) ∧
      TensorCore.exactDot (productTC 0x0001 0x7800) =
        some (TensorCore.pow2 (-9) + 3 * TensorCore.pow2 (-24)) ∧
      (TensorCore.evalBlock (productTC 0x3C01 0x17FE)).map (·.output.bits) = .ok 0x3B0002F8 ∧
      (TensorCore.evalBlock (productTC 0x0001 0x7800)).map (·.output.bits) = .ok 0x3B000000) ∧
    MatrixCore.ProductNonmonotone (productMC3 0x3C01 0x17FE) (productMC3 0x0001 0x7800) ∧
    MatrixCore.ProductNonmonotone (productMC2 0x0400 0x3C00) (productMC2 0x03FF 0x4000) ∧
    (∀ x x' : MatrixCore.BlockInput MatrixCore.sfmaF32, ¬ MatrixCore.ProductNonmonotone x x') ∧
    (∀ x x' : MatrixCore.BlockInput MatrixCore.cdna1F16, ¬ MatrixCore.ProductNonmonotone x x') ∧
    (∀ x x' : MatrixCore.BlockInput MatrixCore.cdna1BF16, ¬ MatrixCore.ProductNonmonotone x x') :=
  ⟨by decide +kernel,
    ⟨by decide +kernel, rfl, 0x3B0006F8, 0x3B000000, by decide +kernel, by decide +kernel,
      by decide +kernel⟩,
    ⟨by decide +kernel, rfl, 0x38800000, 0, by decide +kernel, by decide +kernel,
      by decide +kernel⟩,
    MatrixCore.sfmaF32_not_nonmonotone, MatrixCore.cdna1F16_not_nonmonotone,
    MatrixCore.cdna1BF16_not_nonmonotone⟩

/-! ## The order of the products -/

/-- **The order of the products.** A Tensor Core block FMA depends on its products only as a
multiset, on every model. So do CDNA 1, the SFMA and CDNA 3's global alignment. CDNA 2's pairwise
sum depends on positions, and on CDNA 3 FP8 a permutation of the 16 slots preserves every output
exactly when it preserves the parity of each slot. -/
theorem product_order :
    (∀ {p : TensorCore.Model} {x y : TensorCore.BlockInput p}, x.c = y.c →
      x.products.Perm y.products →
      (TensorCore.evalBlock x).map (·.output) = (TensorCore.evalBlock y).map (·.output)) ∧
    (∀ {P : MatrixCore.Model},
      P.accumulation = .correctRounding ∨ P.accumulation = .globalAlignment →
      ∀ {x y : MatrixCore.Prepared}, x.p.Perm y.p → x.c = y.c →
        MatrixCore.accumulate P x = MatrixCore.accumulate P y) ∧
    (MatrixCore.blockBits (P := MatrixCore.cdna2F16)
        ⟨[0x3C00, 0x0E00, 0x0E00, 0], [0x3C00, 0x1000, 0x1000, 0], 0⟩ = .ok 0x3F800004 ∧
      MatrixCore.blockBits (P := MatrixCore.cdna2F16)
        ⟨[0x0E00, 0x0E00, 0x3C00, 0], [0x1000, 0x1000, 0x3C00, 0], 0⟩ = .ok 0x3F800003) ∧
    ∀ (fa fb : MatrixCore.Format), (fa = MatrixCore.e4m3fnuz ∨ fa = MatrixCore.e5m2fnuz) →
      (fb = MatrixCore.e4m3fnuz ∨ fb = MatrixCore.e5m2fnuz) →
      ∀ {σ : List Nat}, σ.Perm (List.range 16) →
        ((∀ (qs : List ((MatrixCore.cdna3FP8 fa fb).a.Word × (MatrixCore.cdna3FP8 fa fb).b.Word))
            (d : BitVec 32), qs.length = 16 →
            MatrixCore.blockBits (P := MatrixCore.cdna3FP8 fa fb)
                ⟨(MatrixCore.permuteSlots σ (0, 0) qs).map Prod.fst,
                  (MatrixCore.permuteSlots σ (0, 0) qs).map Prod.snd, d⟩ =
              MatrixCore.blockBits (P := MatrixCore.cdna3FP8 fa fb)
                ⟨qs.map Prod.fst, qs.map Prod.snd, d⟩) ↔
          MatrixCore.ParityPreserving σ) :=
  ⟨TensorCore.evalBlock_perm, MatrixCore.accumulate_perm, MatrixCore.pairWiseSum_order_dependent,
    fun fa fb hfa hfb _ hσ => MatrixCore.cdna3FP8_permute_iff fa fb hfa hfb hσ⟩

end CrossVendor
