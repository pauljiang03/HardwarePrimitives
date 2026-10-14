import MMAlgebra.Divergence
import MMAlgebraTC.Exact
import MMAlgebraTC.NegZero
import OzakiTC.TwoPass

/-! # The error contract of the Tensor Core models

The model's error bound (`TensorCore.evalBlock_error_bound`) says that a block FMA with a binary32
block output is within
`(K + 1)·2^(η − F) + ulp(D)` of the exact sum of its inputs, where `η` is the alignment exponent and
`D` the output. In terms of magnitudes (`tc_block_le`): `2^η` is at most `|c| + 2^-126` or, for a
product, 2 to the sum of its operands' exponents (`expMag`, at most `|aᵢbᵢ|` when both operands are
normal), plus `2^-126` for the minimum alignment exponent; and `ulp(D) ≤ 2^-23 |D| + 2^-149` with
`|D| ≤ |c| + Σ|aᵢbᵢ|`. So a block whose accumulator has magnitude at most `A` is within

  `(K + 1)·2^-F·(A + 2^-125 + Σ expMag) + 2^-23·(A + Σ|aᵢbᵢ|) + 2^-149`

of the exact sum: `12u`, `11u` and `10.5u` per unit of input magnitude on V100, A100 and H100 with
normal operands. `tcContract` packages this with binary32 addition as a `MMAlgebra.Contract`, so
`MMAlgebra.eval_error`, `MMAlgebra.divergence` and `MMAlgebra.divergence_shared` apply to every
reduction term on the Tensor Core models (`v100_divergence`, `a100_divergence`, `h100_divergence`). -/

open TensorCore Ozaki.TC

namespace MMAlgebra.TC

/-- 2 to the exponent of a nonzero product of two operand words (`0` for a zero product or a
non-finite word); at most the product's magnitude when both operands are normal. -/
def expMag (p : Model) (q : p.Word × p.Word) : ℚ :=
  match p.decode q.1, p.decode q.2 with
  | some a, some b => if a.significand * b.significand = 0 then 0 else pow2 (a.exponent + b.exponent)
  | _, _ => 0

theorem expMag_nonneg (p : Model) (q : p.Word × p.Word) : 0 ≤ expMag p q := by
  unfold expMag
  split
  · split
    · exact Rat.le_refl
    · exact Rat.le_of_lt (pow2_pos _)
  · exact Rat.le_refl

theorem mapM_isSome_mem {γ δ : Type} (f : γ → Option δ) :
    ∀ {xs : List γ} {ys : List δ}, xs.mapM f = some ys → ∀ x ∈ xs, (f x).isSome
  | [], _, _ => by simp
  | x :: xs, ys, h => by
    simp only [List.mapM_cons] at h
    cases hb : f x with
    | none => simp [hb] at h
    | some b =>
      cases hbs : xs.mapM f with
      | none => simp [hb, hbs] at h
      | some bs =>
        intro y hy
        rcases List.mem_cons.mp hy with rfl | hy
        · rw [hb]; rfl
        · exact mapM_isSome_mem f hbs y hy

theorem prepareProducts_finite {p : Model} {qs : List (p.Word × p.Word)} {ds : List (Decoded × Decoded)}
    (h : prepareProducts p qs = some ds) : ∀ q ∈ qs, (p.decode q.1).isSome ∧ (p.decode q.2).isSome := by
  intro q hq
  have := mapM_isSome_mem _ h q hq
  revert this
  cases ha : p.decode q.1 <;> cases hb : p.decode q.2 <;> simp [ha, hb]

theorem le_sum_of_mem {l : List ℚ} (hl : ∀ x ∈ l, 0 ≤ x) {y : ℚ} (hy : y ∈ l) : y ≤ l.sum := by
  induction l with
  | nil => simp at hy
  | cons x l ih =>
    simp only [List.sum_cons]
    have h1 := hl x (by simp)
    have h2 : 0 ≤ l.sum := by
      have : ∀ (l : List ℚ), (∀ x ∈ l, 0 ≤ x) → 0 ≤ l.sum := by
        intro l h
        induction l with
        | nil => simp
        | cons z l ihz =>
          simp only [List.sum_cons]
          have := h z (by simp); have := ihz (fun w hw => h w (by simp [hw])); grind
      exact this l (fun w hw => hl w (by simp [hw]))
    rcases List.mem_cons.mp hy with rfl | hy
    · grind
    · have := ih (fun w hw => hl w (by simp [hw])) hy; grind

theorem foldl_max_mem : ∀ (es : List ℤ) (acc : Option ℤ) (e : ℤ),
    es.foldl (fun acc e => some (match acc with | none => e | some v => max v e)) acc = some e →
      acc = some e ∨ e ∈ es
  | [], acc, e, h => Or.inl h
  | x :: es, acc, e, h => by
    simp only [List.foldl_cons] at h
    rcases foldl_max_mem es _ e h with h1 | h1
    · cases acc with
      | none => simp at h1; subst h1; right; simp
      | some v =>
        simp only [Option.some.injEq] at h1
        rcases Int.le_total v x with hv | hv
        · rw [Int.max_eq_right hv] at h1; subst h1; right; simp
        · rw [Int.max_eq_left hv] at h1; subst h1; left; rfl
    · right; exact List.mem_cons_of_mem _ h1

/-- The largest exponent of a nonzero term is the exponent of one of them. -/
theorem maxTermExp_attained {ts : List DenormalizedProduct} {e : ℤ} (h : maxTermExp ts = some e) :
    ∃ t ∈ ts, t.significand ≠ 0 ∧ t.exponent = e := by
  unfold maxTermExp at h
  rcases foldl_max_mem _ none e h with h1 | h1
  · cases h1
  · obtain ⟨t, ht, he⟩ := List.mem_filterMap.mp h1
    by_cases hs : t.significand = 0
    · simp [hs] at he
    · simp [hs] at he; exact ⟨t, ht, hs, he⟩

/-- A normal binary32 value is at least 2 to its exponent. -/
theorem normal_lower {c : F32} {dc : Decoded} (h : decode32 c = some dc) (hs : dc.significand ≠ 0)
    (he : -125 ≤ dc.exponent) : pow2 dc.exponent ≤ absQ dc.value := by
  apply Classical.byContradiction
  intro hlt
  have hlt' : Rat.abs dc.value < 2 ^ ((dc.exponent - 1) + 1) := by
    rw [show dc.exponent - 1 + 1 = dc.exponent by omega, ← absQ_eq]
    show absQ dc.value < pow2 dc.exponent
    grind
  have := decode_exp_le (f := fp32) (w := c) h (E := dc.exponent - 1)
    (by show (1 : ℤ) - 127 ≤ dc.exponent - 1; omega) hlt' hs
  omega

/-- A nonzero binary32 value is at least 2 to its exponent, up to `2^-126`. -/
theorem decode32_exp_bound {c : F32} {dc : Decoded} (h : decode32 c = some dc) (hs : dc.significand ≠ 0) :
    pow2 dc.exponent ≤ absQ dc.value + pow2 (-126) := by
  have h0 := absQ_nonneg dc.value
  by_cases he : dc.exponent ≤ -126
  · have := pow2_le_of_le he; grind
  · have := normal_lower h hs (by omega)
    have := pow2_pos (-126)
    grind

/-- The output's unit in the last place is at most `2^-23 |D| + 2^-149`. -/
theorem ulp_bound {b : F32} {v : ℚ} (h : value32 b = some v) :
    pow2 (outputUlpExponent b) ≤ pow2 (-23) * absQ v + pow2 (-149) := by
  unfold value32 at h
  cases hd : decode32 b with
  | none => rw [hd] at h; cases h
  | some dc =>
    rw [hd] at h
    simp only [Option.map_some, Option.some.injEq] at h
    subst h
    have hnn := Rat.mul_nonneg (Rat.le_of_lt (pow2_pos (-23))) (absQ_nonneg dc.value)
    have hfield : outputUlpExponent b = max (((b.toNat / 8388608 % 256 : ℕ) : ℤ) - 127) emin32 - 23 := rfl
    rw [hfield]
    rcases decode32_fields b dc hd with ⟨hE, _, _⟩ | ⟨hE, _, _⟩ | ⟨hE1, hE2, h0⟩
    · rw [hE]; unfold emin32
      rw [show max (((0 : ℕ) : ℤ) - 127) (-126) - 23 = -149 by omega]; grind
    · rw [hE]; unfold emin32
      rw [show max (((0 : ℕ) : ℤ) - 127) (-126) - 23 = -149 by omega]; grind
    · have hexp : dc.exponent = ((b.toNat / 8388608 % 256 : ℕ) : ℤ) - 127 := by rw [h0]
      have hsig : dc.significand ≠ 0 := by rw [h0]; simp only; split <;> omega
      unfold emin32
      rw [show max (((b.toNat / 8388608 % 256 : ℕ) : ℤ) - 127) (-126) - 23 = dc.exponent - 23 by omega]
      by_cases he : dc.exponent = -126
      · rw [he]; show pow2 (-149) ≤ _; grind
      · have hlow := normal_lower hd hsig (by omega)
        have e2 : pow2 (dc.exponent - 23) = pow2 (-23) * pow2 dc.exponent := by
          rw [← pow2_add]; congr 1; omega
        rw [e2]
        have := Rat.mul_le_mul_of_nonneg_left hlow (Rat.le_of_lt (pow2_pos (-23)))
        have := pow2_pos (-149)
        grind

/-! ## The contract -/

theorem wordValue_zero_of (p : Model) (hz : p.decode 0 = some ⟨0, 0, 0⟩) : wordValue p 0 = 0 := by
  unfold wordValue decodeD; rw [hz]; simp [Decoded.value]

theorem sum_le_sum_map {γ : Type} {f g : γ → ℚ} :
    ∀ {l : List γ}, (∀ x ∈ l, f x ≤ g x) → (l.map f).sum ≤ (l.map g).sum
  | [], _ => Rat.le_refl
  | x :: l, h => by
    simp only [List.map_cons, List.sum_cons]
    have := h x (by simp)
    have := sum_le_sum_map (l := l) (fun y hy => h y (by simp [hy]))
    grind

theorem sum_zero_of {l : List ℚ} (h : ∀ x ∈ l, x = 0) : l.sum = 0 := by
  induction l with
  | nil => rfl
  | cons x l ih =>
    rw [List.sum_cons, h x (by simp), ih (fun y hy => h y (by simp [hy])), Rat.zero_add]

theorem slotVal_words (p : Model) (hz : p.decode 0 = some ⟨0, 0, 0⟩) :
    ∀ ps : List (Option (p.Word × p.Word)), (tcMachine p).slotVal ps = wordProducts p (slotPairs p ps)
  | [] => rfl
  | o :: ps => by
    rw [(tcMachine p).slotVal_cons, slotVal_words p hz ps]
    simp only [wordProducts, slotPairs, List.map_cons, List.sum_cons]
    cases o with
    | none => show 0 + _ = wordValue p 0 * wordValue p 0 + _; rw [wordValue_zero_of p hz]; simp
    | some q => rfl

theorem slotAbs_words (p : Model) (hz : p.decode 0 = some ⟨0, 0, 0⟩) :
    ∀ ps : List (Option (p.Word × p.Word)), (tcMachine p).slotAbs ps = wordDotAbs p (slotPairs p ps)
  | [] => rfl
  | o :: ps => by
    rw [(tcMachine p).slotAbs_cons, slotAbs_words p hz ps]
    simp only [wordDotAbs, slotPairs, List.map_cons, List.sum_cons]
    cases o with
    | none =>
      show Rat.abs 0 + _ = Rat.abs (wordValue p 0 * wordValue p 0) + _
      rw [wordValue_zero_of p hz]; simp
    | some q => rfl

/-- **The Tensor Core block contract.** On a model with a binary32 block output, a block whose
accumulator has magnitude at most `A` is within
`(K + 1)·2^-F·(A + 2^-125 + Σ expMag) + 2^-23·(A + Σ|aᵢbᵢ|) + 2^-149` of the exact sum of its
inputs. -/
theorem tc_block_le (p : Model) (hmin : ∀ f ∈ p.eAlignMin, f ≤ -126)
    (hz : p.decode 0 = some ⟨0, 0, 0⟩) (hw : 23 ≤ p.outputFracBits) (d : F32)
    (ps : List (Option (p.Word × p.Word))) (o : F32)
    (A : ℚ) (hA : Rat.abs ((tcMachine p).val d) ≤ A) (h : (tcMachine p).block d ps = some o) :
    Rat.abs ((tcMachine p).val o - ((tcMachine p).val d + (tcMachine p).slotVal ps)) ≤
      ((ps.length : ℚ) + 1) * pow2 (-p.alignFracBits) *
          (A + pow2 (-125) + ((slotPairs p ps).map (expMag p)).sum) +
        pow2 (-23) * (A + (tcMachine p).slotAbs ps) + pow2 (-149) := by
  have h' : (blockOut (p := p) ⟨slotPairs p ps, d⟩).toOption = some o := h
  cases ht : evalBlock (p := p) ⟨slotPairs p ps, d⟩ with
  | error e => unfold blockOut at h'; rw [ht] at h'; simp [Except.map, Except.toOption] at h'
  | ok t =>
    unfold blockOut at h'; rw [ht] at h'
    simp only [Except.map, Except.toOption, Option.some.injEq] at h'
    subst h'
    have hb := evalBlock_error_bound ht hw
    have hprep := evalBlock_prepared ht
    have hev := evalBlock_evalPrepared ht
    unfold prepare at hprep
    cases hc : decode32 d with
    | none => simp [hc] at hprep
    | some dc =>
      cases hps : prepareProducts p (slotPairs p ps) with
      | none => simp [hc, hps] at hprep
      | some ds =>
        simp only [hc, hps, Option.some.injEq] at hprep
        have hds : ds = (slotPairs p ps).map fun q => (decodeD p q.1, decodeD p q.2) := by
          have := prepareProducts_eq p _ (prepareProducts_finite hps)
          rw [hps] at this; exact Option.some.inj this
        have hlen : (ps.length : ℚ) + 1 = (t.block.terms.length : ℚ) := by
          rw [← hprep]; simp [PreparedBlock.terms, hds, slotPairs]
        have hvd : (tcMachine p).val d = dc.value := by
          show value32D d = _; simp [value32D, value32, hc]
        have hvo : (tcMachine p).val t.output.bits = t.output.value := by
          show value32D t.output.bits = _; simp [value32D, value32_output]
        have hexact : t.block.exactDot = dc.value + (tcMachine p).slotVal ps := by
          rw [← hprep, slotVal_words p hz]
          unfold PreparedBlock.exactDot PreparedBlock.exactProducts wordProducts
          rw [sumQ_eq, hds, List.map_map]
          rfl
        -- the alignment term
        have hpos : 0 ≤ ((slotPairs p ps).map (expMag p)).sum := by
          have : ∀ (l : List (p.Word × p.Word)), 0 ≤ (l.map (expMag p)).sum := by
            intro l; induction l with
            | nil => simp
            | cons q l ih => simp only [List.map_cons, List.sum_cons]; have := expMag_nonneg p q; grind
          exact this _
        have hAnn : 0 ≤ A := Rat.le_trans (Ozaki.abs_nonneg _) hA
        have hcA : absQ dc.value ≤ A := by rw [← hvd, absQ_eq]; exact hA
        -- the error is zero when every term is zero
        by_cases hzero : t.block.alignExp = none
        · have hterms0 : ∀ u ∈ t.block.terms, u.significand = 0 := by
            intro u hu
            apply Classical.byContradiction; intro hnz
            obtain ⟨e, he, _⟩ := alignExp_term t.block u hu hnz
            rw [hzero] at he; cases he
          have hval0 : ∀ u ∈ t.block.terms, u.value = 0 := by
            intro u hu; simp [DenormalizedProduct.value, hterms0 u hu]
          have hacc0 : t.block.accumulator = 0 := by
            rw [accumulator_value, sumQ_eq]
            apply sum_zero_of
            intro x hx
            obtain ⟨u, hu, rfl⟩ := List.mem_map.mp hx
            rw [hval0 u hu, truncGrid_zero]
          have hout0 : t.output.value = 0 := by
            rw [evalPrepared_output_value hev (by rw [evalBlock_model ht]; exact hw), hacc0]
            decide +kernel
          have hexact0 : t.block.exactDot = 0 := by
            have hc0 : dc.value = 0 := hval0 ⟨dc.significand, dc.exponent, dc.mantissaBits⟩ (by
              rw [← hprep]; unfold PreparedBlock.terms; exact List.mem_cons_self)
            rw [← hprep]
            unfold PreparedBlock.exactDot PreparedBlock.exactProducts
            rw [hc0, sumQ_eq, Rat.zero_add]
            apply sum_zero_of
            intro x hx
            obtain ⟨⟨a, b⟩, hab, rfl⟩ := List.mem_map.mp hx
            have := hval0 (denormalizedMul a b) (by
              rw [← hprep]; unfold PreparedBlock.terms
              exact List.mem_cons_of_mem _ (List.mem_map.mpr ⟨(a, b), hab, rfl⟩))
            rw [denormalizedProduct_value] at this; exact this
          rw [hvo, hvd, ← hexact, hexact0, hout0]
          have e0 : Rat.abs ((0 : ℚ) - 0) = 0 := by rw [Rat.sub_self]; exact Ozaki.abs_zero
          rw [e0]
          have := Rat.mul_nonneg (Rat.le_of_lt (pow2_pos (-23)))
            (show 0 ≤ A + (tcMachine p).slotAbs ps by
              have := (tcMachine p).slotAbs_nonneg ps; grind)
          have := Rat.mul_nonneg (Rat.mul_nonneg (show (0 : ℚ) ≤ (ps.length : ℚ) + 1 by
            have : (0 : ℚ) ≤ (ps.length : ℚ) := by exact_mod_cast Nat.zero_le _
            grind) (Rat.le_of_lt (pow2_pos (-p.alignFracBits))))
            (show 0 ≤ A + pow2 (-125) + ((slotPairs p ps).map (expMag p)).sum by
              have := pow2_pos (-125); grind)
          have := pow2_pos (-149)
          grind
        · obtain ⟨η, hη⟩ := Option.ne_none_iff_exists'.mp hzero
          have hgrid : t.block.alignGridExponent = η - p.alignFracBits := by
            unfold PreparedBlock.alignGridExponent; rw [hη]; rw [← hprep]; rfl
          -- `2^η` is at most the magnitude terms
          have h2η : pow2 η ≤ A + pow2 (-125) + ((slotPairs p ps).map (expMag p)).sum := by
            unfold PreparedBlock.alignExp Model.applyEAlignMin at hη
            cases hm : maxTermExp t.block.terms with
            | none => rw [hm] at hη; cases hη
            | some e =>
              rw [hm] at hη
              obtain ⟨u, hu, hnz, hue⟩ := maxTermExp_attained hm
              have hue_bound : pow2 e ≤ A + pow2 (-126) + ((slotPairs p ps).map (expMag p)).sum := by
                rw [← hue]
                rw [← hprep] at hu
                unfold PreparedBlock.terms at hu
                rcases List.mem_cons.mp hu with rfl | hu
                · have := decode32_exp_bound hc hnz; grind
                · obtain ⟨⟨a, b⟩, hab, rfl⟩ := List.mem_map.mp hu
                  rw [hds] at hab
                  obtain ⟨q, hq, hqe⟩ := List.mem_map.mp hab
                  simp only [Prod.mk.injEq] at hqe
                  obtain ⟨rfl, rfl⟩ := hqe
                  obtain ⟨h1, h2⟩ := prepareProducts_finite hps q hq
                  obtain ⟨a', ha'⟩ := Option.isSome_iff_exists.mp h1
                  obtain ⟨b', hb'⟩ := Option.isSome_iff_exists.mp h2
                  have hem : expMag p q = pow2 (denormalizedMul (decodeD p q.1) (decodeD p q.2)).exponent := by
                    unfold expMag
                    rw [ha', hb']
                    simp only
                    have hdA : decodeD p q.1 = a' := by simp [decodeD, ha']
                    have hdB : decodeD p q.2 = b' := by simp [decodeD, hb']
                    rw [hdA, hdB] at hnz ⊢
                    simp only [denormalizedMul] at hnz ⊢
                    rw [if_neg hnz]
                  rw [← hem]
                  have := le_sum_of_mem (fun x hx => by
                    obtain ⟨q', _, rfl⟩ := List.mem_map.mp hx; exact expMag_nonneg p q')
                    (List.mem_map.mpr ⟨q, hq, rfl⟩)
                  have := pow2_pos (-126)
                  grind
              have h126 : pow2 (-126) + pow2 (-126) = pow2 (-125) := by decide +kernel
              have hmodel : t.block.model = p := by rw [← hprep]
              rw [hmodel] at hη
              cases hf : p.eAlignMin with
              | none =>
                rw [hf] at hη; simp only [Option.some.injEq] at hη; subst hη
                have := pow2_pos (-126)
                grind
              | some f =>
                rw [hf] at hη; simp only [Option.some.injEq] at hη; subst hη
                have hf126 : f ≤ -126 := hmin f (by rw [hf]; simp)
                rcases Int.le_total e f with hef | hfe
                · rw [Int.max_eq_right hef]
                  have := pow2_le_of_le hf126
                  have := pow2_pos (-126)
                  grind
                · rw [Int.max_eq_left hfe]
                  have := pow2_pos (-126)
                  grind
          -- the output's magnitude
          have hout : absQ t.output.value ≤ A + (tcMachine p).slotAbs ps := by
            rw [evalPrepared_output_value hev (by rw [evalBlock_model ht]; exact hw)]
            refine Rat.le_trans (abs_signedRounded_trunc_le _) ?_
            rw [accumulator_value]
            refine Rat.le_trans (absQ_sumQ_le _) ?_
            rw [List.map_map, sumQ_eq]
            have hle : ((t.block.terms.map ((absQ) ∘ fun u => truncGrid u.value t.block.alignGridExponent))).sum ≤
                (t.block.terms.map fun u => absQ u.value).sum :=
              sum_le_sum_map (l := t.block.terms) (fun u _ => truncGrid_abs_le _ _)
            refine Rat.le_trans hle ?_
            have hterms : t.block.terms = ⟨dc.significand, dc.exponent, dc.mantissaBits⟩ ::
                ds.map (fun x => denormalizedMul x.1 x.2) := by
              rw [← hprep]; rfl
            rw [hterms, List.map_cons, List.sum_cons]
            have hcv : DenormalizedProduct.value ⟨dc.significand, dc.exponent, dc.mantissaBits⟩ = dc.value := rfl
            rw [hcv, slotAbs_words p hz, hds]
            unfold wordDotAbs
            have key : ∀ q : p.Word × p.Word,
                absQ (denormalizedMul (decodeD p q.1) (decodeD p q.2)).value =
                  Rat.abs (wordValue p q.1 * wordValue p q.2) := fun q => by
              rw [denormalizedProduct_value, absQ_eq]; rfl
            simp only [List.map_map, Function.comp_def, key]
            grind
          have hulp := ulp_bound (value32_output t)
          have hlen' : (t.block.terms.length : ℚ) * pow2 t.block.alignGridExponent ≤
              ((ps.length : ℚ) + 1) * pow2 (-p.alignFracBits) *
                (A + pow2 (-125) + ((slotPairs p ps).map (expMag p)).sum) := by
            rw [← hlen, hgrid, show η - p.alignFracBits = η + (-p.alignFracBits) by omega, pow2_add]
            have hn : (0 : ℚ) ≤ (ps.length : ℚ) + 1 := by
              have : (0 : ℚ) ≤ (ps.length : ℚ) := by exact_mod_cast Nat.zero_le _
              grind
            have := Rat.mul_le_mul_of_nonneg_right h2η (Rat.le_of_lt (pow2_pos (-p.alignFracBits)))
            have := Rat.mul_le_mul_of_nonneg_left this hn
            grind
          have hulp' : pow2 (outputUlpExponent t.output.bits) ≤
              pow2 (-23) * (A + (tcMachine p).slotAbs ps) + pow2 (-149) := by
            have := Rat.mul_le_mul_of_nonneg_left hout (Rat.le_of_lt (pow2_pos (-23)))
            grind
          rw [hvo, hvd, ← hexact, Ozaki.abs_sub_comm, ← absQ_eq]
          grind

/-! ## Binary32 addition and the contract -/

/-- **Round to nearest even is within `2^-24 |z| + 2^-150` of `z`.** -/
theorem tc_rne_err {z : ℚ} {o : F32} (h : round32 .nearestEven z = some o) :
    Rat.abs (value32D o - z) ≤ pow2 (-24) * Rat.abs z + pow2 (-150) := by
  by_cases hz : z = 0
  · subst hz
    have h0 : round32 .nearestEven 0 = some (0 : F32) := by decide +kernel
    rw [h0] at h; cases h
    have : value32D (0 : F32) = 0 := by decide +kernel
    rw [this, show (0 : ℚ) - 0 = 0 by grind, Ozaki.abs_zero]
    have := Rat.mul_nonneg (Rat.le_of_lt (pow2_pos (-24))) (Ozaki.abs_nonneg (0 : ℚ))
    have := pow2_pos (-150)
    grind
  · obtain ⟨b, hb, hv, _, _⟩ := round32_nonzero_spec .nearestEven z hz (round32_range h)
    rw [h] at hb; cases hb
    have hvd : value32D o = signedRounded .nearestEven z := by simp [value32D, hv]
    rw [hvd]
    have hm := absQ_pos_of_ne_zero z hz
    obtain ⟨_, _, _, hnorm⟩ := normExp_bounds (absQ z) hm (round32_range h)
    -- the magnitude is rounded to within half a step of the grid `2^(normExp − 23)`
    have hq := pow2_pos (normExp (absQ z) - 23)
    have hhalf : absQ (magnitudeRounded .nearestEven (absQ z) - absQ z) ≤
        pow2 (normExp (absQ z) - 24) := by
      unfold magnitudeRounded roundedSignificand roundSignificand
      generalize hP : pow2 (normExp (absQ z) - 23) = P at hq ⊢
      have hd := rneInt_dist_le_half (absQ z / P)
      have hdiv : absQ z / P * P = absQ z := Rat.div_mul_cancel (Rat.ne_of_gt hq)
      have e : (rneInt (absQ z / P) : ℚ) * P - absQ z = ((rneInt (absQ z / P) : ℚ) - absQ z / P) * P := by
        rw [← hdiv]
        grind
      rw [e, absQ_mul_pos _ _ hq, absQ_sub_comm]
      have e2 : pow2 (normExp (absQ z) - 24) * 2 = P := by
        rw [← hP, show normExp (absQ z) - 23 = (normExp (absQ z) - 24) + 1 by omega, pow2_add]; rfl
      have := Rat.mul_le_mul_of_nonneg_right hd (Rat.le_of_lt hq)
      grind
    have hsig : absQ (signedRounded .nearestEven z - z) =
        absQ (magnitudeRounded .nearestEven (absQ z) - absQ z) := by
      unfold signedRounded
      split
      · rename_i hneg
        rw [absQ_of_neg hneg]
        rw [show -magnitudeRounded .nearestEven (-z) - z = -(magnitudeRounded .nearestEven (-z) - -z)
          by grind, absQ_neg]
      · rename_i hpos
        rw [absQ_of_nonneg (show (0 : ℚ) ≤ z by grind)]
    rw [← absQ_eq, hsig]
    refine Rat.le_trans hhalf ?_
    rcases hnorm with hle | he
    · have e3 : pow2 (normExp (absQ z) - 24) = pow2 (-24) * pow2 (normExp (absQ z)) := by
        rw [← pow2_add]; congr 1; omega
      rw [e3, ← absQ_eq]
      have := Rat.mul_le_mul_of_nonneg_left hle (Rat.le_of_lt (pow2_pos (-24)))
      have := pow2_pos (-150)
      grind
    · rw [he, ← absQ_eq]
      have := Rat.mul_nonneg (Rat.le_of_lt (pow2_pos (-24))) (absQ_nonneg z)
      show pow2 (-150) ≤ _
      grind

theorem tc_add_le (p : Model) (x y o : F32) (h : (tcMachine p).add x y = some o) :
    Rat.abs ((tcMachine p).val o - ((tcMachine p).val x + (tcMachine p).val y)) ≤
      pow2 (-24) * (Rat.abs ((tcMachine p).val x) + Rat.abs ((tcMachine p).val y)) + pow2 (-150) := by
  have e := tc_rne_err (z := value32D x + value32D y) h
  have tri := Ozaki.abs_add_le (value32D x) (value32D y)
  have := Rat.mul_le_mul_of_nonneg_left tri (Rat.le_of_lt (pow2_pos (-24)))
  show Rat.abs (value32D o - (value32D x + value32D y)) ≤
    pow2 (-24) * (Rat.abs (value32D x) + Rat.abs (value32D y)) + pow2 (-150)
  grind

/-- The error contract of a Tensor Core model with a binary32 block output: the block contract
`tc_block_le` and binary32 round-to-nearest addition. -/
def tcContract (p : Model) (hmin : ∀ f ∈ p.eAlignMin, f ≤ -126) (hz : p.decode 0 = some ⟨0, 0, 0⟩)
    (hw : 23 ≤ p.outputFracBits) :
    MMAlgebra.Contract (tcMachine p) where
  blockErr A ps := ((ps.length : ℚ) + 1) * pow2 (-p.alignFracBits) *
      (A + pow2 (-125) + ((slotPairs p ps).map (expMag p)).sum) +
    pow2 (-23) * (A + (tcMachine p).slotAbs ps) + pow2 (-149)
  block_le d ps o A hA h := tc_block_le p hmin hz hw d ps o A hA h
  addRel := pow2 (-24)
  addRel_nonneg := Rat.le_of_lt (pow2_pos _)
  addAbs := pow2 (-150)
  add_le x y o h := tc_add_le p x y o h

/-- With normal operands (each at least 2 to its exponent), `expMag` is at most the product's
magnitude, so the block contract is `(K + 1)·2^-F·(A + Σ|aᵢbᵢ| + 2^-125) + 2^-23·(A + Σ|aᵢbᵢ|) +
2^-149`. -/
theorem expMag_le_of_normal (p : Model) (q : p.Word × p.Word) {a b : Decoded}
    (ha : p.decode q.1 = some a) (hb : p.decode q.2 = some b)
    (hna : pow2 a.exponent ≤ absQ a.value) (hnb : pow2 b.exponent ≤ absQ b.value) :
    expMag p q ≤ Rat.abs ((tcMachine p).pval q) := by
  unfold expMag
  rw [ha, hb]
  simp only
  have hva : wordValue p q.1 = a.value := by simp [wordValue, decodeD, ha]
  have hvb : wordValue p q.2 = b.value := by simp [wordValue, decodeD, hb]
  show _ ≤ Rat.abs (wordValue p q.1 * wordValue p q.2)
  rw [hva, hvb]
  split
  · exact Ozaki.abs_nonneg _
  · rw [pow2_add, ← absQ_eq]
    have hm : absQ (a.value * b.value) = absQ a.value * absQ b.value := by
      rw [absQ_eq, absQ_eq, absQ_eq]; exact Ozaki.abs_mul _ _
    rw [hm]
    have h1 := Rat.mul_le_mul_of_nonneg_right hna (Rat.le_of_lt (pow2_pos b.exponent))
    have h2 := Rat.mul_le_mul_of_nonneg_left hnb (absQ_nonneg a.value)
    exact Rat.le_trans h1 h2

theorem fp16_decode_zero (K neab : ℕ) (e : Option ℤ) :
    (fp16Fp32Model K neab e).decode 0 = some ⟨0, 0, 0⟩ := by
  show (classify fp16 0).finite = some _; decide +kernel

/-- **Divergence on V100.** Any two reduction terms over the same products and `c` on the V100 fp16
model differ by at most the sum of their structural bounds. -/
theorem v100_divergence (q : ℕ → F16 × F16) (c : F32) (t₁ t₂ : MMAlgebra.Term) {o₁ o₂ : F32}
    (he₁ : MMAlgebra.eval (tcMachine v100F16F32) q c c t₁ = some o₁)
    (he₂ : MMAlgebra.eval (tcMachine v100F16F32) q c c t₂ = some o₂)
    (hex : MMAlgebra.exact (tcMachine v100F16F32) q (value32D c) (value32D c) t₁ =
      MMAlgebra.exact (tcMachine v100F16F32) q (value32D c) (value32D c) t₂) :
    Rat.abs (value32D o₁ - value32D o₂) ≤
      MMAlgebra.err (tcContract v100F16F32 (by simp [v100F16F32]) (fp16_decode_zero 4 0 none)
          (by decide)) q
          (Rat.abs (value32D c)) (Rat.abs (value32D c)) t₁ +
        MMAlgebra.err (tcContract v100F16F32 (by simp [v100F16F32]) (fp16_decode_zero 4 0 none)
          (by decide)) q
          (Rat.abs (value32D c)) (Rat.abs (value32D c)) t₂ :=
  MMAlgebra.divergence _ _ q q c c c c t₁ t₂ he₁ he₂ hex

/-- **Divergence on A100.** -/
theorem a100_divergence (q : ℕ → F16 × F16) (c : F32) (t₁ t₂ : MMAlgebra.Term) {o₁ o₂ : F32}
    (he₁ : MMAlgebra.eval (tcMachine ampereF16F32) q c c t₁ = some o₁)
    (he₂ : MMAlgebra.eval (tcMachine ampereF16F32) q c c t₂ = some o₂)
    (hex : MMAlgebra.exact (tcMachine ampereF16F32) q (value32D c) (value32D c) t₁ =
      MMAlgebra.exact (tcMachine ampereF16F32) q (value32D c) (value32D c) t₂) :
    Rat.abs (value32D o₁ - value32D o₂) ≤
      MMAlgebra.err (tcContract ampereF16F32 (by simp [ampereF16F32, fp16Fp32Model])
          (fp16_decode_zero 8 1 _) (by decide)) q (Rat.abs (value32D c)) (Rat.abs (value32D c)) t₁ +
        MMAlgebra.err (tcContract ampereF16F32 (by simp [ampereF16F32, fp16Fp32Model])
          (fp16_decode_zero 8 1 _) (by decide)) q (Rat.abs (value32D c)) (Rat.abs (value32D c)) t₂ :=
  MMAlgebra.divergence _ _ q q c c c c t₁ t₂ he₁ he₂ hex

/-- **Divergence on H100.** -/
theorem h100_divergence (q : ℕ → F16 × F16) (c : F32) (t₁ t₂ : MMAlgebra.Term) {o₁ o₂ : F32}
    (he₁ : MMAlgebra.eval (tcMachine hopperF16F32) q c c t₁ = some o₁)
    (he₂ : MMAlgebra.eval (tcMachine hopperF16F32) q c c t₂ = some o₂)
    (hex : MMAlgebra.exact (tcMachine hopperF16F32) q (value32D c) (value32D c) t₁ =
      MMAlgebra.exact (tcMachine hopperF16F32) q (value32D c) (value32D c) t₂) :
    Rat.abs (value32D o₁ - value32D o₂) ≤
      MMAlgebra.err (tcContract hopperF16F32 (by simp [hopperF16F32, fp16Fp32Model])
          (fp16_decode_zero 16 2 _) (by decide)) q (Rat.abs (value32D c)) (Rat.abs (value32D c)) t₁ +
        MMAlgebra.err (tcContract hopperF16F32 (by simp [hopperF16F32, fp16Fp32Model])
          (fp16_decode_zero 16 2 _) (by decide)) q (Rat.abs (value32D c)) (Rat.abs (value32D c)) t₂ :=
  MMAlgebra.divergence _ _ q q c c c c t₁ t₂ he₁ he₂ hex

end MMAlgebra.TC
