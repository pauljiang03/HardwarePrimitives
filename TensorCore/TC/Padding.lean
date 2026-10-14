import TensorCore.TC.CanonicalEAlignMin
import TensorCore.TC.ExactAlignment
import TensorCore.TC.AcceptedDomain

/-! Padding bits that make FP16 alignment exact. -/

namespace TensorCore

/-- Uniform finite FP16-product/FP32-c metadata bounds. -/
theorem prepare_fp16_term_metadata (K padding : ℕ) (eAlignMin : Option ℤ)
    (x : BlockInput (fp16Fp32Model K padding eAlignMin)) (b : PreparedBlock)
    (h : prepare x = some b) :
    ∀ t ∈ b.terms, t.significand ≠ 0 →
      -149 ≤ t.exponent - t.mantissaBits ∧ t.exponent ≤ 127 := by
  unfold prepare at h
  cases hc : decode32 x.c with
  | none => simp [hc] at h
  | some c =>
    cases hp : prepareProducts (fp16Fp32Model K padding eAlignMin) x.products with
    | none => simp [hc, hp] at h
    | some ps =>
      simp [hc, hp] at h
      subst b
      intro t ht hnz
      simp only [PreparedBlock.terms, List.mem_cons, List.mem_map] at ht
      rcases ht with ht | ⟨pair, hpair, ht⟩
      · subst t
        have hm := classifyNat_metadata fp32 (by decide) x.c.toNat c hc hnz
        change c.mantissaBits = 23 ∧ -126 ≤ c.exponent ∧ c.exponent ≤ 127 at hm
        change -149 ≤ c.exponent - c.mantissaBits ∧ c.exponent ≤ 127
        omega
      · subst t
        obtain ⟨w, _, ha, hb⟩ := prepareProducts_origin _ _ _ hp pair hpair
        have hnza : pair.1.significand ≠ 0 := by
          intro hz; apply hnz; simp [denormalizedMul, hz]
        have hnzb : pair.2.significand ≠ 0 := by
          intro hz; apply hnz; simp [denormalizedMul, hz]
        have hma := classifyNat_metadata fp16 (by decide) w.1.toNat pair.1 ha hnza
        have hmb := classifyNat_metadata fp16 (by decide) w.2.toNat pair.2 hb hnzb
        change pair.1.mantissaBits = 10 ∧ -14 ≤ pair.1.exponent ∧ pair.1.exponent ≤ 15 at hma
        change pair.2.mantissaBits = 10 ∧ -14 ≤ pair.2.exponent ∧ pair.2.exponent ≤ 15 at hmb
        change -149 ≤ (pair.1.exponent + pair.2.exponent) -
          (pair.1.mantissaBits + pair.2.mantissaBits) ∧
          pair.1.exponent + pair.2.exponent ≤ 127
        omega

/-- FP16 products have much narrower scale/grid support than FP32 c. -/
theorem prepare_fp16_products_metadata (K padding : ℕ) (eAlignMin : Option ℤ)
    (x : BlockInput (fp16Fp32Model K padding eAlignMin)) (b : PreparedBlock)
    (h : prepare x = some b) :
    ∀ t ∈ b.products.map (fun (a, b) => denormalizedMul a b), t.significand ≠ 0 →
      -48 ≤ t.exponent - t.mantissaBits ∧ t.exponent ≤ 30 := by
  unfold prepare at h
  cases hc : decode32 x.c with
  | none => simp [hc] at h
  | some c =>
    cases hp : prepareProducts (fp16Fp32Model K padding eAlignMin) x.products with
    | none => simp [hc, hp] at h
    | some ps =>
      simp [hc, hp] at h
      subst b
      intro t ht hnz
      obtain ⟨pair, hpair, rfl⟩ := List.mem_map.mp ht
      obtain ⟨w, _, ha, hb⟩ := prepareProducts_origin _ _ _ hp pair hpair
      have hnza : pair.1.significand ≠ 0 := by
        intro hz; apply hnz; simp [denormalizedMul, hz]
      have hnzb : pair.2.significand ≠ 0 := by
        intro hz; apply hnz; simp [denormalizedMul, hz]
      have hma := classifyNat_metadata fp16 (by decide) w.1.toNat pair.1 ha hnza
      have hmb := classifyNat_metadata fp16 (by decide) w.2.toNat pair.2 hb hnzb
      change pair.1.mantissaBits = 10 ∧ -14 ≤ pair.1.exponent ∧ pair.1.exponent ≤ 15 at hma
      change pair.2.mantissaBits = 10 ∧ -14 ≤ pair.2.exponent ∧ pair.2.exponent ≤ 15 at hmb
      change -48 ≤ (pair.1.exponent + pair.2.exponent) -
        (pair.1.mantissaBits + pair.2.mantissaBits) ∧
        pair.1.exponent + pair.2.exponent ≤ 30
      omega

/-- A sharper sufficient threshold for minimum alignment exponents of at most 30, which covers the models of all source variants. -/
theorem canonical_source_padding_exact (K padding : ℕ) (eAlignMin : Option ℤ)
    (hf : ∀ f ∈ eAlignMin, f ≤ 30) (hpadding : 156 ≤ padding)
    (x : BlockInput (fp16Fp32Model K padding eAlignMin)) (b : PreparedBlock)
    (hp : prepare x = some b) : b.AlignmentExact := by
  have hprof := prepare_model hp
  have hm := prepare_fp16_term_metadata K padding eAlignMin x b hp
  have hpm := prepare_fp16_products_metadata K padding eAlignMin x b hp
  have hu := alignExp_upper b 127 (by
    intro f hmem
    have hf' := hf f (by simpa [hprof, fp16Fp32Model] using hmem)
    omega) (by intro t ht hnz; exact (hm t ht hnz).2)
  have huc := alignExp_upper b (max b.c.exponent 30) (by
    intro f hmem
    have hf' := hf f (by simpa [hprof, fp16Fp32Model] using hmem)
    omega) (by
      intro t ht hnz
      simp only [PreparedBlock.terms, List.mem_cons] at ht
      rcases ht with ht | ht
      · subst t
        change b.c.exponent ≤ max b.c.exponent 30
        omega
      · have hpt := (hpm t ht hnz).2
        omega)
  intro t ht hnz
  obtain ⟨alignExp, he, _⟩ := alignExp_term b t ht hnz
  have hemax := hu alignExp (by simp [he])
  have hec := huc alignExp (by simp [he])
  have hq : b.alignGridExponent = alignExp - (23 + padding : ℕ) := by
    simp [PreparedBlock.alignGridExponent, he, hprof, fp16Fp32Model]
  rw [hq]
  simp only [PreparedBlock.terms, List.mem_cons] at ht
  rcases ht with ht | ht
  · subst t
    have hc := classifyNat_metadata fp32 (by decide) x.c.toNat b.c (prepare_c hp) hnz
    change b.c.mantissaBits = 23 ∧ -126 ≤ b.c.exponent ∧ b.c.exponent ≤ 127 at hc
    change alignExp - (23 + padding : ℕ) ≤ b.c.exponent - b.c.mantissaBits
    omega
  · have hpt := (hpm t ht hnz).1
    omega

theorem canonical_source_padding_accumulator (K padding : ℕ) (eAlignMin : Option ℤ)
    (hf : ∀ f ∈ eAlignMin, f ≤ 30) (hpadding : 156 ≤ padding)
    (x : BlockInput (fp16Fp32Model K padding eAlignMin)) (b : PreparedBlock)
    (hp : prepare x = some b) : b.accumulator = b.exactDot :=
  exact_alignment_accumulator b (canonical_source_padding_exact K padding eAlignMin hf hpadding x b hp)

theorem canonical_source_padding_output (K padding : ℕ) (eAlignMin : Option ℤ)
    (hf : ∀ f ∈ eAlignMin, f ≤ 30) (hpadding : 156 ≤ padding)
    (x : BlockInput (fp16Fp32Model K padding eAlignMin)) (t : BlockTrace)
    (he : evalBlock x = .ok t) :
    round32 .truncate t.block.exactDot = some t.output.bits :=
  (evalBlock_exact_alignment he (canonical_source_padding_exact K padding eAlignMin hf hpadding x
    t.block (evalBlock_prepared he)) (Nat.le_refl 23)).2

theorem canonical_source_padding_success_iff (K padding : ℕ) (eAlignMin : Option ℤ)
    (hf : ∀ f ∈ eAlignMin, f ≤ 30) (hpadding : 156 ≤ padding)
    (x : BlockInput (fp16Fp32Model K padding eAlignMin)) :
    (∃ t, evalBlock x = .ok t) ↔ x.products.length = K ∧
      ∃ b, prepare x = some b ∧ absQ b.exactDot ≤ maxFinite32 := by
  rw [evalBlock_success_iff]
  constructor
  · rintro ⟨hs, b, hp, hr⟩
    rw [canonical_source_padding_accumulator K padding eAlignMin hf hpadding x b hp] at hr
    exact ⟨hs, b, hp, hr⟩
  · rintro ⟨hs, b, hp, hr⟩
    refine ⟨hs, b, hp, ?_⟩
    rwa [canonical_source_padding_accumulator K padding eAlignMin hf hpadding x b hp]

/-- A conservative uniform threshold on the padding bits. -/
theorem canonical_padding_exact (K padding : ℕ) (eAlignMin : Option ℤ)
    (hf : ∀ f ∈ eAlignMin, f ≤ 127) (hpadding : 253 ≤ padding)
    (x : BlockInput (fp16Fp32Model K padding eAlignMin)) (b : PreparedBlock)
    (hp : prepare x = some b) : b.AlignmentExact := by
  have hm := prepare_fp16_term_metadata K padding eAlignMin x b hp
  have hu := maxTermExp_upper b.terms 127 (by intro t ht hnz; exact (hm t ht hnz).2)
  have hprof := prepare_model hp
  intro t ht hnz
  obtain ⟨alignExp, he, _⟩ := alignExp_term b t ht hnz
  have heta : alignExp ≤ 127 := by
    have he' := he
    simp only [PreparedBlock.alignExp, hprof, fp16Fp32Model] at he'
    cases hs : maxTermExp b.terms with
    | none => simp [Model.applyEAlignMin, hs] at he'
    | some e =>
      have hemax := hu e (by simp [hs])
      cases eAlignMin with
      | none => simp [Model.applyEAlignMin, hs] at he'; omega
      | some f =>
        have hf' := hf f (by simp)
        simp [Model.applyEAlignMin, hs] at he'
        omega
  have htmin := (hm t ht hnz).1
  simp only [PreparedBlock.alignGridExponent, he, Option.getD_some,
    hprof, fp16Fp32Model]
  omega

theorem canonical_padding_accumulator (K padding : ℕ) (eAlignMin : Option ℤ)
    (hf : ∀ f ∈ eAlignMin, f ≤ 127) (hpadding : 253 ≤ padding)
    (x : BlockInput (fp16Fp32Model K padding eAlignMin)) (b : PreparedBlock)
    (hp : prepare x = some b) : b.accumulator = b.exactDot :=
  exact_alignment_accumulator b (canonical_padding_exact K padding eAlignMin hf hpadding x b hp)

theorem canonical_padding_output (K padding : ℕ) (eAlignMin : Option ℤ)
    (hf : ∀ f ∈ eAlignMin, f ≤ 127) (hpadding : 253 ≤ padding)
    (x : BlockInput (fp16Fp32Model K padding eAlignMin)) (t : BlockTrace)
    (he : evalBlock x = .ok t) :
    round32 .truncate t.block.exactDot = some t.output.bits :=
  (evalBlock_exact_alignment he (canonical_padding_exact K padding eAlignMin hf hpadding x
    t.block (evalBlock_prepared he)) (Nat.le_refl 23)).2

/-- With enough padding bits, acceptance depends on the ideal sum's range directly. -/
theorem canonical_padding_success_iff (K padding : ℕ) (eAlignMin : Option ℤ)
    (hf : ∀ f ∈ eAlignMin, f ≤ 127) (hpadding : 253 ≤ padding)
    (x : BlockInput (fp16Fp32Model K padding eAlignMin)) :
    (∃ t, evalBlock x = .ok t) ↔ x.products.length = K ∧
      ∃ b, prepare x = some b ∧ absQ b.exactDot ≤ maxFinite32 := by
  rw [evalBlock_success_iff]
  constructor
  · rintro ⟨hs, b, hp, hr⟩
    rw [canonical_padding_accumulator K padding eAlignMin hf hpadding x b hp] at hr
    exact ⟨hs, b, hp, hr⟩
  · rintro ⟨hs, b, hp, hr⟩
    refine ⟨hs, b, hp, ?_⟩
    rwa [canonical_padding_accumulator K padding eAlignMin hf hpadding x b hp]

end TensorCore
