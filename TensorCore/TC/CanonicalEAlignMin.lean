import TensorCore.TC.Canonical

/-! When the alignment floor is inactive on FP16 profiles. -/

namespace TensorCore

private theorem mapM_origin (f : α → Option β) (xs : List α) (ys : List β)
    (h : xs.mapM f = some ys) : ∀ y ∈ ys, ∃ x ∈ xs, f x = some y := by
  induction xs generalizing ys with
  | nil => simp at h; subst ys; simp
  | cons x xs ih =>
    cases hf : f x with
    | none => simp [List.mapM_cons, hf] at h
    | some y =>
      cases ht : xs.mapM f with
      | none => simp [List.mapM_cons, hf, ht] at h
      | some zs =>
        simp [List.mapM_cons, hf, ht] at h
        subst ys
        intro z hz
        simp only [List.mem_cons] at hz
        rcases hz with hz | hz
        · subst z; exact ⟨x, by simp, hf⟩
        · obtain ⟨a, ha, hd⟩ := ih zs ht z hz
          exact ⟨a, by simp [ha], hd⟩

/-- Every prepared factor pair comes from an original encoded pair. -/
theorem prepareProducts_origin (p : Model) (xs : List (p.Word × p.Word))
    (ys : List (Decoded × Decoded)) (h : prepareProducts p xs = some ys) :
    ∀ y ∈ ys, ∃ x ∈ xs, p.decode x.1 = some y.1 ∧ p.decode x.2 = some y.2 := by
  intro y hy
  obtain ⟨x, hx, hd⟩ := mapM_origin _ xs ys h y hy
  refine ⟨x, hx, ?_⟩
  cases ha : p.decode x.1 with
  | none => simp [ha] at hd
  | some a =>
    cases hb : p.decode x.2 with
    | none => simp [ha, hb] at hd
    | some b =>
      simp [ha, hb] at hd
      subst y
      exact ⟨rfl, rfl⟩

theorem prepare_fp16_terms_lower (K neab : ℕ) (eAlignMin : Option ℤ)
    (x : BlockInput (fp16Fp32Model K neab eAlignMin)) (b : PreparedBlock)
    (h : prepare x = some b) :
    ∀ t ∈ b.terms, t.significand ≠ 0 → -126 ≤ t.unnormalizedExp := by
  unfold prepare at h
  cases hc : decode32 x.c with
  | none => simp [hc] at h
  | some c =>
    cases hp : prepareProducts (fp16Fp32Model K neab eAlignMin) x.products with
    | none => simp [hc, hp] at h
    | some ps =>
      simp [hc, hp] at h
      subst b
      intro t ht hnz
      simp only [PreparedBlock.terms, List.mem_cons, List.mem_map] at ht
      rcases ht with ht | ⟨pair, hpair, ht⟩
      · subst t
        exact classifyNat_scale_lower fp32 x.c.toNat c hc hnz
      · subst t
        obtain ⟨w, _, ha, hb⟩ := prepareProducts_origin _ _ _ hp pair hpair
        have hnza : pair.1.significand ≠ 0 := by
          intro hz; apply hnz; simp [unnormalizedMul, hz]
        have hnzb : pair.2.significand ≠ 0 := by
          intro hz; apply hnz; simp [unnormalizedMul, hz]
        have hla := classifyNat_scale_lower fp16 w.1.toNat pair.1 ha hnza
        have hlb := classifyNat_scale_lower fp16 w.2.toNat pair.2 hb hnzb
        change -14 ≤ pair.1.unnormalizedExp at hla
        change -14 ≤ pair.2.unnormalizedExp at hlb
        change -126 ≤ pair.1.unnormalizedExp + pair.2.unnormalizedExp
        omega

theorem maxTermExp_lower (ts : List UnnormalizedProduct) (lower e : ℤ)
    (h : ∀ t ∈ ts, t.significand ≠ 0 → lower ≤ t.unnormalizedExp)
    (he : maxTermExp ts = some e) : lower ≤ e := by
  have hex : ∃ t ∈ ts, t.significand ≠ 0 := by
    by_cases hz : ∀ t ∈ ts, t.significand = 0
    · have hn := (maxTermExp_none ts).mpr hz
      rw [he] at hn
      contradiction
    · grind
  obtain ⟨t, ht, hnz⟩ := hex
  obtain ⟨alignExp, he', hle⟩ := maxTermExp_term ts t ht hnz
  rw [he] at he'
  have heq := Option.some.inj he'
  have hl := h t ht hnz
  omega

/-- Any floor at most -126 is inactive on a prepared canonical invocation. -/
theorem canonical_alignExp_eAlignMin_inactive (K neab : ℕ) (eAlignMin : Option ℤ)
    (hf : ∀ f ∈ eAlignMin, f ≤ -126)
    (x : BlockInput (fp16Fp32Model K neab eAlignMin)) (b : PreparedBlock)
    (h : prepare x = some b) : b.alignExp = maxTermExp b.terms := by
  have hprof : b.model = fp16Fp32Model K neab eAlignMin := by
    unfold prepare at h
    cases hc : decode32 x.c with
    | none => simp [hc] at h
    | some c =>
      cases hp : prepareProducts (fp16Fp32Model K neab eAlignMin) x.products with
      | none => simp [hc, hp] at h
      | some ps => simp [hc, hp] at h; subst b; rfl
  have hl := prepare_fp16_terms_lower K neab eAlignMin x b h
  unfold PreparedBlock.alignExp
  rw [hprof]
  cases he : maxTermExp b.terms with
  | none => rfl
  | some e =>
    have hemin := maxTermExp_lower b.terms (-126) e hl he
    cases eAlignMin with
    | none => rfl
    | some f =>
      have hf' := hf f (by simp)
      change some (max e f) = some e
      congr 1
      omega

end TensorCore
