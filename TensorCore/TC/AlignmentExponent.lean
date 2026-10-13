import TensorCore.Numerics.FormatProperties
import TensorCore.Numerics.Truncation
import TensorCore.TC.AccumulatorWidth
import TensorCore.TC.StageResiduals

/-! The alignment exponent and accumulator capacity. -/

namespace TensorCore

private def maxStep (acc : Option ℤ) (e : ℤ) : Option ℤ :=
  some (match acc with | none => e | some v => max v e)

private theorem fold_max_preserves (es : List ℤ) (e lower : ℤ) (h : lower ≤ e) :
    ∃ alignExp, es.foldl maxStep (some e) = some alignExp ∧ lower ≤ alignExp := by
  induction es generalizing e with
  | nil => exact ⟨e, rfl, h⟩
  | cons x xs ih =>
    apply ih (max e x)
    omega

private theorem fold_max_member (es : List ℤ) (acc : Option ℤ) (e : ℤ)
    (h : e ∈ es) : ∃ alignExp, es.foldl maxStep acc = some alignExp ∧ e ≤ alignExp := by
  induction es generalizing acc with
  | nil => simp at h
  | cons x xs ih =>
    simp only [List.mem_cons] at h
    rcases h with h | h
    · subst x
      cases acc with
      | none => exact fold_max_preserves xs e e (by omega)
      | some v => exact fold_max_preserves xs (max v e) e (by omega)
    · exact ih (maxStep acc x) h

theorem maxTermExp_term (ts : List UnnormalizedProduct) (t : UnnormalizedProduct)
    (hmem : t ∈ ts) (hnz : t.significand ≠ 0) :
    ∃ alignExp, maxTermExp ts = some alignExp ∧ t.unnormalizedExp ≤ alignExp := by
  apply fold_max_member
  apply List.mem_filterMap.mpr
  exact ⟨t, hmem, by simp [hnz]⟩

theorem maxTermExp_none (ts : List UnnormalizedProduct) :
    maxTermExp ts = none ↔ ∀ t ∈ ts, t.significand = 0 := by
  constructor
  · intro h t ht
    by_cases hnz : t.significand = 0
    · exact hnz
    · obtain ⟨alignExp, he, _⟩ := maxTermExp_term ts t ht hnz
      rw [h] at he
      contradiction
  · intro h
    have hf : (ts.filterMap fun t => if t.significand = 0 then none else some t.unnormalizedExp) = [] := by
      apply List.filterMap_eq_nil_iff.mpr
      intro t ht
      simp [h t ht]
    simp [maxTermExp, hf]

theorem alignExp_term (b : PreparedBlock) (t : UnnormalizedProduct) (ht : t ∈ b.terms)
    (hnz : t.significand ≠ 0) :
    ∃ alignExp, b.alignExp = some alignExp ∧ t.unnormalizedExp ≤ alignExp := by
  obtain ⟨e, he, hle⟩ := maxTermExp_term b.terms t ht hnz
  cases hf : b.model.eAlignMin with
  | none => exact ⟨e, by simp [PreparedBlock.alignExp, Model.applyEAlignMin, he, hf], hle⟩
  | some f => exact ⟨max e f, by simp [PreparedBlock.alignExp, Model.applyEAlignMin, he, hf], by omega⟩

theorem aligned_term_coefficient_bound (t : UnnormalizedProduct) (alignExp : ℤ) (F : ℕ)
    (ht : t.Bounded) (he : t.unnormalizedExp ≤ alignExp) :
    (truncBits t.value (alignExp - F)).natAbs < 2 ^ (F + 2) := by
  have hq := pow2_pos (alignExp - F)
  have hp := pow2_le_of_le he
  have hs := truncBits_abs_le t.value (alignExp - F)
  have hb : absQ t.value < 4 * pow2 alignExp := by unfold UnnormalizedProduct.Bounded at ht; grind
  have heq : ((2 ^ (F + 2) : ℕ) : ℚ) * pow2 (alignExp - F) = 4 * pow2 alignExp := by
    rw [← pow2_natCast, ← pow2_add]
    have he' : ((F + 2 : ℕ) : ℤ) + (alignExp - F) = alignExp + 2 := by omega
    rw [he', pow2_add]
    have htwo : pow2 2 = 4 := by decide
    rw [htwo, Rat.mul_comm]
  have hb' : absQ t.value / pow2 (alignExp - F) < ((2 ^ (F + 2) : ℕ) : ℚ) := by
    apply (Rat.div_lt_iff hq).mpr
    rwa [heq]
  apply Rat.natCast_lt_natCast.mp
  grind

theorem prepareProducts_bounds (p : Model) (ps : List (p.Word × p.Word))
    (qs : List (Decoded × Decoded)) (h : prepareProducts p ps = some qs) :
    qs.length = ps.length ∧ ∀ q ∈ qs, q.1.Bounded ∧ q.2.Bounded := by
  induction ps generalizing qs with
  | nil =>
    simp [prepareProducts] at h
    subst qs
    simp
  | cons pair ps ih =>
    rcases pair with ⟨a, b⟩
    cases ha : p.decode a with
    | none => simp [prepareProducts, List.mapM_cons, ha] at h
    | some da =>
      cases hb : p.decode b with
      | none => simp [prepareProducts, List.mapM_cons, ha, hb] at h
      | some db =>
        cases ht : prepareProducts p ps with
        | none =>
          simp [prepareProducts] at ht
          simp [prepareProducts, List.mapM_cons, ha, hb, ht] at h
        | some ds =>
          have hcons : qs = (da, db) :: ds := by
            have ht' := ht
            simp [prepareProducts] at ht'
            simpa [prepareProducts, List.mapM_cons, ha, hb, ht'] using h.symm
          subst qs
          have hi := ih ds ht
          constructor
          · simpa using hi.1
          · intro q hq
            simp only [List.mem_cons] at hq
            rcases hq with hq | hq
            · subst q
              exact ⟨classifyNat_bounded p.input a.toNat da ha,
                classifyNat_bounded p.input b.toNat db hb⟩
            · exact hi.2 q hq

theorem prepare_terms_bounded {p : Model} {x : BlockInput p} {b : PreparedBlock}
    (h : prepare x = some b) :
    b.terms.length = x.products.length + 1 ∧ ∀ t ∈ b.terms, t.Bounded := by
  unfold prepare at h
  cases hc : decode32 x.c with
  | none => simp [hc] at h
  | some c =>
    cases hp : prepareProducts p x.products with
    | none => simp [hc, hp] at h
    | some ps =>
      simp [hc, hp] at h
      subst b
      have hps := prepareProducts_bounds p x.products ps hp
      constructor
      · simpa [PreparedBlock.terms] using hps.1
      · intro t ht
        simp only [PreparedBlock.terms, List.mem_cons, List.mem_map] at ht
        rcases ht with ht | ⟨q, hq, ht⟩
        · subst t
          exact c_term_bounded c (classifyNat_bounded fp32 x.c.toNat c hc)
        · subst t
          exact unnormalizedMul_bounded q.1 q.2 (hps.2 q hq).1 (hps.2 q hq).2

theorem prepared_coefficient_bound (b : PreparedBlock) (F : ℕ)
    (hF : b.model.alignFracBits = F) (ht : ∀ t ∈ b.terms, t.Bounded) :
    ∀ z ∈ b.alignedBits, z.natAbs < 2 ^ (F + 2) := by
  intro z hz
  obtain ⟨t, hmem, rfl⟩ := List.mem_map.mp hz
  by_cases hzero : t.significand = 0
  · simp [UnnormalizedProduct.value, hzero, truncBits, Rat.div_def]
    exact Nat.two_pow_pos _
  · obtain ⟨alignExp, he, hle⟩ := alignExp_term b t hmem hzero
    have hq : b.alignGridExponent = alignExp - F := by
      simp [PreparedBlock.alignGridExponent, he, hF]
    rw [hq]
    exact aligned_term_coefficient_bound t alignExp F (ht t hmem) hle

/-- Capacity follows from finite decoded inputs and shape, before any output-range check. -/
theorem prepare_coefficient_capacity {p : Model} {x : BlockInput p} {b : PreparedBlock}
    (hp : prepare x = some b) (hshape : x.products.length = p.nfma) (F carryBits : ℕ)
    (hF : p.alignFracBits = F) (hcount : p.nfma + 1 ≤ 2 ^ carryBits) :
    magnitudeSum b.alignedBits < 2 ^ ((F + 2 + carryBits + 1) - 1) := by
  have hb := prepare_terms_bounded hp
  have hprof := prepare_model hp
  apply coefficient_width_sufficient
  · exact prepared_coefficient_bound b F (by rw [hprof, hF]) hb.2
  · simpa [PreparedBlock.alignedBits, hb.1, hshape] using hcount

/-- Width derived from decoded inputs, with c included in the member count. -/
theorem evalBlock_coefficient_capacity {p : Model} {x : BlockInput p} {t : BlockTrace}
    (h : evalBlock x = .ok t) (F carryBits : ℕ)
    (hF : p.alignFracBits = F) (hcount : p.nfma + 1 ≤ 2 ^ carryBits) :
    magnitudeSum t.block.alignedBits < 2 ^ ((F + 2 + carryBits + 1) - 1) := by
  have hshape : x.products.length = p.nfma := by
    unfold evalBlock at h
    split at h <;> simp_all
  exact prepare_coefficient_capacity (evalBlock_prepared h) hshape F carryBits hF hcount

theorem evalBlock_machineAccumulator {p : Model} {x : BlockInput p} {t : BlockTrace}
    (h : evalBlock x = .ok t) (F carryBits : ℕ)
    (hF : p.alignFracBits = F) (hcount : p.nfma + 1 ≤ 2 ^ carryBits) :
    t.block.machineAccumulator (F + 2 + carryBits + 1) = t.block.accumulator :=
  machineAccumulator_eq _ _ (by omega) (evalBlock_coefficient_capacity h F carryBits hF hcount)

/-- Every prefix of a successful encoded invocation is safe at the derived width. -/
theorem evalBlock_machinePrefix {p : Model} {x : BlockInput p} {t : BlockTrace}
    (h : evalBlock x = .ok t) (F carryBits : ℕ)
    (hF : p.alignFracBits = F) (hcount : p.nfma + 1 ≤ 2 ^ carryBits)
    (xs ys : List ℤ) (hsplit : t.block.alignedBits = xs ++ ys) :
    (machineAccumulate (F + 2 + carryBits + 1) 0 xs).toInt = sumZ xs := by
  apply machineAccumulate_prefix_exact _ xs ys (by omega)
  rw [← hsplit]
  exact evalBlock_coefficient_capacity h F carryBits hF hcount

/-- The conservative V100 bound is 29 signed bits: 25 magnitude bits per term, three carry bits for five terms, and one sign bit. -/
theorem evalV100_machineAccumulator {x : BlockInput v100F16F32} {t : BlockTrace}
    (h : evalV100 x = .ok t) : t.block.machineAccumulator 29 = t.block.accumulator :=
  evalBlock_machineAccumulator h 23 3 rfl (by decide)

private theorem fold_max_upper (es : List ℤ) (acc : Option ℤ) (upper : ℤ)
    (ha : ∀ e ∈ acc, e ≤ upper) (hs : ∀ e ∈ es, e ≤ upper) :
    ∀ e ∈ es.foldl (fun acc x => some (match acc with
      | none => x | some a => max a x)) acc, e ≤ upper := by
  induction es generalizing acc with
  | nil => exact ha
  | cons x xs ih =>
    apply ih
    · intro e he
      have hx := hs x (by simp)
      cases acc with
      | none => simp at he; omega
      | some a =>
        have hb := ha a (by simp)
        simp at he
        omega
    · intro e he
      exact hs e (by simp [he])

theorem maxTermExp_upper (ts : List UnnormalizedProduct) (upper : ℤ)
    (h : ∀ t ∈ ts, t.significand ≠ 0 → t.unnormalizedExp ≤ upper) :
    ∀ e ∈ maxTermExp ts, e ≤ upper := by
  apply fold_max_upper
  · simp
  · intro e he
    obtain ⟨t, ht, he⟩ := List.mem_filterMap.mp he
    by_cases hz : t.significand = 0
    · simp [hz] at he
    · simp [hz] at he
      subst e
      exact h t ht hz

theorem alignExp_upper (b : PreparedBlock) (upper : ℤ)
    (hf : ∀ f ∈ b.model.eAlignMin, f ≤ upper)
    (ht : ∀ t ∈ b.terms, t.significand ≠ 0 → t.unnormalizedExp ≤ upper) :
    ∀ e ∈ b.alignExp, e ≤ upper := by
  have hu := maxTermExp_upper b.terms upper ht
  intro alignExp he
  unfold PreparedBlock.alignExp Model.applyEAlignMin at he
  cases hs : maxTermExp b.terms with
  | none => simp [hs] at he
  | some e =>
    have hemax := hu e (by simp [hs])
    cases heAlignMin : b.model.eAlignMin with
    | none => simp [hs, heAlignMin] at he; omega
    | some f =>
      have hf' := hf f (by simp [heAlignMin])
      simp [hs, heAlignMin] at he
      omega

end TensorCore
