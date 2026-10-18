import MatrixCore.MC.PairWiseSum
import MatrixCore.MC.LateAccumulation
import MatrixCore.MC.CorrectRounding

/-! # Error of the block output

The distance of `d` from the exact `Σ p_ℓ + c`, for each configuration. -/

namespace MatrixCore

theorem absQ_sub_le (a b c : ℚ) : absQ (a - c) ≤ absQ (a - b) + absQ (b - c) := by
  have := absQ_add_le (a - b) (b - c)
  rwa [show a - b + (b - c) = a - c by grind] at this

theorem sumQ_map_mono {l : List α} {f g : α → ℚ} (h : ∀ a ∈ l, f a ≤ g a) :
    sumQ (l.map f) ≤ sumQ (l.map g) := by
  induction l with
  | nil => exact Rat.le_refl
  | cons a l ih =>
    simp only [List.map_cons, sumQ]
    have h1 := h a (by simp)
    have h2 := ih (fun b hb => h b (by simp [hb]))
    grind

/-! ## One `fl{·}` -/

/-- Error of one `fl{·}`: half an ulp, and `2^-126` more when subnormal results are flushed. -/
def flBound (ftz : Bool) (x : ℚ) : ℚ := halfUlp32 x + if ftz then pow2 (-126) else 0

theorem flBound_nonneg (ftz : Bool) (x : ℚ) : 0 ≤ flBound ftz x := by
  have := halfUlp32_nonneg x
  have := pow2_pos (-126)
  unfold flBound; split <;> grind

theorem flValue_error {ftz : Bool} {x v : ℚ} (h : flValue ftz x = some v) :
    absQ (x - v) ≤ flBound ftz x := by
  have h1 := rneValue_error x
  have hp := pow2_pos (-126)
  cases ftz with
  | false =>
    rw [flValue_false h]; simp only [flBound, Bool.false_eq_true, ↓reduceIte]; grind
  | true =>
    simp only [flBound, ↓reduceIte]
    rcases flValue_true h with ⟨rfl, _⟩ | ⟨rfl, _, hsmall⟩
    · grind
    · have h2 := absQ_add_le (x - rneValue x) (rneValue x)
      rw [show x - rneValue x + rneValue x = x - 0 by grind] at h2
      grind

theorem fl32_value {ftz : Bool} {x : ℚ} {w : F32} (h : fl32 ftz x = some w) :
    value32 w = some (wordValue w) := by
  unfold fl32 at h
  cases hr : rne32 x with
  | none => rw [hr] at h; simp at h
  | some w₀ =>
    rw [hr] at h
    simp only [Option.some.injEq] at h
    subst h
    split
    · simp [wordValue, value32_signedZero32]
    · simp [wordValue, rne32_value hr]

theorem fl32_error {ftz : Bool} {x : ℚ} {w : F32} (h : fl32 ftz x = some w) :
    absQ (x - wordValue w) ≤ flBound ftz x := by
  apply flValue_error
  unfold flValue
  rw [h]
  exact fl32_value h

/-- The final `fl{S_acc}` of every block. -/
theorem evalBlock_output_error {P : Model} {x : BlockInput P} {t : BlockTrace P}
    (h : evalBlock x = .ok t) : absQ (t.sAcc - wordValue t.d) ≤ flBound (!P.subnormals) t.sAcc :=
  fl32_error (evalBlock_ok h).2.2.2.2

/-! ## SFMA and CDNA 1 -/

theorem correctRounding_error {P : Model} (hacc : P.accumulation = .correctRounding)
    (hov : P.productOverflow = false) (hs : P.subnormals = true)
    {x : BlockInput P} {t : BlockTrace P} (h : evalBlock x = .ok t) :
    absQ (t.prepared.exact - wordValue t.d) ≤ halfUlp32 t.prepared.exact := by
  have he := (correctRounding_nearestEven hacc hov hs h).1
  have := evalBlock_output_error h
  rw [hs, he] at this
  simp only [flBound, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at this
  rwa [Rat.add_zero] at this

/-! ## CDNA 2 -/

/-- Error bound of a pairwise group sum: one `flBound` per partial sum, at the computed operands. -/
def pairwiseGroupSumBound (ftz : Bool) : ℕ → List ℚ → ℚ
  | _, [] => 0
  | _, [_] => 0
  | 0, _ => 0
  | depth + 1, xs =>
    match pairwiseGroupSum ftz depth (xs.take (xs.length / 2)),
        pairwiseGroupSum ftz depth (xs.drop (xs.length / 2)) with
    | some u, some v => pairwiseGroupSumBound ftz depth (xs.take (xs.length / 2)) +
        pairwiseGroupSumBound ftz depth (xs.drop (xs.length / 2)) + flBound ftz (u + v)
    | _, _ => 0

theorem sumQ_take_drop (xs : List ℚ) (n : ℕ) : sumQ (xs.take n) + sumQ (xs.drop n) = sumQ xs := by
  rw [← sumQ_append, List.take_append_drop]

theorem pairwiseGroupSum_error (ftz : Bool) : ∀ (depth : ℕ) (xs : List ℚ) (t : ℚ),
    pairwiseGroupSum ftz depth xs = some t → absQ (sumQ xs - t) ≤ pairwiseGroupSumBound ftz depth xs
  | _, [], t, h => by
    simp only [pairwiseGroupSum, Option.some.injEq] at h; subst h
    simp only [sumQ, pairwiseGroupSumBound]; decide +kernel
  | _, [x], t, h => by
    simp only [pairwiseGroupSum, Option.some.injEq] at h; subst h
    simp only [sumQ, pairwiseGroupSumBound]
    rw [show x + 0 - x = 0 by grind]; decide +kernel
  | 0, _ :: _ :: _, t, h => by simp [pairwiseGroupSum] at h
  | depth + 1, x :: y :: rest, t, h => by
    generalize hxs : x :: y :: rest = xs at h
    have hb : pairwiseGroupSumBound ftz (depth + 1) xs =
        match pairwiseGroupSum ftz depth (xs.take (xs.length / 2)),
            pairwiseGroupSum ftz depth (xs.drop (xs.length / 2)) with
        | some u, some v => pairwiseGroupSumBound ftz depth (xs.take (xs.length / 2)) +
            pairwiseGroupSumBound ftz depth (xs.drop (xs.length / 2)) + flBound ftz (u + v)
        | _, _ => 0 := by subst hxs; rfl
    have ht : pairwiseGroupSum ftz (depth + 1) xs = (do
        let u ← pairwiseGroupSum ftz depth (xs.take (xs.length / 2))
        let v ← pairwiseGroupSum ftz depth (xs.drop (xs.length / 2))
        flValue ftz (u + v)) := by subst hxs; rfl
    rw [hb]
    rw [ht] at h
    cases hu : pairwiseGroupSum ftz depth (xs.take (xs.length / 2)) with
    | none => rw [hu] at h; simp at h
    | some u =>
      cases hv : pairwiseGroupSum ftz depth (xs.drop (xs.length / 2)) with
      | none => rw [hu, hv] at h; simp at h
      | some v =>
        rw [hu, hv] at h
        change flValue ftz (u + v) = some t at h
        have e1 := pairwiseGroupSum_error ftz depth _ u hu
        have e2 := pairwiseGroupSum_error ftz depth _ v hv
        have e3 := flValue_error h
        have hs := sumQ_take_drop xs (xs.length / 2)
        have t1 := absQ_add_le (sumQ (xs.take (xs.length / 2)) - u)
          (sumQ (xs.drop (xs.length / 2)) - v)
        have t2 := absQ_add_le (sumQ (xs.take (xs.length / 2)) - u +
          (sumQ (xs.drop (xs.length / 2)) - v)) (u + v - t)
        rw [show sumQ (xs.take (xs.length / 2)) - u + (sumQ (xs.drop (xs.length / 2)) - v) +
          (u + v - t) = sumQ xs - t by grind] at t2
        grind

theorem mapM_flValue_error (ftz : Bool) : ∀ (l : List Unpacked) (ps : List ℚ),
    l.mapM (fun p => flValue ftz p.value) = some ps →
      absQ (sumQ (l.map Unpacked.value) - sumQ ps) ≤ sumQ (l.map fun p => flBound ftz p.value)
  | [], ps, h => by
    simp at h; subst h; simp only [List.map_nil, sumQ]; decide +kernel
  | p :: l, ps, h => by
    simp only [List.mapM_cons] at h
    cases hp : flValue ftz p.value with
    | none => rw [hp] at h; simp at h
    | some q =>
      cases hl : l.mapM (fun p => flValue ftz p.value) with
      | none => rw [hp, hl] at h; simp at h
      | some qs =>
        rw [hp, hl] at h
        simp at h
        subst h
        have e1 := flValue_error hp
        have e2 := mapM_flValue_error ftz l qs hl
        simp only [List.map_cons, sumQ]
        have := absQ_add_le (p.value - q) (sumQ (l.map Unpacked.value) - sumQ qs)
        rw [show p.value - q + (sumQ (l.map Unpacked.value) - sumQ qs) =
          p.value + sumQ (l.map Unpacked.value) - (q + sumQ qs) by grind] at this
        grind

/-- CDNA 2 error bound: input flushing, product conversion and the pairwise sum. -/
def pairwiseBound (P : Model) (x : Prepared) : ℚ :=
  let x' := if P.subnormals then x else x.flushed
  absQ (x.exact - x'.exact) + sumQ (x'.p.map fun p => flBound (!P.subnormals) p.value) +
    match x'.p.mapM fun p => flValue (!P.subnormals) p.value with
    | some ps => pairwiseGroupSumBound (!P.subnormals) ps.length ps
    | none => 0

theorem pairwiseSum_error {P : Model} {x : Prepared} {s : ℚ} (h : pairwiseSum P x = some s) :
    absQ (x.exact - s) ≤ pairwiseBound P x := by
  unfold pairwiseSum at h
  unfold pairwiseBound
  dsimp only at h ⊢
  generalize (if P.subnormals then x else x.flushed) = x' at h ⊢
  generalize (!P.subnormals) = ftz at h ⊢
  cases hm : x'.p.mapM fun p => flValue ftz p.value with
  | none => rw [hm] at h; simp at h
  | some ps =>
    rw [hm] at h
    cases ht : pairwiseGroupSum ftz ps.length ps with
    | none => simp [ht] at h
    | some t =>
      change (pairwiseGroupSum ftz ps.length ps).bind (fun t => some (x'.c.value + t)) = some s at h
      rw [ht] at h
      simp only [Option.bind_some, Option.some.injEq] at h
      subst h
      have e1 := mapM_flValue_error ftz x'.p ps hm
      have e2 := pairwiseGroupSum_error ftz ps.length ps t ht
      have hx' : x'.exact = sumQ (x'.p.map Unpacked.value) + x'.c.value := rfl
      have t1 := absQ_sub_le x.exact x'.exact (x'.c.value + t)
      have t2 := absQ_add_le (sumQ (x'.p.map Unpacked.value) - sumQ ps) (sumQ ps - t)
      rw [show x'.exact - (x'.c.value + t) =
        sumQ (x'.p.map Unpacked.value) - sumQ ps + (sumQ ps - t) by grind] at t1
      simp only
      grind

theorem accumulate_pairwise {P : Model} (hacc : P.accumulation = .pairWiseSum) {x : Prepared}
    {s : ℚ} (h : accumulate P x = .ok s) : pairwiseSum P x = some s := by
  unfold accumulate at h
  split at h
  · simp at h
  · rw [hacc] at h
    simp only at h
    cases hp : pairwiseSum P x with
    | none => rw [hp] at h; simp at h
    | some s' => rw [hp] at h; simp only [Except.ok.injEq] at h; rw [h]

theorem pairwise_error {P : Model} (hacc : P.accumulation = .pairWiseSum)
    {x : BlockInput P} {t : BlockTrace P} (h : evalBlock x = .ok t) :
    absQ (t.prepared.exact - wordValue t.d) ≤
      pairwiseBound P t.prepared + flBound (!P.subnormals) t.sAcc := by
  have e1 := pairwiseSum_error (accumulate_pairwise hacc (evalBlock_ok h).2.2.2.1)
  have e2 := evalBlock_output_error h
  have := absQ_sub_le t.prepared.exact t.sAcc (wordValue t.d)
  grind

/-! ## CDNA 3 -/

/-- Error bound of `S_acc` in Algorithms 1 and 2, by branch. -/
def alignedBound (P : Model) (x : Prepared) : ℚ :=
  let s := productSum P x.p
  let F : ℕ := 23 + P.padding
  let n : ℚ := x.p.length + 2
  match s.1, cExp P x.c with
  | some e, some eC =>
    if eC ≤ e then n * pow2 (e - F) + pow2 (e - P.late.cMantissaBits)
    else n * pow2 (e - F) + pow2 (eC - P.late.sumMantissaBits) +
      pow2 (normExp (absQ (rdGrid s.2 (eC - P.late.sumMantissaBits) + x.c.value)) - P.late.accMantissaBits)
  | none, some eC => pow2 (eC - P.late.sumMantissaBits) +
      pow2 (normExp (absQ (rdGrid s.2 (eC - P.late.sumMantissaBits) + x.c.value)) - P.late.accMantissaBits)
  | some e, none => n * pow2 (e - F)
  | none, none => 0

theorem alignedAccumulation_abs_error (P : Model) (x : Prepared)
    (hcut : ∀ n, P.late.cCutoff = some n → P.late.cMantissaBits ≤ n)
    (hc : ∀ eC, cExp P x.c = some eC → absQ x.c.value < pow2 (eC + 1))
    (hcz : P.cZeroExp ≠ none) :
    absQ (x.exact - alignedAccumulation P x) ≤ alignedBound P x := by
  obtain ⟨h1, h2, h3, h4⟩ := alignedAccumulation_error P x hcut hc
  have hn : (0 : ℚ) ≤ (x.p.length : ℚ) + 2 := by
    have : (0 : ℚ) ≤ (x.p.length : ℚ) := by exact_mod_cast Nat.zero_le _
    grind
  unfold alignedBound
  cases hce : cExp P x.c with
  | none =>
    unfold cExp at hce
    split at hce
    · exact absurd hce hcz
    · simp at hce
  | some eC =>
    cases hs : (productSum P x.p).1 with
    | none =>
      obtain ⟨l, r⟩ := h4 eC hs hce
      simp only [hs]
      rw [absQ_le_iff]
      have := pow2_pos (eC - P.late.sumMantissaBits)
      constructor <;> grind
    | some e =>
      simp only [hs]
      by_cases hle : eC ≤ e
      · simp only [hle, ↓reduceIte]
        exact Rat.le_of_lt (h2 e eC hs hce hle)
      · simp only [hle, ↓reduceIte]
        obtain ⟨l, r⟩ := h3 e eC hs hce (by omega)
        rw [absQ_le_iff]
        have := pow2_pos (eC - P.late.sumMantissaBits)
        have := pow2_pos (normExp (absQ (rdGrid (productSum P x.p).2 (eC - P.late.sumMantissaBits) +
          x.c.value)) - P.late.accMantissaBits)
        have := Rat.mul_nonneg hn (Rat.le_of_lt (pow2_pos (e - ((23 + P.padding : ℕ) : ℤ))))
        constructor <;> grind

theorem accumulate_aligned {P : Model}
    (hacc : P.accumulation = .globalAlignment ∨ P.accumulation = .oddEvenGrouping) {x : Prepared}
    {s : ℚ} (h : accumulate P x = .ok s) : s = alignedAccumulation P x := by
  unfold accumulate at h
  split at h
  · simp at h
  · rcases hacc with hacc | hacc <;> rw [hacc] at h <;> simp only [Except.ok.injEq] at h <;>
      exact h.symm

theorem aligned_error {P : Model}
    (hacc : P.accumulation = .globalAlignment ∨ P.accumulation = .oddEvenGrouping)
    (hcut : ∀ n, P.late.cCutoff = some n → P.late.cMantissaBits ≤ n) (hcz : P.cZeroExp ≠ none)
    {x : BlockInput P} {t : BlockTrace P} (h : evalBlock x = .ok t) :
    absQ (t.prepared.exact - wordValue t.d) ≤
      alignedBound P t.prepared + flBound (!P.subnormals) t.sAcc := by
  have hp := (evalBlock_ok h).2.2.1
  have hs := accumulate_aligned hacc (evalBlock_ok h).2.2.2.1
  have e1 := alignedAccumulation_abs_error P t.prepared hcut (prepare_cExp_bound hp) hcz
  rw [← hs] at e1
  have e2 := evalBlock_output_error h
  have := absQ_sub_le t.prepared.exact t.sAcc (wordValue t.d)
  grind

end MatrixCore
