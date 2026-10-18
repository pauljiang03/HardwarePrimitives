import MatrixCore.EFT.Encoded

/-! # CDNA 2: the overlap is the low parts plus the rounding errors

CDNA 2 does not align its products, so the cut-off is `D`'s last bit. The overlap is then the low
parts plus every rounding error of the Matrix Core, less what flushing to zero removed. -/

namespace MatrixCore

/-- The rounding errors `fl{u + v} − (u + v)` of the pairwise additions of a group. -/
def pairwiseErrors (ftz : Bool) : ℕ → List ℚ → List ℚ
  | _, [] => []
  | _, [_] => []
  | 0, _ => []
  | depth + 1, xs =>
    match pairwiseGroupSum ftz depth (xs.take (xs.length / 2)),
        pairwiseGroupSum ftz depth (xs.drop (xs.length / 2)) with
    | some u, some v =>
      pairwiseErrors ftz depth (xs.take (xs.length / 2)) ++
        pairwiseErrors ftz depth (xs.drop (xs.length / 2)) ++
        ((flValue ftz (u + v)).map fun w => w - (u + v)).toList
    | _, _ => []

theorem pairwiseGroupSum_eq_errors (ftz : Bool) : ∀ (depth : ℕ) (xs : List ℚ) (t : ℚ),
    pairwiseGroupSum ftz depth xs = some t → t = sumQ xs + sumQ (pairwiseErrors ftz depth xs)
  | _, [], t, h => by
    simp only [pairwiseGroupSum, Option.some.injEq] at h; subst h
    simp only [sumQ, pairwiseErrors]; grind
  | _, [x], t, h => by
    simp only [pairwiseGroupSum, Option.some.injEq] at h; subst h
    simp only [sumQ, pairwiseErrors]; grind
  | 0, _ :: _ :: _, t, h => by simp [pairwiseGroupSum] at h
  | depth + 1, x :: y :: rest, t, h => by
    generalize hxs : x :: y :: rest = xs at h
    have hb : pairwiseErrors ftz (depth + 1) xs =
        match pairwiseGroupSum ftz depth (xs.take (xs.length / 2)),
            pairwiseGroupSum ftz depth (xs.drop (xs.length / 2)) with
        | some u, some v =>
          pairwiseErrors ftz depth (xs.take (xs.length / 2)) ++
            pairwiseErrors ftz depth (xs.drop (xs.length / 2)) ++
            ((flValue ftz (u + v)).map fun w => w - (u + v)).toList
        | _, _ => [] := by subst hxs; rfl
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
        have e1 := pairwiseGroupSum_eq_errors ftz depth _ u hu
        have e2 := pairwiseGroupSum_eq_errors ftz depth _ v hv
        have hs := sumQ_take_drop xs (xs.length / 2)
        simp only [h, Option.map_some, Option.toList_some, sumQ_append, sumQ]
        grind

/-- The rounding errors before the final `fl{·}`: each product's conversion, then each addition. -/
def pairwiseRoundingErrors (P : Model) (px : Prepared) : List ℚ :=
  let x' := if P.subnormals then px else px.flushed
  match x'.p.mapM fun p => flValue (!P.subnormals) p.value with
  | some qs => List.zipWith (fun q p => q - p.value) qs x'.p ++
      pairwiseErrors (!P.subnormals) qs.length qs
  | none => []

/-- What flushing subnormal operands to zero removes from the exact sum. -/
def flushLoss (P : Model) (px : Prepared) : ℚ :=
  px.exact - (if P.subnormals then px else px.flushed).exact

theorem sumQ_zipWith_sub : ∀ (qs : List ℚ) (ps : List Unpacked), qs.length = ps.length →
    sumQ (List.zipWith (fun q p => q - p.value) qs ps) = sumQ qs - sumQ (ps.map Unpacked.value)
  | [], [], _ => by simp [sumQ]; grind
  | q :: qs, p :: ps, h => by
    simp only [List.zipWith_cons_cons, List.map_cons, sumQ]
    rw [sumQ_zipWith_sub qs ps (by simpa using h)]
    grind
  | [], _ :: _, h => by simp at h
  | _ :: _, [], h => by simp at h

/-- `S_acc = S − flush loss + Σ rounding errors` on a pairwise-sum block. -/
theorem pairwiseSum_eq_errors {P : Model} {px : Prepared} {s : ℚ} (h : pairwiseSum P px = some s) :
    s = px.exact - flushLoss P px + sumQ (pairwiseRoundingErrors P px) := by
  obtain ⟨qs, u, hm, hu, hs⟩ := pairwiseSum_stages h
  unfold flushLoss pairwiseRoundingErrors
  simp only
  generalize (if P.subnormals then px else px.flushed) = x' at hm hs ⊢
  rw [hm]
  simp only [sumQ_append]
  rw [sumQ_zipWith_sub qs x'.p (mapM_length_option hm), hs,
    pairwiseGroupSum_eq_errors (!P.subnormals) qs.length qs u hu]
  unfold Prepared.exact
  grind

/-- What `D` buys on CDNA 2: the overlap is the low parts plus the Matrix Core's rounding errors. -/
structure PairwiseOverlap {P : Model} (t : BlockTrace P) : Prop where
  cutoff : t.split.q = ulpExp32 (wordValue t.d)
  onGrid : OnGrid (t.split.overlap (wordValue t.d)) t.split.q
  overlap : t.split.overlap (wordValue t.d) = sumQ t.split.lows + (wordValue t.d - t.sAcc) +
    sumQ (pairwiseRoundingErrors P t.prepared) - flushLoss P t.prepared
  overlap_le : absQ (t.split.overlap (wordValue t.d)) ≤ ((P.nfma : ℚ) + 1) * pow2 t.split.q +
    pairwiseBound P t.prepared + flBound (!P.subnormals) t.sAcc

/-- What `D` buys on CDNA 2, for every block of a pairwise-sum model. -/
theorem pairwise_eft {P : Model} (hacc : P.accumulation = .pairWiseSum) {x : BlockInput P}
    {t : BlockTrace P} (h : evalBlock x = .ok t) : PairwiseOverlap t := by
  obtain ⟨ha, hb, hp, hacc', hfl⟩ := evalBlock_ok h
  have hsum := pairwiseSum_eq_errors (accumulate_pairwise hacc hacc')
  have hq : t.split.q = ulpExp32 (wordValue t.d) := by
    show eftCutoff P t.prepared (wordValue t.d) = _
    unfold eftCutoff; rw [hacc]
  obtain ⟨hov, hlow⟩ := overlap_eq_error_add_lows P t.prepared (wordValue t.d)
  have hlen : t.prepared.p.length = P.nfma := by
    obtain ⟨la, lb⟩ := prepare_lengths hp
    rw [Prepared.p_length, la, lb, ha, hb, Nat.min_self]
  have herr := pairwise_error hacc h
  refine ⟨hq, ?_, ?_, ?_⟩
  · rw [hq]; exact overlap_onGrid P t.prepared (fl32_value hfl)
  · unfold BlockTrace.split; rw [hov]; grind
  · unfold BlockTrace.split
    rw [hov]
    rw [hlen] at hlow
    have t1 := absQ_add_le (wordValue t.d - t.prepared.exact)
      (sumQ (eftSplit P t.prepared (wordValue t.d)).lows)
    rw [absQ_sub_comm] at t1
    have : ((P.nfma + 1 : ℕ) : ℚ) = (P.nfma : ℚ) + 1 := by push_cast; rfl
    rw [this] at hlow
    rw [show (eftSplit P t.prepared (wordValue t.d)).q = eftCutoff P t.prepared (wordValue t.d)
      from rfl]
    grind

theorem cdna2F16_eft {x : BlockInput cdna2F16} {t : BlockTrace cdna2F16}
    (h : evalBlock x = .ok t) : PairwiseOverlap t := pairwise_eft rfl h

theorem cdna2BF16_eft {x : BlockInput cdna2BF16} {t : BlockTrace cdna2BF16}
    (h : evalBlock x = .ok t) : PairwiseOverlap t := pairwise_eft rfl h

theorem cdna2BF16_1k_eft {x : BlockInput cdna2BF16_1k} {t : BlockTrace cdna2BF16_1k}
    (h : evalBlock x = .ok t) : PairwiseOverlap t := pairwise_eft rfl h

end MatrixCore
