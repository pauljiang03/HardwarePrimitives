import MatrixCore.MC.Special
import MatrixCore.MC.PairWiseSum
import MatrixCore.MC.AcceptedDomain
import MatrixCore.MC.Prepared

/-! # Agreement of the special-value semantics with the finite model -/

namespace MatrixCore

namespace XVal

theorem toFin_add (a b : XVal) : (add a b).toFin = a.toFin.bind fun p => b.toFin.map (p + ·) := by
  cases a <;> cases b <;> simp only [add] <;> (try split) <;> rfl

theorem toFin_fl (ftz : Bool) (v : XVal) : (fl ftz v).toFin = v.toFin.bind (flValue ftz) := by
  cases v with
  | fin q => unfold fl; cases h : flValue ftz q <;> simp [toFin, h]
  | inf s => rfl
  | nan => rfl

theorem toFin_eq_some {v : XVal} {q : ℚ} : v.toFin = some q ↔ v = .fin q := by
  cases v <;> simp [toFin]

theorem mul_fin {a b : XVal} {q : ℚ} (h : mul a b = .fin q) :
    ∃ p r, a = .fin p ∧ b = .fin r := by
  cases a <;> cases b <;> simp [mul] at h ⊢ <;> split at h <;> simp at h

end XVal

theorem pairwiseGroupSumX_toFin (ftz : Bool) : ∀ (n : ℕ) (xs : List XVal),
    (pairwiseGroupSumX ftz n xs).toFin = (xs.mapM XVal.toFin).bind (pairwiseGroupSum ftz n)
  | _, [] => by simp [pairwiseGroupSumX, pairwiseGroupSum, XVal.toFin]
  | _, [x] => by
    simp only [pairwiseGroupSumX, List.mapM_cons, List.mapM_nil]
    cases hx : x.toFin <;> simp [pairwiseGroupSum]
  | 0, a :: b :: rest => by
    simp only [pairwiseGroupSumX, XVal.toFin]
    cases h : (a :: b :: rest).mapM XVal.toFin with
    | none => rfl
    | some ys =>
      have hl := mapM_length_option h
      match ys, hl with
      | _ :: _ :: _, _ => rfl
  | n + 1, a :: b :: rest => by
    have ih := pairwiseGroupSumX_toFin ftz n
    simp only [pairwiseGroupSumX]
    rw [XVal.toFin_fl, XVal.toFin_add, ih, ih]
    generalize hxs : a :: b :: rest = xs
    have hsplit : xs = xs.take (xs.length / 2) ++ xs.drop (xs.length / 2) := (List.take_append_drop _ _).symm
    conv => rhs; rw [hsplit, mapM_append_option]
    cases h1 : (xs.take (xs.length / 2)).mapM XVal.toFin with
    | none => simp
    | some ys₁ =>
      cases h2 : (xs.drop (xs.length / 2)).mapM XVal.toFin with
      | none => simp
      | some ys₂ =>
        simp only [Option.bind_some, Option.map_some]
        have l1 := mapM_length_option h1
        have l2 := mapM_length_option h2
        have hlen : 2 ≤ xs.length := by rw [← hxs]; simp
        have hys : (ys₁ ++ ys₂).length / 2 = ys₁.length := by
          rw [List.length_append, l1, l2, List.length_take, List.length_drop]; omega
        have hge : 2 ≤ (ys₁ ++ ys₂).length := by
          rw [List.length_append, l1, l2, List.length_take, List.length_drop]; omega
        match hy : ys₁ ++ ys₂, hge with
        | y₁ :: y₂ :: ys, _ =>
          simp only [pairwiseGroupSum]
          rw [← hy, hys, List.take_left' rfl, List.drop_left' rfl]
          cases pairwiseGroupSum ftz n ys₁ <;> cases pairwiseGroupSum ftz n ys₂ <;> simp

theorem finishOutcome_finite (ftz : Bool) (X : XVal) (d : F32) :
    finishOutcome ftz X = .finite d ↔ ∃ s, X.toFin = some s ∧ fl32 ftz s = some d := by
  cases X with
  | fin s => simp [finishOutcome, XVal.toFin, roundOutcome]; split <;> simp_all
  | inf s => simp [finishOutcome, XVal.toFin]
  | nan => simp [finishOutcome, XVal.toFin]

theorem pairwiseOutcome_finite (P : Model) (x : Prepared) (d : F32) :
    pairwiseOutcome P x = .finite d ↔
      ∃ s, pairwiseSum P x = some s ∧ fl32 (!P.subnormals) s = some d := by
  have key : ∀ x' : Prepared,
      (XVal.add (.fin x'.c.value) (pairwiseGroupSumX (!P.subnormals)
        (x'.p.map fun p => XVal.fl (!P.subnormals) (.fin p.value)).length
        (x'.p.map fun p => XVal.fl (!P.subnormals) (.fin p.value)))).toFin =
      (do
        let ps ← x'.p.mapM fun p => flValue (!P.subnormals) p.value
        let t ← pairwiseGroupSum (!P.subnormals) ps.length ps
        return x'.c.value + t) := by
    intro x'
    rw [XVal.toFin_add, pairwiseGroupSumX_toFin, mapM_map_option]
    have hf : (XVal.toFin ∘ fun p : Unpacked => XVal.fl (!P.subnormals) (.fin p.value)) =
        fun p => flValue (!P.subnormals) p.value := by
      funext p
      show (XVal.fl (!P.subnormals) (.fin p.value)).toFin = _
      rw [XVal.toFin_fl]; rfl
    rw [hf, List.length_map]
    cases hq : x'.p.mapM fun p => flValue (!P.subnormals) p.value with
    | none => rfl
    | some qs =>
      show Option.map _ ((pairwiseGroupSum (!P.subnormals) x'.p.length) qs) =
        (pairwiseGroupSum (!P.subnormals) qs.length qs).bind fun t => some (x'.c.value + t)
      rw [mapM_length_option hq]
      cases pairwiseGroupSum (!P.subnormals) x'.p.length qs <;> rfl
  unfold pairwiseOutcome
  dsimp only
  rw [finishOutcome_finite, key]
  unfold pairwiseSum
  dsimp only
  exact Iff.rfl

theorem combineSpecial_ne_finite {xs : List XVal} {d : F32} : combineSpecial xs ≠ some (.finite d) := by
  unfold combineSpecial
  split <;> (try split) <;> (try split) <;> (try split) <;> simp

theorem roundOutcome_finite (ftz : Bool) (s : ℚ) (d : F32) :
    roundOutcome ftz s = .finite d ↔ fl32 ftz s = some d := by
  unfold roundOutcome; split <;> simp_all

theorem finiteOutcome_finite (P : Model) (x : Prepared) (d : F32) :
    finiteOutcome P x = .finite d ↔ ∃ s, accumulate P x = .ok s ∧ fl32 (!P.subnormals) s = some d := by
  unfold finiteOutcome accumulate
  by_cases hov : P.productOverflow && x.productOverflows
  · simp only [hov, ↓reduceIte]
    constructor
    · intro h
      cases hc : combineSpecial (x.p.map fun p =>
          if pow2 128 ≤ absQ p.value then XVal.inf (decide (p.value < 0)) else .fin p.value) with
      | none => rw [hc] at h; simp at h
      | some o => rw [hc] at h; simp at h; subst h; exact absurd hc combineSpecial_ne_finite
    · rintro ⟨s, hs, _⟩; simp at hs
  · simp only [hov, Bool.false_eq_true, ↓reduceIte]
    cases hacc : P.accumulation with
    | correctRounding => simp [roundOutcome_finite]
    | pairWiseSum =>
      simp only [pairwiseOutcome_finite]
      constructor
      · rintro ⟨s, hs, hd⟩; exact ⟨s, by simp [hs], hd⟩
      · rintro ⟨s, hs, hd⟩
        cases h : pairwiseSum P x with
        | none => rw [h] at hs; simp at hs
        | some s' => rw [h] at hs; simp at hs; subst hs; exact ⟨s', rfl, hd⟩
    | globalAlignment => simp [roundOutcome_finite]
    | oddEvenGrouping => simp [roundOutcome_finite]

theorem combineSpecial_allFin {xs : List XVal} (h : ∀ v ∈ xs, ∃ q, v = .fin q) :
    combineSpecial xs = none := by
  have hn : ∀ w : XVal, w ∈ xs → (w == .nan) = false ∧ (w == .inf false) = false ∧
      (w == .inf true) = false := by
    intro w hw
    obtain ⟨q, rfl⟩ := h w hw
    exact ⟨rfl, rfl, rfl⟩
  have h1 : xs.any (· == .nan) = false := List.any_eq_false.mpr fun w hw => by simp [(hn w hw).1]
  have h2 : xs.any (· == .inf false) = false :=
    List.any_eq_false.mpr fun w hw => by simp [(hn w hw).2.1]
  have h3 : xs.any (· == .inf true) = false :=
    List.any_eq_false.mpr fun w hw => by simp [(hn w hw).2.2]
  unfold combineSpecial
  simp [h1, h2, h3]

/-- The special-value semantics gives a finite word exactly when the finite model returns it. -/
theorem blockOutcome_finite_iff {P : Model} (x : BlockInput P) (d : F32) :
    blockOutcome x = some (.finite d) ↔ blockBits x = .ok d := by
  constructor
  · intro h
    unfold blockOutcome at h
    split at h
    · simp at h
    · rename_i hlen
      cases hpx : prepare x with
      | none =>
        rw [hpx] at h
        simp only [Option.some.injEq] at h
        cases hc : combineSpecial (.ofDatum (fp32.decode x.c) :: blockProducts x) with
        | none => rw [hc] at h; simp at h
        | some o =>
          rw [hc] at h; simp only [Option.getD_some] at h
          subst h; exact absurd hc combineSpecial_ne_finite
      | some px =>
        rw [hpx] at h
        simp only [Option.some.injEq] at h
        obtain ⟨s, hs, hd⟩ := (finiteOutcome_finite P px d).mp h
        unfold blockBits evalBlock
        rw [if_neg hlen, hpx]
        simp only [hs, hd]; rfl
  · intro h
    unfold blockBits at h
    cases ht : evalBlock x with
    | error e => rw [ht] at h; simp [Except.map] at h
    | ok t =>
      rw [ht] at h
      simp only [Except.map, Except.ok.injEq] at h
      subst h
      obtain ⟨ha, hb, hp, hs, hd⟩ := evalBlock_ok ht
      unfold blockOutcome
      rw [if_neg (by omega), hp]
      exact congrArg some ((finiteOutcome_finite P t.prepared t.d).mpr ⟨t.sAcc, hs, hd⟩)

end MatrixCore
