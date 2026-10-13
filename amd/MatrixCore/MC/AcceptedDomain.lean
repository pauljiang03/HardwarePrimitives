import MatrixCore.MC.Eval

/-! # Accepted domain of a block

A block evaluates exactly when `a` and `b` have `N_FMA` entries, every operand is finite, the
accumulation stage succeeds, and `S_acc` lies below the binary32 overflow threshold. The output
is then `fl{S_acc}`. -/

namespace MatrixCore

theorem fl32_false (x : ℚ) : fl32 false x = rne32 x := by
  unfold fl32; cases rne32 x <;> simp

theorem fl32_isSome_iff (ftz : Bool) (x : ℚ) :
    (fl32 ftz x).isSome ↔ absQ x < overflowThreshold32 := by
  rw [← rne32_isSome_iff]; unfold fl32; cases rne32 x <;> simp

/-- Every accepted evaluation decomposes into its stages. -/
theorem evalBlock_ok {P : Model} {x : BlockInput P} {t : BlockTrace P}
    (h : evalBlock x = .ok t) :
    x.a.length = P.nfma ∧ x.b.length = P.nfma ∧ prepare x = some t.prepared ∧
      accumulate P t.prepared = .ok t.sAcc ∧ fl32 (!P.subnormals) t.sAcc = some t.d := by
  unfold evalBlock at h
  split at h
  · simp at h
  · rename_i hlen
    split at h
    · simp at h
    · rename_i px hpx
      split at h
      · simp at h
      · rename_i s hs
        split at h
        · simp at h
        · rename_i d hd
          simp only [Except.ok.injEq] at h
          subst h
          exact ⟨by omega, by omega, hpx, hs, hd⟩

/-- Exact accepted domain of `evalBlock`. -/
theorem evalBlock_success_iff {P : Model} (x : BlockInput P) :
    (∃ t, evalBlock x = .ok t) ↔
      x.a.length = P.nfma ∧ x.b.length = P.nfma ∧
        ∃ px s, prepare x = some px ∧ accumulate P px = .ok s ∧ absQ s < overflowThreshold32 := by
  constructor
  · rintro ⟨t, ht⟩
    obtain ⟨ha, hb, hp, hs, hd⟩ := evalBlock_ok ht
    refine ⟨ha, hb, t.prepared, t.sAcc, hp, hs, ?_⟩
    rw [← fl32_isSome_iff (!P.subnormals), hd]; rfl
  · rintro ⟨ha, hb, px, s, hp, hs, hr⟩
    have := (fl32_isSome_iff (!P.subnormals) s).mpr hr
    obtain ⟨d, hd⟩ := Option.isSome_iff_exists.mp this
    refine ⟨⟨px, s, d⟩, ?_⟩
    unfold evalBlock
    rw [if_neg (by omega), hp]
    simp only [hs, hd]

/-- The output of an accepted block on a profile with subnormals is the nearest binary32 value to
`S_acc`, ties to even. -/
theorem evalBlock_nearestEven {P : Model} {x : BlockInput P} {t : BlockTrace P}
    (h : evalBlock x = .ok t) (hs : P.subnormals = true) : NearestEven32 t.sAcc t.d := by
  obtain ⟨_, _, _, _, hd⟩ := evalBlock_ok h
  rw [hs] at hd
  exact rne32_nearestEven (by simpa [fl32_false] using hd)

end MatrixCore
