import MatrixCore.EFT.Encoded

/-! # CDNA 1 and the SFMA: the correction returns `D`

A correctly rounding block already outputs RNE of the exact sum, so the correction from its output
returns that output, and the overlap is the low parts plus the final rounding error. -/

namespace MatrixCore

/-- From a correctly rounding block's output, the correction returns that output. -/
theorem correctRounding_eft {P : Model} (hacc : P.accumulation = .correctRounding)
    (hov : P.productOverflow = false) (hs : P.subnormals = true) {x : BlockInput P}
    {t : BlockTrace P} (h : evalBlock x = .ok t) :
    ∃ r, mcEft x t.d = .ok r ∧ r.bits = some t.d := by
  refine ⟨_, mcEft_of_evalBlock h, ?_⟩
  obtain ⟨_, _, _, ha, hfl⟩ := evalBlock_ok h
  rw [accumulate_correctRounding hacc hov] at ha
  injection ha with ha
  simp only [hs, Bool.not_true, fl32_false] at hfl
  rw [EftSplit.run_bits, eftSplit_exact, ha, hfl]

/-- On CDNA 1 the overlap is the low parts plus the final rounding error, at most half a unit. -/
theorem correctRounding_overlap {P : Model} (hacc : P.accumulation = .correctRounding)
    (hov : P.productOverflow = false) (hs : P.subnormals = true) {x : BlockInput P}
    {t : BlockTrace P} (h : evalBlock x = .ok t) :
    t.split.q = ulpExp32 (wordValue t.d) ∧
      t.split.overlap (wordValue t.d) =
        sumQ t.split.lows + (wordValue t.d - t.prepared.exact) ∧
      absQ (wordValue t.d - t.prepared.exact) ≤ pow2 (t.split.q - 1) := by
  have hq : t.split.q = ulpExp32 (wordValue t.d) := by
    show eftCutoff P t.prepared (wordValue t.d) = _
    unfold eftCutoff; rw [hacc]
  obtain ⟨he, _⟩ := correctRounding_nearestEven hacc hov hs h
  have hfl := (evalBlock_ok h).2.2.2.2
  simp only [hs, Bool.not_true] at hfl
  have hd : wordValue t.d = rneValue t.sAcc := wordValue_of_fl32_false hfl
  refine ⟨hq, ?_, ?_⟩
  · unfold BlockTrace.split; rw [(overlap_eq_error_add_lows P t.prepared _).1]; grind
  · rw [hq, absQ_sub_comm, hd, ← he]; exact rneValue_error_ulp _

theorem cdna1F16_eft {x : BlockInput cdna1F16} {t : BlockTrace cdna1F16}
    (h : evalBlock x = .ok t) : ∃ r, mcEft x t.d = .ok r ∧ r.bits = some t.d :=
  correctRounding_eft rfl rfl rfl h

theorem cdna1BF16_eft {x : BlockInput cdna1BF16} {t : BlockTrace cdna1BF16}
    (h : evalBlock x = .ok t) : ∃ r, mcEft x t.d = .ok r ∧ r.bits = some t.d :=
  correctRounding_eft rfl rfl rfl h

theorem sfmaF32_eft {x : BlockInput sfmaF32} {t : BlockTrace sfmaF32}
    (h : evalBlock x = .ok t) : ∃ r, mcEft x t.d = .ok r ∧ r.bits = some t.d :=
  correctRounding_eft rfl rfl rfl h

end MatrixCore
