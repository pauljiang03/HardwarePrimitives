import MatrixCore.EFT.Core

/-! # The correction on encoded inputs

The cut-off of each configuration and the correction of one encoded block from a finite FP32
word `D`. Any returned word is the FP32 word nearest the exact `Σ a_ℓ b_ℓ + c`, for every `D`. -/

namespace MatrixCore

/-- `e_max`: the largest exponent of a nonzero product, over both groups on FP8. -/
def alignExp (P : Model) (ps : List Unpacked) : Option ℤ :=
  match P.accumulation with
  | .oddEvenGrouping => joinExp (maxExp (oddIndexed ps)) (maxExp (evenIndexed ps))
  | _ => maxExp ps

/-- With the FP8 cutoff, `s'_c = 0` once `e_max − e_c` exceeds it. -/
def cDropped (P : Model) (eMax eC : ℤ) : Bool :=
  match P.late.cCutoff with
  | some n => decide (eMax - eC > n)
  | none => false

/-- The coarsest grid CDNA 3 aligns to: the products' grid, and that of `s'_c` or `S'_{p_i,sum}`. -/
def hwGrid (P : Model) (px : Prepared) : Option ℤ :=
  match alignExp P px.p, cExp P px.c with
  | some e, some eC =>
    if eC ≤ e then some (max (e - (23 + P.padding : ℕ)) (e - P.late.cMantissaBits))
    else some (max (e - (23 + P.padding : ℕ)) (eC - P.late.sumMantissaBits))
  | some e, none => some (e - (23 + P.padding : ℕ))
  | none, some eC => some (eC - P.late.sumMantissaBits)
  | none, none => none

/-- The cut-off exponent: `D`'s last bit, and at least the alignment grid on CDNA 3. -/
def eftCutoff (P : Model) (px : Prepared) (d : ℚ) : ℤ :=
  match P.accumulation with
  | .globalAlignment | .oddEvenGrouping =>
    match hwGrid P px with
    | some g => max (ulpExp32 d) g
    | none => ulpExp32 d
  | _ => ulpExp32 d

/-- `c` is split by RD where CDNA 3 rounds it down to the grid, otherwise by truncation. -/
def cRule (P : Model) (px : Prepared) : SplitRule :=
  match P.accumulation with
  | .globalAlignment | .oddEvenGrouping =>
    match alignExp P px.p, cExp P px.c with
    | some e, some eC => if eC ≤ e ∧ cDropped P e eC = false then .rd else .trunc
    | _, _ => .trunc
  | _ => .trunc

/-- The split of a decoded block for the output value `d`: `c` first, then the products. -/
def eftSplit (P : Model) (px : Prepared) (d : ℚ) : EftSplit :=
  ⟨eftCutoff P px d, (cRule P px, px.c.value) :: px.p.map fun p => (.trunc, p.value)⟩

inductive EftError where
  /-- `a` or `b` does not have `N_FMA` entries. -/
  | wrongLength
  /-- An operand is an infinity or NaN. -/
  | nonfiniteInput
  /-- `D` is an infinity or NaN. -/
  | nonfiniteOutput
  deriving Repr, DecidableEq

/-- The correction of one encoded block from a finite FP32 word `D`. -/
def mcEft {P : Model} (x : BlockInput P) (D : F32) : Except EftError EftResult :=
  if x.a.length ≠ P.nfma ∨ x.b.length ≠ P.nfma then .error .wrongLength
  else
    match prepare x with
    | none => .error .nonfiniteInput
    | some px =>
      match value32 D with
      | none => .error .nonfiniteOutput
      | some d => .ok ((eftSplit P px d).run d)

/-! ## Correctness -/

theorem eftSplit_exact (P : Model) (px : Prepared) (d : ℚ) :
    (eftSplit P px d).exact = px.exact := by
  unfold eftSplit EftSplit.exact Prepared.exact
  simp only [List.map_cons, List.map_map, sumQ]
  rw [show (Prod.snd ∘ fun p : Unpacked => ((SplitRule.trunc, p.value) : SplitRule × ℚ)) =
    Unpacked.value from rfl]
  grind

theorem mcEft_spec {P : Model} {x : BlockInput P} {D : F32} {r : EftResult}
    (h : mcEft x D = .ok r) :
    x.a.length = P.nfma ∧ x.b.length = P.nfma ∧
      ∃ px d, prepare x = some px ∧ value32 D = some d ∧ r = (eftSplit P px d).run d := by
  unfold mcEft at h
  split at h
  · cases h
  · rename_i hl
    split at h
    · cases h
    · rename_i px hp
      split at h
      · cases h
      · rename_i d hd
        cases h
        exact ⟨by omega, by omega, px, d, hp, hd, rfl⟩

/-- Any returned word is RNE of the exact sum of the decoded inputs, for any finite `D`. -/
theorem mcEft_bits {P : Model} {x : BlockInput P} {D : F32} {r : EftResult}
    (h : mcEft x D = .ok r) : ∃ px, prepare x = some px ∧ r.bits = rne32 px.exact := by
  obtain ⟨_, _, px, d, hp, _, rfl⟩ := mcEft_spec h
  exact ⟨px, hp, by rw [EftSplit.run_bits, eftSplit_exact]⟩

/-- A returned word is the FP32 word nearest `Σ a_ℓ b_ℓ + c`, for any `D`. -/
theorem mcEft_correct {P : Model} {x : BlockInput P} {D : F32} {r : EftResult} {b : F32}
    (h : mcEft x D = .ok r) (hb : r.bits = some b) :
    ∃ px, prepare x = some px ∧ RoundsNearestEven32 px.exact b := by
  obtain ⟨px, hp, hr⟩ := mcEft_bits h
  exact ⟨px, hp, rne32_rounds (hr ▸ hb)⟩

/-- A word is returned exactly when the exact sum is below the FP32 overflow threshold. -/
theorem mcEft_isSome_iff {P : Model} {x : BlockInput P} {D : F32} {r : EftResult} {px : Prepared}
    (h : mcEft x D = .ok r) (hp : prepare x = some px) :
    r.bits.isSome = true ↔ absQ px.exact < overflowThreshold32 := by
  obtain ⟨px', hp', hr⟩ := mcEft_bits h
  rw [hp] at hp'
  cases hp'
  rw [hr]
  exact rne32_isSome_iff _

/-- The correction accepts exactly right-shaped blocks with finite operands and a finite `D`. -/
theorem mcEft_ok_iff {P : Model} (x : BlockInput P) (D : F32) :
    (∃ r, mcEft x D = .ok r) ↔
      x.a.length = P.nfma ∧ x.b.length = P.nfma ∧ (∃ px, prepare x = some px) ∧
        ∃ d, value32 D = some d := by
  constructor
  · rintro ⟨r, hr⟩
    obtain ⟨ha, hb, px, d, hp, hd, _⟩ := mcEft_spec hr
    exact ⟨ha, hb, ⟨px, hp⟩, ⟨d, hd⟩⟩
  · rintro ⟨ha, hb, ⟨px, hp⟩, ⟨d, hd⟩⟩
    refine ⟨(eftSplit P px d).run d, ?_⟩
    unfold mcEft
    rw [if_neg (by omega), hp]
    simp only [hd]

/-- From the Matrix Core's own output, the correction runs on the block's trace. -/
theorem mcEft_of_evalBlock {P : Model} {x : BlockInput P} {t : BlockTrace P}
    (h : evalBlock x = .ok t) :
    mcEft x t.d = .ok ((eftSplit P t.prepared (wordValue t.d)).run (wordValue t.d)) := by
  obtain ⟨ha, hb, hp, _, hd⟩ := evalBlock_ok h
  unfold mcEft
  rw [if_neg (by omega), hp]
  simp only [fl32_value hd]

/-! ## The overlap on every configuration -/

/-- The split of an evaluated block at the cut-off chosen from its own output. -/
def BlockTrace.split {P : Model} (t : BlockTrace P) : EftSplit :=
  eftSplit P t.prepared (wordValue t.d)

theorem eftCutoff_ge (P : Model) (px : Prepared) (d : ℚ) : ulpExp32 d ≤ eftCutoff P px d := by
  unfold eftCutoff
  split <;> (try split) <;> omega

/-- The overlap is a whole number of units in `D`'s last place, for every finite `D`. -/
theorem overlap_onGrid (P : Model) (px : Prepared) {D : F32} {d : ℚ} (hd : value32 D = some d) :
    OnGrid ((eftSplit P px d).overlap d) (ulpExp32 d) :=
  (value32_onGrid_ulpExp hd).sub ((eftSplit P px d).H_onGrid.mono (eftCutoff_ge P px d))

/-- The overlap is the error of `D` plus the low parts, which sum to at most `(n + 1) · 2^q`. -/
theorem overlap_eq_error_add_lows (P : Model) (px : Prepared) (d : ℚ) :
    (eftSplit P px d).overlap d = (d - px.exact) + sumQ (eftSplit P px d).lows ∧
      absQ (sumQ (eftSplit P px d).lows) ≤ (px.p.length + 1 : ℕ) * pow2 (eftCutoff P px d) := by
  refine ⟨by rw [EftSplit.overlap_eq, eftSplit_exact], ?_⟩
  have := (eftSplit P px d).sumQ_lows_abs_le
  simpa [eftSplit, Nat.add_comm] using this

end MatrixCore
