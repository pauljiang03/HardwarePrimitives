import MatrixCore.EFT.Encoded

/-! # MC-EFT for inner products of any length

The correction of `c + Σ a_ℓ b_ℓ` from the final output word `D` of a chain of blocks, with every
product and `c` split at the last bit of `D`. -/

namespace MatrixCore

/-- The split of decoded operands of any length at `D`'s last bit: `c` first, then the products. -/
def dotSplit (px : Prepared) (d : ℚ) : EftSplit :=
  ⟨ulpExp32 d, (.trunc, px.c.value) :: px.p.map fun p => (.trunc, p.value)⟩

/-- The correction of an inner product of any length from a finite FP32 word `D`. -/
def mcEftDot (P : Model) (a : List P.a.Word) (b : List P.b.Word) (c D : F32) :
    Except EftError EftResult :=
  if a.length ≠ b.length then .error .wrongLength
  else
    match prepare (P := P) ⟨a, b, c⟩ with
    | none => .error .nonfiniteInput
    | some px =>
      match value32 D with
      | none => .error .nonfiniteOutput
      | some d => .ok ((dotSplit px d).run d)

theorem dotSplit_exact (px : Prepared) (d : ℚ) : (dotSplit px d).exact = px.exact := by
  unfold dotSplit EftSplit.exact Prepared.exact
  simp only [List.map_cons, List.map_map, sumQ]
  rw [show (Prod.snd ∘ fun p : Unpacked => ((SplitRule.trunc, p.value) : SplitRule × ℚ)) =
    Unpacked.value from rfl]
  grind

/-- Decoded operands of any length have the exact inner product `c + Σ a_ℓ b_ℓ`. -/
theorem prepare_exact_dot {P : Model} {a : List P.a.Word} {b : List P.b.Word} {c : F32}
    {px : Prepared} (h : prepare (P := P) ⟨a, b, c⟩ = some px) : px.exact = exactDot P a b c := by
  unfold prepare at h
  cases hA : a.mapM fun w => (P.a.read w).toFinite <;> rw [hA] at h <;> simp at h
  cases hB : b.mapM fun w => (P.b.read w).toFinite <;> rw [hB] at h <;> simp at h
  cases hC : (fp32.decode c).toFinite <;> rw [hC] at h <;> simp at h
  rename_i A B u
  subst h
  unfold Prepared.exact Prepared.p exactDot
  rw [wordValue_of_decode hC, ← mapM_products a b A B hA hB]
  have : (List.zipWith Unpacked.mul A B).map Unpacked.value =
      List.zipWith (fun u v => u.value * v.value) A B := by
    clear hA hB
    induction A generalizing B with
    | nil => rfl
    | cons x xs ih =>
      cases B with
      | nil => rfl
      | cons y ys => simp only [List.zipWith_cons_cons, List.map_cons, Unpacked.value_mul, ih]
  rw [this]
  grind

theorem mcEftDot_spec {P : Model} {a : List P.a.Word} {b : List P.b.Word} {c D : F32}
    {r : EftResult} (h : mcEftDot P a b c D = .ok r) :
    a.length = b.length ∧ ∃ px d, prepare (P := P) ⟨a, b, c⟩ = some px ∧ value32 D = some d ∧
      r = (dotSplit px d).run d := by
  unfold mcEftDot at h
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
        exact ⟨by omega, px, d, hp, hd, rfl⟩

/-- Any returned word is RNE of the exact inner product, for any finite `D`. -/
theorem mcEftDot_bits {P : Model} {a : List P.a.Word} {b : List P.b.Word} {c D : F32}
    {r : EftResult} (h : mcEftDot P a b c D = .ok r) : r.bits = rne32 (exactDot P a b c) := by
  obtain ⟨_, px, d, hp, _, rfl⟩ := mcEftDot_spec h
  rw [EftSplit.run_bits, dotSplit_exact, prepare_exact_dot hp]

/-- A returned word is the FP32 word nearest `c + Σ a_ℓ b_ℓ`, for any `D`. -/
theorem mcEftDot_correct {P : Model} {a : List P.a.Word} {b : List P.b.Word} {c D : F32}
    {r : EftResult} {w : F32} (h : mcEftDot P a b c D = .ok r) (hw : r.bits = some w) :
    RoundsNearestEven32 (exactDot P a b c) w :=
  rne32_rounds (mcEftDot_bits h ▸ hw)

/-- A word is returned exactly when the exact inner product is below the overflow threshold. -/
theorem mcEftDot_isSome_iff {P : Model} {a : List P.a.Word} {b : List P.b.Word} {c D : F32}
    {r : EftResult} (h : mcEftDot P a b c D = .ok r) :
    r.bits.isSome = true ↔ absQ (exactDot P a b c) < overflowThreshold32 := by
  rw [mcEftDot_bits h]; exact rne32_isSome_iff _

/-- The correction accepts exactly equal lengths, finite operands and a finite `D`. -/
theorem mcEftDot_ok_iff (P : Model) (a : List P.a.Word) (b : List P.b.Word) (c D : F32) :
    (∃ r, mcEftDot P a b c D = .ok r) ↔
      a.length = b.length ∧ (∃ px, prepare (P := P) ⟨a, b, c⟩ = some px) ∧
        ∃ d, value32 D = some d := by
  constructor
  · rintro ⟨r, hr⟩
    obtain ⟨hl, px, d, hp, hd, _⟩ := mcEftDot_spec hr
    exact ⟨hl, ⟨px, hp⟩, ⟨d, hd⟩⟩
  · rintro ⟨hl, ⟨px, hp⟩, ⟨d, hd⟩⟩
    refine ⟨(dotSplit px d).run d, ?_⟩
    unfold mcEftDot
    rw [if_neg (by omega), hp]
    simp only [hd]

/-- The overlap is the error of `D` against the exact inner product plus the low parts, which
sum to at most `(k + 1) · 2^q`; from `dotBits`, the error is at most the blocks' bounds. -/
theorem dot_overlap (P : Model) (hn : 0 < P.nfma) {B : BlockTrace P → ℚ}
    (hB : ∀ x t, evalBlock x = .ok t → absQ t.residual ≤ B t)
    {a : List P.a.Word} {b : List P.b.Word} {c D : F32} {px : Prepared} {d : ℚ}
    (hlen : a.length = b.length) (hD : dotBits P a b c = .ok D)
    (hp : prepare (P := P) ⟨a, b, c⟩ = some px) (hd : value32 D = some d) :
    (dotSplit px d).overlap d = (d - exactDot P a b c) + sumQ (dotSplit px d).lows ∧
      absQ (sumQ (dotSplit px d).lows) ≤ (px.p.length + 1 : ℕ) * pow2 (ulpExp32 d) ∧
      ∃ ts, runBlocks P c (blocks P a b) = .ok ts ∧
        absQ (exactDot P a b c - d) ≤ sumQ (ts.map B) := by
  refine ⟨by rw [EftSplit.overlap_eq, dotSplit_exact, prepare_exact_dot hp], ?_, ?_⟩
  · have := (dotSplit px d).sumQ_lows_abs_le
    simpa [dotSplit, Nat.add_comm] using this
  · obtain ⟨ts, hr, _, he⟩ := dotBits_exact_error P hn hB hlen hD
    refine ⟨ts, hr, ?_⟩
    have hw : wordValue D = d := by simp [wordValue, hd]
    rwa [hw] at he

end MatrixCore
