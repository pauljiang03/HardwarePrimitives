import MatrixCore.MC.InnerProduct

/-! # The MFMA operation `D = AB + C`

`mfma P A B C` takes `A` and `C` by rows and `B` by columns. -/

namespace MatrixCore

theorem mfma_length (P : Model) (A : List (List P.a.Word)) (B : List (List P.b.Word))
    (C : List (List F32)) : (mfma P A B C).length = min A.length C.length := by
  simp [mfma]

theorem mfma_row_length (P : Model) (A : List (List P.a.Word)) (B : List (List P.b.Word))
    (C : List (List F32)) {i : ℕ} {row : List (Option Outcome)} (h : (mfma P A B C)[i]? = some row)
    {cRow : List F32} (hc : C[i]? = some cRow) : row.length = min B.length cRow.length := by
  unfold mfma at h
  rw [List.getElem?_zipWith, hc] at h
  cases hA : A[i]? with
  | none => rw [hA] at h; simp at h
  | some aRow => rw [hA] at h; simp at h; rw [← h]; simp

/-- Entry `d_ij` is the observed inner product of row `i` of `A`, column `j` of `B` and `c_ij`. -/
theorem mfma_entry (P : Model) {A : List (List P.a.Word)} {B : List (List P.b.Word)}
    {C : List (List F32)} {i j : ℕ} {row : List P.a.Word} {col : List P.b.Word}
    {cRow : List F32} {c : F32} (hA : A[i]? = some row) (hB : B[j]? = some col)
    (hC : C[i]? = some cRow) (hc : cRow[j]? = some c) :
    ((mfma P A B C)[i]?).bind (·[j]?) = some (dotOutcome P row col c) := by
  unfold mfma
  rw [List.getElem?_zipWith, hA, hC]
  simp only [Option.bind_some]
  rw [List.getElem?_zipWith, hB, hc]

/-- A finite entry is the finite-domain inner product of its row and column. -/
theorem mfma_finite (P : Model) {A : List (List P.a.Word)} {B : List (List P.b.Word)}
    {C : List (List F32)} {i j : ℕ} {row : List P.a.Word} {col : List P.b.Word}
    {cRow : List F32} {c d : F32} (hA : A[i]? = some row) (hB : B[j]? = some col)
    (hC : C[i]? = some cRow) (hc : cRow[j]? = some c)
    (hd : ((mfma P A B C)[i]?).bind (·[j]?) = some (some (.finite d))) :
    row.length = col.length ∧ dotBits P row col c = .ok d := by
  rw [mfma_entry P hA hB hC hc] at hd
  exact dotOutcome_finite P (Option.some.inj hd)

/-- A finite entry `d_ij` is within the sum of its blocks' bounds of `c_ij + Σ_ℓ a_iℓ b_ℓj`. -/
theorem mfma_error (P : Model) (hn : 0 < P.nfma) {Bnd : BlockTrace P → ℚ}
    (hB : ∀ x t, evalBlock x = .ok t → absQ t.residual ≤ Bnd t)
    {A : List (List P.a.Word)} {B : List (List P.b.Word)}
    {C : List (List F32)} {i j : ℕ} {row : List P.a.Word} {col : List P.b.Word}
    {cRow : List F32} {c d : F32} (hA : A[i]? = some row) (hBj : B[j]? = some col)
    (hC : C[i]? = some cRow) (hc : cRow[j]? = some c)
    (hd : ((mfma P A B C)[i]?).bind (·[j]?) = some (some (.finite d))) :
    ∃ ts, runBlocks P c (blocks P row col) = .ok ts ∧ lastOutput c ts = d ∧
      (∀ t ∈ ts, ∃ x, BlockContract x t) ∧
      absQ (exactDot P row col c - wordValue d) ≤ sumQ (ts.map Bnd) := by
  obtain ⟨hlen, hbits⟩ := mfma_finite P hA hBj hC hc hd
  obtain ⟨ts, hr, hl, he⟩ := dotBits_exact_error P hn hB hlen hbits
  exact ⟨ts, hr, hl, runBlocks_all (fun _ _ h => evalBlock_contract h) hr, he⟩

end MatrixCore
