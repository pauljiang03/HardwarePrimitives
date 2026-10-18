import MatrixCore.MC.Stages
import MatrixCore.MC.Prepared

/-! # Error of the CDNA 3 accumulation

Bounds for each lossy stage of Algorithms 1 and 2, and for `S_acc`. -/

namespace MatrixCore

/-! ## Product alignment -/

theorem sumQ_trunc_error (ps : List Unpacked) (g : ℤ) :
    absQ (sumQ (ps.map Unpacked.value) - sumQ (ps.map fun p => truncGrid p.value g)) ≤
      ps.length * pow2 g := by
  rw [← sumQ_map_sub]
  refine Rat.le_trans (absQ_sumQ_le _) ?_
  rw [List.map_map]
  apply sumQ_map_le
  intro p _
  exact Rat.le_of_lt (truncGrid_bounds p.value g).2.1

theorem alignedSum_error {padding : ℕ} {ps : List Unpacked} {e : ℤ} {S : ℚ}
    (h : alignedSum padding ps = (some e, S)) :
    absQ (sumQ (ps.map Unpacked.value) - S) ≤ ps.length * pow2 (e - (23 + padding : ℕ)) := by
  unfold alignedSum at h
  split at h
  · simp at h
  · rename_i e' he
    simp only [Prod.mk.injEq, Option.some.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact sumQ_trunc_error ps _

theorem alignedSum_none {padding : ℕ} {ps : List Unpacked} {S : ℚ} (h : alignedSum padding ps = (none, S)) :
    S = 0 := by
  unfold alignedSum at h; split at h <;> simp_all

theorem alignedSum_none_exact {padding : ℕ} {ps : List Unpacked} {S : ℚ}
    (h : alignedSum padding ps = (none, S)) : S = 0 ∧ sumQ (ps.map Unpacked.value) = 0 := by
  unfold alignedSum at h
  split at h
  · rename_i hm; simp at h; exact ⟨h.symm, sum_of_zero (maxExp_none hm)⟩
  · simp at h

/-- Error of `S_{p_i,sum}` against the exact product sum, for either configuration. -/
theorem productSum_error (P : Model) {ps : List Unpacked} {e : ℤ} {S : ℚ}
    (h : productSum P ps = (some e, S)) :
    absQ (sumQ (ps.map Unpacked.value) - S) ≤ (ps.length + 2) * pow2 (e - (23 + P.padding : ℕ)) := by
  have hg := pow2_pos (e - (23 + P.padding : ℕ))
  unfold productSum at h
  split at h
  · -- odd/even grouping
    generalize hO : alignedSum P.padding (oddIndexed ps) = O at h
    generalize hE : alignedSum P.padding (evenIndexed ps) = E at h
    obtain ⟨eo, So⟩ := O
    obtain ⟨ee, Se⟩ := E
    simp only at h
    split at h
    · simp at h
    · rename_i e' hj
      simp only [Prod.mk.injEq, Option.some.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      obtain ⟨hsum, hlen⟩ := sumQ_odd_even Unpacked.value ps
      have group : ∀ (l : List Unpacked) (eg : Option ℤ) (Sg : ℚ),
          alignedSum P.padding l = (eg, Sg) → (∀ v, eg = some v → v ≤ e') →
          absQ (sumQ (l.map Unpacked.value) - rdGrid Sg (e' - (23 + P.padding : ℕ))) ≤
            (l.length + 1) * pow2 (e' - (23 + P.padding : ℕ)) := by
        intro l eg Sg hl hle
        have hrd := rdGrid_bounds Sg (e' - (23 + P.padding : ℕ))
        have hrd' : absQ (Sg - rdGrid Sg (e' - (23 + P.padding : ℕ))) ≤ pow2 (e' - (23 + P.padding : ℕ)) := by
          rw [absQ_le_iff]; constructor <;> grind
        cases eg with
        | none =>
          obtain ⟨h0, hs⟩ := alignedSum_none_exact hl
          subst h0; rw [hs, rdGrid_zero]
          have : absQ (0 - 0 : ℚ) = 0 := by decide +kernel
          rw [this]
          exact Rat.mul_nonneg (by exact_mod_cast Nat.zero_le _) (Rat.le_of_lt hg)
        | some v =>
          have ha := alignedSum_error hl
          have hv := pow2_le_of_le (show v - (23 + P.padding : ℕ) ≤ e' - (23 + P.padding : ℕ) by
            have := hle v rfl; omega)
          have hlen0 : (0 : ℚ) ≤ l.length := by exact_mod_cast Nat.zero_le _
          have ha' := Rat.le_trans ha (Rat.mul_le_mul_of_nonneg_left hv hlen0)
          have htri := absQ_add_le (sumQ (l.map Unpacked.value) - Sg)
            (Sg - rdGrid Sg (e' - (23 + P.padding : ℕ)))
          have : sumQ (l.map Unpacked.value) - Sg + (Sg - rdGrid Sg (e' - (23 + P.padding : ℕ))) =
              sumQ (l.map Unpacked.value) - rdGrid Sg (e' - (23 + P.padding : ℕ)) := by grind
          rw [this] at htri
          rw [Rat.add_mul, Rat.one_mul]
          grind
      have hjo : ∀ v, eo = some v → v ≤ e' := by
        intro v hv; subst hv; cases ee <;> simp [joinExp] at hj <;> omega
      have hje : ∀ v, ee = some v → v ≤ e' := by
        intro v hv; subst hv; cases eo <;> simp [joinExp] at hj <;> omega
      have go := group _ eo So hO hjo
      have ge := group _ ee Se hE hje
      have htri := absQ_add_le
        (sumQ ((oddIndexed ps).map Unpacked.value) - rdGrid So (e' - (23 + P.padding : ℕ)))
        (sumQ ((evenIndexed ps).map Unpacked.value) - rdGrid Se (e' - (23 + P.padding : ℕ)))
      have hrw : sumQ ((oddIndexed ps).map Unpacked.value) - rdGrid So (e' - (23 + P.padding : ℕ)) +
          (sumQ ((evenIndexed ps).map Unpacked.value) - rdGrid Se (e' - (23 + P.padding : ℕ))) =
          sumQ (ps.map Unpacked.value) -
            (rdGrid So (e' - (23 + P.padding : ℕ)) + rdGrid Se (e' - (23 + P.padding : ℕ))) := by
        rw [← hsum]; grind
      rw [hrw] at htri
      have hcount : ((oddIndexed ps).length + 1 : ℚ) + ((evenIndexed ps).length + 1) =
          (ps.length + 2 : ℚ) := by
        have : ((oddIndexed ps).length : ℚ) + (evenIndexed ps).length = ps.length := by
          exact_mod_cast hlen
        grind
      have hfin : ((oddIndexed ps).length + 1 : ℚ) * pow2 (e' - (23 + P.padding : ℕ)) +
          ((evenIndexed ps).length + 1 : ℚ) * pow2 (e' - (23 + P.padding : ℕ)) =
          (ps.length + 2 : ℚ) * pow2 (e' - (23 + P.padding : ℕ)) := by
        rw [← Rat.add_mul, hcount]
      grind
  · -- global alignment
    have ha := alignedSum_error h
    have : (ps.length : ℚ) * pow2 (e - (23 + P.padding : ℕ)) ≤
        (ps.length + 2) * pow2 (e - (23 + P.padding : ℕ)) :=
      Rat.mul_le_mul_of_nonneg_right (by grind) (Rat.le_of_lt hg)
    exact Rat.le_trans ha this

/-! ## Late addition of `c` -/

/-- `s'_c` differs from `c` by less than one alignment step, also with the FP8 cutoff. -/
theorem shiftedC_error (P : Model) {eMax eC : ℤ} (c : Unpacked) (hcut : ∀ n, P.late.cCutoff = some n → P.late.cMantissaBits ≤ n)
    (hc : absQ c.value < pow2 (eC + 1)) :
    absQ (c.value - shiftedC P eMax eC c) < pow2 (eMax - P.late.cMantissaBits) := by
  have hrd := rdGrid_bounds c.value (eMax - P.late.cMantissaBits)
  have hrd' : absQ (c.value - rdGrid c.value (eMax - P.late.cMantissaBits)) <
      pow2 (eMax - P.late.cMantissaBits) := by
    rw [absQ_lt_iff]; constructor <;> grind
  unfold shiftedC
  split
  · rename_i n hn
    split
    · rename_i hgt
      have hle := hcut n hn
      have := pow2_le_of_le (show eC + 1 ≤ eMax - P.late.cMantissaBits by omega)
      have hz : c.value - 0 = c.value := by grind
      rw [hz]; grind
    · exact hrd'
  · exact hrd'

/-- When `e_c > e_max`, `S_acc` rounds `S_{p_i,sum} + c` down, by less than two RD steps. -/
theorem shiftedSum_bounds (P : Model) (eC : ℤ) (S : ℚ) (c : Unpacked) :
    let T := rdGrid S (eC - P.late.sumMantissaBits) + c.value
    shiftedSum P eC S c ≤ S + c.value ∧
      S + c.value < shiftedSum P eC S c + pow2 (eC - P.late.sumMantissaBits) +
        pow2 (normExp (absQ T) - P.late.accMantissaBits) := by
  intro T
  have h1 := rdGrid_bounds S (eC - P.late.sumMantissaBits)
  have hp := pow2_pos (normExp (absQ T) - P.late.accMantissaBits)
  unfold shiftedSum normalizeRD
  by_cases hT : rdGrid S (eC - P.late.sumMantissaBits) + c.value = 0
  · simp only [hT, ↓reduceIte]
    constructor <;> grind
  · simp only [hT, ↓reduceIte]
    have h2 := rdGrid_bounds T (normExp (absQ T) - P.late.accMantissaBits)
    constructor <;> grind

theorem lateSum_cases (P : Model) (eMax : Option ℤ) (S : ℚ) (c : Unpacked) :
    (cExp P c = none ∧ lateSum P eMax S c = S) ∨
    (∃ e eC, eMax = some e ∧ cExp P c = some eC ∧ eC ≤ e ∧
      lateSum P eMax S c = S + shiftedC P e eC c) ∨
    (∃ eC, cExp P c = some eC ∧ (∀ e, eMax = some e → e < eC) ∧
      lateSum P eMax S c = shiftedSum P eC S c) := by
  unfold lateSum
  cases hc : cExp P c with
  | none => left; exact ⟨rfl, rfl⟩
  | some eC =>
    cases hm : eMax with
    | none => right; right; exact ⟨eC, rfl, by simp, rfl⟩
    | some e =>
      simp only
      by_cases hle : eC ≤ e
      · right; left; exact ⟨e, eC, rfl, rfl, hle, by simp [hle]⟩
      · right; right
        exact ⟨eC, rfl, by intro e' he'; cases he'; omega, by simp [hle]⟩

/-! ## Error of `S_acc` -/

theorem productSum_none (P : Model) {ps : List Unpacked} {S : ℚ}
    (h : productSum P ps = (none, S)) : S = 0 ∧ sumQ (ps.map Unpacked.value) = 0 := by
  unfold productSum at h
  split at h
  · dsimp only at h
    generalize hO : alignedSum P.padding (oddIndexed ps) = O at h
    generalize hE : alignedSum P.padding (evenIndexed ps) = E at h
    obtain ⟨eo, So⟩ := O
    obtain ⟨ee, Se⟩ := E
    simp only at h
    split at h
    · rename_i hj
      simp only [Prod.mk.injEq, true_and] at h
      cases eo <;> cases ee <;> simp [joinExp] at hj
      have ho := (alignedSum_none_exact hO).2
      have he := (alignedSum_none_exact hE).2
      refine ⟨h.symm, ?_⟩
      rw [← (sumQ_odd_even Unpacked.value ps).1, ho, he]; grind
    · simp at h
  · exact alignedSum_none_exact h

theorem cExp_none {P : Model} {c : Unpacked} (h : cExp P c = none) : c.value = 0 := by
  unfold cExp at h
  split at h
  · rename_i hm; exact (Unpacked.value_eq_zero_iff c).mpr hm
  · simp at h

/-- Error of `S_acc` (Algorithms 1 and 2) against the exact `Σ p_ℓ + c`, by branch. -/
theorem alignedAccumulation_error (P : Model) (x : Prepared)
    (hcut : ∀ n, P.late.cCutoff = some n → P.late.cMantissaBits ≤ n)
    (hc : ∀ eC, cExp P x.c = some eC → absQ x.c.value < pow2 (eC + 1)) :
    let s := productSum P x.p
    let F : ℕ := 23 + P.padding
    let D := x.exact - alignedAccumulation P x
    (cExp P x.c = none → ∀ e, s.1 = some e → absQ D ≤ (x.p.length + 2) * pow2 (e - F)) ∧
    (∀ e eC, s.1 = some e → cExp P x.c = some eC → eC ≤ e →
      absQ D < (x.p.length + 2) * pow2 (e - F) + pow2 (e - P.late.cMantissaBits)) ∧
    (∀ e eC, s.1 = some e → cExp P x.c = some eC → e < eC →
      let T := rdGrid s.2 (eC - P.late.sumMantissaBits) + x.c.value
      0 ≤ D + (x.p.length + 2) * pow2 (e - F) ∧
        D < (x.p.length + 2) * pow2 (e - F) + pow2 (eC - P.late.sumMantissaBits) +
          pow2 (normExp (absQ T) - P.late.accMantissaBits)) ∧
    (∀ eC, s.1 = none → cExp P x.c = some eC →
      let T := rdGrid s.2 (eC - P.late.sumMantissaBits) + x.c.value
      0 ≤ D ∧ D < pow2 (eC - P.late.sumMantissaBits) + pow2 (normExp (absQ T) - P.late.accMantissaBits)) := by
  intro s F D
  have hex : x.exact = sumQ (x.p.map Unpacked.value) + x.c.value := rfl
  have hD : D = (sumQ (x.p.map Unpacked.value) - s.2) + (s.2 + x.c.value - lateSum P s.1 s.2 x.c) := by
    show x.exact - lateSum P s.1 s.2 x.c = _
    rw [hex]; grind
  have hprod : ∀ e, s.1 = some e → absQ (sumQ (x.p.map Unpacked.value) - s.2) ≤
      (x.p.length + 2) * pow2 (e - F) := by
    intro e he
    have : productSum P x.p = (some e, s.2) := by rw [← he]
    exact productSum_error P this
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro hn e he
    have hl : lateSum P s.1 s.2 x.c = s.2 := by unfold lateSum; rw [hn]
    rw [hD, hl, cExp_none hn]
    have : sumQ (x.p.map Unpacked.value) - s.2 + (s.2 + 0 - s.2) =
        sumQ (x.p.map Unpacked.value) - s.2 := by grind
    rw [this]; exact hprod e he
  · intro e eC he hc' hle
    have hl : lateSum P s.1 s.2 x.c = s.2 + shiftedC P e eC x.c := by
      unfold lateSum; rw [hc', he]; simp [hle]
    rw [hD, hl]
    have h1 := hprod e he
    have h2 := shiftedC_error P (eMax := e) x.c hcut (hc eC hc')
    have : s.2 + x.c.value - (s.2 + shiftedC P e eC x.c) = x.c.value - shiftedC P e eC x.c := by
      grind
    rw [this]
    have h3 := absQ_add_le (sumQ (x.p.map Unpacked.value) - s.2) (x.c.value - shiftedC P e eC x.c)
    grind
  · intro e eC he hc' hlt
    have hl : lateSum P s.1 s.2 x.c = shiftedSum P eC s.2 x.c := by
      unfold lateSum; rw [hc', he]; simp [show ¬ eC ≤ e by omega]
    rw [hD, hl]
    have h1 := (absQ_le_iff _ _).mp (hprod e he)
    have h2 := shiftedSum_bounds P eC s.2 x.c
    simp only at h2
    constructor <;> grind
  · intro eC hn hc'
    have hl : lateSum P s.1 s.2 x.c = shiftedSum P eC s.2 x.c := by
      unfold lateSum; rw [hc', hn]
    have h0 : productSum P x.p = (none, s.2) := by rw [← hn]
    have hz := productSum_none P h0
    rw [hD, hl, hz.2, hz.1]
    have h2 := shiftedSum_bounds P eC 0 x.c
    simp only at h2
    constructor <;> grind

end MatrixCore
