import MatrixCore.Specification.Bridge

/-! # The specification's stages agree with the implementation

Algorithms 1 and 2 of the specification, on decoded inputs, compute the implementation's
`S_acc`. -/

namespace MatrixCore.Spec

open MatrixCore

/-- The specification's late-addition parameters of a model. -/
def lateOf (P : Model) : Late :=
  ⟨P.neab, P.late.cFracBits, P.late.sumFracBits, P.late.accFracBits, P.late.cCutoff, P.cZeroExp⟩

theorem cExp_eq (P : Model) (c : Unpacked) : cExp (lateOf P) (numOf c) = MatrixCore.cExp P c := rfl

theorem log2Floor_natCast {n : ℕ} (hn : n ≠ 0) : log2Floor (n : ℚ) = (n.log2 : ℤ) := by
  apply log2Floor_eq
  · rw [pow2_natCast]; exact_mod_cast Nat.log2_self_le hn
  · rw [show (n.log2 : ℤ) + 1 = ((n.log2 + 1 : ℕ) : ℤ) by omega, pow2_natCast]
    exact_mod_cast Nat.lt_log2_self

theorem intCast_shiftRD_add (V W : ℤ) (g g' h : ℤ) :
    ((shiftRD V g h + shiftRD W g' h : ℤ) : ℚ) * pow2 h =
      rdGrid ((V : ℚ) * pow2 g) h + rdGrid ((W : ℚ) * pow2 g') h := by
  rw [Rat.intCast_add, Rat.add_mul, shiftRD_eq, shiftRD_eq]

/-- `c` on the grid of `S'_{p_i,sum}`. -/
theorem c_onGrid (c : Unpacked) (ec : ℤ) (k : ℕ) (hc : c.t ≤ k)
    (hec : c.m ≠ 0 → ec = c.e) : OnGrid c.value (ec - k) := by
  by_cases hm : c.m = 0
  · rw [(Unpacked.value_eq_zero_iff c).mpr hm]; exact OnGrid.zero _
  · rw [hec hm]; exact c.value_onGrid.mono (by omega)

theorem shiftedBranch_eq (P : Model) (S : ℤ) (g : ℤ) (c : Unpacked) (ec : ℤ)
    (hc : c.t ≤ P.late.sumFracBits) (hec : c.m ≠ 0 → ec = c.e) :
    shiftedBranch (lateOf P) S g (numOf c) ec = shiftedSum P ec ((S : ℚ) * pow2 g) c := by
  unfold shiftedBranch shiftedSum normalizeRD
  simp only [lateOf]
  obtain ⟨A, hA⟩ : ∃ A, shiftRD S g (ec - P.late.sumFracBits) +
      shiftRD (numOf c).int ((numOf c).e - (numOf c).f) (ec - P.late.sumFracBits) = A := ⟨_, rfl⟩
  simp only [hA]
  have hT : (A : ℚ) * pow2 (ec - P.late.sumFracBits) =
      rdFrac ((S : ℚ) * pow2 g) ec P.late.sumFracBits + c.value := by
    rw [← hA, intCast_shiftRD_add]
    congr 1
    have hcv : ((numOf c).int : ℚ) * pow2 ((numOf c).e - (numOf c).f) = c.value := int_numOf_val c
    rw [hcv]
    exact rdGrid_of_onGrid (c_onGrid c ec _ hc hec)
  simp only [← hT]
  by_cases h0 : A = 0
  · simp [h0]
  · have hA0 : (A : ℚ) * pow2 (ec - P.late.sumFracBits) ≠ 0 := by
      intro h
      rcases Rat.mul_eq_zero.mp h with h | h
      · exact h0 (by exact_mod_cast h)
      · exact pow2_ne_zero _ h
    simp only [h0, ↓reduceIte, hA0, two_zpow]
    have hlead : normExp (absQ ((A : ℚ) * pow2 (ec - P.late.sumFracBits))) =
        max ((A.natAbs.log2 : ℤ) + (ec - P.late.sumFracBits)) (-126) := by
      unfold normExp
      rw [absQ_mul_pos _ _ (pow2_pos _), absQ_intCast,
        log2Floor_mul_pow2 (by exact_mod_cast Nat.pos_of_ne_zero (by omega)),
        log2Floor_natCast (by omega)]
    rw [hlead, shiftRD_eq]

theorem cExp_some {P : Model} {c : Unpacked} {x : ℤ} (h : MatrixCore.cExp P c = some x)
    (hm : c.m ≠ 0) : x = c.e := by
  unfold MatrixCore.cExp at h; simp [hm] at h; exact h.symm

theorem F_cast (n : ℕ) : ((23 + n : ℕ) : ℤ) = 23 + (n : ℤ) := by omega

/-- The late addition of `c` (Algorithm 1 lines 3–11), for a product sum `S` on the grid
`2^(e_max − F)`. -/
theorem lateC_eq (P : Model) (e : Option ℤ) (S : ℤ) (c : Unpacked)
    (hc : c.t ≤ P.late.sumFracBits) (hS : e = none → S = 0) :
    lateC (lateOf P) e S (numOf c) =
      lateSum P e ((S : ℚ) * pow2 (e.getD 0 - (23 + P.neab : ℕ))) c := by
  unfold lateC lateSum
  rw [cExp_eq]
  cases hce : MatrixCore.cExp P c with
  | none =>
    cases e with
    | none => simp [hS rfl]
    | some e => simp only [Option.getD_some, two_zpow, F_cast]; rfl
  | some ec =>
    have hec : c.m ≠ 0 → ec = c.e := cExp_some hce
    cases e with
    | none =>
      simp only [hS rfl, Rat.intCast_zero, Rat.zero_mul]
      have := shiftedBranch_eq P 0 0 c ec hc hec
      simp only [Rat.intCast_zero, Rat.zero_mul] at this
      exact this
    | some e =>
      simp only [Option.getD_some]
      by_cases hle : ec ≤ e
      · simp only [hle, ↓reduceIte, two_zpow, lateOf, F_cast]
        congr 1
        unfold shiftedC
        have hsc : ((shiftRD (numOf c).int ((numOf c).e - (numOf c).f) (e - P.late.cFracBits) : ℤ) : ℚ) *
            pow2 (e - P.late.cFracBits) = rdFrac c.value e P.late.cFracBits := by
          rw [shiftRD_eq]; exact congrArg (rdGrid · _) (int_numOf_val c)
        obtain ⟨cut, hcut⟩ : ∃ x, P.late.cCutoff = x := ⟨_, rfl⟩
        simp only [hcut]
        cases cut with
        | none => simpa using hsc
        | some n =>
          by_cases hgt : e - ec > n
          · simp [hgt]
          · simp only [hgt, decide_false, Bool.false_eq_true, ↓reduceIte]; exact hsc
      · simp only [hle, ↓reduceIte]
        rw [shiftedBranch_eq P S _ c ec hc hec, F_cast]
        simp [lateOf]

theorem sum_alignTrunc (ps : List Unpacked) (e : ℤ) (k : ℕ) :
    (((ps.map numOf).map fun p => alignTrunc p e k).sum : ℚ) * pow2 (e - k) =
      sumQ (ps.map fun p => truncGrid p.value (e - k)) := by
  induction ps with
  | nil => simp [sumQ]
  | cons p ps ih =>
    simp only [List.map_cons, List.sum_cons, Rat.intCast_add, Rat.add_mul, sumQ, ih, alignTrunc_eq]

/-- Algorithm 1 computes the implementation's `S_acc` for `global_alignment`. -/
theorem algorithm1_eq (P : Model) (hP : P.accumulation = .globalAlignment) (ps : List Unpacked)
    (c : Unpacked) (hc : c.t ≤ P.late.sumFracBits) :
    algorithm1 (lateOf P) (ps.map numOf) (numOf c) = lateSum P (productSum P ps).1 (productSum P ps).2 c := by
  unfold algorithm1 productSum alignedSum
  rw [emax_eq, hP]
  simp only
  cases hm : maxExp ps with
  | none =>
    simp only
    have := lateC_eq P none 0 c hc (fun _ => rfl)
    simpa using this
  | some e =>
    simp only
    rw [lateC_eq P (some e) _ c hc (by simp)]
    simp only [Option.getD_some]
    rw [show (lateOf P).neab = P.neab from rfl, sum_alignTrunc]

/-! ## Algorithm 2 -/

theorem odd_even_cons : ∀ (a : α) (l : List α),
    oddIndexed (a :: l) = a :: evenIndexed l ∧ evenIndexed (a :: l) = oddIndexed l
  | _, [] => by simp [oddIndexed, evenIndexed]
  | _, [_] => by simp [oddIndexed, evenIndexed]
  | a, b :: c :: r => by
    obtain ⟨h1, h2⟩ := odd_even_cons c r
    simp only [oddIndexed, evenIndexed] at h1 h2 ⊢
    exact ⟨by rw [h1], by rw [h2]⟩

theorem zipIdx_parity (l : List α) (n : ℕ) :
    ((l.zipIdx n).filter (fun q => decide (q.2 % 2 = n % 2))).map (·.1) = oddIndexed l ∧
      ((l.zipIdx n).filter (fun q => decide (q.2 % 2 = (n + 1) % 2))).map (·.1) = evenIndexed l := by
  induction l generalizing n with
  | nil => simp [oddIndexed, evenIndexed]
  | cons a l ih =>
    obtain ⟨h1, h2⟩ := ih (n + 1)
    have hp : (fun q : α × ℕ => decide (q.2 % 2 = (n + 1 + 1) % 2)) =
        fun q => decide (q.2 % 2 = n % 2) := by
      funext q; simp only [show (n + 1 + 1) % 2 = n % 2 by omega]
    rw [hp] at h2
    obtain ⟨o1, o2⟩ := odd_even_cons a l
    simp only [List.zipIdx_cons, List.filter_cons]
    constructor
    · simp only [decide_true, ↓reduceIte, List.map_cons, h2, o1]
    · have : ¬ (n % 2 = (n + 1) % 2) := by omega
      simp only [this, decide_false, Bool.false_eq_true, ↓reduceIte, h1, o2]

theorem oddIndexed_map (f : α → β) : ∀ l : List α,
    oddIndexed (l.map f) = (oddIndexed l).map f ∧ evenIndexed (l.map f) = (evenIndexed l).map f
  | [] => by simp [oddIndexed, evenIndexed]
  | [_] => by simp [oddIndexed, evenIndexed]
  | a :: b :: r => by
    obtain ⟨h1, h2⟩ := oddIndexed_map f r
    simp [oddIndexed, evenIndexed, h1, h2]

theorem odds_map (ps : List Unpacked) : odds (ps.map numOf) = (oddIndexed ps).map numOf := by
  have := (zipIdx_parity (ps.map numOf) 0).1
  unfold odds; simp only [Nat.zero_mod] at this
  rw [this, (oddIndexed_map numOf ps).1]

theorem evens_map (ps : List Unpacked) : evens (ps.map numOf) = (evenIndexed ps).map numOf := by
  have := (zipIdx_parity (ps.map numOf) 0).2
  unfold evens; simp only [Nat.zero_add, Nat.one_mod] at this
  rw [this, (oddIndexed_map numOf ps).2]

/-! ### Exponent of the two groups -/

/-- The exponent a product contributes to `e_max`. -/
def stepExp (p : Unpacked) : Option ℤ := if p.m = 0 then none else some p.e

theorem joinExp_assoc (a b c : Option ℤ) : joinExp (joinExp a b) c = joinExp a (joinExp b c) := by
  cases a <;> cases b <;> cases c <;> simp [joinExp] <;> omega

theorem joinExp_comm (a b : Option ℤ) : joinExp a b = joinExp b a := by
  cases a <;> cases b <;> simp [joinExp] <;> omega

theorem joinExp_none (a : Option ℤ) : joinExp a none = a := by cases a <;> rfl

theorem maxExpStep_eq (acc : Option ℤ) (p : Unpacked) : maxExpStep acc p = joinExp acc (stepExp p) := by
  unfold maxExpStep stepExp
  by_cases h : p.m = 0
  · simp [h, joinExp_none]
  · cases acc <;> simp [h, joinExp]

theorem foldl_maxExpStep (l : List Unpacked) (acc : Option ℤ) :
    l.foldl maxExpStep acc = joinExp acc (maxExp l) := by
  induction l generalizing acc with
  | nil => simp [maxExp, joinExp_none]
  | cons p l ih =>
    simp only [List.foldl_cons, maxExp]
    rw [ih, ih (maxExpStep none p), maxExpStep_eq, maxExpStep_eq, joinExp_assoc]
    cases acc <;> rfl

theorem maxExp_cons (p : Unpacked) (l : List Unpacked) :
    maxExp (p :: l) = joinExp (stepExp p) (maxExp l) := by
  show List.foldl maxExpStep (maxExpStep none p) l = _
  rw [foldl_maxExpStep, maxExpStep_eq]; cases stepExp p <;> rfl

theorem maxExp_odd_even : ∀ l : List Unpacked,
    maxExp l = joinExp (maxExp (oddIndexed l)) (maxExp (evenIndexed l))
  | [] => rfl
  | [p] => by
    simp only [oddIndexed, evenIndexed, maxExp_cons, show maxExp ([] : List Unpacked) = none from rfl,
      joinExp_none]
  | p :: q :: r => by
    simp only [oddIndexed, evenIndexed, maxExp_cons]
    rw [maxExp_odd_even r]
    generalize stepExp p = x; generalize stepExp q = y
    generalize maxExp (oddIndexed r) = u; generalize maxExp (evenIndexed r) = v
    cases x <;> cases y <;> cases u <;> cases v <;> simp [joinExp] <;> omega

/-- One group's sum, shifted to the common `e_max` and RD. -/
theorem part_eq (neab : ℕ) (qs : List Unpacked) (e : ℤ) :
    ((groupPart (23 + neab) (qs.map numOf) e : ℤ) : ℚ) * pow2 (e - (23 + neab : ℕ)) =
      rdFrac (alignedSum neab qs).2 e (23 + neab) := by
  unfold groupPart
  rw [emax_eq]
  unfold alignedSum
  cases maxExp qs with
  | none => simp [rdGrid_zero]
  | some eq =>
    simp only
    rw [shiftRD_eq, sum_alignTrunc]

/-- Algorithm 2 computes the implementation's `S_acc` for `odd_even_grouping`. -/
theorem algorithm2_eq (P : Model) (hP : P.accumulation = .oddEvenGrouping) (ps : List Unpacked)
    (c : Unpacked) (hc : c.t ≤ P.late.sumFracBits) :
    algorithm2 (lateOf P) (ps.map numOf) (numOf c) = lateSum P (productSum P ps).1 (productSum P ps).2 c := by
  unfold algorithm2 productSum
  rw [hP, emax_eq, maxExp_odd_even, odds_map, evens_map]
  simp only
  have hO : (alignedSum P.neab (oddIndexed ps)).1 = maxExp (oddIndexed ps) := by
    unfold alignedSum; cases maxExp (oddIndexed ps) <;> rfl
  have hE : (alignedSum P.neab (evenIndexed ps)).1 = maxExp (evenIndexed ps) := by
    unfold alignedSum; cases maxExp (evenIndexed ps) <;> rfl
  rw [hO, hE]
  cases joinExp (maxExp (oddIndexed ps)) (maxExp (evenIndexed ps)) with
  | none =>
    simp only
    have := lateC_eq P none 0 c hc (fun _ => rfl)
    simpa using this
  | some e =>
    simp only
    rw [lateC_eq P (some e) _ c hc (by simp)]
    simp only [Option.getD_some, Rat.intCast_add, Rat.add_mul]
    rw [show (lateOf P).neab = P.neab from rfl, part_eq, part_eq]

end MatrixCore.Spec
