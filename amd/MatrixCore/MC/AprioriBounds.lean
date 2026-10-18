import MatrixCore.MC.Monotonicity

/-! # Error bounds from the inputs alone

Bounds on `|exact − d|` in terms of `Σ|p_ℓ| + |c|`, the number of products and `e_max`. -/

namespace MatrixCore

/-- `Σ|p_ℓ| + |c|`. -/
def Prepared.absSum (x : Prepared) : ℚ := sumQ (x.p.map fun p => absQ p.value) + absQ x.c.value

theorem absQ_sumQ_map_le (l : List α) (f : α → ℚ) :
    absQ (sumQ (l.map f)) ≤ sumQ (l.map fun a => absQ (f a)) := by
  have := absQ_sumQ_le (l.map f)
  rwa [List.map_map] at this

theorem Prepared.absQ_exact_le (x : Prepared) : absQ x.exact ≤ x.absSum := by
  unfold Prepared.exact Prepared.absSum
  have := absQ_add_le (sumQ (x.p.map Unpacked.value)) x.c.value
  have := absQ_sumQ_map_le x.p Unpacked.value
  grind

theorem sumQ_abs_nonneg (l : List α) (f : α → ℚ) : 0 ≤ sumQ (l.map fun a => absQ (f a)) := by
  induction l with
  | nil => exact Rat.le_refl
  | cons a l ih => simp only [List.map_cons, sumQ]; have := absQ_nonneg (f a); grind

theorem Prepared.absSum_nonneg (x : Prepared) : 0 ≤ x.absSum := by
  unfold Prepared.absSum
  have := sumQ_abs_nonneg x.p Unpacked.value
  have := absQ_nonneg x.c.value
  grind

/-! ## One `fl{·}` -/

theorem flBound_le (ftz : Bool) (x : ℚ) :
    flBound ftz x ≤ pow2 (-24) * absQ x + pow2 (-150) + (if ftz then pow2 (-126) else 0) := by
  have := halfUlp32_le x
  unfold flBound; grind

theorem normalizeRD_error (x : ℚ) : absQ (x - normalizeRD 31 x) ≤ pow2 (-31) * absQ x + pow2 (-157) := by
  have h157 := pow2_pos (-157)
  have hm := Rat.mul_nonneg (Rat.le_of_lt (pow2_pos (-31))) (absQ_nonneg x)
  by_cases hx : x = 0
  · subst hx
    have : normalizeRD 31 0 = 0 := by unfold normalizeRD; simp
    rw [this, show absQ ((0 : ℚ) - 0) = 0 by decide +kernel]; grind
  · have hlo := normalizeRD_le 31 x
    have hgt := normalizeRD_gt 31 hx
    have hax := absQ_pos hx
    obtain ⟨_, h2, h3⟩ := normExp_bounds hax
    have hD : absQ (x - normalizeRD 31 x) ≤ pow2 (normExp (absQ x) - ((31 : ℕ) : ℤ)) := by
      rw [absQ_le_iff]; constructor <;> grind
    refine Rat.le_trans hD ?_
    by_cases hn : normExp (absQ x) = -126
    · rw [hn]; have : (-126 : ℤ) - ((31 : ℕ) : ℤ) = -157 := by omega
      rw [this]; grind
    · have h := h2 hn
      have : pow2 (normExp (absQ x) - ((31 : ℕ) : ℤ)) = pow2 (-31) * pow2 (normExp (absQ x)) := by
        rw [← pow2_add]; congr 1; omega
      rw [this]
      have := Rat.mul_le_mul_of_nonneg_left h (Rat.le_of_lt (pow2_pos (-31)))
      grind

/-! ## SFMA and CDNA 1 -/

theorem correctRounding_apriori {P : Model} (hacc : P.accumulation = .correctRounding)
    (hov : P.productOverflow = false) (hs : P.subnormals = true)
    {x : BlockInput P} {t : BlockTrace P} (h : evalBlock x = .ok t) :
    absQ (t.prepared.exact - wordValue t.d) ≤ pow2 (-24) * t.prepared.absSum + pow2 (-150) := by
  have e1 := correctRounding_error hacc hov hs h
  have e2 := halfUlp32_le t.prepared.exact
  have e3 := Rat.mul_le_mul_of_nonneg_left t.prepared.absQ_exact_le (Rat.le_of_lt (pow2_pos (-24)))
  grind

/-! ## CDNA 3 -/

/-- `2^(e_max − 24)`, the alignment step; `0` when every product is zero. -/
def gridTerm : Option ℤ → ℚ
  | none => 0
  | some e => pow2 (e - 24)

theorem gridTerm_nonneg (o : Option ℤ) : 0 ≤ gridTerm o := by
  cases o
  · exact Rat.le_refl
  · exact Rat.le_of_lt (pow2_pos _)

theorem productSum_none_exact (P : Model) {ps : List Unpacked}
    (h : (productSum P ps).1 = none) : (productSum P ps).2 = 0 ∧ sumQ (ps.map Unpacked.value) = 0 := by
  unfold productSum at h ⊢
  cases hacc : P.accumulation <;> simp only [hacc] at h ⊢
  case oddEvenGrouping =>
    generalize hO : alignedSum P.padding (oddIndexed ps) = O at h ⊢
    generalize hE : alignedSum P.padding (evenIndexed ps) = E at h ⊢
    obtain ⟨eo, So⟩ := O
    obtain ⟨ee, Se⟩ := E
    simp only at h ⊢
    cases hj : joinExp eo ee with
    | some e => rw [hj] at h; simp at h
    | none =>
      have ho : eo = none := by cases eo <;> cases ee <;> simp [joinExp] at hj ⊢
      have he : ee = none := by cases eo <;> cases ee <;> simp [joinExp] at hj ⊢
      subst ho; subst he
      refine ⟨rfl, ?_⟩
      rw [← (sumQ_odd_even Unpacked.value ps).1, (alignedSum_none_exact hO).2,
        (alignedSum_none_exact hE).2]
      decide +kernel
  all_goals
    cases hs : alignedSum P.padding ps with
    | mk o S =>
      rw [hs] at h
      change o = none at h
      subst h
      exact alignedSum_none_exact hs

theorem lin_shifted {X a r t T s c P A B G q k : ℚ}
    (h1 : X ≤ a + r + t) (h2 : a ≤ B) (h3 : r ≤ q) (h4 : t ≤ (1 / 2147483648) * T + 2 * k)
    (h5 : T ≤ s + q + c) (h6 : s ≤ P + B) (h7 : q ≤ (1 / 4294967296) * c + k)
    (hA : A = P + c) (hB : B ≤ 18 * G) (hG : 0 ≤ G) (hc : 0 ≤ c) (hP : 0 ≤ P) (hk : 0 ≤ k) :
    X ≤ B + G + (1 / 1073741824) * A + 4 * k := by grind

theorem lin_output {D eS eD S A B G k : ℚ} (h1 : D ≤ eS + eD)
    (h2 : eS ≤ B + (1 / 1073741824) * A + k) (h3 : eD ≤ (1 / 16777216) * S + 64 * k)
    (h4 : S ≤ A + eS) (hB : B ≤ 19 * G) (hG : 0 ≤ G) (hA : 0 ≤ A) (hk : 0 ≤ k) :
    D ≤ (1 / 8388608) * A + B + G + 128 * k := by grind

/-- The error of `S_acc` from the inputs alone. -/
theorem alignedAccumulation_apriori {P : Model} (hL : LateModel P) (x : Prepared)
    {eC : ℤ} (hce : cExp P x.c = some eC) (h32 : C32 x.c.value eC) (hn : x.p.length ≤ 16) :
    absQ (x.exact - alignedAccumulation P x) ≤
      (x.p.length + 3) * gridTerm (productSum P x.p).1 + pow2 (-30) * x.absSum + pow2 (-156) := by
  have hA := x.absSum_nonneg
  have hAc : absQ x.c.value ≤ x.absSum := by
    unfold Prepared.absSum; have := sumQ_abs_nonneg x.p Unpacked.value; grind
  have hAp : sumQ (x.p.map fun p => absQ p.value) ≤ x.absSum := by
    unfold Prepared.absSum; have := absQ_nonneg x.c.value; grind
  have hsp := absQ_sumQ_map_le x.p Unpacked.value
  have hex : x.exact = sumQ (x.p.map Unpacked.value) + x.c.value := rfl
  have c30 : pow2 (-30) = 1 / 1073741824 := by decide +kernel
  have c31 : pow2 (-31) = 1 / 2147483648 := by decide +kernel
  have c32 : pow2 (-32) = 1 / 4294967296 := by decide +kernel
  have c156 : pow2 (-156) = 2 * pow2 (-157) := by decide +kernel
  have c158 : pow2 (-157) = 2 * pow2 (-158) := by decide +kernel
  have h158 := pow2_pos (-158)
  have hl0 : (0 : ℚ) ≤ x.p.length := by exact_mod_cast Nat.zero_le _
  have hl16 : (x.p.length : ℚ) ≤ 16 := by exact_mod_cast hn
  have hstep : pow2 (eC - ((32 : ℕ) : ℤ)) ≤ pow2 (-32) * absQ x.c.value + pow2 (-158) := by
    by_cases he : eC = -126
    · rw [he, show (-126 : ℤ) - ((32 : ℕ) : ℤ) = -158 by omega]
      have := Rat.mul_nonneg (Rat.le_of_lt (pow2_pos (-32))) (absQ_nonneg x.c.value); grind
    · have h := h32.ge he
      have : pow2 (eC - ((32 : ℕ) : ℤ)) = pow2 (-32) * pow2 eC := by rw [← pow2_add]; congr 1; omega
      rw [this]
      have := Rat.mul_le_mul_of_nonneg_left h (Rat.le_of_lt (pow2_pos (-32))); grind
  unfold alignedAccumulation lateSum
  simp only
  rw [hce]
  simp only
  cases hs : (productSum P x.p).1 with
  | none =>
    obtain ⟨h0, hz⟩ := productSum_none_exact P hs
    simp only [gridTerm]
    unfold shiftedSum
    rw [h0, hL.accMantissa, show rdMantissa 0 eC P.late.sumMantissaBits = 0 from rdGrid_zero _, hex, hz]
    have hN := normalizeRD_error (0 + x.c.value)
    rw [Rat.zero_add] at hN ⊢
    rw [c31] at hN
    generalize absQ (x.c.value - normalizeRD 31 x.c.value) = X at *
    generalize absQ x.c.value = ac at *
    rw [c30, c156, c158]
    rw [c158] at hN
    grind
  | some e =>
    have hpe := productSum_error P (show productSum P x.p = (some e, (productSum P x.p).2) by rw [← hs])
    rw [show e - ((23 + P.padding : ℕ) : ℤ) = e - 24 by rw [hL.padding]; rfl] at hpe
    simp only [gridTerm]
    have hG := pow2_pos (e - 24)
    by_cases hle : eC ≤ e
    · simp only [hle, ↓reduceIte]
      have hsc := shiftedC_error P (eMax := e) x.c (fun n h => by rw [hL.cMantissa]; exact hL.cut n h)
        (h32.lt)
      rw [hL.cMantissa] at hsc
      have t := absQ_add_le (sumQ (x.p.map Unpacked.value) - (productSum P x.p).2)
        (x.c.value - shiftedC P e eC x.c)
      rw [show sumQ (x.p.map Unpacked.value) - (productSum P x.p).2 + (x.c.value - shiftedC P e eC x.c) =
        x.exact - ((productSum P x.p).2 + shiftedC P e eC x.c) by rw [hex]; grind] at t
      have := Rat.mul_nonneg (Rat.le_of_lt (pow2_pos (-30))) hA
      have := pow2_pos (-156)
      grind
    · simp only [hle, ↓reduceIte]
      unfold shiftedSum
      rw [hL.accMantissa, hL.sumMantissa]
      show absQ (x.exact - normalizeRD 31 (rdGrid (productSum P x.p).2 (eC - ((32 : ℕ) : ℤ)) + x.c.value)) ≤ _
      generalize hS : (productSum P x.p).2 = S at hpe
      have ⟨r1, r2⟩ := rdGrid_bounds S (eC - ((32 : ℕ) : ℤ))
      generalize hT : rdGrid S (eC - ((32 : ℕ) : ℤ)) + x.c.value = T
      have hN := normalizeRD_error T
      have hTb : absQ T ≤ absQ S + pow2 (eC - ((32 : ℕ) : ℤ)) + absQ x.c.value := by
        have := absQ_rdGrid_le S (eC - ((32 : ℕ) : ℤ))
        have := absQ_add_le (rdGrid S (eC - ((32 : ℕ) : ℤ))) x.c.value
        rw [hT] at this; grind
      have hSb : absQ S ≤ sumQ (x.p.map fun p => absQ p.value) + (x.p.length + 2) * pow2 (e - 24) := by
        have := absQ_add_le (sumQ (x.p.map Unpacked.value)) (S - sumQ (x.p.map Unpacked.value))
        rw [show sumQ (x.p.map Unpacked.value) + (S - sumQ (x.p.map Unpacked.value)) = S by grind,
          absQ_sub_comm S] at this
        grind
      have hTA := Rat.mul_le_mul_of_nonneg_left hTb (Rat.le_of_lt (pow2_pos (-31)))
      have hlin : (x.p.length + 2) * pow2 (e - 24) ≤ 18 * pow2 (e - 24) :=
        Rat.mul_le_mul_of_nonneg_right (by grind) (Rat.le_of_lt hG)
      have t1 := absQ_add_le (sumQ (x.p.map Unpacked.value) - S) (S - rdGrid S (eC - ((32 : ℕ) : ℤ)))
      have t2 := absQ_add_le (sumQ (x.p.map Unpacked.value) - S + (S - rdGrid S (eC - ((32 : ℕ) : ℤ))))
        (T - normalizeRD 31 T)
      rw [show sumQ (x.p.map Unpacked.value) - S + (S - rdGrid S (eC - ((32 : ℕ) : ℤ))) +
        (T - normalizeRD 31 T) = x.exact - normalizeRD 31 T by rw [hex, ← hT]; grind] at t2
      have hrd : absQ (S - rdGrid S (eC - ((32 : ℕ) : ℤ))) ≤ pow2 (eC - ((32 : ℕ) : ℤ)) := by
        rw [absQ_le_iff]; constructor <;> grind
      have key := lin_shifted (X := absQ (x.exact - normalizeRD 31 T))
        (t := absQ (T - normalizeRD 31 T)) (T := absQ T) (c := absQ x.c.value)
        (B := (x.p.length + 2) * pow2 (e - 24)) (Rat.le_trans t2 (Rat.add_le_add_right.mpr t1)) hpe hrd
        (by rw [c31, c158] at hN; grind) hTb hSb (by rw [c32] at hstep; exact hstep) rfl hlin
        (Rat.le_of_lt hG) (absQ_nonneg _) (sumQ_abs_nonneg _ _) (Rat.le_of_lt h158)
      have hAdef : x.absSum = sumQ (x.p.map fun p => absQ p.value) + absQ x.c.value := rfl
      rw [c30, c156, c158, hAdef]
      grind

/-- CDNA 3 error bound from the inputs alone. -/
theorem aligned_apriori {P : Model} (hL : LateModel P)
    (hacc : P.accumulation = .globalAlignment ∨ P.accumulation = .oddEvenGrouping)
    (hsub : P.subnormals = true) {x : BlockInput P} {t : BlockTrace P} (h : evalBlock x = .ok t) :
    absQ (t.prepared.exact - wordValue t.d) ≤ pow2 (-23) * t.prepared.absSum +
      (t.prepared.p.length + 4) * gridTerm (productSum P t.prepared.p).1 + pow2 (-149) := by
  obtain ⟨hla, _, hp, hs, _⟩ := evalBlock_ok h
  obtain ⟨eC, hce, h32⟩ := c32_of_decode hL.cZero (prepare_c hp)
  have hn : t.prepared.p.length ≤ 16 := by
    have h1 := Prepared.p_length t.prepared
    have h2 : t.prepared.a.length = x.a.length := (prepare_bounded hp).1
    have := hL.nfma
    have : t.prepared.p.length ≤ t.prepared.a.length := by rw [h1]; exact Nat.min_le_left _ _
    omega
  have eS := alignedAccumulation_apriori hL t.prepared hce h32 hn
  rw [← accumulate_aligned hacc hs] at eS
  have eD := evalBlock_output_error h
  rw [hsub] at eD
  simp only [flBound, Bool.not_true, Bool.false_eq_true, ↓reduceIte, Rat.add_zero] at eD
  have hu := halfUlp32_le t.sAcc
  have hSa : absQ t.sAcc ≤ t.prepared.absSum + absQ (t.prepared.exact - t.sAcc) := by
    have := absQ_add_le t.prepared.exact (t.sAcc - t.prepared.exact)
    rw [show t.prepared.exact + (t.sAcc - t.prepared.exact) = t.sAcc by grind,
      absQ_sub_comm t.sAcc] at this
    have := t.prepared.absQ_exact_le
    grind
  have tri := absQ_sub_le t.prepared.exact t.sAcc (wordValue t.d)
  have hG := gridTerm_nonneg (productSum P t.prepared.p).1
  have hA := t.prepared.absSum_nonneg
  have hl16 : (t.prepared.p.length : ℚ) + 3 ≤ 19 := by
    have : (t.prepared.p.length : ℚ) ≤ 16 := by exact_mod_cast hn
    grind
  have hB := Rat.mul_le_mul_of_nonneg_right hl16 hG
  have c23 : pow2 (-23) = 1 / 8388608 := by decide +kernel
  have c30 : pow2 (-30) = 1 / 1073741824 := by decide +kernel
  have c24 : pow2 (-24) = 1 / 16777216 := by decide +kernel
  have c149 : pow2 (-149) = 128 * pow2 (-156) := by decide +kernel
  have c150 : pow2 (-150) = 64 * pow2 (-156) := by decide +kernel
  have key := lin_output (B := (t.prepared.p.length + 3) * gridTerm (productSum P t.prepared.p).1)
    tri (by rw [c30] at eS; exact eS) (by rw [c24, c150] at hu; exact Rat.le_trans eD hu) hSa hB hG hA
    (Rat.le_of_lt (pow2_pos _))
  rw [c23, c149]
  grind

/-! ## CDNA 2 -/

/-- Relative error growth of a pairwise sum with `h` levels of rounding. -/
def gam (h : ℕ) : ℚ := (1 + pow2 (-24)) ^ h - 1

/-- Absolute error count of a pairwise sum with `h` levels of rounding. -/
def kap : ℕ → ℚ
  | 0 => 0
  | h + 1 => 2 * (1 + pow2 (-24)) * kap h + 1

/-- Absolute error of one `fl{·}`, with or without flushing. -/
def eta (ftz : Bool) : ℚ := pow2 (-150) + if ftz then pow2 (-126) else 0

theorem one_le_pow_u (h : ℕ) : 1 ≤ (1 + pow2 (-24)) ^ h := by
  induction h with
  | zero => simp
  | succ h ih =>
    rw [Rat.pow_succ]
    have hu := pow2_pos (-24)
    have := Rat.mul_le_mul_of_nonneg_left (show (1 : ℚ) ≤ 1 + pow2 (-24) by grind) (by grind : (0 : ℚ) ≤ (1 + pow2 (-24)) ^ h)
    grind

theorem gam_nonneg (h : ℕ) : 0 ≤ gam h := by have := one_le_pow_u h; unfold gam; grind

theorem gam_succ (h : ℕ) : gam (h + 1) = gam h + pow2 (-24) * (1 + gam h) := by
  unfold gam; rw [Rat.pow_succ]; grind

theorem kap_nonneg : ∀ h, 0 ≤ kap h
  | 0 => Rat.le_refl
  | h + 1 => by
    have := kap_nonneg h
    have hu := pow2_pos (-24)
    have := Rat.mul_nonneg (show (0 : ℚ) ≤ 2 * (1 + pow2 (-24)) by grind) this
    simp only [kap]; grind

theorem eta_nonneg (ftz : Bool) : 0 ≤ eta ftz := by
  have := pow2_pos (-150); have := pow2_pos (-126); unfold eta; split <;> grind

theorem flValue_apriori {ftz : Bool} {x v : ℚ} (h : flValue ftz x = some v) :
    absQ (x - v) ≤ pow2 (-24) * absQ x + eta ftz := by
  have := flValue_error h
  have := flBound_le ftz x
  unfold eta; grind

theorem lin_node {X e1 e2 e3 s A1 A2 G K U E : ℚ}
    (hX : X ≤ e1 + e2 + e3) (h1 : e1 ≤ G * A1 + K * E) (h2 : e2 ≤ G * A2 + K * E)
    (h3 : e3 ≤ U * s + E) (hs : s ≤ A1 + A2 + e1 + e2) (hU : 0 ≤ U) :
    X ≤ (G + U * (1 + G)) * (A1 + A2) + (2 * (1 + U) * K + 1) * E := by
  have m1 := Rat.mul_le_mul_of_nonneg_left hs hU
  have m2 := Rat.mul_le_mul_of_nonneg_left (show e1 + e2 ≤ G * A1 + K * E + (G * A2 + K * E) by grind) hU
  grind

theorem sumQ_abs_take_drop (xs : List ℚ) (n : ℕ) :
    sumQ ((xs.take n).map absQ) + sumQ ((xs.drop n).map absQ) = sumQ (xs.map absQ) := by
  rw [← sumQ_append, ← List.map_append, List.take_append_drop]

theorem sumQ_absQ_nonneg (xs : List ℚ) : 0 ≤ sumQ (xs.map absQ) := by
  induction xs with
  | nil => exact Rat.le_refl
  | cons x xs ih => simp only [List.map_cons, sumQ]; have := absQ_nonneg x; grind

theorem pairwiseGroupSum_short (ftz : Bool) (d : ℕ) {xs : List ℚ} {t : ℚ} (hl : xs.length ≤ 1)
    (h : pairwiseGroupSum ftz d xs = some t) : absQ (sumQ xs - t) = 0 := by
  match xs, hl with
  | [], _ => simp [pairwiseGroupSum] at h; subst h; decide +kernel
  | [x], _ =>
    simp only [pairwiseGroupSum, Option.some.injEq] at h; subst h
    simp only [sumQ]
    rw [show ∀ y : ℚ, y + 0 - y = 0 from fun y => by grind]; decide +kernel

/-- Error bound of a pairwise sum with `h` levels of rounding, from its summands. -/
theorem pairwiseGroupSum_apriori (ftz : Bool) : ∀ (h d : ℕ) (xs : List ℚ) (t : ℚ), xs.length ≤ 2 ^ h →
    pairwiseGroupSum ftz d xs = some t →
      absQ (sumQ xs - t) ≤ gam h * sumQ (xs.map absQ) + kap h * eta ftz := by
  intro h
  induction h with
  | zero =>
    intro d xs t hl ht
    rw [pairwiseGroupSum_short ftz d (by simpa using hl) ht]
    exact Rat.add_nonneg (Rat.mul_nonneg (gam_nonneg 0) (sumQ_absQ_nonneg xs))
      (Rat.mul_nonneg (kap_nonneg 0) (eta_nonneg ftz))
  | succ h ih =>
    intro d xs t hl ht
    by_cases hshort : xs.length ≤ 1
    · rw [pairwiseGroupSum_short ftz d hshort ht]
      exact Rat.add_nonneg (Rat.mul_nonneg (gam_nonneg (h + 1)) (sumQ_absQ_nonneg xs))
        (Rat.mul_nonneg (kap_nonneg (h + 1)) (eta_nonneg ftz))
    · match xs, d, hshort, ht with
      | [], _, hs, _ => simp at hs
      | [_], _, hs, _ => simp at hs
      | x :: y :: rest, 0, _, ht => simp [pairwiseGroupSum] at ht
      | x :: y :: rest, d + 1, _, ht =>
        generalize hxs : x :: y :: rest = xs at ht hl ⊢
        have htr : pairwiseGroupSum ftz (d + 1) xs = (do
            let u ← pairwiseGroupSum ftz d (xs.take (xs.length / 2))
            let v ← pairwiseGroupSum ftz d (xs.drop (xs.length / 2))
            flValue ftz (u + v)) := by subst hxs; rfl
        rw [htr] at ht
        cases hu : pairwiseGroupSum ftz d (xs.take (xs.length / 2)) with
        | none => rw [hu] at ht; simp at ht
        | some u =>
          cases hv : pairwiseGroupSum ftz d (xs.drop (xs.length / 2)) with
          | none => rw [hu, hv] at ht; simp at ht
          | some v =>
            rw [hu, hv] at ht
            change flValue ftz (u + v) = some t at ht
            have hp : 2 ^ (h + 1) = 2 * 2 ^ h := by rw [Nat.pow_succ]; omega
            have l1 : (xs.take (xs.length / 2)).length ≤ 2 ^ h := by simp; omega
            have l2 : (xs.drop (xs.length / 2)).length ≤ 2 ^ h := by simp; omega
            have e1 := ih d _ u l1 hu
            have e2 := ih d _ v l2 hv
            have e3 := flValue_apriori ht
            have hs := sumQ_take_drop xs (xs.length / 2)
            have ha := sumQ_abs_take_drop xs (xs.length / 2)
            have b1 := absQ_sumQ_le (xs.take (xs.length / 2))
            have b2 := absQ_sumQ_le (xs.drop (xs.length / 2))
            have suv : absQ (u + v) ≤ sumQ ((xs.take (xs.length / 2)).map absQ) +
                sumQ ((xs.drop (xs.length / 2)).map absQ) + absQ (sumQ (xs.take (xs.length / 2)) - u) +
                absQ (sumQ (xs.drop (xs.length / 2)) - v) := by
              have := absQ_add_le u v
              have := absQ_sub_le u (sumQ (xs.take (xs.length / 2))) 0
              have q1 := absQ_add_le (sumQ (xs.take (xs.length / 2)))
                (u - sumQ (xs.take (xs.length / 2)))
              have q2 := absQ_add_le (sumQ (xs.drop (xs.length / 2)))
                (v - sumQ (xs.drop (xs.length / 2)))
              rw [show sumQ (xs.take (xs.length / 2)) + (u - sumQ (xs.take (xs.length / 2))) = u by grind,
                absQ_sub_comm u] at q1
              rw [show sumQ (xs.drop (xs.length / 2)) + (v - sumQ (xs.drop (xs.length / 2))) = v by grind,
                absQ_sub_comm v] at q2
              grind
            have tri : absQ (sumQ xs - t) ≤ absQ (sumQ (xs.take (xs.length / 2)) - u) +
                absQ (sumQ (xs.drop (xs.length / 2)) - v) + absQ (u + v - t) := by
              have := absQ_add_le (sumQ (xs.take (xs.length / 2)) - u + (sumQ (xs.drop (xs.length / 2)) - v))
                (u + v - t)
              have := absQ_add_le (sumQ (xs.take (xs.length / 2)) - u) (sumQ (xs.drop (xs.length / 2)) - v)
              rw [show sumQ (xs.take (xs.length / 2)) - u + (sumQ (xs.drop (xs.length / 2)) - v) +
                (u + v - t) = sumQ xs - t by grind] at *
              grind
            have key := lin_node tri e1 e2 e3 suv (Rat.le_of_lt (pow2_pos (-24)))
            rw [gam_succ, show kap (h + 1) = 2 * (1 + pow2 (-24)) * kap h + 1 from rfl, ← ha]
            exact key

theorem mapM_flValue_abs (ftz : Bool) : ∀ (l : List Unpacked) (ps : List ℚ),
    l.mapM (fun p => flValue ftz p.value) = some ps →
      sumQ (ps.map absQ) ≤ sumQ (l.map fun p => absQ p.value) + sumQ (l.map fun p => flBound ftz p.value)
  | [], ps, h => by simp at h; subst h; simp only [List.map_nil, sumQ]; grind
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
        have e2 := mapM_flValue_abs ftz l qs hl
        have := absQ_add_le p.value (q - p.value)
        rw [show p.value + (q - p.value) = q by grind, absQ_sub_comm q] at this
        simp only [List.map_cons, sumQ]
        grind

theorem sumQ_flBound_le (ftz : Bool) (l : List Unpacked) :
    sumQ (l.map fun p => flBound ftz p.value) ≤
      pow2 (-24) * sumQ (l.map fun p => absQ p.value) + l.length * eta ftz := by
  induction l with
  | nil =>
    have := eta_nonneg ftz
    simp only [List.map_nil, sumQ, List.length_nil]
    rw [show ((0 : ℕ) : ℚ) = 0 from rfl]; grind
  | cons p l ih =>
    have := flBound_le ftz p.value
    simp only [List.map_cons, sumQ, List.length_cons]
    rw [Rat.natCast_add, show ((1 : ℕ) : ℚ) = 1 from rfl]
    unfold eta at *
    grind

theorem lin_pairwise {X F d1 d2 d3 Pp C Q Tt Sv E k L : ℚ}
    (hX : X ≤ F + d1 + d2 + d3) (h1 : d1 ≤ (1 / 16777216) * Pp + L * E)
    (hQ : Q ≤ Pp + ((1 / 16777216) * Pp + L * E))
    (h2 : d2 ≤ (33554433 / 281474976710656) * Q + (3 + 1 / 8388608) * E)
    (hT : Tt ≤ Q + d2) (hS : Sv ≤ C + Tt) (h3 : d3 ≤ (1 / 16777216) * Sv + E)
    (hL : L ≤ 4) (hE : 0 ≤ E) (hEk : E ≤ k) (hP : 0 ≤ Pp) (hC : 0 ≤ C) :
    X ≤ F + (1 / 2097152) * (Pp + C) + 32 * k := by
  have m1 := Rat.mul_le_mul_of_nonneg_right hL hE
  grind

/-- CDNA 2 error bound (`N_FMA ≤ 4`) from the inputs after flushing subnormals. -/
theorem pairwise_apriori {P : Model} (hacc : P.accumulation = .pairWiseSum) (hn : P.nfma ≤ 4)
    {x : BlockInput P} {t : BlockTrace P} (h : evalBlock x = .ok t) :
    absQ (t.prepared.exact - wordValue t.d) ≤
      absQ (t.prepared.exact - (if P.subnormals then t.prepared else t.prepared.flushed).exact) +
        pow2 (-21) * (if P.subnormals then t.prepared else t.prepared.flushed).absSum + pow2 (-120) := by
  obtain ⟨hla, _, hp, hacc', _⟩ := evalBlock_ok h
  have hs := accumulate_pairwise hacc hacc'
  have eD := evalBlock_output_error h
  have eDb := flBound_le (!P.subnormals) t.sAcc
  have hlen : t.prepared.p.length ≤ 4 := by
    have h1 := Prepared.p_length t.prepared
    have h2 : t.prepared.a.length = x.a.length := (prepare_bounded hp).1
    have : t.prepared.p.length ≤ t.prepared.a.length := by rw [h1]; exact Nat.min_le_left _ _
    omega
  have hlen' : (if P.subnormals then t.prepared else t.prepared.flushed).p.length ≤ 4 := by
    split
    · exact hlen
    · simp only [Prepared.p, Prepared.flushed, List.length_zipWith, List.length_map]
      simp only [Prepared.p, List.length_zipWith] at hlen
      exact hlen
  unfold pairwiseSum at hs
  dsimp only at hs
  generalize (if P.subnormals then t.prepared else t.prepared.flushed) = x' at hs hlen' ⊢
  have eta' : eta (!P.subnormals) = pow2 (-150) + if (!P.subnormals) then pow2 (-126) else 0 := rfl
  generalize (!P.subnormals) = ftz at hs eD eDb eta' ⊢
  cases hm : x'.p.mapM fun p => flValue ftz p.value with
  | none => rw [hm] at hs; simp at hs
  | some ps =>
    rw [hm] at hs
    cases ht : pairwiseGroupSum ftz ps.length ps with
    | none => simp [ht] at hs
    | some tt =>
      change (pairwiseGroupSum ftz ps.length ps).bind (fun t => some (x'.c.value + t)) = some t.sAcc at hs
      rw [ht] at hs
      simp only [Option.bind_some, Option.some.injEq] at hs
      have hpl : ps.length = x'.p.length := mapM_length_option hm
      have e1 := mapM_flValue_error ftz x'.p ps hm
      have e1b := sumQ_flBound_le ftz x'.p
      have eQ := mapM_flValue_abs ftz x'.p ps hm
      have e2 := pairwiseGroupSum_apriori ftz 2 ps.length ps tt (by rw [hpl]; simpa using hlen') ht
      have g2 : gam 2 = 33554433 / 281474976710656 := by unfold gam; decide +kernel
      have k2 : kap 2 = 3 + 1 / 8388608 := by simp only [kap]; decide +kernel
      have u24 : pow2 (-24) = 1 / 16777216 := by decide +kernel
      have c21 : pow2 (-21) = 1 / 2097152 := by decide +kernel
      have c120 : pow2 (-120) = 32 * pow2 (-125) := by decide +kernel
      have hEk : eta ftz ≤ pow2 (-125) := by
        unfold eta; cases ftz <;> simp <;> decide +kernel
      have hE := eta_nonneg ftz
      have hTt : absQ tt ≤ sumQ (ps.map absQ) + absQ (sumQ ps - tt) := by
        have := absQ_add_le (sumQ ps) (tt - sumQ ps)
        rw [show sumQ ps + (tt - sumQ ps) = tt by grind, absQ_sub_comm tt] at this
        have := absQ_sumQ_le ps
        grind
      have hSv : absQ t.sAcc ≤ absQ x'.c.value + absQ tt := by rw [← hs]; exact absQ_add_le _ _
      have hex' : x'.exact = sumQ (x'.p.map Unpacked.value) + x'.c.value := rfl
      have hX : absQ (t.prepared.exact - wordValue t.d) ≤ absQ (t.prepared.exact - x'.exact) +
          absQ (sumQ (x'.p.map Unpacked.value) - sumQ ps) + absQ (sumQ ps - tt) +
          absQ (t.sAcc - wordValue t.d) := by
        have a1 := absQ_add_le (t.prepared.exact - x'.exact) (sumQ (x'.p.map Unpacked.value) - sumQ ps)
        have a2 := absQ_add_le (t.prepared.exact - x'.exact + (sumQ (x'.p.map Unpacked.value) - sumQ ps))
          (sumQ ps - tt)
        have a3 := absQ_add_le (t.prepared.exact - x'.exact + (sumQ (x'.p.map Unpacked.value) - sumQ ps) +
          (sumQ ps - tt)) (t.sAcc - wordValue t.d)
        rw [show t.prepared.exact - x'.exact + (sumQ (x'.p.map Unpacked.value) - sumQ ps) +
          (sumQ ps - tt) + (t.sAcc - wordValue t.d) = t.prepared.exact - wordValue t.d by
            rw [hex', ← hs]; grind] at a3
        grind
      rw [g2, k2] at e2
      rw [u24] at e1b eDb
      have h3 : absQ (t.sAcc - wordValue t.d) ≤ 1 / 16777216 * absQ t.sAcc + eta ftz := by
        have := Rat.le_trans eD eDb; rw [eta']; grind
      have key := lin_pairwise (L := (x'.p.length : ℚ)) (E := eta ftz) (k := pow2 (-125))
        (Pp := sumQ (x'.p.map fun p => absQ p.value)) (C := absQ x'.c.value) hX
        (Rat.le_trans e1 e1b) (Rat.le_trans eQ (Rat.add_le_add_left.mpr e1b)) e2 hTt hSv h3
        (by exact_mod_cast hlen') hE hEk (sumQ_abs_nonneg _ _) (absQ_nonneg _)
      have hAs : x'.absSum = sumQ (x'.p.map fun p => absQ p.value) + absQ x'.c.value := rfl
      rw [c21, c120, hAs]
      exact key

end MatrixCore
