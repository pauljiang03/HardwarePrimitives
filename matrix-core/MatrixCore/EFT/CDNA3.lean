import MatrixCore.EFT.Encoded

/-! # CDNA 3: what the Matrix Core's output buys

With `D` the block's output, the Matrix Core's `S_acc` is the high sum plus what its alignment
keeps of the low parts, so the overlap is that kept part plus the final rounding error. -/

namespace MatrixCore

/-! ## Nested grids -/

theorem rdGrid_add_onGrid {h : ℚ} {g : ℤ} (hh : OnGrid h g) (y : ℚ) :
    rdGrid (h + y) g = h + rdGrid y g := by
  obtain ⟨k, rfl⟩ := hh
  unfold rdGrid
  have e : ((k : ℚ) * pow2 g + y) / pow2 g = (k : ℚ) + y / pow2 g := by
    rw [div_pow2, div_pow2, Rat.add_mul, Rat.mul_assoc, ← pow2_add,
      show g + -g = 0 by omega, pow2_zero, Rat.mul_one]
  have hf : ((k : ℚ) + y / pow2 g).floor = k + (y / pow2 g).floor := by
    rw [floor_eq_iff]
    have := floor_bounds (y / pow2 g)
    push_cast
    constructor <;> grind
  rw [e, hf]
  push_cast
  grind

theorem rdGrid_split (x : ℚ) {g q : ℤ} (hgq : g ≤ q) :
    rdGrid x g = rdGrid x q + rdGrid (x - rdGrid x q) g := by
  have := rdGrid_add_onGrid ((rdGrid_onGrid x q).mono hgq) (x - rdGrid x q)
  rwa [show rdGrid x q + (x - rdGrid x q) = x by grind] at this

theorem truncGrid_of_nonneg {y : ℚ} (hy : 0 ≤ y) (g : ℤ) : truncGrid y g = rdGrid y g := by
  unfold truncGrid rdGrid; rw [if_neg (by grind)]

theorem truncGrid_of_nonpos {y : ℚ} (hy : y ≤ 0) (g : ℤ) : truncGrid y g = -rdGrid (-y) g := by
  by_cases h : y < 0
  · unfold truncGrid rdGrid; rw [if_pos h]
  · have : y = 0 := by grind
    subst this
    rw [truncGrid_zero, Rat.neg_zero, rdGrid_zero, Rat.neg_zero]

theorem truncGrid_split (x : ℚ) {g q : ℤ} (hgq : g ≤ q) :
    truncGrid x g = truncGrid x q + truncGrid (x - truncGrid x q) g := by
  by_cases hx : 0 ≤ x
  · have h1 := rdGrid_bounds x q
    rw [truncGrid_of_nonneg hx, truncGrid_of_nonneg hx, truncGrid_of_nonneg (by grind)]
    exact rdGrid_split x hgq
  · have hx' : x ≤ 0 := by grind
    have h1 := rdGrid_bounds (-x) q
    rw [truncGrid_of_nonpos hx', truncGrid_of_nonpos hx', truncGrid_of_nonpos (by grind),
      rdGrid_split (-x) hgq, show -(x - -rdGrid (-x) q) = -x - rdGrid (-x) q by grind]
    grind

theorem truncGrid_eq_zero {x : ℚ} {g : ℤ} (h : absQ x < pow2 g) : truncGrid x g = 0 :=
  onGrid_eq_zero (truncGrid_onGrid x g) (Std.lt_of_le_of_lt (truncGrid_bounds x g).1 h)

theorem rdGrid_nonneg {x : ℚ} (h : 0 ≤ x) (g : ℤ) : 0 ≤ rdGrid x g := le_rdGrid (OnGrid.zero g) h

theorem rdGrid_eq_zero {x : ℚ} {g : ℤ} (h0 : 0 ≤ x) (h : x < pow2 g) : rdGrid x g = 0 := by
  apply onGrid_eq_zero (rdGrid_onGrid x g)
  rw [absQ_of_nonneg (rdGrid_nonneg h0 g)]
  exact Std.lt_of_le_of_lt (rdGrid_bounds x g).1 h

theorem rdGrid_abs_le (y : ℚ) (g : ℤ) : absQ (rdGrid y g) ≤ absQ y + pow2 g := by
  have := rdGrid_bounds y g
  have := pow2_pos g
  rw [absQ_le_iff]
  unfold absQ; split <;> constructor <;> grind

/-! ## The alignment applied to other values -/

/-- The CDNA 3 alignment of the products `ps` applied to values `xs` at the same positions. -/
def alignAt (padding : ℕ) (eG : Option ℤ) (xs : List ℚ) : ℚ :=
  match eG with
  | none => 0
  | some e => sumQ (xs.map fun x => truncMantissa x e (23 + padding))

def productSumAt (P : Model) (ps : List Unpacked) (xs : List ℚ) : ℚ :=
  match P.accumulation with
  | .oddEvenGrouping =>
    match joinExp (maxExp (oddIndexed ps)) (maxExp (evenIndexed ps)) with
    | none => 0
    | some e =>
      rdMantissa (alignAt P.padding (maxExp (oddIndexed ps)) (oddIndexed xs)) e (23 + P.padding) +
        rdMantissa (alignAt P.padding (maxExp (evenIndexed ps)) (evenIndexed xs)) e (23 + P.padding)
  | _ => alignAt P.padding (maxExp ps) xs

theorem oddEvenIndexed_map (f : α → β) : ∀ l : List α,
    oddIndexed (l.map f) = (oddIndexed l).map f ∧ evenIndexed (l.map f) = (evenIndexed l).map f
  | [] => by simp [oddIndexed, evenIndexed]
  | [_] => by simp [oddIndexed, evenIndexed]
  | a :: b :: r => by
    obtain ⟨h1, h2⟩ := oddEvenIndexed_map f r
    simp [oddIndexed, evenIndexed, h1, h2]

theorem alignedSum_eq (padding : ℕ) (ps : List Unpacked) :
    alignedSum padding ps = (maxExp ps, alignAt padding (maxExp ps) (ps.map Unpacked.value)) := by
  cases h : maxExp ps <;> simp [alignedSum, alignAt, h, Function.comp_def]

theorem productSum_eq (P : Model) (ps : List Unpacked) :
    productSum P ps = (alignExp P ps, productSumAt P ps (ps.map Unpacked.value)) := by
  unfold productSum alignExp productSumAt
  cases P.accumulation <;> simp only [alignedSum_eq]
  rw [(oddEvenIndexed_map Unpacked.value ps).1, (oddEvenIndexed_map Unpacked.value ps).2]
  cases joinExp (maxExp (oddIndexed ps)) (maxExp (evenIndexed ps)) <;> rfl

theorem joinExp_some {a b : Option ℤ} {e : ℤ} (h : joinExp a b = some e) :
    (∀ v, a = some v → v ≤ e) ∧ (∀ v, b = some v → v ≤ e) := by
  cases a <;> cases b <;> simp [joinExp] at h ⊢ <;> omega

theorem joinExp_none {a b : Option ℤ} (h : joinExp a b = none) : a = none ∧ b = none := by
  cases a <;> cases b <;> simp [joinExp] at h ⊢

theorem sumQ_trunc_of_zero {ps : List Unpacked} (h : ∀ p ∈ ps, p.m = 0) (q : ℤ) :
    sumQ (ps.map fun p => truncGrid p.value q) = 0 := by
  rw [← sum_of_zero h]
  congr 1
  apply List.map_congr_left
  intro p hp
  rw [(Unpacked.value_eq_zero_iff p).mpr (h p hp), truncGrid_zero]

theorem alignAt_split (padding : ℕ) (ps : List Unpacked) (q : ℤ)
    (hq : ∀ e, maxExp ps = some e → e - (23 + padding : ℕ) ≤ q) :
    alignAt padding (maxExp ps) (ps.map Unpacked.value) =
      sumQ (ps.map fun p => truncGrid p.value q) +
        alignAt padding (maxExp ps) (ps.map fun p => p.value - truncGrid p.value q) := by
  cases h : maxExp ps with
  | none =>
    simp only [alignAt, sumQ_trunc_of_zero (maxExp_none h) q]
    grind
  | some e =>
    simp only [alignAt, List.map_map]
    rw [← sumQ_map_add]
    congr 1
    apply List.map_congr_left
    intro p _
    exact truncGrid_split p.value (hq e h)

/-- The products' sum is their high sum plus the alignment applied to their low parts. -/
theorem productSumAt_split (P : Model) (ps : List Unpacked) (q : ℤ)
    (hq : ∀ e, alignExp P ps = some e → e - (23 + P.padding : ℕ) ≤ q) :
    productSumAt P ps (ps.map Unpacked.value) =
      sumQ (ps.map fun p => truncGrid p.value q) +
        productSumAt P ps (ps.map fun p => p.value - truncGrid p.value q) := by
  unfold productSumAt
  unfold alignExp at hq
  cases hacc : P.accumulation <;> simp only [hacc] at hq ⊢
  case oddEvenGrouping =>
    rw [(oddEvenIndexed_map Unpacked.value ps).1, (oddEvenIndexed_map Unpacked.value ps).2,
      (oddEvenIndexed_map (fun p => p.value - truncGrid p.value q) ps).1,
      (oddEvenIndexed_map (fun p => p.value - truncGrid p.value q) ps).2]
    have hsum := (sumQ_odd_even (fun p : Unpacked => truncGrid p.value q) ps).1
    cases hj : joinExp (maxExp (oddIndexed ps)) (maxExp (evenIndexed ps)) with
    | none =>
      obtain ⟨ho, he⟩ := joinExp_none hj
      rw [← hsum, sumQ_trunc_of_zero (maxExp_none ho), sumQ_trunc_of_zero (maxExp_none he)]
      grind
    | some e =>
      have hle := hq e hj
      obtain ⟨hjo, hje⟩ := joinExp_some hj
      simp only
      rw [alignAt_split _ (oddIndexed ps) q (fun v hv => by have := hjo v hv; omega),
        alignAt_split _ (evenIndexed ps) q (fun v hv => by have := hje v hv; omega)]
      have hg : ∀ l : List Unpacked,
          OnGrid (sumQ (l.map fun p => truncGrid p.value q)) (e - ((23 + P.padding : ℕ) : ℤ)) := by
        intro l
        apply onGrid_sumQ
        intro v hv
        simp only [List.mem_map] at hv
        obtain ⟨p, _, rfl⟩ := hv
        exact (truncGrid_onGrid _ _).mono hle
      simp only [rdMantissa]
      rw [rdGrid_add_onGrid (hg _), rdGrid_add_onGrid (hg _), ← hsum]
      grind
  all_goals exact alignAt_split _ _ _ hq

theorem alignAt_abs_le (padding : ℕ) (eG : Option ℤ) (xs : List ℚ) {B : ℚ} (hB : 0 ≤ B)
    (h : ∀ x ∈ xs, absQ x ≤ B) : absQ (alignAt padding eG xs) ≤ xs.length * B := by
  cases eG with
  | none =>
    simp only [alignAt, show absQ (0 : ℚ) = 0 from rfl]
    exact Rat.mul_nonneg (by exact_mod_cast Nat.zero_le _) hB
  | some e =>
    simp only [alignAt]
    refine Rat.le_trans (absQ_sumQ_le _) ?_
    rw [List.map_map]
    exact sumQ_map_le _ _ B fun x hx =>
      Rat.le_trans (truncGrid_bounds x _).1 (h x hx)

theorem productSumAt_abs_le (P : Model) (ps : List Unpacked) (xs : List ℚ) {B : ℚ} (hB : 0 ≤ B)
    (h : ∀ x ∈ xs, absQ x ≤ B)
    (hg : ∀ e, alignExp P ps = some e → pow2 (e - (23 + P.padding : ℕ)) ≤ B) :
    absQ (productSumAt P ps xs) ≤ ((xs.length : ℚ) + 2) * B := by
  have h2 : (xs.length : ℚ) * B ≤ ((xs.length : ℚ) + 2) * B :=
    Rat.mul_le_mul_of_nonneg_right (by grind) hB
  unfold productSumAt
  unfold alignExp at hg
  cases hacc : P.accumulation <;> simp only [hacc] at hg ⊢
  case oddEvenGrouping =>
    cases hj : joinExp (maxExp (oddIndexed ps)) (maxExp (evenIndexed ps)) with
    | none =>
      simp only [show absQ (0 : ℚ) = 0 from rfl]
      have : (0 : ℚ) ≤ (xs.length : ℚ) + 2 := by
        have : (0 : ℚ) ≤ xs.length := by exact_mod_cast Nat.zero_le _
        grind
      exact Rat.mul_nonneg this hB
    | some e =>
      simp only
      have hge := hg e hj
      have ho := alignAt_abs_le P.padding (maxExp (oddIndexed ps)) (oddIndexed xs) hB
        (fun x hx => h x (oddIndexed_subset xs x hx))
      have he := alignAt_abs_le P.padding (maxExp (evenIndexed ps)) (evenIndexed xs) hB
        (fun x hx => h x (evenIndexed_subset xs x hx))
      have r1 := rdGrid_abs_le (alignAt P.padding (maxExp (oddIndexed ps)) (oddIndexed xs))
        (e - ((23 + P.padding : ℕ) : ℤ))
      have r2 := rdGrid_abs_le (alignAt P.padding (maxExp (evenIndexed ps)) (evenIndexed xs))
        (e - ((23 + P.padding : ℕ) : ℤ))
      have hl := (sumQ_odd_even (fun _ => (0 : ℚ)) xs).2
      have hl' : ((oddIndexed xs).length : ℚ) + (evenIndexed xs).length = xs.length := by
        exact_mod_cast hl
      have t := absQ_add_le
        (rdGrid (alignAt P.padding (maxExp (oddIndexed ps)) (oddIndexed xs))
          (e - ((23 + P.padding : ℕ) : ℤ)))
        (rdGrid (alignAt P.padding (maxExp (evenIndexed ps)) (evenIndexed xs))
          (e - ((23 + P.padding : ℕ) : ℤ)))
      have hexp : ((xs.length : ℚ) + 2) * B =
          ((oddIndexed xs).length : ℚ) * B + ((evenIndexed xs).length : ℚ) * B + B + B := by
        rw [← hl']; grind
      rw [hexp]
      grind
  all_goals exact Rat.le_trans (alignAt_abs_le _ _ _ hB h) h2

theorem productSum_onGrid (P : Model) (ps : List Unpacked) {e : ℤ} (he : alignExp P ps = some e) :
    OnGrid (productSum P ps).2 (e - (23 + P.padding : ℕ)) := by
  rw [productSum_eq]
  unfold productSumAt
  unfold alignExp at he
  cases hacc : P.accumulation <;> simp only [hacc] at he ⊢
  case oddEvenGrouping =>
    rw [he]
    exact (rdGrid_onGrid _ _).add (rdGrid_onGrid _ _)
  all_goals
    rw [he]
    apply onGrid_sumQ
    intro v hv
    simp only [List.mem_map] at hv
    obtain ⟨p, _, rfl⟩ := hv
    exact truncGrid_onGrid _ _

/-! ## What the Matrix Core keeps of the low parts -/

def lateKept (P : Model) (px : Prepared) (eC : ℤ) (A εc : ℚ) : ℚ :=
  let T := rdMantissa (productSum P px.p).2 eC P.late.sumMantissaBits + px.c.value
  let X := rdMantissa A eC P.late.sumMantissaBits + εc
  if T = 0 then X else rdGrid X (normExp (absQ T) - P.late.accMantissaBits)

/-- What the Matrix Core keeps of the low parts: its alignment, `s'_c`, or late normalization. -/
def keptLow (P : Model) (px : Prepared) (q : ℤ) : ℚ :=
  let A := productSumAt P px.p (px.p.map fun p => p.value - truncGrid p.value q)
  let εc := px.c.value - (cRule P px).high px.c.value q
  match alignExp P px.p, cExp P px.c with
  | _, none => A
  | some e, some eC =>
    if eC ≤ e then A + (if cDropped P e eC then 0 else rdMantissa εc e P.late.cMantissaBits)
    else lateKept P px eC A εc
  | none, some eC => lateKept P px eC A εc

theorem shiftedC_eq (P : Model) (eMax eC : ℤ) (c : Unpacked) :
    shiftedC P eMax eC c =
      if cDropped P eMax eC then 0 else rdMantissa c.value eMax P.late.cMantissaBits := by
  unfold shiftedC cDropped
  cases P.late.cCutoff with
  | none => rfl
  | some n => by_cases h : eMax - eC > (n : ℤ) <;> simp [h]

theorem cDropped_small (P : Model) {e eC : ℤ}
    (hcut : ∀ n, P.late.cCutoff = some n → P.late.cMantissaBits ≤ n)
    (hd : cDropped P e eC = true) : eC + 1 ≤ e - P.late.cMantissaBits := by
  unfold cDropped at hd
  cases hn : P.late.cCutoff with
  | none => rw [hn] at hd; cases hd
  | some n =>
    rw [hn] at hd
    have := hcut n hn
    simp only [decide_eq_true_eq] at hd
    omega

theorem normalizeRD_grid_le {k : ℕ} (hk : 23 ≤ k) {T : ℚ} (hT : T ≠ 0) {w : F32}
    (hw : rne32 (normalizeRD k T) = some w) :
    normExp (absQ T) - k ≤ ulpExp32 (rneValue (normalizeRD k T)) := by
  have ha := absQ_pos hT
  obtain ⟨_, hnorm, hemin⟩ := normExp_bounds ha
  by_cases h126 : normExp (absQ T) = -126
  · have := ulpExp32_ge (rneValue (normalizeRD k T)); omega
  have hlo := hnorm h126
  generalize hE : normExp (absQ T) = E at hlo hemin h126 ⊢
  have hS : normalizeRD k T = rdGrid T (E - k) := by
    unfold normalizeRD; rw [if_neg hT, hE]
  rw [hS] at hw ⊢
  have hgrid : OnGrid (pow2 E) (E - k) := onGrid_pow2 E k
  have hbig : pow2 E ≤ absQ (rdGrid T (E - k)) := by
    by_cases hpos : 0 < T
    · rw [absQ_of_nonneg (Rat.le_of_lt hpos)] at hlo
      have := le_rdGrid hgrid hlo
      rw [absQ_of_nonneg (Rat.le_trans (Rat.le_of_lt (pow2_pos E)) this)]
      exact this
    · have hneg : T < 0 := by grind
      rw [absQ_of_neg hneg] at hlo
      have := (rdGrid_bounds T (E - k)).1
      have hp := pow2_pos E
      rw [absQ_of_neg (by grind)]
      grind
  have hE127 : E ≤ 127 := by
    have h1 := (rne32_isSome_iff (rdGrid T (E - k))).mp (by rw [hw]; rfl)
    have h2 : overflowThreshold32 < pow2 128 := by decide +kernel
    have h3 := pow2_lt_iff.mp (Std.lt_of_le_of_lt hbig (Std.lt_of_lt_of_le h1 (Rat.le_of_lt h2)))
    omega
  have hfin : FiniteValue32 (pow2 E) :=
    ⟨8388608, E, hemin, hE127, by decide, by
      rw [show (8388608 : ℤ) = ((2 ^ 23 : ℕ) : ℤ) by rfl, Rat.intCast_natCast, ← pow2_natCast,
        ← pow2_add]; congr 1; omega⟩
  have hR : pow2 E ≤ absQ (rneValue (rdGrid T (E - k))) := by
    by_cases hpos : 0 ≤ rdGrid T (E - k)
    · rw [absQ_of_nonneg hpos] at hbig
      have := rneValue_mono hbig
      rw [rneValue_of_finiteValue32 hfin] at this
      rw [absQ_of_nonneg (Rat.le_trans (Rat.le_of_lt (pow2_pos E)) this)]
      exact this
    · have hneg : rdGrid T (E - k) < 0 := by grind
      rw [absQ_of_neg hneg] at hbig
      have := rneValue_mono (show rdGrid T (E - k) ≤ -pow2 E by grind)
      rw [rneValue_of_finiteValue32 hfin.neg] at this
      have hp := pow2_pos E
      rw [absQ_of_neg (by grind)]
      grind
  have hne : rneValue (rdGrid T (E - k)) ≠ 0 := by
    intro h0; rw [h0, show absQ (0 : ℚ) = 0 from rfl] at hR
    exact Rat.not_le.mpr (pow2_pos E) hR
  have hm := normExp_mono (pow2_pos E) hR
  rw [normExp_pow2 hemin] at hm
  unfold ulpExp32
  rw [if_neg hne]
  omega

/-! ## The overlap on CDNA 3 -/

theorem eftCutoff_aligned {P : Model}
    (hacc : P.accumulation = .globalAlignment ∨ P.accumulation = .oddEvenGrouping)
    (px : Prepared) (d : ℚ) :
    eftCutoff P px d =
      match hwGrid P px with
      | some g => max (ulpExp32 d) g
      | none => ulpExp32 d := by
  unfold eftCutoff; rcases hacc with h | h <;> rw [h] <;> rfl

theorem cRule_aligned {P : Model}
    (hacc : P.accumulation = .globalAlignment ∨ P.accumulation = .oddEvenGrouping)
    (px : Prepared) :
    cRule P px =
      match alignExp P px.p, cExp P px.c with
      | some e, some eC => if eC ≤ e ∧ cDropped P e eC = false then .rd else .trunc
      | _, _ => .trunc := by
  unfold cRule; rcases hacc with h | h <;> rw [h] <;> rfl

theorem shiftedSum_split (P : Model) (px : Prepared) (eC q : ℤ) (A : ℚ)
    (hPS : (productSum P px.p).2 = sumQ (px.p.map fun p => truncGrid p.value q) + A)
    (hq1 : eC - P.late.sumMantissaBits ≤ q)
    (hq2 : rdMantissa (productSum P px.p).2 eC P.late.sumMantissaBits + px.c.value ≠ 0 →
      normExp (absQ (rdMantissa (productSum P px.p).2 eC P.late.sumMantissaBits + px.c.value)) -
        P.late.accMantissaBits ≤ q) :
    shiftedSum P eC (productSum P px.p).2 px.c =
      (truncGrid px.c.value q + sumQ (px.p.map fun p => truncGrid p.value q)) +
        lateKept P px eC A (px.c.value - truncGrid px.c.value q) := by
  have hHp : OnGrid (sumQ (px.p.map fun p => truncGrid p.value q)) q := by
    apply onGrid_sumQ
    intro v hv
    simp only [List.mem_map] at hv
    obtain ⟨p, _, rfl⟩ := hv
    exact truncGrid_onGrid _ _
  have hhc : OnGrid (truncGrid px.c.value q) q := truncGrid_onGrid _ _
  have hrd : rdMantissa (productSum P px.p).2 eC P.late.sumMantissaBits =
      sumQ (px.p.map fun p => truncGrid p.value q) + rdMantissa A eC P.late.sumMantissaBits := by
    simp only [rdMantissa]; rw [hPS, rdGrid_add_onGrid (hHp.mono hq1)]
  unfold shiftedSum lateKept normalizeRD
  simp only
  generalize hT : rdMantissa (productSum P px.p).2 eC P.late.sumMantissaBits + px.c.value = T at *
  have hTe : T = (truncGrid px.c.value q + sumQ (px.p.map fun p => truncGrid p.value q)) +
      (rdMantissa A eC P.late.sumMantissaBits + (px.c.value - truncGrid px.c.value q)) := by
    rw [← hT, hrd]; grind
  by_cases h0 : T = 0
  · rw [if_pos h0, if_pos h0]; rw [hTe] at h0; grind
  · rw [if_neg h0, if_neg h0]
    have hg := hq2 h0
    simp only [rdMantissa]
    generalize normExp (absQ T) - (P.late.accMantissaBits : ℤ) = g at hg ⊢
    rw [hTe, rdGrid_add_onGrid ((hhc.add hHp).mono hg)]

theorem lateKept_abs_lt (P : Model) (px : Prepared) (eC q : ℤ) (A εc : ℚ)
    (hq1 : eC - P.late.sumMantissaBits ≤ q)
    (hq2 : rdMantissa (productSum P px.p).2 eC P.late.sumMantissaBits + px.c.value ≠ 0 →
      normExp (absQ (rdMantissa (productSum P px.p).2 eC P.late.sumMantissaBits + px.c.value)) -
        P.late.accMantissaBits ≤ q)
    (hε : absQ εc < pow2 q) : absQ (lateKept P px eC A εc) < absQ A + 3 * pow2 q := by
  have r1 := rdGrid_abs_le A (eC - P.late.sumMantissaBits)
  have p1 := pow2_le_of_le hq1
  have t1 := absQ_add_le (rdMantissa A eC P.late.sumMantissaBits) εc
  have hp := pow2_pos q
  unfold lateKept
  simp only
  split
  · simp only [rdMantissa] at t1; grind
  · rename_i h0
    have r2 := rdGrid_abs_le (rdMantissa A eC P.late.sumMantissaBits + εc)
      (normExp (absQ (rdMantissa (productSum P px.p).2 eC P.late.sumMantissaBits + px.c.value)) -
        P.late.accMantissaBits)
    have p2 := pow2_le_of_le (hq2 h0)
    simp only [rdMantissa] at t1 r2 ⊢
    grind

theorem hwGrid_early {P : Model} {px : Prepared} {e eC : ℤ} (he : alignExp P px.p = some e)
    (hce : cExp P px.c = some eC) (hle : eC ≤ e) :
    hwGrid P px = some (max (e - (23 + P.padding : ℕ)) (e - P.late.cMantissaBits)) := by
  simp [hwGrid, he, hce, hle]

theorem hwGrid_late {P : Model} {px : Prepared} {e eC : ℤ} (he : alignExp P px.p = some e)
    (hce : cExp P px.c = some eC) (hlt : ¬ eC ≤ e) :
    hwGrid P px = some (max (e - (23 + P.padding : ℕ)) (eC - P.late.sumMantissaBits)) := by
  simp [hwGrid, he, hce, hlt]

theorem hwGrid_noC {P : Model} {px : Prepared} {e : ℤ} (he : alignExp P px.p = some e)
    (hce : cExp P px.c = none) : hwGrid P px = some (e - (23 + P.padding : ℕ)) := by
  simp [hwGrid, he, hce]

theorem hwGrid_noP {P : Model} {px : Prepared} {eC : ℤ} (he : alignExp P px.p = none)
    (hce : cExp P px.c = some eC) : hwGrid P px = some (eC - P.late.sumMantissaBits) := by
  simp [hwGrid, he, hce]

/-- From the output `D`, `S_acc` is `H` plus a kept part of the low parts below `(n + 5)·2^q`. -/
theorem aligned_kept {P : Model}
    (hacc : P.accumulation = .globalAlignment ∨ P.accumulation = .oddEvenGrouping)
    (hs : P.subnormals = true) (hcut : ∀ n, P.late.cCutoff = some n → P.late.cMantissaBits ≤ n)
    (hk : 23 ≤ P.late.accMantissaBits) {x : BlockInput P} {t : BlockTrace P}
    (h : evalBlock x = .ok t) :
    t.sAcc = t.split.H + keptLow P t.prepared t.split.q ∧
      absQ (keptLow P t.prepared t.split.q) <
        ((t.prepared.p.length : ℚ) + 5) * pow2 t.split.q := by
  obtain ⟨_, _, hp, hacc', hfl⟩ := evalBlock_ok h
  have hS : t.sAcc = alignedAccumulation P t.prepared := accumulate_aligned hacc hacc'
  simp only [hs, Bool.not_true] at hfl
  have hd : wordValue t.d = rneValue t.sAcc := wordValue_of_fl32_false hfl
  rw [fl32_false] at hfl
  have hcb := prepare_cExp_bound hp
  unfold BlockTrace.split
  generalize wordValue t.d = d at hd ⊢
  generalize t.sAcc = sAcc at hS hfl hd ⊢
  generalize t.prepared = px at hS hcb ⊢
  have hqD : ulpExp32 d ≤ (eftSplit P px d).q := eftCutoff_ge P px d
  have hqdef : (eftSplit P px d).q = eftCutoff P px d := rfl
  have hH : (eftSplit P px d).H = (cRule P px).high px.c.value (eftSplit P px d).q +
      sumQ (px.p.map fun p => truncGrid p.value (eftSplit P px d).q) := by
    simp [eftSplit, EftSplit.H, EftSplit.highs, sumQ, List.map_map, Function.comp_def,
      SplitRule.high]
  rw [hH]
  unfold keptLow
  simp only
  generalize (eftSplit P px d).q = q at hqD hqdef ⊢
  rw [eftCutoff_aligned hacc] at hqdef
  have hqP : ∀ e, alignExp P px.p = some e → e - (23 + P.padding : ℕ) ≤ q := by
    intro e he
    cases hce : cExp P px.c with
    | none => rw [hwGrid_noC he hce] at hqdef; simp only at hqdef; omega
    | some eC =>
      by_cases hle : eC ≤ e
      · rw [hwGrid_early he hce hle] at hqdef; simp only at hqdef; omega
      · rw [hwGrid_late he hce hle] at hqdef; simp only at hqdef; omega
  have hpq := pow2_pos q
  have hA := productSumAt_abs_le P px.p (px.p.map fun p => p.value - truncGrid p.value q)
    (Rat.le_of_lt hpq)
    (fun v hv => by
      simp only [List.mem_map] at hv
      obtain ⟨p, _, rfl⟩ := hv
      exact Rat.le_of_lt (truncGrid_bounds p.value q).2.1)
    (fun e he => pow2_le_of_le (hqP e he))
  rw [List.length_map] at hA
  have hPS : (productSum P px.p).2 = sumQ (px.p.map fun p => truncGrid p.value q) +
      productSumAt P px.p (px.p.map fun p => p.value - truncGrid p.value q) := by
    rw [productSum_eq]; exact productSumAt_split P px.p q hqP
  have hfst : (productSum P px.p).1 = alignExp P px.p := by rw [productSum_eq]
  have hn : (0 : ℚ) ≤ px.p.length := by exact_mod_cast Nat.zero_le _
  have h25 : ((px.p.length : ℚ) + 2) * pow2 q + 3 * pow2 q = ((px.p.length : ℚ) + 5) * pow2 q := by
    grind
  unfold alignedAccumulation at hS
  simp only at hS
  rw [hfst] at hS
  generalize productSumAt P px.p (px.p.map fun p => p.value - truncGrid p.value q) = A at hA hPS
  -- the late branch, shared by `e_c > e_max` and by blocks of zero products
  have late : ∀ eC, eC - P.late.sumMantissaBits ≤ q →
      sAcc = shiftedSum P eC (productSum P px.p).2 px.c →
      sAcc = (truncGrid px.c.value q + sumQ (px.p.map fun p => truncGrid p.value q)) +
          lateKept P px eC A (px.c.value - truncGrid px.c.value q) ∧
        absQ (lateKept P px eC A (px.c.value - truncGrid px.c.value q)) <
          ((px.p.length : ℚ) + 5) * pow2 q := by
    intro eC hq1 hsum
    have hq2 : rdMantissa (productSum P px.p).2 eC P.late.sumMantissaBits + px.c.value ≠ 0 →
        normExp (absQ (rdMantissa (productSum P px.p).2 eC P.late.sumMantissaBits + px.c.value)) -
          P.late.accMantissaBits ≤ q := by
      intro h0
      have hw : rne32 (normalizeRD P.late.accMantissaBits
          (rdMantissa (productSum P px.p).2 eC P.late.sumMantissaBits + px.c.value)) =
            some t.d := by
        rw [← hfl, hsum]; rfl
      have := normalizeRD_grid_le hk h0 hw
      have e1 : normalizeRD P.late.accMantissaBits
          (rdMantissa (productSum P px.p).2 eC P.late.sumMantissaBits + px.c.value) = sAcc := by
        rw [hsum]; rfl
      rw [e1, ← hd] at this
      omega
    refine ⟨by rw [hsum]; exact shiftedSum_split P px eC q A hPS hq1 hq2, ?_⟩
    have := lateKept_abs_lt P px eC q A (px.c.value - truncGrid px.c.value q) hq1 hq2
      (truncGrid_bounds px.c.value q).2.1
    grind
  have hsmallA : absQ A < ((px.p.length : ℚ) + 5) * pow2 q := by grind
  have hrt : ∀ eC, ¬ (∃ e, alignExp P px.p = some e ∧ eC ≤ e ∧ cDropped P e eC = false) →
      cExp P px.c = some eC → cRule P px = .trunc := by
    intro eC hn hce
    rw [cRule_aligned hacc, hce]
    cases hae : alignExp P px.p with
    | none => rfl
    | some e =>
      simp only
      rw [if_neg (fun hc => hn ⟨e, hae, hc.1, hc.2⟩)]
  cases hae : alignExp P px.p with
  | none =>
    cases hce : cExp P px.c with
    | none =>
      have hc0 := cExp_none hce
      unfold lateSum at hS
      rw [hce] at hS
      simp only [hc0]
      rw [show (cRule P px).high 0 q = 0 by
        cases cRule P px <;> simp [SplitRule.high, truncGrid_zero, rdGrid_zero]]
      exact ⟨by rw [hS, hPS]; grind, hsmallA⟩
    | some eC =>
      unfold lateSum at hS
      rw [hce, hae] at hS
      simp only at hS
      have hq1 : eC - P.late.sumMantissaBits ≤ q := by
        rw [hwGrid_noP hae hce] at hqdef; simp only at hqdef; omega
      simp only
      rw [hrt eC (fun ⟨e, he, _⟩ => by rw [hae] at he; cases he) hce]
      exact late eC hq1 hS
  | some e =>
    cases hce : cExp P px.c with
    | none =>
      have hc0 := cExp_none hce
      unfold lateSum at hS
      rw [hce] at hS
      simp only [hc0]
      rw [show (cRule P px).high 0 q = 0 by
        cases cRule P px <;> simp [SplitRule.high, truncGrid_zero, rdGrid_zero]]
      exact ⟨by rw [hS, hPS]; grind, hsmallA⟩
    | some eC =>
      unfold lateSum at hS
      rw [hce, hae] at hS
      simp only at hS
      simp only
      by_cases hle : eC ≤ e
      · rw [if_pos hle] at hS
        rw [if_pos hle]
        have hqc : e - P.late.cMantissaBits ≤ q := by
          rw [hwGrid_early hae hce hle] at hqdef; simp only at hqdef; omega
        rw [shiftedC_eq] at hS
        cases hdrop : cDropped P e eC with
        | true =>
          have hsmall := cDropped_small P hcut hdrop
          have hr : cRule P px = .trunc :=
            hrt eC (fun ⟨e', he', _, hd'⟩ => by
              rw [hae] at he'; cases he'; rw [hdrop] at hd'; cases hd') hce
          have hc0 : truncGrid px.c.value q = 0 :=
            truncGrid_eq_zero (Std.lt_of_lt_of_le (hcb eC hce) (pow2_le_of_le (by omega)))
          rw [hr]
          simp only [SplitRule.high, hc0, ↓reduceIte]
          simp only [hdrop, ↓reduceIte] at hS
          exact ⟨by rw [hS, hPS]; grind, by grind⟩
        | false =>
          have hr : cRule P px = .rd := by
            rw [cRule_aligned hacc, hae, hce]; simp [hle, hdrop]
          rw [hr]
          simp only [SplitRule.high, Bool.false_eq_true, ↓reduceIte]
          simp only [hdrop, Bool.false_eq_true, ↓reduceIte] at hS
          have hb := rdGrid_bounds px.c.value q
          have hε0 : 0 ≤ px.c.value - rdGrid px.c.value q := by grind
          have hε1 : px.c.value - rdGrid px.c.value q < pow2 q := by grind
          have hφ0 := rdGrid_nonneg hε0 (e - P.late.cMantissaBits)
          have hφ1 :=
            (rdGrid_bounds (px.c.value - rdGrid px.c.value q) (e - P.late.cMantissaBits)).1
          refine ⟨?_, ?_⟩
          · rw [hS, hPS]
            simp only [rdMantissa]
            rw [rdGrid_split px.c.value hqc]
            grind
          · simp only [rdMantissa]
            have t := absQ_add_le A (rdGrid (px.c.value - rdGrid px.c.value q)
              (e - P.late.cMantissaBits))
            rw [absQ_of_nonneg hφ0] at t
            grind
      · rw [if_neg hle] at hS
        rw [if_neg hle]
        have hq1 : eC - P.late.sumMantissaBits ≤ q := by
          rw [hwGrid_late hae hce hle] at hqdef; simp only at hqdef; omega
        rw [hrt eC (fun ⟨e', he', hle', _⟩ => by rw [hae] at he'; cases he'; exact hle hle') hce]
        exact late eC hq1 hS

theorem evalBlock_p_length {P : Model} {x : BlockInput P} {t : BlockTrace P}
    (h : evalBlock x = .ok t) : t.prepared.p.length = P.nfma := by
  obtain ⟨ha, hb, hp, _, _⟩ := evalBlock_ok h
  obtain ⟨la, lb⟩ := prepare_lengths hp
  rw [Prepared.p_length, la, lb, ha, hb, Nat.min_self]

/-- What the output `D` of a CDNA 3 block buys: `S_acc = H + kept`, and the overlap is small. -/
structure AlignedOverlap {P : Model} (t : BlockTrace P) : Prop where
  kept : t.sAcc = t.split.H + keptLow P t.prepared t.split.q
  kept_lt : absQ (keptLow P t.prepared t.split.q) < ((P.nfma : ℚ) + 5) * pow2 t.split.q
  final : absQ (wordValue t.d - t.sAcc) ≤ pow2 (ulpExp32 (wordValue t.d) - 1)
  overlap : t.split.overlap (wordValue t.d) =
    keptLow P t.prepared t.split.q + (wordValue t.d - t.sAcc)
  overlap_lt : absQ (t.split.overlap (wordValue t.d)) < ((P.nfma : ℚ) + 6) * pow2 t.split.q
  loss : t.prepared.exact - t.sAcc = sumQ t.split.lows - keptLow P t.prepared t.split.q

/-- What `D` buys on CDNA 3, for every global-alignment or odd/even-grouping block. -/
theorem aligned_eft {P : Model}
    (hacc : P.accumulation = .globalAlignment ∨ P.accumulation = .oddEvenGrouping)
    (hs : P.subnormals = true) (hcut : ∀ n, P.late.cCutoff = some n → P.late.cMantissaBits ≤ n)
    (hk : 23 ≤ P.late.accMantissaBits) {x : BlockInput P} {t : BlockTrace P}
    (h : evalBlock x = .ok t) : AlignedOverlap t := by
  obtain ⟨hkept, hlt⟩ := aligned_kept hacc hs hcut hk h
  rw [evalBlock_p_length h] at hlt
  have hfl := (evalBlock_ok h).2.2.2.2
  simp only [hs, Bool.not_true] at hfl
  have hd : wordValue t.d = rneValue t.sAcc := wordValue_of_fl32_false hfl
  have hfin : absQ (wordValue t.d - t.sAcc) ≤ pow2 (ulpExp32 (wordValue t.d) - 1) := by
    rw [absQ_sub_comm, hd]; exact rneValue_error_ulp _
  have hex : t.prepared.exact = t.split.H + sumQ t.split.lows := by
    unfold BlockTrace.split; rw [← EftSplit.exact_eq, eftSplit_exact]
  have hov : t.split.overlap (wordValue t.d) =
      keptLow P t.prepared t.split.q + (wordValue t.d - t.sAcc) := by
    unfold EftSplit.overlap; grind
  refine ⟨hkept, hlt, hfin, hov, ?_, by grind⟩
  have hq : ulpExp32 (wordValue t.d) - 1 ≤ t.split.q := by
    have := eftCutoff_ge P t.prepared (wordValue t.d)
    show ulpExp32 _ - 1 ≤ eftCutoff P t.prepared (wordValue t.d)
    omega
  have h1 := pow2_le_of_le hq
  have h2 := absQ_add_le (keptLow P t.prepared t.split.q) (wordValue t.d - t.sAcc)
  rw [hov]
  have : ((P.nfma : ℚ) + 5) * pow2 t.split.q + pow2 t.split.q =
      ((P.nfma : ℚ) + 6) * pow2 t.split.q := by grind
  grind

/-- If `D`'s last bit is at or below the alignment grid, the final rounding is exact. -/
theorem aligned_exact_rounding {P : Model}
    (hacc : P.accumulation = .globalAlignment ∨ P.accumulation = .oddEvenGrouping)
    (hs : P.subnormals = true) (hgrid : P.late.cMantissaBits = 23 + P.padding)
    {x : BlockInput P} {t : BlockTrace P} (h : evalBlock x = .ok t) {e : ℤ}
    (he : alignExp P t.prepared.p = some e) (hc : ∀ eC, cExp P t.prepared.c = some eC → eC ≤ e)
    (hD : ulpExp32 (wordValue t.d) ≤ e - (23 + P.padding : ℕ)) : wordValue t.d = t.sAcc := by
  obtain ⟨_, _, _, hacc', hfl⟩ := evalBlock_ok h
  have hS : t.sAcc = alignedAccumulation P t.prepared := accumulate_aligned hacc hacc'
  simp only [hs, Bool.not_true] at hfl
  have hd : wordValue t.d = rneValue t.sAcc := wordValue_of_fl32_false hfl
  rw [fl32_false] at hfl
  have hfst : (productSum P t.prepared.p).1 = alignExp P t.prepared.p := by rw [productSum_eq]
  have hP := productSum_onGrid P t.prepared.p he
  have hg : OnGrid t.sAcc (e - (23 + P.padding : ℕ)) := by
    rw [hS]
    unfold alignedAccumulation lateSum
    simp only
    rw [hfst, he]
    cases hce : cExp P t.prepared.c with
    | none => exact hP
    | some eC =>
      simp only [hc eC hce, ↓reduceIte]
      rw [shiftedC_eq]
      split
      · rw [Rat.add_zero]; exact hP
      · refine hP.add ?_
        show OnGrid (rdGrid t.prepared.c.value (e - P.late.cMantissaBits)) _
        rw [hgrid]
        exact rdGrid_onGrid _ _
  rw [hd]
  exact rneValue_eq_of_onGrid hfl (hg.mono (by rw [← hd]; exact hD))

theorem alignAt_eq_zero (padding : ℕ) (e : ℤ) (xs : List ℚ)
    (h : ∀ x ∈ xs, absQ x < pow2 (e - (23 + padding : ℕ))) : alignAt padding (some e) xs = 0 := by
  simp only [alignAt]
  have : (xs.map fun x => truncMantissa x e (23 + padding)) = xs.map fun _ => (0 : ℚ) :=
    List.map_congr_left fun x hx => truncGrid_eq_zero (h x hx)
  rw [this]
  clear this h
  induction xs with
  | nil => rfl
  | cons _ _ ih => simp only [List.map_cons, sumQ, ih]; exact Rat.add_zero 0

/-- With global alignment and `D`'s last bit at or below the grid, `H = D` and `S = D + Σ εᵢ`. -/
theorem globalAlignment_exact_rounding {P : Model} (hacc : P.accumulation = .globalAlignment)
    (hs : P.subnormals = true) (hcut : ∀ n, P.late.cCutoff = some n → P.late.cMantissaBits ≤ n)
    (hk : 23 ≤ P.late.accMantissaBits) (hgrid : P.late.cMantissaBits = 23 + P.padding)
    {x : BlockInput P} {t : BlockTrace P} (h : evalBlock x = .ok t) {e : ℤ}
    (he : alignExp P t.prepared.p = some e) (hc : ∀ eC, cExp P t.prepared.c = some eC → eC ≤ e)
    (hD : ulpExp32 (wordValue t.d) ≤ e - (23 + P.padding : ℕ)) :
    keptLow P t.prepared t.split.q = 0 ∧ t.split.H = wordValue t.d ∧
      t.split.overlap (wordValue t.d) = 0 ∧
      t.prepared.exact = wordValue t.d + sumQ t.split.lows := by
  have hD' := aligned_exact_rounding (Or.inl hacc) hs hgrid h he hc hD
  have hkept := (aligned_kept (Or.inl hacc) hs hcut hk h).1
  have hex : t.prepared.exact = t.split.H + sumQ t.split.lows := by
    unfold BlockTrace.split; rw [← EftSplit.exact_eq, eftSplit_exact]
  have hq : t.split.q = e - (23 + P.padding : ℕ) := by
    show eftCutoff P t.prepared (wordValue t.d) = _
    rw [eftCutoff_aligned (Or.inl hacc)]
    cases hce : cExp P t.prepared.c with
    | none => rw [hwGrid_noC he hce]; simp only; omega
    | some eC => rw [hwGrid_early he hce (hc eC hce), hgrid]; simp only; omega
  have h0 : keptLow P t.prepared t.split.q = 0 := by
    rw [hq]
    generalize hqq : e - ((23 + P.padding : ℕ) : ℤ) = q
    have hA : productSumAt P t.prepared.p
        (t.prepared.p.map fun p => p.value - truncGrid p.value q) = 0 := by
      unfold productSumAt
      rw [hacc]
      simp only
      have hm : maxExp t.prepared.p = some e := by unfold alignExp at he; rw [hacc] at he; exact he
      rw [hm]
      apply alignAt_eq_zero
      intro v hv
      simp only [List.mem_map] at hv
      obtain ⟨p, _, rfl⟩ := hv
      rw [hqq]
      exact (truncGrid_bounds p.value q).2.1
    unfold keptLow
    simp only [hA, he]
    cases hce : cExp P t.prepared.c with
    | none => rfl
    | some eC =>
      simp only [hc eC hce, ↓reduceIte, Rat.zero_add]
      split
      · rfl
      · rename_i hdrop
        have hr : cRule P t.prepared = .rd := by
          rw [cRule_aligned (Or.inl hacc), he, hce]; simp [hc eC hce, hdrop]
        rw [hr]
        simp only [SplitRule.high, rdMantissa]
        have hb := rdGrid_bounds t.prepared.c.value q
        rw [hgrid, hqq]
        exact rdGrid_eq_zero (by grind) (by grind)
  have hHs : t.split.H = t.sAcc := by rw [hkept, h0, Rat.add_zero]
  refine ⟨h0, hHs.trans hD'.symm, ?_, ?_⟩
  · unfold EftSplit.overlap; rw [hHs, hD']; grind
  · rw [hex, hHs, hD']

/-! ## The CDNA 3 models -/

theorem cdna3F16_eft {x : BlockInput cdna3F16} {t : BlockTrace cdna3F16}
    (h : evalBlock x = .ok t) : AlignedOverlap t :=
  aligned_eft (Or.inl rfl) rfl (fun _ h => by simp [cdna3F16] at h) (by decide) h

theorem cdna3BF16_eft {x : BlockInput cdna3BF16} {t : BlockTrace cdna3BF16}
    (h : evalBlock x = .ok t) : AlignedOverlap t :=
  aligned_eft (Or.inl rfl) rfl (fun _ h => by simp [cdna3BF16] at h) (by decide) h

theorem cdna3XF32_eft {x : BlockInput cdna3XF32} {t : BlockTrace cdna3XF32}
    (h : evalBlock x = .ok t) : AlignedOverlap t :=
  aligned_eft (Or.inl rfl) rfl (fun _ h => by simp [cdna3XF32] at h) (by decide) h

theorem cdna3FP8_eft (fa fb : Format) {x : BlockInput (cdna3FP8 fa fb)}
    {t : BlockTrace (cdna3FP8 fa fb)} (h : evalBlock x = .ok t) : AlignedOverlap t :=
  aligned_eft (Or.inr rfl) rfl (fun n h => by simp [cdna3FP8] at h ⊢; omega) (by simp [cdna3FP8]) h

theorem cdna3F16_exact_rounding {x : BlockInput cdna3F16} {t : BlockTrace cdna3F16}
    (h : evalBlock x = .ok t) {e : ℤ} (he : alignExp cdna3F16 t.prepared.p = some e)
    (hc : ∀ eC, cExp cdna3F16 t.prepared.c = some eC → eC ≤ e)
    (hD : ulpExp32 (wordValue t.d) ≤ e - 24) :
    t.split.H = wordValue t.d ∧ t.split.overlap (wordValue t.d) = 0 ∧
      t.prepared.exact = wordValue t.d + sumQ t.split.lows :=
  (globalAlignment_exact_rounding rfl rfl (fun _ h => by simp [cdna3F16] at h) (by decide) rfl h
    he hc hD).2

theorem cdna3BF16_exact_rounding {x : BlockInput cdna3BF16} {t : BlockTrace cdna3BF16}
    (h : evalBlock x = .ok t) {e : ℤ} (he : alignExp cdna3BF16 t.prepared.p = some e)
    (hc : ∀ eC, cExp cdna3BF16 t.prepared.c = some eC → eC ≤ e)
    (hD : ulpExp32 (wordValue t.d) ≤ e - 24) :
    t.split.H = wordValue t.d ∧ t.split.overlap (wordValue t.d) = 0 ∧
      t.prepared.exact = wordValue t.d + sumQ t.split.lows :=
  (globalAlignment_exact_rounding rfl rfl (fun _ h => by simp [cdna3BF16] at h) (by decide) rfl h
    he hc hD).2

theorem cdna3XF32_exact_rounding {x : BlockInput cdna3XF32} {t : BlockTrace cdna3XF32}
    (h : evalBlock x = .ok t) {e : ℤ} (he : alignExp cdna3XF32 t.prepared.p = some e)
    (hc : ∀ eC, cExp cdna3XF32 t.prepared.c = some eC → eC ≤ e)
    (hD : ulpExp32 (wordValue t.d) ≤ e - 24) :
    t.split.H = wordValue t.d ∧ t.split.overlap (wordValue t.d) = 0 ∧
      t.prepared.exact = wordValue t.d + sumQ t.split.lows :=
  (globalAlignment_exact_rounding rfl rfl (fun _ h => by simp [cdna3XF32] at h) (by decide) rfl h
    he hc hD).2

theorem cdna3FP8_exact_rounding (fa fb : Format) {x : BlockInput (cdna3FP8 fa fb)}
    {t : BlockTrace (cdna3FP8 fa fb)} (h : evalBlock x = .ok t) {e : ℤ}
    (he : alignExp (cdna3FP8 fa fb) t.prepared.p = some e)
    (hc : ∀ eC, cExp (cdna3FP8 fa fb) t.prepared.c = some eC → eC ≤ e)
    (hD : ulpExp32 (wordValue t.d) ≤ e - 24) : wordValue t.d = t.sAcc :=
  aligned_exact_rounding (Or.inr rfl) rfl rfl h he hc hD

end MatrixCore
