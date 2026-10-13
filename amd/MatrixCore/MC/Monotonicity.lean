import MatrixCore.MC.ErrorBounds
import MatrixCore.MC.Chain

/-! # Monotonicity in `c`

On NVIDIA Tensor Cores every term, products and `c` alike, is aligned to the largest exponent and
truncated, so perturbing whichever term holds that exponent can change how much of the others
survives and raise the output when the term is lowered (the TC-EFT paper's flowback; its
construction perturbs `c`). On AMD `c` never takes part in the products' alignment, so on every
configuration of the paper the output is monotone in `c`: for the same `a` and `b`, a larger `c` never gives a smaller `d`
(`evalBlock_c_monotone`), and the same holds for inner products of any length
(`dotBits_c_monotone`).

* SFMA and CDNA 1: `d = fl{Σ p_ℓ + c}`, and RNE is monotone.
* CDNA 2: `c` is flushed (monotone), added to the pairwise sum of the products, and rounded.
* CDNA 3: `c` is aligned *after* the products (late addition), so `e_max` and `S_{p_i,sum}` do
  not depend on `c`; each branch of the late addition is monotone, and so is the switch between
  them: when `e_c` passes `e_max`, the RD of `S_{p_i,sum}` to 32 and of `S_acc` to 31
  fractional bits loses less than the step of `c`.

Monotonicity in the *products* is different: see `MatrixCore.MC.ProductMonotonicity`. -/

namespace MatrixCore

/-! ## Rounding -/

theorem flValue_eq {ftz : Bool} {x v : ℚ} (h : flValue ftz x = some v) :
    v = if ftz then flushValue (rneValue x) else rneValue x := by
  cases ftz with
  | false => exact flValue_false h
  | true =>
    simp only [↓reduceIte, flushValue]
    rcases flValue_true h with ⟨rfl, h0 | hge⟩ | ⟨rfl, _, hsmall⟩
    · rw [h0]; simp
    · have : ¬ absQ (rneValue x) < pow2 (-126) := Rat.not_lt.mpr hge
      simp [this]
    · simp [hsmall]

theorem flValue_mono {ftz : Bool} {x y v w : ℚ} (hx : flValue ftz x = some v)
    (hy : flValue ftz y = some w) (h : x ≤ y) : v ≤ w := by
  rw [flValue_eq hx, flValue_eq hy]
  cases ftz
  · exact rneValue_mono h
  · exact flushValue_mono (rneValue_mono h)

/-- The final `fl{·}` is monotone. -/
theorem fl32_mono {ftz : Bool} {s s' : ℚ} {d d' : F32} (h : fl32 ftz s = some d)
    (h' : fl32 ftz s' = some d') (hs : s ≤ s') : wordValue d ≤ wordValue d' := by
  apply flValue_mono (ftz := ftz) _ _ hs
  · unfold flValue; rw [h]; exact fl32_value h
  · unfold flValue; rw [h']; exact fl32_value h'

/-! ## RD and normalization -/

theorem rdGrid_mono {x y : ℚ} (g : ℤ) (h : x ≤ y) : rdGrid x g ≤ rdGrid y g := by
  unfold rdGrid
  have hq := pow2_pos g
  apply Rat.mul_le_mul_of_nonneg_right _ (Rat.le_of_lt hq)
  have : x / pow2 g ≤ y / pow2 g := by
    rw [Rat.div_def, Rat.div_def]
    exact Rat.mul_le_mul_of_nonneg_right h (Rat.le_of_lt (Rat.inv_pos.mpr hq))
  exact Rat.intCast_le_intCast.mpr (floor_mono this)

/-- RD is at least every grid point below its argument. -/
theorem le_rdGrid {x y : ℚ} {g : ℤ} (hy : OnGrid y g) (h : y ≤ x) : y ≤ rdGrid x g := by
  have := rdGrid_mono g h
  rwa [rdGrid_of_onGrid hy] at this

/-- RD on a coarser grid gives a smaller value. -/
theorem rdGrid_coarse (x : ℚ) {g g' : ℤ} (hg : g ≤ g') : rdGrid x g' ≤ rdGrid x g :=
  le_rdGrid ((rdGrid_onGrid x g').mono hg) (rdGrid_bounds x g').1

theorem onGrid_pow2 (e : ℤ) (k : ℕ) : OnGrid (pow2 e) (e - k) :=
  ⟨2 ^ k, by rw [pow2_split e k]; simp⟩

theorem normalizeRD_le (k : ℕ) (x : ℚ) : normalizeRD k x ≤ x := by
  unfold normalizeRD; split
  · rename_i h; rw [h]; exact Rat.le_refl
  · exact (rdGrid_bounds x _).1

theorem normalizeRD_gt (k : ℕ) {x : ℚ} (hx : x ≠ 0) :
    x - pow2 (normExp (absQ x) - k) < normalizeRD k x := by
  unfold normalizeRD; rw [if_neg hx]
  have := (rdGrid_bounds x (normExp (absQ x) - k)).2
  grind

theorem le_normalizeRD (k : ℕ) {x y : ℚ} (hx : x ≠ 0) (hy : OnGrid y (normExp (absQ x) - k))
    (h : y ≤ x) : y ≤ normalizeRD k x := by
  unfold normalizeRD; rw [if_neg hx]
  exact le_rdGrid hy h

theorem normalizeRD_onGrid (k : ℕ) {x : ℚ} (hx : x ≠ 0) :
    OnGrid (normalizeRD k x) (normExp (absQ x) - k) := by
  unfold normalizeRD; rw [if_neg hx]; exact rdGrid_onGrid _ _

/-- Subnormal-aware normalization followed by RD is monotone: the grid of each binade contains
the grid of every larger binade, and the binade boundaries lie on both. -/
theorem normalizeRD_mono (k : ℕ) {x y : ℚ} (h : x ≤ y) : normalizeRD k x ≤ normalizeRD k y := by
  by_cases hx : x = 0
  · subst hx
    have h0 : normalizeRD k 0 = 0 := by unfold normalizeRD; simp
    rw [h0]
    by_cases hy : y = 0
    · subst hy; rw [h0]; exact Rat.le_refl
    · exact le_normalizeRD k hy (OnGrid.zero _) h
  by_cases hy : y = 0
  · subst hy
    have h0 : normalizeRD k 0 = 0 := by unfold normalizeRD; simp
    rw [h0]; exact Rat.le_trans (normalizeRD_le k x) h
  have hax := absQ_pos hx
  have hay := absQ_pos hy
  by_cases hle : normExp (absQ y) ≤ normExp (absQ x)
  · apply le_normalizeRD k hy _ (Rat.le_trans (normalizeRD_le k x) h)
    exact (normalizeRD_onGrid k hx).mono (by omega)
  · obtain ⟨hx1, _, hx3⟩ := normExp_bounds hax
    obtain ⟨_, hy2, _⟩ := normExp_bounds hay
    have hy2 := hy2 (by omega)
    have hp := pow2_le_of_le (show normExp (absQ x) + 1 ≤ normExp (absQ y) by omega)
    have hxa : x ≤ absQ x := by unfold absQ; split <;> grind
    have hypos : 0 < y := by
      by_cases hyn : y < 0
      · exfalso
        have hya : absQ y ≤ -y := by rw [absQ_of_neg hyn]; exact Rat.le_refl
        have hax' : -x ≤ absQ x := by rw [absQ_of_neg (by grind)]; exact Rat.le_refl
        have hxy : -y ≤ -x := by grind
        have h1 := Rat.le_trans hp (Rat.le_trans hy2 (Rat.le_trans hya (Rat.le_trans hxy hax')))
        exact Rat.not_le.mpr hx1 h1
      · grind
    have hya : absQ y = y := absQ_of_nonneg (Rat.le_of_lt hypos)
    rw [hya] at hy2
    have hg := le_normalizeRD k hy (by rw [hya]; exact onGrid_pow2 _ k) hy2
    have := normalizeRD_le k x
    grind

/-! ## `c` as a binary32 value -/

/-- `v` is a finite binary32 value and `eC` its exponent for the late addition: `−126` for zero
and subnormals. -/
structure C32 (v : ℚ) (eC : ℤ) : Prop where
  emin : -126 ≤ eC
  lt : absQ v < pow2 (eC + 1)
  ge : eC ≠ -126 → pow2 eC ≤ absQ v
  grid : OnGrid v (eC - 23)

theorem c32_of_decode {P : Model} (hcz : P.cZeroExp = some (-126)) {w : F32} {c : Unpacked}
    (h : (binary32.decode w).toFinite = some c) : ∃ eC, cExp P c = some eC ∧ C32 c.value eC := by
  obtain ⟨ht, hm, he1, _, hn⟩ := decode32_finite_fields (toFinite_some h)
  unfold cExp
  by_cases h0 : c.m = 0
  · refine ⟨-126, by simp [h0, hcz], ?_⟩
    rw [(Unpacked.value_eq_zero_iff c).mpr h0]
    exact ⟨by omega, by rw [show absQ (0 : ℚ) = 0 from rfl]; exact pow2_pos _,
      fun h => absurd rfl h, OnGrid.zero _⟩
  · refine ⟨c.e, by simp [h0], he1, ?_, ?_, ?_⟩
    · exact Unpacked.absQ_value_lt (by rw [ht]; exact hm)
    · intro hne
      have hm' : 8388608 ≤ c.m := by omega
      rw [Unpacked.absQ_value, ht]
      have : pow2 c.e = ((8388608 : ℕ) : ℚ) * pow2 (c.e - ((23 : ℕ) : ℤ)) := by
        rw [← show ((2 ^ 23 : ℕ) : ℚ) = ((8388608 : ℕ) : ℚ) from rfl, ← pow2_natCast, ← pow2_add]
        congr 1; omega
      rw [this]
      exact Rat.mul_le_mul_of_nonneg_right (by exact_mod_cast hm') (Rat.le_of_lt (pow2_pos _))
    · have := Unpacked.value_onGrid c
      rwa [ht] at this

/-- A value of exponent at most `e` is at most `2^(e+1) − 2^(e−23)` in magnitude. -/
theorem C32.le {v : ℚ} {eC e : ℤ} (hc : C32 v eC) (he : eC ≤ e) :
    absQ v ≤ 16777215 * pow2 (e - 23) := by
  obtain ⟨k, hk⟩ := hc.grid
  have hq := pow2_pos (eC - 23)
  have hv : absQ v = (k.natAbs : ℚ) * pow2 (eC - 23) := by
    rw [hk, absQ_mul_pos _ _ hq, absQ_intCast]
  have h24 : pow2 (eC + 1) = 16777216 * pow2 (eC - 23) := by
    rw [pow2_split (eC + 1) 24, show eC + 1 - ((24 : ℕ) : ℤ) = eC - 23 by omega]; rfl
  have hlt := hc.lt
  rw [hv, h24] at hlt
  have hk' : (k.natAbs : ℚ) < 16777216 := by
    apply Rat.not_le.mp; intro hc'
    exact Rat.not_le.mpr hlt (Rat.mul_le_mul_of_nonneg_right hc' (Rat.le_of_lt hq))
  have hk'' : k.natAbs ≤ 16777215 := by
    have : k.natAbs < 16777216 := by exact_mod_cast hk'
    omega
  have hkq : (k.natAbs : ℚ) ≤ 16777215 := by exact_mod_cast hk''
  rw [hv]
  have h1 := Rat.mul_le_mul_of_nonneg_right hkq (Rat.le_of_lt hq)
  have h2 := pow2_le_of_le (show eC - 23 ≤ e - 23 by omega)
  have h3 := Rat.mul_le_mul_of_nonneg_left h2 (show (0 : ℚ) ≤ 16777215 by decide)
  grind

/-! ## The product sum does not depend on `c` -/

theorem Unpacked.absQ_value_lt2 {u : Unpacked} (hm : u.m < 2 ^ (u.t + 2)) :
    absQ u.value < pow2 (u.e + 2) := by
  rw [Unpacked.absQ_value]
  have hmq : (u.m : ℚ) < pow2 ((u.t + 2 : ℕ) : ℤ) := by rw [pow2_natCast]; exact_mod_cast hm
  have := Rat.mul_lt_mul_of_pos_right hmq (pow2_pos (u.e - u.t))
  rwa [← pow2_add, show ((u.t + 2 : ℕ) : ℤ) + (u.e - u.t) = u.e + 2 by omega] at this

theorem absQ_rdGrid_le (x : ℚ) (g : ℤ) : absQ (rdGrid x g) ≤ absQ x + pow2 g := by
  have ⟨h1, h2⟩ := rdGrid_bounds x g
  have hx := absQ_le_iff x (absQ x)
  have := (hx.mp (by unfold absQ; split <;> grind))
  rw [absQ_le_iff]; constructor <;> grind

theorem alignedSum_facts {neab : ℕ} {ps : List Unpacked} {e : ℤ} {S : ℚ}
    (hb : ∀ p ∈ ps, p.m < 2 ^ (p.t + 2)) (h : alignedSum neab ps = (some e, S)) :
    OnGrid S (e - (23 + neab : ℕ)) ∧ absQ S ≤ ps.length * pow2 (e + 2) := by
  unfold alignedSum at h
  split at h
  · simp at h
  · rename_i e' he
    simp only [Prod.mk.injEq, Option.some.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    constructor
    · apply onGrid_sumQ
      intro x hx
      simp only [List.mem_map] at hx
      obtain ⟨p, _, rfl⟩ := hx
      exact truncGrid_onGrid _ _
    · refine Rat.le_trans (absQ_sumQ_le _) ?_
      rw [List.map_map]
      apply sumQ_map_le
      intro p hp
      simp only [Function.comp_apply]
      have h1 := (truncGrid_bounds p.value (e' - ((23 + neab : ℕ) : ℤ))).1
      have hp2 := pow2_pos (e' + 2)
      by_cases hm : p.m = 0
      · rw [(Unpacked.value_eq_zero_iff p).mpr hm,
          show truncFrac (0 : ℚ) e' (23 + neab) = 0 from truncGrid_zero _]
        exact Rat.le_of_lt (show absQ (0 : ℚ) < pow2 (e' + 2) from hp2)
      · have h2 := Unpacked.absQ_value_lt2 (hb p hp)
        have h3 := pow2_le_of_le (show p.e + 2 ≤ e' + 2 by have := maxExp_le he p hp hm; omega)
        grind

/-- `S_{p_i,sum}` lies on the alignment grid and is at most `|ps| · 2^(e_max+2)` plus two RD
steps. -/
theorem productSum_facts (P : Model) {ps : List Unpacked} (hb : ∀ p ∈ ps, p.m < 2 ^ (p.t + 2)) :
    ((productSum P ps).1 = none → (productSum P ps).2 = 0) ∧
    (∀ e, (productSum P ps).1 = some e →
      OnGrid (productSum P ps).2 (e - (23 + P.neab : ℕ)) ∧
      absQ (productSum P ps).2 ≤ ps.length * pow2 (e + 2) + 2 * pow2 (e - (23 + P.neab : ℕ))) := by
  have hq := pow2_pos (0 : ℤ)
  unfold productSum
  split
  · -- odd/even grouping
    obtain ⟨_, hlen⟩ := sumQ_odd_even Unpacked.value ps
    have hbo : ∀ p ∈ oddIndexed ps, p.m < 2 ^ (p.t + 2) := fun p hp => hb p (oddIndexed_subset ps p hp)
    have hbe : ∀ p ∈ evenIndexed ps, p.m < 2 ^ (p.t + 2) := fun p hp => hb p (evenIndexed_subset ps p hp)
    generalize hO : alignedSum P.neab (oddIndexed ps) = O
    generalize hE : alignedSum P.neab (evenIndexed ps) = E
    obtain ⟨eo, So⟩ := O
    obtain ⟨ee, Se⟩ := E
    simp only
    cases hj : joinExp eo ee with
    | none => exact ⟨fun _ => rfl, fun _ h => by simp at h⟩
    | some e =>
      refine ⟨fun h => by simp at h, fun e' he' => ?_⟩
      simp only [Option.some.injEq] at he'
      subst he'
      have hg := pow2_pos (e - ((23 + P.neab : ℕ) : ℤ))
      have group : ∀ (l : List Unpacked) (eg : Option ℤ) (Sg : ℚ),
          (∀ p ∈ l, p.m < 2 ^ (p.t + 2)) → alignedSum P.neab l = (eg, Sg) →
          (∀ v, eg = some v → v ≤ e) → absQ Sg ≤ l.length * pow2 (e + 2) := by
        intro l eg Sg hbl hl hle
        cases eg with
        | none =>
          rw [alignedSum_none hl]
          have : (0 : ℚ) ≤ l.length * pow2 (e + 2) :=
            Rat.mul_nonneg (by exact_mod_cast Nat.zero_le _) (Rat.le_of_lt (pow2_pos _))
          rw [show absQ (0 : ℚ) = 0 from rfl]; exact this
        | some v =>
          have := (alignedSum_facts hbl hl).2
          have h2 := pow2_le_of_le (show v + 2 ≤ e + 2 by have := hle v rfl; omega)
          have h3 := Rat.mul_le_mul_of_nonneg_left h2 (show (0 : ℚ) ≤ l.length by exact_mod_cast Nat.zero_le _)
          grind
      have hjo : ∀ v, eo = some v → v ≤ e := by
        intro v hv; subst hv; cases ee <;> simp [joinExp] at hj <;> omega
      have hje : ∀ v, ee = some v → v ≤ e := by
        intro v hv; subst hv; cases eo <;> simp [joinExp] at hj <;> omega
      have go := group _ eo So hbo hO hjo
      have ge := group _ ee Se hbe hE hje
      have ro := absQ_rdGrid_le So (e - ((23 + P.neab : ℕ) : ℤ))
      have re := absQ_rdGrid_le Se (e - ((23 + P.neab : ℕ) : ℤ))
      have tri := absQ_add_le (rdGrid So (e - ((23 + P.neab : ℕ) : ℤ)))
        (rdGrid Se (e - ((23 + P.neab : ℕ) : ℤ)))
      have hl : ((oddIndexed ps).length : ℚ) + (evenIndexed ps).length = ps.length := by
        exact_mod_cast hlen
      refine ⟨(rdGrid_onGrid _ _).add (rdGrid_onGrid _ _), ?_⟩
      have : ((oddIndexed ps).length : ℚ) * pow2 (e + 2) + (evenIndexed ps).length * pow2 (e + 2) =
          ps.length * pow2 (e + 2) := by rw [← Rat.add_mul, hl]
      grind
  · -- global alignment
    cases hs : alignedSum P.neab ps with
    | mk o S =>
      simp only
      refine ⟨fun ho => by subst ho; exact alignedSum_none hs, fun e he => ?_⟩
      subst he
      obtain ⟨hg, hS⟩ := alignedSum_facts hb hs
      refine ⟨hg, ?_⟩
      have := pow2_pos (e - ((23 + P.neab : ℕ) : ℤ))
      grind

/-! ## The late addition of `c` -/

/-- The CDNA 3 late-addition parameters: `n_eab = 1`, `e_{c=0} = −126`, `(24, 32, RD)` and 31
fractional bits after normalization, a cutoff (if any) beyond 24, and at most 16 products. -/
structure LateModel (P : Model) : Prop where
  neab : P.neab = 1
  cZero : P.cZeroExp = some (-126)
  cFrac : P.late.cFracBits = 24
  sumFrac : P.late.sumFracBits = 32
  accFrac : P.late.accFracBits = 31
  cut : ∀ n, P.late.cCutoff = some n → 24 ≤ n
  nfma : P.nfma ≤ 16

/-- `s'_c` on the product grid, between `−2^(e+1)` and `2^(e+1) − 2^(e−23)`. -/
theorem shiftedC_bounds {P : Model} (hL : LateModel P) {e eC : ℤ} {c : Unpacked}
    (hc : C32 c.value eC) (he : eC ≤ e) :
    OnGrid (shiftedC P e eC c) (e - 24) ∧ shiftedC P e eC c ≤ 16777215 * pow2 (e - 23) ∧
      -pow2 (e + 1) ≤ shiftedC P e eC c := by
  have hle := hc.le he
  have hp := pow2_pos (e + 1)
  have hlt := hc.lt
  have hp1 := pow2_le_of_le (show eC + 1 ≤ e + 1 by omega)
  have rd : OnGrid (rdGrid c.value (e - 24)) (e - 24) ∧
      rdGrid c.value (e - 24) ≤ 16777215 * pow2 (e - 23) ∧
      -pow2 (e + 1) ≤ rdGrid c.value (e - 24) := by
    refine ⟨rdGrid_onGrid _ _, ?_, ?_⟩
    · have := (rdGrid_bounds c.value (e - 24)).1
      have : c.value ≤ absQ c.value := by unfold absQ; split <;> grind
      grind
    · apply le_rdGrid
      · have := (onGrid_pow2 (e + 1) 25).neg
        rwa [show e + 1 - ((25 : ℕ) : ℤ) = e - 24 by omega] at this
      · rw [absQ_lt_iff] at hlt; grind
  have zero : OnGrid (0 : ℚ) (e - 24) ∧ (0 : ℚ) ≤ 16777215 * pow2 (e - 23) ∧ -pow2 (e + 1) ≤ 0 := by
    have := pow2_pos (e - 23)
    exact ⟨OnGrid.zero _, by grind, by grind⟩
  unfold shiftedC
  rw [hL.cFrac]
  split
  · split
    · exact zero
    · exact rd
  · exact rd

theorem shiftedC_mono {P : Model} (hL : LateModel P) {e eC eC' : ℤ} {c c' : Unpacked}
    (hc : C32 c.value eC) (hc' : C32 c'.value eC') (hv : c.value ≤ c'.value) :
    shiftedC P e eC c ≤ shiftedC P e eC' c' := by
  unfold shiftedC
  rw [hL.cFrac]
  have hlt := hc.lt
  have hlt' := hc'.lt
  have := hc.emin
  have := hc'.emin
  split
  · rename_i n hn
    have hn24 := hL.cut n hn
    by_cases h1 : e - eC > n <;> by_cases h2 : e - eC' > n <;> simp only [h1, h2, ↓reduceIte]
    · exact Rat.le_refl
    · -- `c` is cut off, `c'` is not: `c' ≥ 0`
      have hge := hc'.ge (by omega)
      have hp := pow2_le_of_le (show eC + 1 ≤ eC' by omega)
      apply le_rdGrid (OnGrid.zero _)
      rw [absQ_lt_iff] at hlt
      by_cases hneg : c'.value < 0
      · rw [absQ_of_neg hneg] at hge; grind
      · grind
    · -- `c'` is cut off, `c` is not: `c ≤ 0`
      have hge := hc.ge (by omega)
      have hp := pow2_le_of_le (show eC' + 1 ≤ eC by omega)
      have := (rdGrid_bounds c.value (e - ((24 : ℕ) : ℤ))).1
      rw [absQ_lt_iff] at hlt'
      by_cases hpos : 0 < c.value
      · rw [absQ_of_nonneg (Rat.le_of_lt hpos)] at hge; grind
      · grind
    · exact rdGrid_mono _ hv
  · exact rdGrid_mono _ hv

/-- **The late addition is monotone in `c`.** With `e_max` and `S_{p_i,sum}` fixed, a larger `c`
gives a larger `S_acc`, within either branch and across the switch at `e_c = e_max`. -/
theorem lateSum_mono {P : Model} (hL : LateModel P) {eMax : Option ℤ} {pSum : ℚ}
    (hpn : eMax = none → pSum = 0)
    (hps : ∀ e, eMax = some e → OnGrid pSum (e - 24) ∧ absQ pSum < pow2 (e + 7))
    {c c' : Unpacked} {eC eC' : ℤ} (hc : cExp P c = some eC) (hc' : cExp P c' = some eC')
    (h32 : C32 c.value eC) (h32' : C32 c'.value eC') (hv : c.value ≤ c'.value) :
    lateSum P eMax pSum c ≤ lateSum P eMax pSum c' := by
  unfold lateSum shiftedSum
  rw [hc, hc', hL.accFrac, hL.sumFrac]
  simp only
  cases eMax with
  | none =>
    rw [hpn rfl, show rdFrac 0 eC 32 = 0 from rdGrid_zero _, show rdFrac 0 eC' 32 = 0 from rdGrid_zero _]
    exact normalizeRD_mono 31 (by grind)
  | some e =>
    obtain ⟨hgrid, hbound⟩ := hps e rfl
    have hpb := (absQ_lt_iff pSum (pow2 (e + 7))).mp hbound
    have e7 : pow2 (e + 7) = 1073741824 * pow2 (e - 23) := by
      rw [pow2_split (e + 7) 30, show e + 7 - ((30 : ℕ) : ℤ) = e - 23 by omega]; rfl
    have e1 : pow2 (e + 1) = 16777216 * pow2 (e - 23) := by
      rw [pow2_split (e + 1) 24, show e + 1 - ((24 : ℕ) : ℤ) = e - 23 by omega]; rfl
    have hB := pow2_pos (e - 23)
    simp only
    by_cases h1 : eC ≤ e <;> by_cases h2 : eC' ≤ e <;> simp only [h1, h2, ↓reduceIte]
    · -- both before `e_max`
      have := shiftedC_mono (e := e) hL h32 h32' hv
      grind
    · -- the switch: `c` before `e_max`, `c'` after
      obtain ⟨hsg, hsu, _⟩ := shiftedC_bounds hL h32 h1
      have hle := h32.le h1
      have hneq : eC' ≠ -126 := by have := h32.emin; omega
      have hge' := h32'.ge hneq
      have hpe := pow2_le_of_le (show e + 1 ≤ eC' by omega)
      have hvpos : 0 ≤ c'.value := by
        by_cases hneg : c'.value < 0
        · exfalso
          rw [absQ_of_neg hneg] at hge'
          rw [absQ_le_iff] at hle
          grind
        · grind
      rw [absQ_of_nonneg hvpos] at hge'
      have eA : pow2 eC' = 4294967296 * pow2 (eC' - ((32 : ℕ) : ℤ)) := by
        rw [pow2_split eC' 32]; rfl
      have hA := pow2_pos (eC' - ((32 : ℕ) : ℤ))
      have ⟨r1, r2⟩ := rdGrid_bounds pSum (eC' - ((32 : ℕ) : ℤ))
      show pSum + shiftedC P e eC c ≤
        normalizeRD 31 (rdGrid pSum (eC' - ((32 : ℕ) : ℤ)) + c'.value)
      have hYg : OnGrid (pSum + shiftedC P e eC c) (e - 24) := hgrid.add hsg
      generalize hT : rdGrid pSum (eC' - ((32 : ℕ) : ℤ)) + c'.value = T
      have hTY : pSum + shiftedC P e eC c < T := by grind
      by_cases hT0 : T = 0
      · subst hT0
        have : normalizeRD 31 0 = 0 := by unfold normalizeRD; simp
        rw [this]
        exact Rat.le_of_lt hTY
      · have hTa := absQ_pos hT0
        by_cases hn : normExp (absQ T) ≤ e + 7
        · exact le_normalizeRD 31 hT0 (hYg.mono (by omega)) (Rat.le_of_lt hTY)
        · obtain ⟨_, hn2, hn3⟩ := normExp_bounds hTa
          have hn2 := hn2 (by have := h32.emin; omega)
          have hpn8 := pow2_le_of_le (show e + 8 ≤ normExp (absQ T) by omega)
          have e8 : pow2 (e + 8) = 2 * pow2 (e + 7) := by
            rw [show e + 8 = (e + 7) + 1 by omega, pow2_succ, Rat.mul_comm]
          have hTpos : 0 < T := by
            by_cases hneg : T < 0
            · exfalso; have := absQ_of_neg hneg; grind
            · grind
          have hTabs := absQ_of_nonneg (Rat.le_of_lt hTpos)
          have hgt := normalizeRD_gt 31 hT0
          have eN : pow2 (normExp (absQ T)) =
              2147483648 * pow2 (normExp (absQ T) - ((31 : ℕ) : ℤ)) := by
            rw [pow2_split _ 31]; rfl
          grind
    · -- the switch back: `c` after `e_max`, `c'` before
      obtain ⟨_, _, hsl⟩ := shiftedC_bounds hL h32' h2
      have hneq : eC ≠ -126 := by have := h32'.emin; omega
      have hge := h32.ge hneq
      have hlt' := h32'.lt
      have hp := pow2_le_of_le (show eC' + 1 ≤ e + 1 by omega)
      have hp2 := pow2_le_of_le (show e + 1 ≤ eC by omega)
      have hvneg : c.value < 0 := by
        by_cases hpos : 0 ≤ c.value
        · exfalso
          rw [absQ_of_nonneg hpos] at hge
          rw [absQ_lt_iff] at hlt'
          grind
        · grind
      rw [absQ_of_neg hvneg] at hge
      have := normalizeRD_le 31 (rdFrac pSum eC 32 + c.value)
      have := (rdGrid_bounds pSum (eC - ((32 : ℕ) : ℤ))).1
      show normalizeRD 31 (rdGrid pSum (eC - ((32 : ℕ) : ℤ)) + c.value) ≤ _
      grind
    · -- both after `e_max`
      apply normalizeRD_mono 31
      show rdGrid pSum (eC - ((32 : ℕ) : ℤ)) + c.value ≤ rdGrid pSum (eC' - ((32 : ℕ) : ℤ)) + c'.value
      rcases Int.lt_trichotomy eC eC' with hlt | heq | hgt
      · have hneq : eC' ≠ -126 := by have := h32.emin; omega
        have hge' := h32'.ge hneq
        have hlt := h32.lt
        have hp := pow2_le_of_le (show eC + 1 ≤ eC' by omega)
        have hvpos : 0 ≤ c'.value := by
          by_cases hneg : c'.value < 0
          · exfalso
            rw [absQ_of_neg hneg] at hge'
            rw [absQ_lt_iff] at hlt
            grind
          · grind
        rw [absQ_of_nonneg hvpos] at hge'
        have hle := h32.le (show eC ≤ eC' - 1 by omega)
        have : c.value ≤ absQ c.value := by unfold absQ; split <;> grind
        have e24 : pow2 eC' = 16777216 * pow2 (eC' - 1 - 23) := by
          rw [pow2_split eC' 24, show eC' - ((24 : ℕ) : ℤ) = eC' - 1 - 23 by omega]; rfl
        have e32 : pow2 (eC' - 1 - 23) = 256 * pow2 (eC' - ((32 : ℕ) : ℤ)) := by
          rw [pow2_split (eC' - 1 - 23) 8, show eC' - 1 - 23 - ((8 : ℕ) : ℤ) = eC' - ((32 : ℕ) : ℤ) by omega]
          rfl
        have := pow2_pos (eC' - ((32 : ℕ) : ℤ))
        have ⟨r1, _⟩ := rdGrid_bounds pSum (eC - ((32 : ℕ) : ℤ))
        have ⟨_, r2⟩ := rdGrid_bounds pSum (eC' - ((32 : ℕ) : ℤ))
        grind
      · subst heq; grind
      · have := rdGrid_coarse pSum (show eC' - ((32 : ℕ) : ℤ) ≤ eC - ((32 : ℕ) : ℤ) by omega)
        grind

/-! ## One block -/

theorem prepare_same {P : Model} {a : List P.a.Word} {b : List P.b.Word} {c c' : F32}
    {px px' : Prepared} (h : prepare (P := P) ⟨a, b, c⟩ = some px)
    (h' : prepare (P := P) ⟨a, b, c'⟩ = some px') : px.a = px'.a ∧ px.b = px'.b := by
  unfold prepare at h h'
  cases hA : a.mapM fun w => (P.a.read w).toFinite <;> rw [hA] at h h' <;> simp at h h'
  cases hB : b.mapM fun w => (P.b.read w).toFinite <;> rw [hB] at h h' <;> simp at h h'
  cases hC : (binary32.decode c).toFinite <;> rw [hC] at h <;> simp at h
  cases hC' : (binary32.decode c').toFinite <;> rw [hC'] at h' <;> simp at h'
  rw [← h, ← h']; exact ⟨rfl, rfl⟩

/-- Flushing a decoded binary32 value is `flushValue` of its value. -/
theorem flush_value32 {w : F32} {c : Unpacked} (h : (binary32.decode w).toFinite = some c) :
    c.flush.value = flushValue c.value := by
  obtain ⟨ht, hm, he1, _, hn⟩ := decode32_finite_fields (toFinite_some h)
  unfold Unpacked.flush flushValue
  rw [ht]
  have hq := pow2_pos (c.e - 23)
  by_cases hs : c.m < 2 ^ 23
  · have he : c.e = -126 := by
      have : (2 : ℕ) ^ 23 = 8388608 := rfl
      rcases hn with hn | hn
      · omega
      · exact hn
    have hsmall : absQ c.value < pow2 (-126) := by
      rw [Unpacked.absQ_value, ht, he]
      have : (c.m : ℚ) < ((2 ^ 23 : ℕ) : ℚ) := by exact_mod_cast hs
      have h2 := Rat.mul_lt_mul_of_pos_right this (pow2_pos (-126 - ((23 : ℕ) : ℤ)))
      rwa [← pow2_natCast, ← pow2_add, show ((23 : ℕ) : ℤ) + (-126 - ((23 : ℕ) : ℤ)) = -126 by omega] at h2
    simp only [hs, ↓reduceIte, hsmall]
    exact (Unpacked.value_eq_zero_iff _).mpr rfl
  · have hbig : ¬ absQ c.value < pow2 (-126) := by
      apply Rat.not_lt.mpr
      rw [Unpacked.absQ_value, ht]
      have : ((2 ^ 23 : ℕ) : ℚ) ≤ (c.m : ℚ) := by exact_mod_cast (Nat.not_lt.mp hs)
      have h2 := Rat.mul_le_mul_of_nonneg_right this (Rat.le_of_lt (pow2_pos (c.e - ((23 : ℕ) : ℤ))))
      rw [← pow2_natCast, ← pow2_add, show ((23 : ℕ) : ℤ) + (c.e - ((23 : ℕ) : ℤ)) = c.e by omega] at h2
      exact Rat.le_trans (pow2_le_of_le he1) h2
    simp only [hs, ↓reduceIte, hbig]

theorem pairwiseSum_c {P : Model} {px px' : Prepared} {s s' : ℚ} (ha : px.a = px'.a)
    (hb : px.b = px'.b) (h : pairwiseSum P px = some s) (h' : pairwiseSum P px' = some s') :
    s - (if P.subnormals then px else px.flushed).c.value =
      s' - (if P.subnormals then px' else px'.flushed).c.value := by
  have hp : (if P.subnormals then px else px.flushed).p = (if P.subnormals then px' else px'.flushed).p := by
    split <;> simp [Prepared.p, Prepared.flushed, ha, hb]
  unfold pairwiseSum at h h'
  dsimp only at h h'
  rw [hp] at h
  generalize (if P.subnormals then px' else px'.flushed) = y' at h h' ⊢
  generalize (if P.subnormals then px else px.flushed) = y at h h' ⊢
  cases hm : y'.p.mapM fun p => flValue (!P.subnormals) p.value with
  | none => rw [hm] at h; simp at h
  | some ps =>
    rw [hm] at h h'
    cases ht : pairwiseGroupSum (!P.subnormals) ps.length ps with
    | none => simp [ht] at h
    | some t =>
      change (pairwiseGroupSum (!P.subnormals) ps.length ps).bind (fun t => some (y.c.value + t)) = some s at h
      change (pairwiseGroupSum (!P.subnormals) ps.length ps).bind (fun t => some (y'.c.value + t)) = some s' at h'
      rw [ht] at h h'
      simp only [Option.bind_some, Option.some.injEq] at h h'
      subst h; subst h'
      grind

/-- A model whose output is monotone in `c`: every configuration of the paper. -/
def MonotoneModel (P : Model) : Prop :=
  P.accumulation = .correctRounding ∨ P.accumulation = .pairWiseSum ∨
    ((P.accumulation = .globalAlignment ∨ P.accumulation = .oddEvenGrouping) ∧ LateModel P)

theorem accumulate_c_mono {P : Model} (hP : MonotoneModel P) {a : List P.a.Word}
    {b : List P.b.Word} {c c' : F32} {px px' : Prepared}
    (hp : prepare (P := P) ⟨a, b, c⟩ = some px) (hp' : prepare (P := P) ⟨a, b, c'⟩ = some px')
    (hlen : a.length = P.nfma) (hv : px.c.value ≤ px'.c.value) {s s' : ℚ}
    (hs : accumulate P px = .ok s) (hs' : accumulate P px' = .ok s') : s ≤ s' := by
  obtain ⟨ha, hb⟩ := prepare_same hp hp'
  have hpp : px.p = px'.p := by simp [Prepared.p, ha, hb]
  rcases hP with hacc | hacc | ⟨hacc, hL⟩
  · unfold accumulate at hs hs'
    rw [hacc] at hs hs'
    split at hs <;> simp at hs
    split at hs' <;> simp at hs'
    subst hs; subst hs'
    unfold Prepared.exact
    rw [hpp]; grind
  · have h1 := accumulate_pairwise hacc hs
    have h2 := accumulate_pairwise hacc hs'
    have hd := pairwiseSum_c ha hb h1 h2
    have hc1 := flush_value32 (prepare_c hp)
    have hc2 := flush_value32 (prepare_c hp')
    have hf := flushValue_mono hv
    split at hd
    · grind
    · simp only [Prepared.flushed] at hd
      grind
  · rw [accumulate_aligned hacc hs, accumulate_aligned hacc hs']
    unfold alignedAccumulation
    simp only
    rw [hpp]
    obtain ⟨_, hA, hB⟩ := prepare_bounded hp'
    have hprod := products_bounded hA hB
    have hplen : px'.p.length ≤ 16 := by
      have h1 := Prepared.p_length px'
      have h2 : px'.a.length = a.length := (prepare_bounded hp').1
      have := hL.nfma
      have : px'.p.length ≤ px'.a.length := by rw [h1]; exact Nat.min_le_left _ _
      omega
    obtain ⟨hn, hsome⟩ := productSum_facts P hprod
    obtain ⟨eC, hce, h32⟩ := c32_of_decode hL.cZero (prepare_c hp)
    obtain ⟨eC', hce', h32'⟩ := c32_of_decode hL.cZero (prepare_c hp')
    apply lateSum_mono hL hn _ hce hce' h32 h32' hv
    intro e he
    obtain ⟨hg, hbd⟩ := hsome e he
    have h24 : e - ((23 + P.neab : ℕ) : ℤ) = e - 24 := by rw [hL.neab]; rfl
    rw [h24] at hg hbd
    refine ⟨hg, ?_⟩
    have hq := pow2_pos (e - 24)
    have e2 : pow2 (e + 2) = 67108864 * pow2 (e - 24) := by
      rw [pow2_split (e + 2) 26, show e + 2 - ((26 : ℕ) : ℤ) = e - 24 by omega]; rfl
    have e7 : pow2 (e + 7) = 2147483648 * pow2 (e - 24) := by
      rw [pow2_split (e + 7) 31, show e + 7 - ((31 : ℕ) : ℤ) = e - 24 by omega]; rfl
    have hl : (px'.p.length : ℚ) ≤ 16 := by exact_mod_cast hplen
    have := Rat.mul_le_mul_of_nonneg_right hl (Rat.le_of_lt (pow2_pos (e + 2)))
    grind

/-- **Monotonicity in `c`.** On every configuration of the paper, for the same `a` and `b`, a
larger `c` never gives a smaller output. -/
theorem evalBlock_c_monotone {P : Model} (hP : MonotoneModel P) {a : List P.a.Word}
    {b : List P.b.Word} {c c' : F32} {t t' : BlockTrace P}
    (h : evalBlock (P := P) ⟨a, b, c⟩ = .ok t) (h' : evalBlock (P := P) ⟨a, b, c'⟩ = .ok t')
    (hc : wordValue c ≤ wordValue c') : wordValue t.d ≤ wordValue t'.d := by
  obtain ⟨hla, _, hp, hs, hd⟩ := evalBlock_ok h
  obtain ⟨_, _, hp', hs', hd'⟩ := evalBlock_ok h'
  have hv : t.prepared.c.value ≤ t'.prepared.c.value := by
    rw [← wordValue_of_decode (prepare_c hp), ← wordValue_of_decode (prepare_c hp')]; exact hc
  exact fl32_mono hd hd' (accumulate_c_mono hP hp hp' hla hv hs hs')

/-! ## Inner products -/

theorem runBlocks_c_monotone {P : Model} (hP : MonotoneModel P) :
    ∀ (bs : List (List P.a.Word × List P.b.Word)) (c c' : F32) (ts ts' : List (BlockTrace P)),
      runBlocks P c bs = .ok ts → runBlocks P c' bs = .ok ts' → wordValue c ≤ wordValue c' →
      wordValue (lastOutput c ts) ≤ wordValue (lastOutput c' ts')
  | [], c, c', ts, ts', h, h', hc => by
    simp [runBlocks] at h h'; subst h; subst h'; exact hc
  | ab :: rest, c, c', ts, ts', h, h', hc => by
    obtain ⟨t, us, he, hr, rfl⟩ := runBlocks_cons h
    obtain ⟨t', us', he', hr', rfl⟩ := runBlocks_cons h'
    exact runBlocks_c_monotone hP rest t.d t'.d us us' hr hr' (evalBlock_c_monotone hP he he' hc)

/-- **Inner products are monotone in `c`.** -/
theorem dotBits_c_monotone {P : Model} (hP : MonotoneModel P) {a : List P.a.Word}
    {b : List P.b.Word} {c c' d d' : F32} (hlen : a.length = b.length)
    (h : dotBits P a b c = .ok d) (h' : dotBits P a b c' = .ok d')
    (hc : wordValue c ≤ wordValue c') : wordValue d ≤ wordValue d' := by
  obtain ⟨ts, hr, hl⟩ := (dotBits_ok_iff P c d hlen).mp h
  obtain ⟨ts', hr', hl'⟩ := (dotBits_ok_iff P c' d' hlen).mp h'
  rw [← hl, ← hl']
  exact runBlocks_c_monotone hP _ c c' ts ts' hr hr' hc

/-! ## The models -/

theorem lateModel_cdna3F16 : LateModel cdna3F16 :=
  ⟨rfl, rfl, rfl, rfl, rfl, fun _ h => by simp [cdna3F16] at h, by decide⟩
theorem lateModel_cdna3BF16 : LateModel cdna3BF16 :=
  ⟨rfl, rfl, rfl, rfl, rfl, fun _ h => by simp [cdna3BF16] at h, by decide⟩
theorem lateModel_cdna3XF32 : LateModel cdna3XF32 :=
  ⟨rfl, rfl, rfl, rfl, rfl, fun _ h => by simp [cdna3XF32] at h, by decide⟩
theorem lateModel_cdna3FP8 (fa fb : Format) : LateModel (cdna3FP8 fa fb) :=
  ⟨rfl, rfl, rfl, rfl, rfl, fun n h => by simp [cdna3FP8] at h; omega, by simp [cdna3FP8]⟩

/-- Every architecture and input format of the paper is monotone in `c`. -/
theorem paper_models_monotone :
    MonotoneModel sfmaF32 ∧ MonotoneModel cdna1F16 ∧ MonotoneModel cdna1BF16 ∧
    MonotoneModel cdna2F16 ∧ MonotoneModel cdna2BF16 ∧ MonotoneModel cdna2BF16_1k ∧
    MonotoneModel cdna3F16 ∧ MonotoneModel cdna3BF16 ∧ MonotoneModel cdna3XF32 ∧
    ∀ fa fb, MonotoneModel (cdna3FP8 fa fb) :=
  ⟨Or.inl rfl, Or.inl rfl, Or.inl rfl, Or.inr (Or.inl rfl), Or.inr (Or.inl rfl),
    Or.inr (Or.inl rfl), Or.inr (Or.inr ⟨Or.inl rfl, lateModel_cdna3F16⟩),
    Or.inr (Or.inr ⟨Or.inl rfl, lateModel_cdna3BF16⟩),
    Or.inr (Or.inr ⟨Or.inl rfl, lateModel_cdna3XF32⟩),
    fun fa fb => Or.inr (Or.inr ⟨Or.inr rfl, lateModel_cdna3FP8 fa fb⟩)⟩

end MatrixCore
