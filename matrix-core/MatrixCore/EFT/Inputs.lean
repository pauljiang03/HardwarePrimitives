import MatrixCore.EFT.Dot

/-! # The fast path from the inputs alone

A condition on the decoded inputs and a bound on the error of `D`, such as a generation's a priori
error bound, under which the guard holds: the low parts fit 24 bits above their lowest bit, and the
overlap and `H` are FP32 values. -/

namespace MatrixCore

/-! ## The lowest bit of a dyadic -/

theorem trailingZerosAux_pow_mul {o : ℕ} (ho : o % 2 = 1) :
    ∀ (n fuel : ℕ), n ≤ fuel → trailingZerosAux fuel (2 ^ n * o) = n
  | 0, 0, _ => by simp [trailingZerosAux]
  | 0, fuel + 1, _ => by simp [trailingZerosAux]; omega
  | n + 1, fuel + 1, h => by
    have hpos : 0 < 2 ^ (n + 1) * o := Nat.mul_pos (Nat.two_pow_pos _) (by omega)
    have heven : 2 ^ (n + 1) * o % 2 = 0 := by
      rw [Nat.pow_succ', Nat.mul_assoc]; exact Nat.mul_mod_right 2 _
    have hhalf : 2 ^ (n + 1) * o / 2 = 2 ^ n * o := by
      rw [Nat.pow_succ', Nat.mul_assoc, Nat.mul_div_cancel_left _ (by decide)]
    unfold trailingZerosAux
    rw [if_pos ⟨by omega, heven⟩, hhalf, trailingZerosAux_pow_mul ho n fuel (by omega)]

theorem two_pow_le_self_mul {o : ℕ} (ho : 0 < o) (n : ℕ) : n ≤ 2 ^ n * o :=
  Nat.le_trans (Nat.le_of_lt Nat.lt_two_pow_self) (Nat.le_mul_of_pos_right _ ho)

theorem coprime_two_pow_of_odd {o : ℕ} (ho : o % 2 = 1) (m : ℕ) : (2 ^ m).gcd o = 1 := by
  have h2 : Nat.Coprime o 2 := by
    show Nat.gcd o 2 = 1
    rw [Nat.gcd_comm, Nat.gcd_rec, ho]; rfl
  exact (Nat.Coprime.pow_right m h2).symm.gcd_eq_one

/-- An odd multiple of `2^ℓ` has its lowest bit at `ℓ`. -/
theorem lowestBitExp_odd {k : ℤ} (hk : k.natAbs % 2 = 1) (ℓ : ℤ) :
    lowestBitExp ((k : ℚ) * pow2 ℓ) = ℓ := by
  have hk0 : 0 < k.natAbs := by omega
  unfold lowestBitExp
  rcases Int.eq_nat_or_neg ℓ with ⟨n, rfl | rfl⟩
  · have hx : (k : ℚ) * pow2 (n : ℤ) = ((k * 2 ^ n : ℤ) : ℚ) := by
      rw [pow2_natCast]; push_cast; rfl
    rw [hx, Rat.num_intCast, Rat.den_intCast]
    have ha : (k * 2 ^ n).natAbs = 2 ^ n * k.natAbs := by
      rw [Int.natAbs_mul, Int.natAbs_pow]; simp [Nat.mul_comm]
    rw [ha, trailingZerosAux_pow_mul hk n _ (two_pow_le_self_mul hk0 n)]
    have : Nat.log2 1 = 0 := by decide
    rw [this]; omega
  · have hx : (k : ℚ) * pow2 (-(n : ℤ)) = mkRat k (2 ^ n) := by
      rw [Rat.mkRat_eq_div, Rat.div_def, ← pow2_natCast]
      congr 1
      unfold pow2; rw [Rat.zpow_neg]
    have hg : (2 ^ n).gcd k.natAbs = 1 := coprime_two_pow_of_odd hk n
    have hnum : (mkRat k (2 ^ n)).num = k := by
      rw [Rat.num_mkRat, if_neg (Nat.pos_iff_ne_zero.mp (Nat.two_pow_pos n)), hg]; simp
    have hden : (mkRat k (2 ^ n)).den = 2 ^ n := by
      rw [Rat.den_mkRat, if_neg (Nat.pos_iff_ne_zero.mp (Nat.two_pow_pos n)), hg]; simp
    rw [hx, hnum, hden, Nat.log2_two_pow]
    have := trailingZerosAux_pow_mul hk 0 k.natAbs (Nat.zero_le _)
    simp only [Nat.pow_zero, Nat.one_mul] at this
    rw [this]; omega

theorem exists_two_pow_mul_odd : ∀ n : ℕ, 0 < n → ∃ v o, o % 2 = 1 ∧ n = 2 ^ v * o
  | n, hn => by
    rcases Nat.mod_two_eq_zero_or_one n with h | h
    · have hlt : n / 2 < n := Nat.div_lt_self hn (by decide)
      obtain ⟨v, o, ho, he⟩ := exists_two_pow_mul_odd (n / 2) (by omega)
      refine ⟨v + 1, o, ho, ?_⟩
      rw [Nat.pow_succ, Nat.mul_comm (2 ^ v) 2, Nat.mul_assoc, ← he]; omega
    · exact ⟨0, n, h, by simp⟩

/-- A nonzero multiple of `2^ℓ` lies on the grid of its lowest bit, at or above `ℓ`. -/
theorem lowestBitExp_onGrid {x : ℚ} {ℓ : ℤ} (hx : x ≠ 0) (h : OnGrid x ℓ) :
    ℓ ≤ lowestBitExp x ∧ OnGrid x (lowestBitExp x) := by
  obtain ⟨j, rfl⟩ := h
  have hj : j ≠ 0 := by rintro rfl; simp at hx
  obtain ⟨v, o, ho, he⟩ := exists_two_pow_mul_odd j.natAbs (by omega)
  obtain ⟨k, hk⟩ : ∃ k : ℤ, k = if 0 ≤ j then (o : ℤ) else -(o : ℤ) := ⟨_, rfl⟩
  have hsign : j = k * 2 ^ v := by
    rw [hk]
    rcases Int.natAbs_eq j with h | h <;> rw [h, he] <;> split <;> push_cast <;> grind
  have hodd : k.natAbs % 2 = 1 := by rw [hk]; split <;> simp [ho]
  have hval : (j : ℚ) * pow2 ℓ = (k : ℚ) * pow2 (ℓ + v) := by
    rw [hsign, Rat.intCast_mul, show ((2 ^ v : ℤ) : ℚ) = pow2 (v : ℤ) by
      rw [pow2_natCast]; push_cast; rfl, pow2_add]
    grind
  rw [hval, lowestBitExp_odd hodd]
  exact ⟨by omega, ⟨_, rfl⟩⟩

/-! ## The guard from grids and bounds -/

theorem representable32_of_finite {x : ℚ} (h : FiniteValue32 x) : representable32 x = true := by
  obtain ⟨w, hw⟩ := Option.isSome_iff_exists.mp ((rne32_isSome_iff x).mpr h.abs_lt)
  unfold representable32
  rw [hw, Option.bind_some, rne32_value hw, rneValue_of_finiteValue32 h]
  simp

theorem floor_div_mul_of_onGrid {x : ℚ} {g : ℤ} (h : OnGrid x g) :
    (((x / pow2 g).floor : ℤ) : ℚ) * pow2 g = x := by
  obtain ⟨k, rfl⟩ := h
  rw [Rat.mul_div_cancel (pow2_ne_zero g), Rat.floor_intCast]

theorem sumQ_map_lt {xs : List α} {f : α → ℚ} {B : ℚ} (hne : xs ≠ []) (h : ∀ x ∈ xs, f x < B) :
    sumQ (xs.map f) < xs.length * B := by
  induction xs with
  | nil => exact absurd rfl hne
  | cons x xs ih =>
    simp only [List.map_cons, sumQ, List.length_cons, Rat.natCast_add, Rat.add_mul]
    have hx := h x (List.mem_cons_self ..)
    by_cases hn : xs = []
    · subst hn; simp [sumQ]; grind
    · have := ih hn (fun y hy => h y (List.mem_cons_of_mem _ hy))
      grind

/-- One step of the fold that finds the lowest bit of the nonzero low parts. -/
def lowBitStep (e : ℤ) (x : ℚ) : ℤ := if x = 0 then e else min e (lowestBitExp x)

theorem foldl_lowBitStep_ge {ℓ : ℤ} : ∀ (xs : List ℚ) (e : ℤ), ℓ ≤ e →
    (∀ x ∈ xs, x ≠ 0 → ℓ ≤ lowestBitExp x) → ℓ ≤ xs.foldl lowBitStep e
  | [], _, he, _ => he
  | x :: xs, e, he, h => by
    simp only [List.foldl_cons]
    apply foldl_lowBitStep_ge xs _ _ (fun y hy => h y (List.mem_cons_of_mem _ hy))
    unfold lowBitStep
    split
    · exact he
    · rename_i hx; exact Int.le_min.mpr ⟨he, h x (List.mem_cons_self ..) hx⟩

theorem foldl_lowBitStep_le : ∀ (xs : List ℚ) (e : ℤ),
    xs.foldl lowBitStep e ≤ e ∧ ∀ x ∈ xs, x ≠ 0 → xs.foldl lowBitStep e ≤ lowestBitExp x
  | [], _ => ⟨Int.le_refl _, by simp⟩
  | x :: xs, e => by
    simp only [List.foldl_cons]
    obtain ⟨h1, h2⟩ := foldl_lowBitStep_le xs (lowBitStep e x)
    have hs : lowBitStep e x ≤ e := by unfold lowBitStep; split <;> omega
    refine ⟨Int.le_trans h1 hs, fun y hy hy0 => ?_⟩
    rcases List.mem_cons.mp hy with rfl | hy
    · have : lowBitStep e y ≤ lowestBitExp y := by unfold lowBitStep; rw [if_neg hy0]; omega
      exact Int.le_trans h1 this
    · exact h2 y hy hy0

theorem EftSplit.lowBit_eq (s : EftSplit) : s.lowBit = s.lows.foldl lowBitStep s.q := rfl

theorem EftSplit.lows_onGrid (s : EftSplit) {L : ℤ} (hterms : ∀ t ∈ s.terms, OnGrid t.2 L) :
    ∀ x ∈ s.lows, OnGrid x (min L s.q) := by
  intro x hx
  simp only [EftSplit.lows, List.mem_map] at hx
  obtain ⟨t, ht, rfl⟩ := hx
  exact ((hterms t ht).mono (Int.min_le_left _ _)).sub
    ((EftSplit.high_onGrid t.1 t.2 s.q).mono (Int.min_le_right _ _))

/-- The guard holds when every term lies on `2^L` with `L ≥ −149`, the low parts span at most 24
bits and lie in range, and the overlap and `H` are FP32 values. -/
theorem EftSplit.guard_of_grid (s : EftSplit) (D : ℚ) {L : ℤ} (hq : -149 ≤ s.q) (hL : -149 ≤ L)
    (hterms : ∀ t ∈ s.terms, OnGrid t.2 L)
    (hspan : (s.terms.length : ℚ) * pow2 (s.q - min L s.q) ≤ pow2 24)
    (hrange : (s.terms.length : ℚ) * pow2 s.q ≤ pow2 128)
    (hO : FiniteValue32 (s.overlap D)) (hH : FiniteValue32 s.H) : s.guard D = true := by
  have hgrid := s.lows_onGrid hterms
  have hlb : min L s.q ≤ s.lowBit := by
    rw [EftSplit.lowBit_eq]
    exact foldl_lowBitStep_ge _ _ (Int.min_le_right _ _)
      (fun x hx hx0 => (lowestBitExp_onGrid hx0 (hgrid x hx)).1)
  have hon : ∀ x ∈ s.lows, OnGrid x s.lowBit := by
    intro x hx
    by_cases hx0 : x = 0
    · subst hx0; exact OnGrid.zero _
    · have h1 := (lowestBitExp_onGrid hx0 (hgrid x hx)).2
      have h2 := (foldl_lowBitStep_le s.lows s.q).2 x hx hx0
      rw [← EftSplit.lowBit_eq] at h2
      exact h1.mono h2
  have hcoeffs : s.lowCoeffs.map (fun (z : ℤ) => (z : ℚ) * pow2 s.lowBit) = s.lows := by
    unfold EftSplit.lowCoeffs
    rw [List.map_map]
    conv => rhs; rw [← List.map_id s.lows]
    apply List.map_congr_left
    intro x hx
    exact floor_div_mul_of_onGrid (hon x hx)
  have hmag : (magnitudeSum s.lowCoeffs : ℚ) * pow2 s.lowBit = sumQ (s.lows.map absQ) := by
    rw [← hcoeffs]
    clear hcoeffs hon
    generalize s.lowCoeffs = zs
    induction zs with
    | nil => simp [magnitudeSum, sumQ]
    | cons z zs ih =>
      simp only [magnitudeSum, List.map_cons, sumQ, Rat.natCast_add, Rat.add_mul, ih]
      rw [absQ_mul_pos _ _ (pow2_pos _), absQ_intCast]
  have hlen : s.lows.length = s.terms.length := by simp [EftSplit.lows]
  have hsum : sumQ (s.lows.map absQ) ≤ (s.terms.length : ℚ) * pow2 s.q ∧
      (s.terms ≠ [] → sumQ (s.lows.map absQ) < (s.terms.length : ℚ) * pow2 s.q) := by
    refine ⟨?_, fun hne => ?_⟩
    · have := sumQ_map_le s.lows absQ (pow2 s.q) (fun e he => Rat.le_of_lt (s.lows_abs_lt e he))
      rwa [hlen] at this
    · have := sumQ_map_lt (f := absQ) (by simpa [EftSplit.lows] using hne)
        (fun e he => s.lows_abs_lt e he)
      rwa [hlen] at this
  have hM : magnitudeSum s.lowCoeffs < 2 ^ 24 := by
    by_cases hne : s.terms = []
    · have : s.lowCoeffs = [] := by simp [EftSplit.lowCoeffs, EftSplit.lows, hne]
      rw [this]; simp [magnitudeSum]
    · have h1 := hsum.2 hne
      rw [← hmag] at h1
      have h2 : (s.terms.length : ℚ) * pow2 s.q =
          ((s.terms.length : ℚ) * pow2 (s.q - s.lowBit)) * pow2 s.lowBit := by
        rw [Rat.mul_assoc, ← pow2_add]; congr 2; omega
      rw [h2] at h1
      have h3 := Rat.lt_of_mul_lt_mul_right h1 (Rat.le_of_lt (pow2_pos _))
      have h4 : (s.terms.length : ℚ) * pow2 (s.q - s.lowBit) ≤
          (s.terms.length : ℚ) * pow2 (s.q - min L s.q) :=
        Rat.mul_le_mul_of_nonneg_left (pow2_le_of_le (by omega)) Rat.natCast_nonneg
      have h5 : (magnitudeSum s.lowCoeffs : ℚ) < ((2 ^ 24 : ℕ) : ℚ) := by
        rw [← pow2_natCast]
        exact Std.lt_of_lt_of_le h3 (Rat.le_trans h4 hspan)
      exact_mod_cast h5
  have hR : (magnitudeSum s.lowCoeffs : ℚ) * pow2 s.lowBit < pow2 128 := by
    rw [hmag]
    by_cases hne : s.terms = []
    · have : s.lows = [] := by simp [EftSplit.lows, hne]
      rw [this]; exact pow2_pos _
    · exact Std.lt_of_lt_of_le (hsum.2 hne) hrange
  unfold EftSplit.guard
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq]
  exact ⟨⟨⟨⟨⟨Int.le_trans (Int.le_min.mpr ⟨hL, hq⟩) hlb, hcoeffs.symm⟩, hM⟩, hR⟩,
    representable32_of_finite hO⟩, representable32_of_finite hH⟩

/-! ## The condition on the inputs -/

/-- The cut-off of `eftCutoff`, for a last bit `g` of `D`. -/
def cutoffAt (P : Model) (px : Prepared) (g : ℤ) : ℤ :=
  match P.accumulation with
  | .globalAlignment | .oddEvenGrouping =>
    match hwGrid P px with
    | some h => max g h
    | none => g
  | _ => g

theorem eftCutoff_eq (P : Model) (px : Prepared) (d : ℚ) :
    eftCutoff P px d = cutoffAt P px (ulpExp32 d) := rfl

theorem cutoffAt_mono (P : Model) (px : Prepared) {g g' : ℤ} (h : g ≤ g') :
    cutoffAt P px g ≤ cutoffAt P px g' := by
  unfold cutoffAt; split <;> (try split) <;> omega

/-- The values of the terms `c, p_1, …`; they do not depend on `D`. -/
def termValues (px : Prepared) : List ℚ := px.c.value :: px.p.map Unpacked.value

theorem eftSplit_values (P : Model) (px : Prepared) (d : ℚ) :
    (eftSplit P px d).terms.map Prod.snd = termValues px := by
  simp [eftSplit, termValues, Function.comp_def]

/-- The inputs alone place the fast path: for a bound `E` on the error of `D` against the exact
sum `S`, the low parts span at most 24 bits above `2^-149`, and the overlap and `H` fit FP32 for
every `D` within `E` of `S`. -/
def InputFast (P : Model) (px : Prepared) (E : ℚ) : Prop :=
  let S := absQ px.exact
  let n : ℚ := (px.p.length + 1 : ℕ)
  let gLo := if E < S then normExp (S - E) - 23 else -149
  let qLo := cutoffAt P px gLo
  let qHi := cutoffAt P px (normExp (S + E) - 23)
  let low := (termValues px).foldl lowBitStep qLo
  let B := S + 2 * E + n * pow2 qHi
  (-149 : ℤ) ≤ low ∧ n * pow2 (qHi - low) ≤ pow2 24 ∧ E + n * pow2 qHi < pow2 (gLo + 24) ∧
    B < pow2 (qLo + 24) ∧ B < pow2 128

instance (P : Model) (px : Prepared) (E : ℚ) : Decidable (InputFast P px E) := by
  unfold InputFast; infer_instance

theorem finite_of_onGrid {x : ℚ} {g : ℤ} (hx : OnGrid x g) (hg : -149 ≤ g)
    (h24 : absQ x < pow2 (g + 24)) (h128 : absQ x < pow2 128) : FiniteValue32 x := by
  obtain ⟨k, rfl⟩ := hx
  rw [absQ_mul_pos _ _ (pow2_pos _), absQ_intCast] at h24 h128
  have hk : ((k.natAbs : ℕ) : ℚ) < ((2 ^ 24 : ℕ) : ℚ) := by
    rw [pow2_add] at h24
    rw [← pow2_natCast, Rat.mul_comm (pow2 g)] at *
    exact Rat.lt_of_mul_lt_mul_right h24 (Rat.le_of_lt (pow2_pos g))
  exact grid_finiteValue32 k g hg (by exact_mod_cast hk) h128

/-- From the inputs and any bound `E` on the error of a finite `D`, `InputFast` implies the
guard. -/
theorem guard_of_inputs {P : Model} {px : Prepared} {D : F32} {d E : ℚ}
    (hd : value32 D = some d) (hE : absQ (px.exact - d) ≤ E) (hc : InputFast P px E) :
    (eftSplit P px d).guard d = true := by
  obtain ⟨hlow, hspan, hov, hB, hB128⟩ := hc
  generalize hS : absQ px.exact = S at *
  have hE0 : 0 ≤ E := Rat.le_trans (absQ_nonneg _) hE
  have hd1 : absQ d ≤ S + E := by
    have := absQ_add_le px.exact (d - px.exact)
    rw [absQ_sub_comm] at hE
    have h' : px.exact + (d - px.exact) = d := by grind
    rw [h', hS] at this; grind
  have hd2 : S - E ≤ absQ d := by
    have := absQ_add_le d (px.exact - d)
    have h' : d + (px.exact - d) = px.exact := by grind
    rw [h', hS] at this; grind
  generalize hgLo : (if E < S then normExp (S - E) - 23 else -149) = gLo at *
  have hgHi : ulpExp32 d ≤ normExp (S + E) - 23 := by
    unfold ulpExp32
    split
    · unfold normExp; omega
    · rename_i hd0
      have := normExp_mono (absQ_pos hd0) hd1; omega
  have hgLo' : gLo ≤ ulpExp32 d := by
    rw [← hgLo]
    split
    · rename_i hlt
      have hpos : 0 < S - E := by grind
      have hd0 : d ≠ 0 := by
        intro h0; rw [h0] at hd2; simp [absQ] at hd2; grind
      unfold ulpExp32; rw [if_neg hd0]
      have := normExp_mono hpos hd2; omega
    · exact ulpExp32_ge d
  generalize hqHi : cutoffAt P px (normExp (S + E) - 23) = qHi at *
  have hq := eftCutoff_eq P px d
  have hqLo : cutoffAt P px gLo ≤ eftCutoff P px d := hq ▸ cutoffAt_mono P px hgLo'
  have hqHi' : eftCutoff P px d ≤ qHi := hqHi ▸ hq ▸ cutoffAt_mono P px hgHi
  generalize hlowdef : (termValues px).foldl lowBitStep (cutoffAt P px gLo) = low at *
  have hfold := foldl_lowBitStep_le (termValues px) (cutoffAt P px gLo)
  rw [hlowdef] at hfold
  have hq149 : -149 ≤ (eftSplit P px d).q := Int.le_trans (ulpExp32_ge d) (eftCutoff_ge P px d)
  have hqd : (eftSplit P px d).q = eftCutoff P px d := rfl
  have hterms : ∀ t ∈ (eftSplit P px d).terms, OnGrid t.2 low := by
    intro t ht
    have hv : t.2 ∈ termValues px := by
      rw [← eftSplit_values P px d]; exact List.mem_map_of_mem ht
    by_cases h0 : t.2 = 0
    · rw [h0]; exact OnGrid.zero _
    · have hg : OnGrid t.2 (lowestBitExp t.2) := by
        have hgrid : ∃ u : Unpacked, t.2 = u.value := by
          simp only [termValues, List.mem_cons, List.mem_map] at hv
          rcases hv with h | ⟨u, _, h⟩
          · exact ⟨_, h⟩
          · exact ⟨u, h.symm⟩
        obtain ⟨u, hu⟩ := hgrid
        exact (lowestBitExp_onGrid h0 (hu ▸ u.value_onGrid)).2
      exact hg.mono (hfold.2 _ hv h0)
  have hmin : min low (eftSplit P px d).q = low := by
    rw [hqd]; exact Int.min_eq_left (Int.le_trans hfold.1 hqLo)
  have hlen : ((eftSplit P px d).terms.length : ℚ) = ((px.p.length + 1 : ℕ) : ℚ) := by
    simp [eftSplit]
  have hn0 : (0 : ℚ) ≤ ((px.p.length + 1 : ℕ) : ℚ) := Rat.natCast_nonneg
  have hnq : ((px.p.length + 1 : ℕ) : ℚ) * pow2 (eftCutoff P px d) ≤
      ((px.p.length + 1 : ℕ) : ℚ) * pow2 qHi :=
    Rat.mul_le_mul_of_nonneg_left (pow2_le_of_le hqHi') hn0
  obtain ⟨hoveq, hlows⟩ := overlap_eq_error_add_lows P px d
  have hovb : absQ ((eftSplit P px d).overlap d) ≤ E + ((px.p.length + 1 : ℕ) : ℚ) * pow2 qHi := by
    rw [hoveq]
    have := absQ_add_le (d - px.exact) (sumQ (eftSplit P px d).lows)
    rw [absQ_sub_comm] at this
    grind
  apply EftSplit.guard_of_grid (eftSplit P px d) d hq149 hlow hterms
  · rw [hmin, hlen, hqd]
    refine Rat.le_trans (Rat.mul_le_mul_of_nonneg_left (pow2_le_of_le (by omega)) hn0) hspan
  · rw [hlen, hqd]
    have : (0 : ℚ) ≤ S := hS ▸ absQ_nonneg _
    have h2 : pow2 128 = pow2 128 := rfl
    grind
  · apply finite_of_onGrid (overlap_onGrid P px hd) (ulpExp32_ge d)
    · exact Std.lt_of_le_of_lt hovb (Std.lt_of_lt_of_le hov (pow2_le_of_le (by omega)))
    · have : (0 : ℚ) ≤ S := hS ▸ absQ_nonneg _
      grind
  · apply finite_of_onGrid (eftSplit P px d).H_onGrid hq149
    · have hH : absQ (eftSplit P px d).H ≤ S + 2 * E + ((px.p.length + 1 : ℕ) : ℚ) * pow2 qHi := by
        have h1 : (eftSplit P px d).H = d - (eftSplit P px d).overlap d := by
          unfold EftSplit.overlap; grind
        have := absQ_add_le d (-(eftSplit P px d).overlap d)
        rw [absQ_neg] at this
        rw [h1, show d - (eftSplit P px d).overlap d = d + -(eftSplit P px d).overlap d by grind]
        grind
      exact Std.lt_of_le_of_lt hH (Std.lt_of_lt_of_le hB (pow2_le_of_le (by rw [hqd]; omega)))
    · have hH : absQ (eftSplit P px d).H ≤ S + 2 * E + ((px.p.length + 1 : ℕ) : ℚ) * pow2 qHi := by
        have h1 : (eftSplit P px d).H = d + -(eftSplit P px d).overlap d := by
          unfold EftSplit.overlap; grind
        have := absQ_add_le d (-(eftSplit P px d).overlap d)
        rw [absQ_neg] at this
        rw [h1]
        grind
      exact Std.lt_of_le_of_lt hH hB128

/-! ## The fast path on the Matrix Core's output -/

/-- With `E` bounding the error of the block's output, `InputFast` and an exact sum in range give
the fast path on that output. -/
theorem mcEft_fast_of_inputs {P : Model} {x : BlockInput P} {t : BlockTrace P} {E : ℚ}
    (h : evalBlock x = .ok t) (hE : absQ (t.prepared.exact - wordValue t.d) ≤ E)
    (hc : InputFast P t.prepared E) (hS : absQ t.prepared.exact < overflowThreshold32) :
    ∃ b, mcEft x t.d = .ok (.fast b) := by
  obtain ⟨_, _, _, _, hd⟩ := evalBlock_ok h
  have hg := guard_of_inputs (fl32_value hd) hE hc
  have hs : (rne32 (eftSplit P t.prepared (wordValue t.d)).exact).isSome = true := by
    rw [eftSplit_exact]; exact (rne32_isSome_iff _).mpr hS
  obtain ⟨b, hb⟩ := (EftSplit.run_fast_iff _ _).mpr ⟨hg, hs⟩
  exact ⟨b, by rw [mcEft_of_evalBlock h, hb]⟩

/-- The a priori bound of correct rounding (CDNA 1 and the SFMA). -/
def correctRoundingApriori (px : Prepared) : ℚ := pow2 (-24) * px.absSum + pow2 (-150)

/-- The a priori bound of the pairwise sums of CDNA 2. -/
def pairwiseApriori (P : Model) (px : Prepared) : ℚ :=
  absQ (px.exact - (if P.subnormals then px else px.flushed).exact) +
    pow2 (-21) * (if P.subnormals then px else px.flushed).absSum + pow2 (-120)

/-- The a priori bound of global alignment (CDNA 3). -/
def alignedApriori (P : Model) (px : Prepared) : ℚ :=
  pow2 (-23) * px.absSum + (px.p.length + 4) * gridTerm (productSum P px.p).1 + pow2 (-149)

/-- CDNA 1 and the SFMA, from the inputs alone. -/
theorem correctRounding_fast {P : Model} (hacc : P.accumulation = .correctRounding)
    (hov : P.productOverflow = false) (hs : P.subnormals = true) {x : BlockInput P}
    {t : BlockTrace P} (h : evalBlock x = .ok t)
    (hc : InputFast P t.prepared (correctRoundingApriori t.prepared))
    (hS : absQ t.prepared.exact < overflowThreshold32) : ∃ b, mcEft x t.d = .ok (.fast b) :=
  mcEft_fast_of_inputs h (correctRounding_apriori hacc hov hs h) hc hS

/-- CDNA 2, from the inputs alone. -/
theorem pairwise_fast {P : Model} (hacc : P.accumulation = .pairWiseSum) (hn : P.nfma ≤ 4)
    {x : BlockInput P} {t : BlockTrace P} (h : evalBlock x = .ok t)
    (hc : InputFast P t.prepared (pairwiseApriori P t.prepared))
    (hS : absQ t.prepared.exact < overflowThreshold32) : ∃ b, mcEft x t.d = .ok (.fast b) :=
  mcEft_fast_of_inputs h (pairwise_apriori hacc hn h) hc hS

/-- CDNA 3, from the inputs alone. -/
theorem aligned_fast {P : Model} (hL : LateModel P)
    (hacc : P.accumulation = .globalAlignment ∨ P.accumulation = .oddEvenGrouping)
    (hsub : P.subnormals = true) {x : BlockInput P} {t : BlockTrace P} (h : evalBlock x = .ok t)
    (hc : InputFast P t.prepared (alignedApriori P t.prepared))
    (hS : absQ t.prepared.exact < overflowThreshold32) : ∃ b, mcEft x t.d = .ok (.fast b) :=
  mcEft_fast_of_inputs h (aligned_apriori hL hacc hsub h) hc hS

/-! ## Inner products of any length -/

theorem dotSplit_eq (px : Prepared) (d : ℚ) : dotSplit px d = eftSplit sfmaF32 px d := rfl

/-- The output of an inner product with a finite `c` is a finite word. -/
theorem dotBits_finite {P : Model} {a : List P.a.Word} {b : List P.b.Word} {c D : F32}
    (hlen : a.length = b.length) (hD : dotBits P a b c = .ok D) (hc : ∃ v, value32 c = some v) :
    ∃ d, value32 D = some d := by
  obtain ⟨ts, hr, rfl⟩ := (dotBits_ok_iff P c D hlen).mp hD
  have hall : ∀ t ∈ ts, ∃ v, value32 t.d = some v := by
    intro t ht
    obtain ⟨x, hx⟩ := runBlocks_mem hr t ht
    obtain ⟨_, _, _, _, hd⟩ := evalBlock_ok hx
    exact ⟨_, fl32_value hd⟩
  clear hr hD
  induction ts generalizing c with
  | nil => exact hc
  | cons t ts ih =>
    exact ih (hall t (List.mem_cons_self ..)) (fun u hu => hall u (List.mem_cons_of_mem _ hu))

/-- `InputFast` with the cut-off at `D`'s last bit, as on inner products. -/
abbrev DotInputFast (px : Prepared) (E : ℚ) : Prop := InputFast sfmaF32 px E

/-- With `E` bounding the error of an inner product's output, for example the sum of its blocks'
bounds, `DotInputFast` and an exact sum in range give the fast path. -/
theorem mcEftDot_fast {P : Model} {a : List P.a.Word} {b : List P.b.Word} {c D : F32}
    {px : Prepared} {E : ℚ} (hlen : a.length = b.length) (hD : dotBits P a b c = .ok D)
    (hp : prepare (P := P) ⟨a, b, c⟩ = some px) (hE : absQ (exactDot P a b c - wordValue D) ≤ E)
    (hc : DotInputFast px E) (hS : absQ (exactDot P a b c) < overflowThreshold32) :
    ∃ w, mcEftDot P a b c D = .ok (.fast w) := by
  obtain ⟨d, hd⟩ : ∃ d, value32 D = some d :=
    dotBits_finite hlen hD ⟨px.c.value, by simp [value32, prepare_c hp]⟩
  have hw : wordValue D = d := by simp [wordValue, hd]
  rw [hw, ← prepare_exact_dot hp] at hE
  rw [← prepare_exact_dot hp] at hS
  have hg : (dotSplit px d).guard d = true := by rw [dotSplit_eq]; exact guard_of_inputs hd hE hc
  have hs : (rne32 (dotSplit px d).exact).isSome = true := by
    rw [dotSplit_exact]; exact (rne32_isSome_iff _).mpr hS
  obtain ⟨w, hw'⟩ := (EftSplit.run_fast_iff _ _).mpr ⟨hg, hs⟩
  refine ⟨w, ?_⟩
  unfold mcEftDot
  rw [if_neg (by omega), hp]
  simp only [hd, hw']

end MatrixCore
