import MatrixCore.MC.Block

/-! # Facts about decoded blocks

What `prepare` guarantees and how the exponent and grouping helpers behave, in one place for the
theory files and for downstream proofs:

* `e_max` bounds every nonzero product and is `none` only when all products are zero;
* odd- and even-indexed positions partition the products;
* every finite operand has a significand below 2, so every product has one below 4;
* `prepare` keeps the operand counts, and `c` has 23 mantissa bits. -/

namespace MatrixCore

/-! ## `e_max` -/

theorem foldl_maxExp_none (ps : List Unpacked) : ∀ acc : Option ℤ,
    ps.foldl maxExpStep acc = none → acc = none ∧ ∀ p ∈ ps, p.m = 0 := by
  induction ps with
  | nil => intro acc h; exact ⟨h, by simp⟩
  | cons q qs ih =>
    intro acc h
    simp only [List.foldl_cons] at h
    by_cases hq : q.m = 0
    · simp only [maxExpStep, hq, ↓reduceIte] at h
      obtain ⟨h1, h2⟩ := ih acc h
      refine ⟨h1, ?_⟩
      intro p hp
      rcases List.mem_cons.mp hp with rfl | hp
      · exact hq
      · exact h2 p hp
    · simp only [maxExpStep, hq, ↓reduceIte] at h
      exact absurd (ih _ h).1 (by simp)

/-- No exponent means every product is zero. -/
theorem maxExp_none {ps : List Unpacked} (h : maxExp ps = none) : ∀ p ∈ ps, p.m = 0 :=
  (foldl_maxExp_none ps none h).2

theorem foldl_maxExpStep_le (ps : List Unpacked) (acc : Option ℤ) (r : ℤ)
    (h : ps.foldl maxExpStep acc = some r) :
    (∀ v, acc = some v → v ≤ r) ∧ ∀ p ∈ ps, p.m ≠ 0 → p.e ≤ r := by
  induction ps generalizing acc with
  | nil =>
    simp only [List.foldl_nil] at h
    subst h
    refine ⟨fun v hv => ?_, by simp⟩
    simp only [Option.some.injEq] at hv
    omega
  | cons q qs ih =>
    simp only [List.foldl_cons] at h
    obtain ⟨h1, h2⟩ := ih _ h
    refine ⟨fun v hv => ?_, fun p hp hm => ?_⟩
    · subst hv
      unfold maxExpStep at h1
      by_cases hq : q.m = 0
      · exact h1 v (by simp [hq])
      · have := h1 (max v q.e) (by simp [hq]); omega
    · rcases List.mem_cons.mp hp with rfl | hp
      · unfold maxExpStep at h1
        cases acc with
        | none => exact h1 p.e (by simp [hm])
        | some v => have := h1 (max v p.e) (by simp [hm]); omega
      · exact h2 p hp hm

/-- `e_max` bounds the exponent of every nonzero product. -/
theorem maxExp_le {ps : List Unpacked} {e : ℤ} (h : maxExp ps = some e) :
    ∀ p ∈ ps, p.m ≠ 0 → p.e ≤ e :=
  (foldl_maxExpStep_le ps none e h).2

theorem maxExp_perm {ps qs : List Unpacked} (h : ps.Perm qs) : maxExp ps = maxExp qs := by
  unfold maxExp
  apply h.foldl_eq'
  intro x _ y _ z
  unfold maxExpStep
  by_cases hx : x.m = 0 <;> by_cases hy : y.m = 0 <;> simp only [hx, hy, ↓reduceIte]
  cases z <;> simp <;> omega

theorem sum_of_zero {ps : List Unpacked} (h : ∀ p ∈ ps, p.m = 0) : sumQ (ps.map Unpacked.value) = 0 := by
  induction ps with
  | nil => rfl
  | cons p ps ih =>
    show p.value + sumQ (ps.map Unpacked.value) = 0
    rw [(Unpacked.value_eq_zero_iff p).mpr (h p (by simp)), ih (fun q hq => h q (by simp [hq]))]
    grind

/-! ## Odd and even positions -/

/-- Odd- and even-indexed positions partition a list. -/
theorem sumQ_odd_even (f : α → ℚ) : ∀ l : List α,
    sumQ ((oddIndexed l).map f) + sumQ ((evenIndexed l).map f) = sumQ (l.map f) ∧
      (oddIndexed l).length + (evenIndexed l).length = l.length
  | [] => by constructor <;> simp [oddIndexed, evenIndexed, sumQ] <;> grind
  | [x] => by constructor <;> simp [oddIndexed, evenIndexed, sumQ] <;> grind
  | x :: y :: rest => by
    obtain ⟨h1, h2⟩ := sumQ_odd_even f rest
    simp only [oddIndexed, evenIndexed, List.map_cons, sumQ, List.length_cons]
    constructor
    · grind
    · omega

theorem oddIndexed_subset : ∀ l : List α, ∀ x ∈ oddIndexed l, x ∈ l
  | [] => by simp [oddIndexed]
  | [x] => by simp [oddIndexed]
  | x :: y :: rest => by
    intro z hz
    simp only [oddIndexed, List.mem_cons] at hz ⊢
    rcases hz with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inr (oddIndexed_subset rest z h))

theorem evenIndexed_subset : ∀ l : List α, ∀ x ∈ evenIndexed l, x ∈ l
  | [] => by simp [evenIndexed]
  | [x] => by simp [evenIndexed]
  | x :: y :: rest => by
    intro z hz
    simp only [evenIndexed, List.mem_cons] at hz ⊢
    rcases hz with h | h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (evenIndexed_subset rest z h))

/-! ## Decoded operands -/

theorem toFinite_some {d : Datum} {u : Unpacked} (h : d.toFinite = some u) : d = .finite u := by
  cases d <;> simp [Datum.toFinite] at h; rw [h]

theorem unpackFields_bounded (f : Format) (negative : Bool) (E M : ℕ)
    (hM : M < 2 ^ f.mantissaBits) :
    (f.unpackFields negative E M).t = f.mantissaBits ∧
      (f.unpackFields negative E M).m < 2 ^ (f.mantissaBits + 1) := by
  unfold Format.unpackFields
  rw [Nat.pow_succ]
  split <;> simp <;> omega

theorem decodeNat_bounded {f : Format} {n : ℕ} {u : Unpacked} (h : f.decodeNat n = .finite u) :
    u.t = f.mantissaBits ∧ u.m < 2 ^ (f.mantissaBits + 1) := by
  have hM : n % 2 ^ f.mantissaBits < 2 ^ f.mantissaBits := Nat.mod_lt _ (Nat.two_pow_pos _)
  unfold Format.decodeNat at h
  dsimp only at h
  split at h
  · split at h
    · split at h <;> simp at h
    · simp only [Datum.finite.injEq] at h; subst h; exact unpackFields_bounded _ _ _ _ hM
  · split at h
    · simp at h
    · simp only [Datum.finite.injEq] at h; subst h; exact unpackFields_bounded _ _ _ _ hM

/-- Every finite operand has a significand below 2: `m < 2^(t + 1)`. -/
theorem read_bounded {i : InputFormat} {w : i.Word} {u : Unpacked}
    (h : (i.read w).toFinite = some u) : u.m < 2 ^ (u.t + 1) := by
  cases i with
  | packed f =>
    simp only [InputFormat.read, Format.decode] at h
    cases hd : f.decodeNat w.toNat <;> rw [hd] at h <;> simp [Datum.toFinite] at h
    subst h
    obtain ⟨ht, hm⟩ := decodeNat_bounded hd
    rw [ht]; exact hm
  | xf32 =>
    simp only [InputFormat.read] at h
    cases hd : fp32.decode w <;> rw [hd] at h <;> simp [Datum.toFinite] at h
    subst h
    obtain ⟨_, hm⟩ := decodeNat_bounded (f := fp32) (n := BitVec.toNat w) hd
    simp only [InputFormat.truncateXF32]
    have hm' : _ < 16777216 := hm
    apply (Nat.div_lt_iff_lt_mul (Nat.two_pow_pos 13)).mpr
    simp only [Nat.reducePow, Nat.reduceAdd, Nat.reduceMul]
    omega

/-! ## Prepared blocks -/

theorem prepare_lengths {P : Model} {x : BlockInput P} {px : Prepared} (h : prepare x = some px) :
    px.a.length = x.a.length ∧ px.b.length = x.b.length := by
  unfold prepare at h
  cases hA : x.a.mapM fun w => (P.a.read w).toFinite <;> rw [hA] at h <;> simp at h
  cases hB : x.b.mapM fun w => (P.b.read w).toFinite <;> rw [hB] at h <;> simp at h
  cases hC : (MatrixCore.fp32.decode x.c).toFinite <;> rw [hC] at h <;> simp at h
  subst h
  exact ⟨mapM_length_option hA, mapM_length_option hB⟩

theorem prepare_c_t {P : Model} {x : BlockInput P} {px : Prepared} (h : prepare x = some px) :
    px.c.t = 23 := by
  unfold prepare at h
  cases hA : x.a.mapM fun w => (P.a.read w).toFinite <;> rw [hA] at h <;> simp at h
  cases hB : x.b.mapM fun w => (P.b.read w).toFinite <;> rw [hB] at h <;> simp at h
  cases hC : (MatrixCore.fp32.decode x.c).toFinite <;> rw [hC] at h <;> simp at h
  rename_i c
  subst h
  have hd : MatrixCore.fp32.decode x.c = .finite c := by
    cases hd : MatrixCore.fp32.decode x.c <;> rw [hd] at hC <;> simp [Datum.toFinite] at hC; rw [hC]
  exact (decode32_finite_fields hd).1

theorem prepare_bounded {P : Model} {x : BlockInput P} {px : Prepared} (h : prepare x = some px) :
    px.a.length = x.a.length ∧ (∀ u ∈ px.a, u.m < 2 ^ (u.t + 1)) ∧
      ∀ u ∈ px.b, u.m < 2 ^ (u.t + 1) := by
  unfold prepare at h
  cases hA : x.a.mapM fun w => (P.a.read w).toFinite <;> rw [hA] at h <;> simp at h
  cases hB : x.b.mapM fun w => (P.b.read w).toFinite <;> rw [hB] at h <;> simp at h
  cases hC : (fp32.decode x.c).toFinite <;> rw [hC] at h <;> simp at h
  subst h
  refine ⟨mapM_length_option hA, fun u hu => ?_, fun u hu => ?_⟩
  · obtain ⟨w, _, hw⟩ := mapM_mem_option hA u hu
    exact read_bounded hw
  · obtain ⟨w, _, hw⟩ := mapM_mem_option hB u hu
    exact read_bounded hw

/-- Every product has a significand below 4. -/
theorem products_bounded {px : Prepared} (ha : ∀ u ∈ px.a, u.m < 2 ^ (u.t + 1))
    (hb : ∀ u ∈ px.b, u.m < 2 ^ (u.t + 1)) : ∀ p ∈ px.p, p.m < 2 ^ (p.t + 2) := by
  intro p hp
  obtain ⟨a, ha', b, hb', rfl⟩ := mem_zipWith' hp
  have h1 := ha a ha'
  have h2 := hb b hb'
  simp only [Unpacked.mul]
  calc a.m * b.m < 2 ^ (a.t + 1) * 2 ^ (b.t + 1) := Nat.mul_lt_mul'' h1 h2
    _ = 2 ^ (a.t + b.t + 2) := by rw [← Nat.pow_add]; congr 1; omega

/-- A significand below 2 bounds the value by the next power of two. -/
theorem Unpacked.absQ_value_lt {u : Unpacked} (hm : u.m < 2 ^ (u.t + 1)) :
    absQ u.value < pow2 (u.e + 1) := by
  rw [Unpacked.absQ_value]
  have hmq : (u.m : ℚ) < pow2 ((u.t + 1 : ℕ) : ℤ) := by rw [pow2_natCast]; exact_mod_cast hm
  have := Rat.mul_lt_mul_of_pos_right hmq (pow2_pos (u.e - u.t))
  rwa [← pow2_add, show ((u.t + 1 : ℕ) : ℤ) + (u.e - u.t) = u.e + 1 by omega] at this

/-- The decoded `c` of a prepared block is the decoding of its word. -/
theorem prepare_c {P : Model} {x : BlockInput P} {px : Prepared} (h : prepare x = some px) :
    (fp32.decode x.c).toFinite = some px.c := by
  unfold prepare at h
  cases hA : x.a.mapM fun w => (P.a.read w).toFinite <;> rw [hA] at h <;> simp at h
  cases hB : x.b.mapM fun w => (P.b.read w).toFinite <;> rw [hB] at h <;> simp at h
  cases hC : (fp32.decode x.c).toFinite <;> rw [hC] at h <;> simp at h
  subst h
  rfl

theorem prepare_c_bounded {P : Model} {x : BlockInput P} {px : Prepared}
    (h : prepare x = some px) : px.c.m < 2 ^ (px.c.t + 1) := by
  obtain ⟨ht, hm⟩ := decodeNat_bounded (f := fp32) (n := x.c.toNat) (toFinite_some (prepare_c h))
  rw [ht]; exact hm

/-- `|c| < 2^(e_c + 1)` for the exponent `e_c` the late addition uses. -/
theorem prepare_cExp_bound {P : Model} {x : BlockInput P} {px : Prepared}
    (h : prepare x = some px) : ∀ eC, cExp P px.c = some eC → absQ px.c.value < pow2 (eC + 1) := by
  intro eC he
  unfold cExp at he
  split at he
  · rename_i hm
    rw [(Unpacked.value_eq_zero_iff px.c).mpr hm, show absQ 0 = 0 from rfl]
    exact pow2_pos _
  · simp only [Option.some.injEq] at he
    subst he
    exact Unpacked.absQ_value_lt (prepare_c_bounded h)

end MatrixCore
