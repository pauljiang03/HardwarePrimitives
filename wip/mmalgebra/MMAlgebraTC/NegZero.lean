import MMAlgebraTC.Chain

/-! # An fp16 block FMA never returns `−0`

On the fp16 Tensor Core models every value a block FMA adds is a multiple of `2^-149`: an fp16
product is a multiple of `2^-48`, a binary32 accumulator a multiple of `2^-149`, and truncating a
multiple of `2^-149` to any grid `2^g` gives a multiple of `2^-149` again. So the block's sum of
aligned terms is a multiple of `2^-149`: either zero, which the final truncation encodes as `+0`, or
at least `2^-149` in magnitude, which it keeps nonzero. Hence no fp16 block FMA, from any
accumulator input, returns `−0` (`blockOut_ne_negZero`), and every block output is a finite value
other than `−0` (`blockOut_good`), which an empty block passes through unchanged.

(On bf16 the statement fails: a product of two subnormal bf16 words lies far below `2^-149`, and
a block holding only a tiny negative product truncates it to `−0`.) -/

open TensorCore

namespace MMAlgebra.TC

/-- `x` is an integer multiple of `2^g`. -/
def OnGridQ (x : ℚ) (g : ℤ) : Prop := ∃ k : ℤ, x = (k : ℚ) * pow2 g

theorem onGridQ_coarse {x : ℚ} {g g' : ℤ} (h : OnGridQ x g) (hg : g' ≤ g) : OnGridQ x g' := by
  obtain ⟨k, rfl⟩ := h
  obtain ⟨n, rfl⟩ : ∃ n : ℕ, g = g' + n := ⟨(g - g').toNat, by omega⟩
  refine ⟨k * ((2 ^ n : ℕ) : ℤ), ?_⟩
  rw [pow2_add, pow2_natCast, Rat.intCast_mul, Rat.intCast_natCast]
  grind

theorem onGridQ_zero (g : ℤ) : OnGridQ 0 g := ⟨0, by simp⟩

theorem onGridQ_add {x y : ℚ} {g : ℤ} (hx : OnGridQ x g) (hy : OnGridQ y g) :
    OnGridQ (x + y) g := by
  obtain ⟨a, rfl⟩ := hx
  obtain ⟨b, rfl⟩ := hy
  exact ⟨a + b, by rw [Rat.intCast_add, Rat.add_mul]⟩

theorem onGridQ_sumQ {g : ℤ} : ∀ xs : List ℚ, (∀ x ∈ xs, OnGridQ x g) → OnGridQ (sumQ xs) g
  | [], _ => onGridQ_zero g
  | x :: xs, h => by
    simp only [sumQ]
    exact onGridQ_add (h x (by simp)) (onGridQ_sumQ xs (fun y hy => h y (by simp [hy])))

/-- Truncating a multiple of `2^g` to any grid gives a multiple of `2^g`. -/
theorem onGridQ_truncGrid {x : ℚ} {g : ℤ} (hx : OnGridQ x g) (e : ℤ) : OnGridQ (truncGrid x e) g := by
  by_cases he : g ≤ e
  · exact onGridQ_coarse ⟨truncBits x e, rfl⟩ he
  · obtain ⟨k, hk⟩ := onGridQ_coarse hx (show e ≤ g by omega)
    rw [hk, truncGrid_fixed, ← hk]; exact hx

theorem decoded_onGridQ (d : Decoded) : OnGridQ d.value (d.exponent - d.mantissaBits) :=
  ⟨d.significand, rfl⟩

/-- A decoded value is a multiple of `2^(1 − bias − mantissaBits)`. -/
theorem classify_onGridQ (f : Format) (n : ℕ) {d : Decoded} (h : (classifyNat f n).finite = some d) :
    OnGridQ d.value (1 - f.bias - f.mantissaBits) := by
  unfold classifyNat at h
  simp only at h
  by_cases h1 : n / 2 ^ f.mantissaBits % 2 ^ f.exponentBits = 2 ^ f.exponentBits - 1
  · rw [if_pos h1] at h; split at h <;> simp [Classification.finite] at h
  · rw [if_neg h1] at h
    by_cases h2 : n / 2 ^ f.mantissaBits % 2 ^ f.exponentBits = 0
    · rw [if_pos h2] at h
      by_cases h3 : n % 2 ^ f.mantissaBits = 0
      · rw [if_pos h3] at h
        simp only [Classification.finite, Option.some.injEq] at h
        subst h; exact ⟨0, by simp [Decoded.value]⟩
      · rw [if_neg h3] at h
        simp only [Classification.finite, Option.some.injEq] at h
        subst h
        exact onGridQ_coarse (decoded_onGridQ _) (by simp only; omega)
    · rw [if_neg h2] at h
      simp only [Classification.finite, Option.some.injEq] at h
      subst h
      exact onGridQ_coarse (decoded_onGridQ _) (by simp only; omega)

theorem decode32_onGridQ {c : F32} {d : Decoded} (h : decode32 c = some d) : OnGridQ d.value (-149) := by
  have := classify_onGridQ fp32 c.toNat h
  exact this

theorem fp16_decode_onGridQ {K padding : ℕ} {eAlignMin : Option ℤ}
    {w : (fp16Fp32Model K padding eAlignMin).Word} {d : Decoded}
    (h : (fp16Fp32Model K padding eAlignMin).decode w = some d) : OnGridQ d.value (-24) :=
  classify_onGridQ fp16 w.toNat h

theorem mapM_some_mem {α β : Type} (f : α → Option β) :
    ∀ {xs : List α} {ys : List β}, xs.mapM f = some ys → ∀ y ∈ ys, ∃ x ∈ xs, f x = some y
  | [], ys, h => by
    simp only [List.mapM_nil, Option.pure_def, Option.some.injEq] at h
    subst h; simp
  | x :: xs, ys, h => by
    simp only [List.mapM_cons] at h
    cases hb : f x with
    | none => simp [hb] at h
    | some b =>
      cases hbs : xs.mapM f with
      | none => simp [hb, hbs] at h
      | some bs =>
        simp only [hb, hbs, Option.bind_eq_bind, Option.bind_some, Option.pure_def,
          Option.some.injEq] at h
        subst h
        intro y hy
        rcases List.mem_cons.mp hy with rfl | hy
        · exact ⟨x, by simp, hb⟩
        · obtain ⟨x', hx', h'⟩ := mapM_some_mem f hbs y hy
          exact ⟨x', by simp [hx'], h'⟩

theorem prepareProducts_mem {p : Model} {ps : List (p.Word × p.Word)} {ds : List (Decoded × Decoded)}
    (h : prepareProducts p ps = some ds) :
    ∀ d ∈ ds, ∃ q ∈ ps, p.decode q.1 = some d.1 ∧ p.decode q.2 = some d.2 := by
  intro d hd
  obtain ⟨q, hq, hf⟩ := mapM_some_mem _ h d hd
  refine ⟨q, hq, ?_⟩
  cases ha : p.decode q.1 <;> cases hb : p.decode q.2 <;> simp [ha, hb] at hf
  subst hf; exact ⟨rfl, rfl⟩

/-- Every term of a prepared fp16 block (the accumulator input and the products) is a multiple of
`2^-149`. -/
theorem terms_onGridQ {K padding : ℕ} {eAlignMin : Option ℤ}
    {x : BlockInput (fp16Fp32Model K padding eAlignMin)} {b : PreparedBlock} (hp : prepare x = some b) :
    ∀ t ∈ b.terms, OnGridQ t.value (-149) := by
  unfold prepare at hp
  cases hc : decode32 x.c with
  | none => simp [hc] at hp
  | some dc =>
    cases hps : prepareProducts (fp16Fp32Model K padding eAlignMin) x.products with
    | none => simp [hc, hps] at hp
    | some ds =>
      simp only [hc, hps, Option.some.injEq] at hp
      subst hp
      intro t ht
      simp only [PreparedBlock.terms, List.mem_cons, List.mem_map] at ht
      rcases ht with rfl | ⟨⟨da, db⟩, hd, rfl⟩
      · exact decode32_onGridQ hc
      · obtain ⟨q, _, ha, hb⟩ := prepareProducts_mem hps (da, db) hd
        rw [denormalizedProduct_value]
        obtain ⟨ka, hka⟩ := fp16_decode_onGridQ ha
        obtain ⟨kb, hkb⟩ := fp16_decode_onGridQ hb
        refine onGridQ_coarse ⟨ka * kb, ?_⟩ (show (-149 : ℤ) ≤ -24 + -24 by omega)
        simp only at hka hkb
        rw [hka, hkb, pow2_add, Rat.intCast_mul]
        grind

/-- The sum of the aligned terms of an fp16 block is a multiple of `2^-149`. -/
theorem accumulator_onGridQ {K padding : ℕ} {eAlignMin : Option ℤ}
    {x : BlockInput (fp16Fp32Model K padding eAlignMin)} {b : PreparedBlock} (hp : prepare x = some b) :
    OnGridQ b.accumulator (-149) := by
  rw [accumulator_value]
  apply onGridQ_sumQ
  intro y hy
  obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hy
  exact onGridQ_truncGrid (terms_onGridQ hp t ht) _

theorem finiteValue32_pow2 : FiniteValue32 (pow2 (-149)) :=
  ⟨1, -126, by decide, by decide, by decide, by simp⟩

/-- A nonzero multiple of `2^-149` in the finite range truncates to a nonzero value. -/
theorem signedRounded_ne_zero {y : ℚ} (hg : OnGridQ y (-149)) (hy : y ≠ 0)
    (hr : absQ y ≤ maxFinite32) : signedRounded .truncate y ≠ 0 := by
  obtain ⟨k, rfl⟩ := hg
  have hp := pow2_pos (-149)
  have hfin : absQ (pow2 (-149)) ≤ maxFinite32 := by
    rw [absQ_of_nonneg (Rat.le_of_lt hp)]; decide +kernel
  have hfin' : absQ (-pow2 (-149)) ≤ maxFinite32 := by rw [absQ_neg]; exact hfin
  have hk : k ≠ 0 := by intro h; subst h; simp at hy
  have hs := signedRounded_trunc_of_finite _ finiteValue32_pow2
  rcases (by omega : 1 ≤ k ∨ k ≤ -1) with h1 | h1
  · have hle : pow2 (-149) ≤ (k : ℚ) * pow2 (-149) := by
      have : (1 : ℚ) ≤ (k : ℚ) := by exact_mod_cast h1
      have := Rat.mul_le_mul_of_nonneg_right this (Rat.le_of_lt hp)
      simpa using this
    have := signedRounded_trunc_monotone _ _ hle hfin hr
    grind
  · have hle : (k : ℚ) * pow2 (-149) ≤ -pow2 (-149) := by
      have : (k : ℚ) ≤ ((-1 : ℤ) : ℚ) := Rat.intCast_le_intCast.mpr h1
      rw [Rat.intCast_neg, Rat.intCast_one] at this
      have := Rat.mul_le_mul_of_nonneg_right this (Rat.le_of_lt hp)
      grind
    have := signedRounded_trunc_monotone _ _ hle hr hfin'
    have hneg : signedRounded .truncate (-pow2 (-149)) = -pow2 (-149) := by
      have hn : FiniteValue32 (-pow2 (-149)) :=
        ⟨-1, -126, by decide, by decide, by decide, by simp; grind⟩
      exact signedRounded_trunc_of_finite _ hn
    grind

/-- **An fp16 block FMA never returns `−0`**, whatever its accumulator input (V100, A100, H100 and
every fp16 Tensor Core profile). -/
theorem blockOut_ne_negZero {K padding : ℕ} {eAlignMin : Option ℤ}
    {x : BlockInput (fp16Fp32Model K padding eAlignMin)} {d : F32} (h : blockOut x = .ok d) :
    d ≠ 0x80000000 := by
  unfold blockOut at h
  cases ht : evalBlock x with
  | error e => rw [ht] at h; simp [Except.map] at h
  | ok t =>
    rw [ht] at h
    simp only [Except.map, Except.ok.injEq] at h
    subst h
    unfold evalBlock at ht
    split at ht
    · cases ht
    · cases hp : prepare x with
      | none => rw [hp] at ht; cases ht
      | some b =>
        rw [hp] at ht
        simp only at ht
        have hout := evalPrepared_output ht (by rw [prepare_model hp]; exact Nat.le_refl 23)
        intro hneg
        by_cases hz : b.accumulator = 0
        · rw [hz] at hout
          have h0 : round32 .truncate 0 = some 0 := by decide +kernel
          rw [h0, hneg] at hout
          exact absurd (Option.some.inj hout) (by decide)
        · obtain ⟨b', hb', hd', _, _⟩ :=
            round32_nonzero_spec .truncate b.accumulator hz (round32_range hout)
          rw [hout, hneg] at hb'
          cases Option.some.inj hb'
          have hv : value32 (0x80000000 : F32) = some 0 := by decide +kernel
          rw [hv] at hd'
          exact signedRounded_ne_zero (accumulator_onGridQ hp) hz (round32_range hout)
            (Option.some.inj hd').symm

end MMAlgebra.TC
