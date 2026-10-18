import MatrixCore.Numerics.Exact

/-! # Fixed-point alignment operations

Truncation and RD (rounding toward −∞) onto the grid of multiples of `2^g`. -/

namespace MatrixCore

/-- RD onto multiples of `2^g`: the largest multiple of `2^g` not above `x`. -/
def rdGrid (x : ℚ) (g : ℤ) : ℚ := ((x / pow2 g).floor : ℚ) * pow2 g

/-- Magnitude truncation onto multiples of `2^g`; the sign is kept. -/
def truncGrid (x : ℚ) (g : ℤ) : ℚ :=
  if x < 0 then -(((-x / pow2 g).floor : ℚ) * pow2 g) else ((x / pow2 g).floor : ℚ) * pow2 g

/-- Shift to exponent `e` and RD to `k` mantissa bits. -/
abbrev rdMantissa (x : ℚ) (e : ℤ) (k : ℕ) : ℚ := rdGrid x (e - k)

/-- Shift to exponent `e` and truncate to `k` mantissa bits. -/
abbrev truncMantissa (x : ℚ) (e : ℤ) (k : ℕ) : ℚ := truncGrid x (e - k)

/-- `x` is an integer multiple of `2^g`. -/
def OnGrid (x : ℚ) (g : ℤ) : Prop := ∃ k : ℤ, x = (k : ℚ) * pow2 g

theorem floor_bounds (t : ℚ) : (t.floor : ℚ) ≤ t ∧ t < (t.floor : ℚ) + 1 := by
  have h1 := Rat.floor_le t
  have h2 := Rat.lt_floor_add_one t
  simp only [Rat.intCast_add, Rat.intCast_one] at h2
  exact ⟨h1, h2⟩

theorem div_mul_pow2 (x : ℚ) (g : ℤ) : x / pow2 g * pow2 g = x :=
  Rat.div_mul_cancel (pow2_ne_zero g)

theorem rdGrid_bounds (x : ℚ) (g : ℤ) : rdGrid x g ≤ x ∧ x < rdGrid x g + pow2 g := by
  have ⟨h1, h2⟩ := floor_bounds (x / pow2 g)
  have hp := pow2_pos g
  have a := Rat.mul_le_mul_of_nonneg_right h1 (Rat.le_of_lt hp)
  have b := Rat.mul_lt_mul_of_pos_right h2 hp
  rw [div_mul_pow2] at a b
  unfold rdGrid
  constructor
  · exact a
  · rw [Rat.add_mul, Rat.one_mul] at b; exact b

theorem rdGrid_onGrid (x : ℚ) (g : ℤ) : OnGrid (rdGrid x g) g := ⟨_, rfl⟩

theorem truncGrid_onGrid (x : ℚ) (g : ℤ) : OnGrid (truncGrid x g) g := by
  unfold truncGrid
  split
  · exact ⟨-((-x / pow2 g).floor), by rw [Rat.intCast_neg, Rat.neg_mul]⟩
  · exact ⟨_, rfl⟩

theorem rdGrid_of_onGrid {x : ℚ} {g : ℤ} (h : OnGrid x g) : rdGrid x g = x := by
  obtain ⟨k, rfl⟩ := h
  unfold rdGrid
  rw [Rat.mul_div_cancel (pow2_ne_zero g)]
  simp

theorem truncGrid_of_onGrid {x : ℚ} {g : ℤ} (h : OnGrid x g) : truncGrid x g = x := by
  obtain ⟨k, rfl⟩ := h
  unfold truncGrid
  split
  · rw [show -((k : ℚ) * pow2 g) / pow2 g = ((-k : ℤ) : ℚ) by
      rw [show -((k : ℚ) * pow2 g) = ((-k : ℤ) : ℚ) * pow2 g by rw [Rat.intCast_neg, Rat.neg_mul],
        Rat.mul_div_cancel (pow2_ne_zero g)]]
    rw [Rat.floor_intCast, Rat.intCast_neg, Rat.neg_mul, Rat.neg_neg]
  · rw [Rat.mul_div_cancel (pow2_ne_zero g), Rat.floor_intCast]

theorem OnGrid.mono {x : ℚ} {g g' : ℤ} (h : OnGrid x g') (hg : g ≤ g') : OnGrid x g := by
  obtain ⟨k, rfl⟩ := h
  refine ⟨k * 2 ^ (g' - g).toNat, ?_⟩
  have : pow2 g' = pow2 ((g' - g).toNat : ℤ) * pow2 g := by rw [← pow2_add]; congr 1; omega
  rw [this, ← Rat.mul_assoc, intCast_mul_pow2_nat]

theorem OnGrid.add {x y : ℚ} {g : ℤ} (hx : OnGrid x g) (hy : OnGrid y g) : OnGrid (x + y) g := by
  obtain ⟨a, rfl⟩ := hx; obtain ⟨b, rfl⟩ := hy
  exact ⟨a + b, by rw [Rat.intCast_add, Rat.add_mul]⟩

theorem OnGrid.neg {x : ℚ} {g : ℤ} (hx : OnGrid x g) : OnGrid (-x) g := by
  obtain ⟨a, rfl⟩ := hx
  exact ⟨-a, by rw [Rat.intCast_neg, Rat.neg_mul]⟩

theorem OnGrid.zero (g : ℤ) : OnGrid 0 g := ⟨0, by simp⟩

theorem OnGrid.sub {x y : ℚ} {g : ℤ} (hx : OnGrid x g) (hy : OnGrid y g) : OnGrid (x - y) g := by
  rw [Rat.sub_eq_add_neg]; exact hx.add hy.neg

theorem onGrid_sumQ {xs : List ℚ} {g : ℤ} (h : ∀ x ∈ xs, OnGrid x g) : OnGrid (sumQ xs) g := by
  induction xs with
  | nil => exact OnGrid.zero g
  | cons x xs ih =>
    exact (h x (by simp)).add (ih fun y hy => h y (by simp [hy]))

theorem truncGrid_bounds (x : ℚ) (g : ℤ) :
    absQ (truncGrid x g) ≤ absQ x ∧ absQ (x - truncGrid x g) < pow2 g ∧
      (0 ≤ x → 0 ≤ truncGrid x g ∧ truncGrid x g ≤ x) ∧
      (x ≤ 0 → x ≤ truncGrid x g ∧ truncGrid x g ≤ 0) := by
  have hp := pow2_pos g
  unfold truncGrid
  by_cases hx : x < 0
  · have ⟨h1, h2⟩ := floor_bounds (-x / pow2 g)
    have a := Rat.mul_le_mul_of_nonneg_right h1 (Rat.le_of_lt hp)
    have b := Rat.mul_lt_mul_of_pos_right h2 hp
    rw [div_mul_pow2] at a b
    rw [Rat.add_mul, Rat.one_mul] at b
    have hf0 : (0 : ℚ) ≤ ((-x / pow2 g).floor : ℚ) * pow2 g := by
      have : (0 : ℤ) ≤ (-x / pow2 g).floor := by
        apply Rat.le_floor_iff.mpr
        have : 0 ≤ -x / pow2 g := by
          rw [Rat.div_def]; exact Rat.mul_nonneg (by grind) (Rat.le_of_lt (Rat.inv_pos.mpr hp))
        simpa using this
      exact Rat.mul_nonneg (by exact_mod_cast this) (Rat.le_of_lt hp)
    simp only [hx, ↓reduceIte]
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [absQ_neg, absQ_of_nonneg hf0, absQ_of_neg hx]; exact a
    · rw [absQ_lt_iff]; grind
    · intro h; grind
    · intro _; grind
  · have hx' : 0 ≤ x := by grind
    have ⟨h1, h2⟩ := floor_bounds (x / pow2 g)
    have a := Rat.mul_le_mul_of_nonneg_right h1 (Rat.le_of_lt hp)
    have b := Rat.mul_lt_mul_of_pos_right h2 hp
    rw [div_mul_pow2] at a b
    rw [Rat.add_mul, Rat.one_mul] at b
    have hf0 : (0 : ℚ) ≤ ((x / pow2 g).floor : ℚ) * pow2 g := by
      have : (0 : ℤ) ≤ (x / pow2 g).floor := by
        apply Rat.le_floor_iff.mpr
        have : 0 ≤ x / pow2 g := by
          rw [Rat.div_def]; exact Rat.mul_nonneg hx' (Rat.le_of_lt (Rat.inv_pos.mpr hp))
        simpa using this
      exact Rat.mul_nonneg (by exact_mod_cast this) (Rat.le_of_lt hp)
    simp only [hx, ↓reduceIte]
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [absQ_of_nonneg hf0, absQ_of_nonneg hx']; exact a
    · rw [absQ_lt_iff]; grind
    · intro _; exact ⟨hf0, a⟩
    · intro h; grind

theorem truncGrid_zero (g : ℤ) : truncGrid 0 g = 0 :=
  truncGrid_of_onGrid (OnGrid.zero g)

theorem rdGrid_zero (g : ℤ) : rdGrid 0 g = 0 :=
  rdGrid_of_onGrid (OnGrid.zero g)

theorem onGrid_intCast_mul (k : ℤ) (g g' : ℤ) (h : g' ≤ g) : OnGrid ((k : ℚ) * pow2 g) g' :=
  OnGrid.mono ⟨k, rfl⟩ h

end MatrixCore
