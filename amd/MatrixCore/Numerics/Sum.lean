import MatrixCore.Numerics.RoundingContract

/-! # Integer sums and their bit width

`magnitudeSum` bounds every partial sum of aligned significands, and so the register width. -/

namespace MatrixCore

def sumZ : List ℤ → ℤ
  | [] => 0
  | z :: zs => z + sumZ zs

/-- Sum of absolute values. -/
def magnitudeSum : List ℤ → ℕ
  | [] => 0
  | z :: zs => z.natAbs + magnitudeSum zs

theorem sumZ_natAbs_le (zs : List ℤ) : (sumZ zs).natAbs ≤ magnitudeSum zs := by
  induction zs with
  | nil => simp [sumZ, magnitudeSum]
  | cons z zs ih =>
    have := Int.natAbs_add_le z (sumZ zs)
    simp only [sumZ, magnitudeSum]
    omega

theorem magnitudeSum_append (xs ys : List ℤ) :
    magnitudeSum (xs ++ ys) = magnitudeSum xs + magnitudeSum ys := by
  induction xs with
  | nil => simp [magnitudeSum]
  | cons x xs ih => simp [magnitudeSum, ih, Nat.add_assoc]

theorem magnitudeSum_le_length_mul (zs : List ℤ) (B : ℕ)
    (h : ∀ z ∈ zs, z.natAbs ≤ B) : magnitudeSum zs ≤ zs.length * B := by
  induction zs with
  | nil => simp [magnitudeSum]
  | cons z zs ih =>
    have hz := h z (by simp)
    have ht := ih (by intro t ht; exact h t (by simp [ht]))
    simp only [magnitudeSum, List.length_cons, Nat.add_mul, Nat.one_mul]
    omega

/-- Width `B + c + 1` suffices: `B` bits per term, `c` carry bits, and a sign bit. -/
theorem coefficient_width_sufficient (zs : List ℤ) (B c : ℕ)
    (hterm : ∀ z ∈ zs, z.natAbs < 2 ^ B) (hcount : zs.length ≤ 2 ^ c) :
    magnitudeSum zs < 2 ^ ((B + c + 1) - 1) := by
  have hp := Nat.two_pow_pos B
  have hc := Nat.two_pow_pos c
  have hs := magnitudeSum_le_length_mul zs (2 ^ B - 1) (by
    intro z hz; have := hterm z hz; omega)
  have hm := Nat.mul_le_mul_right (2 ^ B - 1) hcount
  have he : (B + c + 1) - 1 = B + c := by omega
  rw [he, Nat.pow_add, Nat.mul_comm]
  have hd : 2 ^ c * (2 ^ B - 1) < 2 ^ c * 2 ^ B :=
    Nat.mul_lt_mul_of_pos_left (by omega) hc
  omega

theorem magnitudeSum_perm {xs ys : List ℤ} (h : xs.Perm ys) : magnitudeSum xs = magnitudeSum ys := by
  induction h with
  | nil => rfl
  | cons x _ ih => simp only [magnitudeSum, ih]
  | swap x y zs => simp only [magnitudeSum]; omega
  | trans _ _ ih1 ih2 => exact ih1.trans ih2

theorem sumQ_map_intCast_mul (zs : List ℤ) (g : ℤ) :
    sumQ (zs.map fun (z : ℤ) => (z : ℚ) * pow2 g) = (sumZ zs : ℚ) * pow2 g := by
  induction zs with
  | nil => simp [sumQ, sumZ]
  | cons z zs ih =>
    simp only [List.map_cons, sumQ, sumZ, ih, Rat.intCast_add, Rat.add_mul]

/-! ## Aligned significands as integers -/

/-- `truncGrid` counted in steps of `2^g`, as a signed integer. -/
def truncBits (x : ℚ) (g : ℤ) : ℤ :=
  if x < 0 then -((-x / pow2 g).floor) else (x / pow2 g).floor

/-- RD onto multiples of `2^g`, counted in steps. -/
def rdBits (x : ℚ) (g : ℤ) : ℤ := (x / pow2 g).floor

theorem truncGrid_eq_truncBits (x : ℚ) (g : ℤ) : truncGrid x g = (truncBits x g : ℚ) * pow2 g := by
  unfold truncGrid truncBits
  split <;> simp [Rat.intCast_neg, Rat.neg_mul]

theorem rdGrid_eq_rdBits (x : ℚ) (g : ℤ) : rdGrid x g = (rdBits x g : ℚ) * pow2 g := rfl

theorem truncBits_natAbs_le (x : ℚ) (g : ℤ) :
    ((truncBits x g).natAbs : ℚ) * pow2 g ≤ absQ x := by
  have h := (truncGrid_bounds x g).1
  rwa [truncGrid_eq_truncBits, absQ_mul_pos _ _ (pow2_pos g), absQ_intCast] at h

theorem floor_eq_iff {q : ℚ} {z : ℤ} : q.floor = z ↔ (z : ℚ) ≤ q ∧ q < (z : ℚ) + 1 := by
  constructor
  · rintro rfl; exact floor_bounds q
  · rintro ⟨h1, h2⟩
    have a := Rat.le_floor_iff.mpr h1
    have b : q.floor < z + 1 := Rat.floor_lt_iff.mpr (by simpa using h2)
    omega

theorem floor_intCast_div (V : ℤ) (n : ℕ) (hn : 0 < n) : ((V : ℚ) / (n : ℚ)).floor = V / (n : ℤ) := by
  rw [floor_eq_iff]
  have hnq : (0 : ℚ) < n := by exact_mod_cast hn
  have h1 := Int.ediv_mul_le V (show (n : ℤ) ≠ 0 by omega)
  have h2 := Int.lt_ediv_add_one_mul_self V (show (0 : ℤ) < n by omega)
  constructor
  · apply le_div_of_mul_le hnq
    have : ((V / (n : ℤ) * n : ℤ) : ℚ) ≤ (V : ℚ) := by exact_mod_cast h1
    simpa [Rat.intCast_natCast] using this
  · rw [Rat.div_lt_iff hnq]
    have : (V : ℚ) < (((V / (n : ℤ) + 1) * n : ℤ) : ℚ) := by exact_mod_cast h2
    simpa [Rat.add_mul, Rat.intCast_natCast] using this

theorem rdBits_intCast_mul (z : ℤ) (g : ℤ) (n : ℕ) :
    rdBits ((z : ℚ) * pow2 g) (g + n) = z >>> n := by
  have hg := pow2_ne_zero g
  have hN : ((2 ^ n : ℕ) : ℚ) ≠ 0 := by
    have := Nat.two_pow_pos n
    exact_mod_cast Nat.pos_iff_ne_zero.mp this
  have hq : (z : ℚ) * pow2 g / pow2 (g + n) = (z : ℚ) / ((2 ^ n : ℕ) : ℚ) := by
    rw [pow2_add, pow2_natCast]
    grind
  unfold rdBits
  rw [hq, floor_intCast_div z _ (Nat.two_pow_pos n), Int.shiftRight_eq_div_pow]

end MatrixCore
