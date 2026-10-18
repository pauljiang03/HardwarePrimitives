import TensorCore.Numerics.Exact

/-! Finite sums and coefficient bounds. -/

namespace TensorCore

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

/-- `B` coefficient bits, `c` carry bits for the term count and a sign bit suffice. -/
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

theorem sumZ_replicate (K : ℕ) (z : ℤ) : sumZ (List.replicate K z) = K * z := by
  induction K with
  | zero => simp [sumZ]
  | succ n ih =>
    simp only [List.replicate_succ, sumZ, ih]
    have : ((n + 1 : ℕ) : ℤ) = (n : ℤ) + 1 := by omega
    rw [this]; grind

theorem sumQ_map_sub (l : List α) (g h : α → ℚ) :
    sumQ (l.map fun x => g x - h x) = sumQ (l.map g) - sumQ (l.map h) := by
  induction l with
  | nil => change (0 : ℚ) = 0 - 0; grind
  | cons x xs ih => simp only [List.map_cons, sumQ, ih]; grind

theorem sumQ_map_add (l : List α) (g h : α → ℚ) :
    sumQ (l.map fun x => g x + h x) = sumQ (l.map g) + sumQ (l.map h) := by
  induction l with
  | nil => change (0 : ℚ) = 0 + 0; grind
  | cons x xs ih => simp only [List.map_cons, sumQ, ih]; grind

theorem absQ_sumQ_le (xs : List ℚ) : absQ (sumQ xs) ≤ sumQ (xs.map absQ) := by
  induction xs with
  | nil =>
    simp only [sumQ, List.map_nil]
    have : absQ 0 = 0 := by decide +kernel
    rw [this]
    exact Rat.le_refl
  | cons x xs ih =>
    simp only [sumQ, List.map_cons]
    have := absQ_add_le x (sumQ xs)
    grind

theorem sumQ_map_le (xs : List α) (f : α → ℚ) (B : ℚ) (h : ∀ x ∈ xs, f x ≤ B) :
    sumQ (xs.map f) ≤ (xs.length : ℚ) * B := by
  induction xs with
  | nil =>
    simp only [List.map_nil, sumQ, List.length_nil]
    grind
  | cons x xs ih =>
    have hx := h x (by simp)
    have hrest := ih (fun y hy => h y (by simp [hy]))
    have hs : ((xs.length + 1 : ℕ) : ℚ) = (xs.length : ℚ) + 1 := by
      rw [Rat.natCast_add]; rfl
    simp only [List.map_cons, sumQ, List.length_cons, hs]
    grind

theorem sumQ_map_lt (xs : List α) (hne : xs ≠ []) (f : α → ℚ) (B : ℚ)
    (h : ∀ y ∈ xs, f y < B) : sumQ (xs.map f) < (xs.length : ℚ) * B := by
  cases xs with
  | nil => exact absurd rfl hne
  | cons x xs =>
    have hx := h x (by simp)
    have hrest := sumQ_map_le xs f B (fun y hy => Rat.le_of_lt (h y (by simp [hy])))
    have hs : ((xs.length + 1 : ℕ) : ℚ) = (xs.length : ℚ) + 1 := by
      rw [Rat.natCast_add]; rfl
    simp only [List.map_cons, sumQ, List.length_cons, hs]
    grind

theorem sumQ_map_zero (xs : List α) : sumQ (xs.map fun _ => (0 : ℚ)) = 0 := by
  induction xs with
  | nil => rfl
  | cons _ _ ih => simp only [List.map_cons, sumQ, ih]; grind

theorem magnitudeSum_perm {xs ys : List ℤ} (h : xs.Perm ys) : magnitudeSum xs = magnitudeSum ys := by
  induction h with
  | nil => rfl
  | cons x _ ih => simp only [magnitudeSum, ih]
  | swap x y zs => simp only [magnitudeSum]; omega
  | trans _ _ ih1 ih2 => exact ih1.trans ih2

theorem sumZ_perm {xs ys : List ℤ} (h : xs.Perm ys) : sumZ xs = sumZ ys := by
  induction h with
  | nil => rfl
  | cons x _ ih => simp only [sumZ, ih]
  | swap x y zs => simp only [sumZ]; omega
  | trans _ _ ih1 ih2 => exact ih1.trans ih2

/-- Ceiling of log₂ n for positive n, extended by zero at n = 0. -/
def ceilLog2 (n : ℕ) : ℕ := if n ≤ 1 then 0 else (n - 1).log2 + 1

theorem ceilLog2_le_iff (n c : ℕ) : ceilLog2 n ≤ c ↔ n ≤ 2 ^ c := by
  by_cases hn : n ≤ 1
  · simp only [ceilLog2, if_pos hn, Nat.zero_le, true_iff]
    have := Nat.two_pow_pos c
    omega
  · have hlog := Nat.log2_lt (n := n - 1) (k := c) (by omega)
    simp only [ceilLog2, if_neg hn]
    omega

theorem le_two_pow_ceilLog2 (n : ℕ) : n ≤ 2 ^ ceilLog2 n :=
  (ceilLog2_le_iff n _).mp (Nat.le_refl _)

/-- The bit-width form of Theorem IV.8's stronger sufficient coefficient bound. -/
theorem coefficient_bitSpan_sufficient (zs : List ℤ) (B P : ℕ)
    (hterm : ∀ z ∈ zs, z.natAbs < 2 ^ B) (hspan : B + ceilLog2 zs.length ≤ P) :
    magnitudeSum zs < 2 ^ P := by
  have h := coefficient_width_sufficient zs B (ceilLog2 zs.length) hterm
    (le_two_pow_ceilLog2 _)
  have hp := Nat.pow_le_pow_right (show 0 < 2 by decide) hspan
  have he : (B + ceilLog2 zs.length + 1) - 1 = B + ceilLog2 zs.length := by omega
  rw [he] at h
  omega

/-- Theorem IV.8's coefficient bound from `|Tᵢ| < 2^(b+1)` and `b − ℓ + 1 + ⌈log₂ n⌉ ≤ P`. -/
theorem bitSpan_coefficient_bound (zs : List ℤ) (b ℓ : ℤ) (P : ℕ)
    (hterm : ∀ z ∈ zs, absQ ((z : ℚ) * pow2 ℓ) < pow2 (b + 1))
    (hspan : b - ℓ + 1 + (ceilLog2 zs.length : ℤ) ≤ P) : magnitudeSum zs < 2 ^ P := by
  by_cases hB : ℓ ≤ b + 1
  · let B := (b - ℓ + 1).toNat
    have hBe : (B : ℤ) = b - ℓ + 1 := by dsimp [B]; omega
    apply coefficient_bitSpan_sufficient zs B P
    · intro z hz
      have h := hterm z hz
      rw [absQ_mul_pos _ _ (pow2_pos _), absQ_intCast, Rat.intCast_natCast] at h
      have he : b + 1 = (B : ℤ) + ℓ := by omega
      rw [he, pow2_add, pow2_natCast] at h
      exact Rat.natCast_lt_natCast.mp (Rat.lt_of_mul_lt_mul_right h (Rat.le_of_lt (pow2_pos _)))
    · omega
  · have hzero : ∀ z ∈ zs, z.natAbs ≤ 0 := by
      intro z hz
      have h := hterm z hz
      have hgrid := pow2_le_of_le (show b + 1 ≤ ℓ by omega)
      rw [absQ_mul_pos _ _ (pow2_pos _), absQ_intCast, Rat.intCast_natCast] at h
      have hz1 : (z.natAbs : ℚ) * pow2 ℓ < 1 * pow2 ℓ := by grind
      have hz2 : z.natAbs < 1 :=
        Rat.natCast_lt_natCast.mp (Rat.lt_of_mul_lt_mul_right hz1 (Rat.le_of_lt (pow2_pos _)))
      omega
    have := magnitudeSum_le_length_mul zs 0 hzero
    have := Nat.two_pow_pos P
    omega

end TensorCore
