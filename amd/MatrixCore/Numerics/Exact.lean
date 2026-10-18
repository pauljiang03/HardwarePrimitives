import MatrixCore.Numerics.Notation
import Init.GrindInstances.Ring.Rat

deriving instance DecidableEq for Except

/-! # Exact arithmetic

Powers of two, magnitudes, sums, and the binary exponent `⌊log₂ |x|⌋` over exact rationals. -/

namespace MatrixCore

def pow2 (e : ℤ) : ℚ := (2 : ℚ) ^ e

theorem pow2_add (e f : ℤ) : pow2 (e + f) = pow2 e * pow2 f :=
  Rat.zpow_add (by decide) e f

theorem pow2_pos (e : ℤ) : 0 < pow2 e := Rat.zpow_pos (by decide)

theorem pow2_ne_zero (e : ℤ) : pow2 e ≠ 0 := Rat.ne_of_gt (pow2_pos e)

theorem pow2_zero : pow2 0 = 1 := by simp [pow2]

theorem pow2_one : pow2 1 = 2 := Rat.zpow_one 2

theorem pow2_natCast (n : ℕ) : pow2 (n : ℤ) = ((2 ^ n : ℕ) : ℚ) := by
  unfold pow2; rw [Rat.zpow_natCast]; simp

theorem pow2_succ (e : ℤ) : pow2 (e + 1) = pow2 e * 2 := by rw [pow2_add, pow2_one]

theorem pow2_sub (e f : ℤ) : pow2 (e - f) = pow2 e / pow2 f := by
  have h : pow2 e = pow2 (e - f) * pow2 f := by rw [← pow2_add]; congr 1; omega
  rw [h, Rat.mul_div_cancel (pow2_ne_zero f)]

theorem div_pow2 (x : ℚ) (e : ℤ) : x / pow2 e = x * pow2 (-e) := by
  unfold pow2; rw [Rat.div_def, Rat.zpow_neg]

theorem pow2_le_of_le {e f : ℤ} (h : e ≤ f) : pow2 e ≤ pow2 f := by
  have hsplit : pow2 f = pow2 e * pow2 ((f - e).toNat : ℤ) := by
    rw [← pow2_add]; congr 1; omega
  rw [hsplit, pow2_natCast]
  have h1 : (1 : ℚ) ≤ ((2 ^ (f - e).toNat : ℕ) : ℚ) :=
    Rat.natCast_le_natCast.mpr Nat.one_le_two_pow
  have := Rat.mul_le_mul_of_nonneg_left h1 (Rat.le_of_lt (pow2_pos e))
  grind

theorem pow2_lt_of_lt {e f : ℤ} (h : e < f) : pow2 e < pow2 f := by
  have h1 := pow2_le_of_le (show e + 1 ≤ f by omega)
  have h2 : pow2 e < pow2 (e + 1) := by rw [pow2_succ]; have := pow2_pos e; grind
  grind

theorem pow2_le_iff {e f : ℤ} : pow2 e ≤ pow2 f ↔ e ≤ f := by
  constructor
  · intro h
    apply Classical.byContradiction
    intro hn
    have := pow2_lt_of_lt (show f < e by omega)
    grind
  · exact pow2_le_of_le

theorem pow2_lt_iff {e f : ℤ} : pow2 e < pow2 f ↔ e < f := by
  constructor
  · intro h
    apply Classical.byContradiction
    intro hn
    have := pow2_le_of_le (show f ≤ e by omega)
    grind
  · exact pow2_lt_of_lt

theorem intCast_mul_pow2_nat (k : ℤ) (n : ℕ) :
    (k : ℚ) * pow2 (n : ℤ) = ((k * 2 ^ n : ℤ) : ℚ) := by
  rw [pow2_natCast, Rat.intCast_mul, Rat.intCast_pow]
  simp

def absQ (x : ℚ) : ℚ := if x < 0 then -x else x

theorem absQ_nonneg (x : ℚ) : 0 ≤ absQ x := by unfold absQ; split <;> grind
theorem absQ_of_nonneg {x : ℚ} (h : 0 ≤ x) : absQ x = x := by unfold absQ; split <;> grind
theorem absQ_of_neg {x : ℚ} (h : x < 0) : absQ x = -x := by unfold absQ; split <;> grind
theorem absQ_neg (x : ℚ) : absQ (-x) = absQ x := by unfold absQ; split <;> split <;> grind
theorem absQ_le_iff (x c : ℚ) : absQ x ≤ c ↔ -c ≤ x ∧ x ≤ c := by unfold absQ; split <;> grind
theorem absQ_lt_iff (x c : ℚ) : absQ x < c ↔ -c < x ∧ x < c := by unfold absQ; split <;> grind
theorem absQ_pos {x : ℚ} (h : x ≠ 0) : 0 < absQ x := by unfold absQ; split <;> grind
theorem absQ_eq_zero {x : ℚ} : absQ x = 0 ↔ x = 0 := by unfold absQ; split <;> grind
theorem absQ_sub_comm (x y : ℚ) : absQ (x - y) = absQ (y - x) := by
  unfold absQ; split <;> split <;> grind
theorem absQ_add_le (x y : ℚ) : absQ (x + y) ≤ absQ x + absQ y := by
  unfold absQ; split <;> split <;> split <;> grind

theorem absQ_mul_pos (x q : ℚ) (hq : 0 < q) : absQ (x * q) = absQ x * q := by
  unfold absQ
  by_cases hx : x < 0
  · have : x * q < 0 := by
      have := Rat.mul_lt_mul_of_pos_right hx hq; simpa using this
    simp [hx, this]; grind
  · have hx' : 0 ≤ x := by grind
    have : ¬ (x * q < 0) := by
      have := Rat.mul_nonneg hx' (Rat.le_of_lt hq); grind
    simp [hx, this]

theorem absQ_intCast (k : ℤ) : absQ (k : ℚ) = ((k.natAbs : ℕ) : ℚ) := by
  unfold absQ
  split
  · have hk : k < 0 := by
      have := Rat.intCast_lt_intCast (a := k) (b := 0); simp at this; grind
    have : ((k.natAbs : ℕ) : ℤ) = -k := by omega
    rw [← Rat.intCast_natCast, this, Rat.intCast_neg]
  · have hk : 0 ≤ k := by
      have := Rat.intCast_le_intCast (a := 0) (b := k); simp at this; grind
    have : ((k.natAbs : ℕ) : ℤ) = k := by omega
    rw [← Rat.intCast_natCast, this]

def sumQ : List ℚ → ℚ
  | [] => 0
  | x :: xs => x + sumQ xs

theorem sumQ_append (xs ys : List ℚ) : sumQ (xs ++ ys) = sumQ xs + sumQ ys := by
  induction xs with
  | nil => simp [sumQ]; grind
  | cons x xs ih => simp [sumQ, ih]; grind

theorem sumQ_map_sub (l : List α) (f g : α → ℚ) :
    sumQ (l.map fun x => f x - g x) = sumQ (l.map f) - sumQ (l.map g) := by
  induction l with
  | nil => simp [sumQ]; grind
  | cons x xs ih => simp [sumQ, ih]; grind

theorem sumQ_map_add (l : List α) (f g : α → ℚ) :
    sumQ (l.map fun x => f x + g x) = sumQ (l.map f) + sumQ (l.map g) := by
  induction l with
  | nil => simp [sumQ]; grind
  | cons x xs ih => simp [sumQ, ih]; grind

theorem absQ_sumQ_le (xs : List ℚ) : absQ (sumQ xs) ≤ sumQ (xs.map absQ) := by
  induction xs with
  | nil => simp [sumQ, absQ]
  | cons x xs ih =>
    simp only [sumQ, List.map_cons]
    have := absQ_add_le x (sumQ xs)
    grind

theorem sumQ_map_le (xs : List α) (f : α → ℚ) (B : ℚ) (h : ∀ x ∈ xs, f x ≤ B) :
    sumQ (xs.map f) ≤ xs.length * B := by
  induction xs with
  | nil => simp [sumQ]
  | cons x xs ih =>
    simp only [List.map_cons, sumQ, List.length_cons]
    have h1 := h x (by simp)
    have h2 := ih (fun y hy => h y (by simp [hy]))
    have : ((xs.length + 1 : ℕ) : ℚ) * B = (xs.length : ℚ) * B + B := by
      rw [Rat.natCast_add, Rat.add_mul]; simp
    rw [this]; grind

/-! ## Binary exponent -/

/-- `⌊log₂ x⌋` for positive `x`. -/
def log2Floor (x : ℚ) : ℤ :=
  let e : ℤ := (x.num.natAbs.log2 : ℤ) - (x.den.log2 : ℤ)
  if x < pow2 e then e - 1 else e

theorem log2Floor_spec {x : ℚ} (hx : 0 < x) :
    pow2 (log2Floor x) ≤ x ∧ x < pow2 (log2Floor x + 1) := by
  have hden : (0 : ℚ) < x.den := Rat.natCast_pos.mpr x.den_pos
  have hnum0 : x.num ≠ 0 := fun h => by
    have := Rat.num_eq_zero.mp h; subst this; exact Rat.lt_irrefl hx
  have hnumnn : 0 ≤ x.num := Rat.num_nonneg.mpr (Rat.le_of_lt hx)
  have hxd : x * x.den = x.num := by
    have h := Rat.num_divInt_den x
    rw [Rat.divInt_eq_div, Rat.intCast_natCast] at h
    calc x * x.den = (x.num / (x.den : ℚ)) * x.den := by rw [h]
      _ = x.num := Rat.div_mul_cancel (Rat.ne_of_gt hden)
  have hnR : ((x.num.natAbs : ℕ) : ℚ) = (x.num : ℚ) := by
    rw [← Rat.intCast_natCast, Int.natAbs_of_nonneg hnumnn]
  have hn0 : x.num.natAbs ≠ 0 := fun h => hnum0 (Int.natAbs_eq_zero.mp h)
  have hd0 : x.den ≠ 0 := Nat.pos_iff_ne_zero.mp x.den_pos
  have h1 : ((2 ^ x.num.natAbs.log2 : ℕ) : ℚ) ≤ x.num.natAbs :=
    Rat.natCast_le_natCast.mpr (Nat.log2_self_le hn0)
  have h2 : (x.num.natAbs : ℚ) < ((2 ^ (x.num.natAbs.log2 + 1) : ℕ) : ℚ) :=
    Rat.natCast_lt_natCast.mpr Nat.lt_log2_self
  have h3 : ((2 ^ x.den.log2 : ℕ) : ℚ) ≤ x.den :=
    Rat.natCast_le_natCast.mpr (Nat.log2_self_le hd0)
  have h4 : (x.den : ℚ) < ((2 ^ (x.den.log2 + 1) : ℕ) : ℚ) :=
    Rat.natCast_lt_natCast.mpr Nat.lt_log2_self
  rw [← pow2_natCast] at h1 h2 h3 h4
  rw [hnR] at h1 h2
  generalize hA : (x.num.natAbs.log2 : ℤ) = a at *
  generalize hB : (x.den.log2 : ℤ) = b at *
  have hc1 : ((x.num.natAbs.log2 + 1 : ℕ) : ℤ) = a + 1 := by omega
  have hc2 : ((x.den.log2 + 1 : ℕ) : ℤ) = b + 1 := by omega
  rw [hc1] at h2; rw [hc2] at h4
  have lo : pow2 (a - b - 1) < x := by
    have hq := pow2_pos (a - b - 1)
    have e1 : pow2 (a - b - 1) * pow2 (b + 1) = pow2 a := by rw [← pow2_add]; congr 1; omega
    have e2 : pow2 (a - b - 1) * x.den < pow2 (a - b - 1) * pow2 (b + 1) :=
      (Rat.mul_lt_mul_left hq).mpr h4
    rw [e1] at e2
    have e3 : pow2 (a - b - 1) * x.den < x * x.den := by rw [hxd]; grind
    exact Rat.lt_of_mul_lt_mul_right e3 (Rat.le_of_lt hden)
  have hi : x < pow2 (a - b + 1) := by
    have hq := pow2_pos (a - b + 1)
    have e1 : pow2 (a - b + 1) * pow2 b = pow2 (a + 1) := by rw [← pow2_add]; congr 1; omega
    have e2 : pow2 (a - b + 1) * pow2 b ≤ pow2 (a - b + 1) * x.den :=
      Rat.mul_le_mul_of_nonneg_left h3 (Rat.le_of_lt hq)
    rw [e1] at e2
    have e3 : x * x.den < pow2 (a - b + 1) * x.den := by rw [hxd]; grind
    exact Rat.lt_of_mul_lt_mul_right e3 (Rat.le_of_lt hden)
  have hdef : log2Floor x = if x < pow2 (a - b) then a - b - 1 else a - b := by
    unfold log2Floor; rw [hA, hB]
  rw [hdef]
  split
  · have : a - b - 1 + 1 = a - b := by omega
    rw [this]; exact ⟨Rat.le_of_lt lo, by assumption⟩
  · exact ⟨by grind, hi⟩

theorem log2Floor_eq {x : ℚ} {e : ℤ} (h1 : pow2 e ≤ x) (h2 : x < pow2 (e + 1)) :
    log2Floor x = e := by
  have hx : 0 < x := by have := pow2_pos e; grind
  obtain ⟨hlo, hhi⟩ := log2Floor_spec hx
  have a := pow2_lt_iff.mp (show pow2 (log2Floor x) < pow2 (e + 1) by grind)
  have b := pow2_lt_iff.mp (show pow2 e < pow2 (log2Floor x + 1) by grind)
  omega

theorem log2Floor_mul_pow2 {x : ℚ} (hx : 0 < x) (k : ℤ) :
    log2Floor (x * pow2 k) = log2Floor x + k := by
  obtain ⟨hlo, hhi⟩ := log2Floor_spec hx
  have hk := pow2_pos k
  apply log2Floor_eq
  · rw [pow2_add]; exact Rat.mul_le_mul_of_nonneg_right hlo (Rat.le_of_lt hk)
  · rw [show log2Floor x + k + 1 = (log2Floor x + 1) + k by omega, pow2_add]
    exact Rat.mul_lt_mul_of_pos_right hhi hk

end MatrixCore
