import TensorCore.Numerics.Notation
import Std
import Init.Data.Rat
import Init.GrindInstances.Ring.Rat

deriving instance DecidableEq for Except

/-! Exact rational arithmetic over integer/dyadic inputs. -/
namespace TensorCore

def pow2 (e : ℤ) : ℚ := (2 : ℚ) ^ e

theorem pow2_add (e f : ℤ) : pow2 (e + f) = pow2 e * pow2 f :=
  Rat.zpow_add (by decide) e f

theorem pow2_pos (e : ℤ) : 0 < pow2 e := Rat.zpow_pos (by decide)

theorem pow2_natCast (n : ℕ) : pow2 (n : ℤ) = ((2 ^ n : ℕ) : ℚ) := by
  unfold pow2; rw [Rat.zpow_natCast]; simp

theorem pow2_one : pow2 1 = 2 := Rat.zpow_one 2

theorem pow2_succ (e : ℤ) : pow2 (e + 1) = pow2 e * 2 := by rw [pow2_add, pow2_one]

theorem pow2_lt_succ (e : ℤ) : pow2 e < pow2 (e + 1) := by
  rw [pow2_succ]; have := pow2_pos e; grind

/-- Monotonicity of the binary grid in its exponent. -/
theorem pow2_le_of_le {e f : ℤ} (h : e ≤ f) : pow2 e ≤ pow2 f := by
  have hd : (f - e).toNat = (f - e) := by omega
  have : pow2 f = pow2 e * pow2 ((f - e).toNat : ℤ) := by
    rw [← pow2_add]; congr 1; omega
  rw [this, pow2_natCast]
  have hp := pow2_pos e
  have h1 : (1 : ℚ) ≤ ((2 ^ (f - e).toNat : ℕ) : ℚ) :=
    Rat.natCast_le_natCast.mpr (Nat.one_le_two_pow)
  have := Rat.mul_le_mul_of_nonneg_left h1 (Rat.le_of_lt hp)
  grind

def sumQ : List ℚ → ℚ
  | [] => 0
  | x :: xs => x + sumQ xs

def sumZ : List ℤ → ℤ
  | [] => 0
  | x :: xs => x + sumZ xs

def absQ (x : ℚ) : ℚ := if x < 0 then -x else x

theorem absQ_nonneg (x : ℚ) : 0 ≤ absQ x := by unfold absQ; split <;> grind
theorem absQ_le_iff (x c : ℚ) : absQ x ≤ c ↔ -c ≤ x ∧ x ≤ c := by unfold absQ; split <;> grind
theorem absQ_lt_iff (x c : ℚ) : absQ x < c ↔ -c < x ∧ x < c := by unfold absQ; split <;> grind
theorem absQ_neg (x : ℚ) : absQ (-x) = absQ x := by unfold absQ; split <;> split <;> grind
theorem absQ_sub_comm (x y : ℚ) : absQ (x - y) = absQ (y - x) := by
  unfold absQ; split <;> split <;> grind
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
theorem absQ_of_nonneg {x : ℚ} (h : 0 ≤ x) : absQ x = x := by unfold absQ; split <;> grind
theorem absQ_of_neg {x : ℚ} (h : x < 0) : absQ x = -x := by unfold absQ; split <;> grind

/-- Signed magnitude truncation. -/
def truncBits (x : ℚ) (e : ℤ) : ℤ :=
  if x < 0 then -((-x / pow2 e).floor) else (x / pow2 e).floor

def truncGrid (x : ℚ) (e : ℤ) : ℚ := (truncBits x e : ℚ) * pow2 e

theorem sum_coefficients (zs : List ℤ) (q : ℚ) :
    sumQ (zs.map fun (z : ℤ) => (z : ℚ) * q) = (sumZ zs : ℚ) * q := by
  induction zs with
  | nil => simp [sumQ, sumZ]
  | cons z zs ih => simp [sumQ, sumZ, ih, Rat.add_mul]

theorem pow2_zero : pow2 0 = 1 := by simp [pow2]

theorem pow2_div (a b : ℤ) : pow2 a / pow2 b = pow2 (a - b) := by
  have h : pow2 a = pow2 (a - b) * pow2 b := by
    rw [← pow2_add]; congr 1; omega
  rw [h, Rat.mul_div_cancel (Rat.ne_of_gt (pow2_pos b))]

theorem div_pow2 (x : ℚ) (e : ℤ) : x / pow2 e = x * pow2 (-e) := by
  have h1 : pow2 (-e) * pow2 e = 1 := by
    rw [← pow2_add]
    have : -e + e = 0 := by omega
    rw [this, pow2_zero]
  have hne := Rat.ne_of_gt (pow2_pos e)
  calc x / pow2 e = x * pow2 (-e) * pow2 e / pow2 e := by rw [Rat.mul_assoc, h1, Rat.mul_one]
    _ = x * pow2 (-e) := Rat.mul_div_cancel hne

theorem div_nonneg_of_pos (x q : ℚ) (hx : 0 ≤ x) (hq : 0 < q) : 0 ≤ x / q := by
  rw [Rat.div_def]
  exact Rat.mul_nonneg hx (Rat.le_of_lt (Rat.inv_pos.mpr hq))

theorem le_div_of_mul_le (a y q : ℚ) (hq : 0 < q) (h : a * q ≤ y) : a ≤ y / q := by
  have hinv := Rat.le_of_lt (Rat.inv_pos.mpr hq)
  have := Rat.mul_le_mul_of_nonneg_right h hinv
  rw [Rat.mul_assoc, Rat.mul_inv_cancel q (Rat.ne_of_gt hq), Rat.mul_one, ← Rat.div_def] at this
  exact this

theorem div_le_div_of_le_right (x y q : ℚ) (hq : 0 < q) (h : x ≤ y) : x / q ≤ y / q := by
  rw [Rat.div_def, Rat.div_def]
  exact Rat.mul_le_mul_of_nonneg_right h (Rat.le_of_lt (Rat.inv_pos.mpr hq))

theorem absQ_add_le (x y : ℚ) : absQ (x + y) ≤ absQ x + absQ y := by
  have hx := (absQ_le_iff x (absQ x)).mp Rat.le_refl
  have hy := (absQ_le_iff y (absQ y)).mp Rat.le_refl
  apply (absQ_le_iff _ _).mpr
  constructor <;> grind

theorem absQ_intCast (k : ℤ) : absQ (k : ℚ) = ((k.natAbs : ℤ) : ℚ) := by
  unfold absQ
  split
  · have hk : k < 0 := by
      have := Rat.intCast_lt_intCast (a := k) (b := 0); simp at this; grind
    rw [← Int.natAbs_neg, Int.natAbs_of_nonneg (by omega), Rat.intCast_neg]
  · have hk : 0 ≤ k := by
      have := Rat.intCast_le_intCast (a := 0) (b := k); simp at this; grind
    rw [Int.natAbs_of_nonneg hk]

theorem pow2_24 : pow2 24 = 16777216 := by decide

/-- A finite value with exponent below `e` is at most `2^e - 2^(e-24)` in magnitude. -/
theorem finite_below_binade (k e2 e : ℤ) (hk : k.natAbs < 2 ^ 24) (h : e2 < e) :
    absQ ((k : ℚ) * pow2 (e2 - 23)) ≤ pow2 e - pow2 (e - 24) := by
  have hq := pow2_pos (e2 - 23)
  rw [absQ_mul_pos _ _ hq, absQ_intCast]
  have hk' : ((k.natAbs : ℤ) : ℚ) ≤ (16777215 : ℚ) := by
    have h1 : (k.natAbs : ℤ) ≤ 16777215 := by omega
    have h2 := Rat.intCast_le_intCast.mpr h1
    simpa using h2
  have hgrid : pow2 (e2 - 23) ≤ pow2 (e - 24) := pow2_le_of_le (by omega)
  have hnn : (0 : ℚ) ≤ ((k.natAbs : ℤ) : ℚ) := Rat.intCast_nonneg.mpr (by omega)
  have step1 : ((k.natAbs : ℤ) : ℚ) * pow2 (e2 - 23) ≤ 16777215 * pow2 (e - 24) :=
    calc ((k.natAbs : ℤ) : ℚ) * pow2 (e2 - 23)
        ≤ ((k.natAbs : ℤ) : ℚ) * pow2 (e - 24) := Rat.mul_le_mul_of_nonneg_left hgrid hnn
      _ ≤ 16777215 * pow2 (e - 24) :=
          Rat.mul_le_mul_of_nonneg_right hk' (Rat.le_of_lt (pow2_pos _))
  have step2 : (16777215 : ℚ) * pow2 (e - 24) = pow2 e - pow2 (e - 24) := by
    have : pow2 e = pow2 (e - 24) * pow2 24 := by rw [← pow2_add]; congr 1; omega
    rw [this, pow2_24]
    grind
  rw [← step2]; exact step1

theorem finite_on_grid (k e2 e : ℤ) (h : e ≤ e2) :
    ∃ j : ℤ, (k : ℚ) * pow2 (e2 - 23) = j * pow2 (e - 23) := by
  refine ⟨k * 2 ^ (e2 - e).toNat, ?_⟩
  have : pow2 (e2 - 23) = pow2 (e - 23) * pow2 ((e2 - e).toNat : ℤ) := by
    rw [← pow2_add]; congr 1; omega
  rw [this, pow2_natCast, Rat.intCast_mul, Rat.intCast_pow]
  simp only [Rat.intCast_ofNat, Rat.natCast_pow, Rat.natCast_ofNat]
  grind

end TensorCore
