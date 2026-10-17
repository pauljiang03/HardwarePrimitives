import Std
import Init.Data.Rat
import Init.GrindInstances.Ring.Rat

/-! # Exact arithmetic

Powers of two, absolute values, sums and dot products over Lean's exact integers and rationals.

The scheme library is shared by the NVIDIA (`TensorCore`) and AMD (`MatrixCore`) instantiations,
which cannot be imported together: both declare the `ℕ ℤ ℚ` notation and their own arithmetic
helpers. This library therefore declares the notation locally in each file, writes powers of two as
`(2 : ℚ) ^ e`, absolute values as `Rat.abs`, and sums as `List.sum`, and adds no declaration
outside the `Ozaki` namespace. Both models define `pow2 e` as `(2 : ℚ) ^ e`, so their statements
meet these by definitional unfolding. -/

local notation "ℕ" => Nat
local notation "ℤ" => Int
local notation "ℚ" => Rat

namespace Ozaki

/-! ## Powers of two -/

theorem two_pow_pos (e : ℤ) : 0 < (2 : ℚ) ^ e := Rat.zpow_pos (by decide)

theorem two_pow_ne_zero (e : ℤ) : (2 : ℚ) ^ e ≠ 0 := Rat.ne_of_gt (two_pow_pos e)

theorem two_pow_add (a b : ℤ) : (2 : ℚ) ^ (a + b) = 2 ^ a * 2 ^ b := Rat.zpow_add (by decide) a b

theorem two_pow_zero : (2 : ℚ) ^ (0 : ℤ) = 1 := Rat.zpow_zero 2

theorem two_pow_one : (2 : ℚ) ^ (1 : ℤ) = 2 := Rat.zpow_one 2

theorem two_pow_natCast (n : ℕ) : (2 : ℚ) ^ (n : ℤ) = ((2 ^ n : ℕ) : ℚ) := by
  rw [Rat.zpow_natCast, Rat.natCast_pow]; rfl

theorem two_pow_succ (e : ℤ) : (2 : ℚ) ^ (e + 1) = 2 ^ e * 2 := by rw [two_pow_add, two_pow_one]

theorem two_pow_sub (a b : ℤ) : (2 : ℚ) ^ (a - b) = 2 ^ a / 2 ^ b := by
  have h : (2 : ℚ) ^ a = 2 ^ (a - b) * 2 ^ b := by rw [← two_pow_add]; congr 1; omega
  rw [h, Rat.mul_div_cancel (two_pow_ne_zero b)]

theorem two_pow_neg_mul (e : ℤ) : (2 : ℚ) ^ (-e) * 2 ^ e = 1 := by
  rw [← two_pow_add, Int.add_left_neg, two_pow_zero]

theorem div_two_pow (x : ℚ) (e : ℤ) : x / 2 ^ e = x * 2 ^ (-e) := by
  calc x / 2 ^ e = x * 2 ^ (-e) * 2 ^ e / 2 ^ e := by
        rw [Rat.mul_assoc, two_pow_neg_mul, Rat.mul_one]
    _ = x * 2 ^ (-e) := Rat.mul_div_cancel (two_pow_ne_zero e)

theorem two_pow_le {a b : ℤ} (h : a ≤ b) : (2 : ℚ) ^ a ≤ 2 ^ b := by
  have hb : (2 : ℚ) ^ b = 2 ^ a * 2 ^ ((b - a).toNat : ℤ) := by
    rw [← two_pow_add]; congr 1; omega
  rw [hb, two_pow_natCast]
  have h1 : (1 : ℚ) ≤ ((2 ^ (b - a).toNat : ℕ) : ℚ) :=
    Rat.natCast_le_natCast.mpr Nat.one_le_two_pow
  have := Rat.mul_le_mul_of_nonneg_left h1 (Rat.le_of_lt (two_pow_pos a))
  grind

theorem two_pow_lt {a b : ℤ} (h : a < b) : (2 : ℚ) ^ a < 2 ^ b := by
  have h1 := two_pow_le (show a + 1 ≤ b by omega)
  rw [two_pow_succ] at h1
  have := two_pow_pos a
  grind

theorem two_pow_le_iff {a b : ℤ} : (2 : ℚ) ^ a ≤ 2 ^ b ↔ a ≤ b := by
  refine ⟨fun h => ?_, two_pow_le⟩
  apply Classical.byContradiction
  intro hn
  have := two_pow_lt (show b < a by omega)
  grind

theorem two_pow_lt_iff {a b : ℤ} : (2 : ℚ) ^ a < 2 ^ b ↔ a < b := by
  refine ⟨fun h => ?_, two_pow_lt⟩
  apply Classical.byContradiction
  intro hn
  have := two_pow_le (show b ≤ a by omega)
  grind

/-- `1 ≤ 2^e` for natural exponents. -/
theorem one_le_two_pow_nat (n : ℕ) : (1 : ℚ) ≤ (2 : ℚ) ^ (n : ℤ) := by
  have := two_pow_le (show (0 : ℤ) ≤ n by omega)
  rwa [two_pow_zero] at this

/-! ## Absolute values -/

theorem lt_of_le_of_lt' {a b c : ℚ} (h1 : a ≤ b) (h2 : b < c) : a < c := by grind

theorem abs_def (x : ℚ) : Rat.abs x = if 0 ≤ x then x else -x := rfl

theorem abs_nonneg (x : ℚ) : 0 ≤ Rat.abs x := by rw [abs_def]; split <;> grind

theorem abs_of_nonneg {x : ℚ} (h : 0 ≤ x) : Rat.abs x = x := by rw [abs_def]; split <;> grind

theorem abs_of_neg {x : ℚ} (h : x < 0) : Rat.abs x = -x := by rw [abs_def]; split <;> grind

theorem abs_neg (x : ℚ) : Rat.abs (-x) = Rat.abs x := by
  rw [abs_def, abs_def]; split <;> split <;> grind

theorem abs_le_iff (x c : ℚ) : Rat.abs x ≤ c ↔ -c ≤ x ∧ x ≤ c := by
  rw [abs_def]; split <;> grind

theorem abs_lt_iff (x c : ℚ) : Rat.abs x < c ↔ -c < x ∧ x < c := by
  rw [abs_def]; split <;> grind

theorem le_abs_self (x : ℚ) : x ≤ Rat.abs x := by rw [abs_def]; split <;> grind

theorem neg_abs_le (x : ℚ) : -Rat.abs x ≤ x := by rw [abs_def]; split <;> grind

theorem abs_sub_comm (x y : ℚ) : Rat.abs (x - y) = Rat.abs (y - x) := by
  rw [abs_def, abs_def]; split <;> split <;> grind

theorem abs_add_le (x y : ℚ) : Rat.abs (x + y) ≤ Rat.abs x + Rat.abs y := by
  rw [abs_def, abs_def x, abs_def y]; split <;> split <;> split <;> grind

theorem abs_sub_le (x y : ℚ) : Rat.abs (x - y) ≤ Rat.abs x + Rat.abs y := by
  rw [abs_def, abs_def x, abs_def y]; split <;> split <;> split <;> grind

theorem abs_eq_zero {x : ℚ} : Rat.abs x = 0 ↔ x = 0 := by rw [abs_def]; split <;> grind

theorem abs_zero : Rat.abs 0 = 0 := by decide

theorem abs_mul (x y : ℚ) : Rat.abs (x * y) = Rat.abs x * Rat.abs y := by
  by_cases hx : 0 ≤ x <;> by_cases hy : 0 ≤ y
  · rw [abs_of_nonneg hx, abs_of_nonneg hy, abs_of_nonneg (Rat.mul_nonneg hx hy)]
  · have h := Rat.mul_nonneg hx (show 0 ≤ -y by grind)
    rw [abs_of_nonneg hx, abs_of_neg (by grind : y < 0), Rat.abs_of_nonpos (by grind : x * y ≤ 0)]
    grind
  · have h := Rat.mul_nonneg (show 0 ≤ -x by grind) hy
    rw [abs_of_neg (by grind : x < 0), abs_of_nonneg hy, Rat.abs_of_nonpos (by grind : x * y ≤ 0)]
    grind
  · have h := Rat.mul_nonneg (show 0 ≤ -x by grind) (show 0 ≤ -y by grind)
    rw [abs_of_neg (by grind : x < 0), abs_of_neg (by grind : y < 0),
      abs_of_nonneg (by grind : 0 ≤ x * y)]
    grind

theorem abs_two_pow (e : ℤ) : Rat.abs ((2 : ℚ) ^ e) = 2 ^ e :=
  abs_of_nonneg (Rat.le_of_lt (two_pow_pos e))

theorem abs_mul_two_pow (x : ℚ) (e : ℤ) : Rat.abs (x * 2 ^ e) = Rat.abs x * 2 ^ e := by
  rw [abs_mul, abs_two_pow]

theorem div_le_iff {a b c : ℚ} (hc : 0 < c) : a / c ≤ b ↔ a ≤ b * c := by
  constructor
  · intro h
    apply Classical.byContradiction
    intro hn
    have := (Rat.lt_div_iff hc).mpr (show b * c < a by grind)
    grind
  · intro h
    apply Classical.byContradiction
    intro hn
    have := (Rat.lt_div_iff hc).mp (show b < a / c by grind)
    grind

theorem abs_div_two_pow (a : ℚ) (g : ℤ) : Rat.abs (a / 2 ^ g) = Rat.abs a / 2 ^ g := by
  rw [Rat.div_def, abs_mul, abs_of_nonneg (Rat.le_of_lt (Rat.inv_pos.mpr (two_pow_pos g))),
    ← Rat.div_def]

theorem abs_intCast (z : ℤ) : Rat.abs (z : ℚ) = ((z.natAbs : ℕ) : ℚ) := by
  by_cases h : 0 ≤ z
  · rw [abs_of_nonneg (Rat.intCast_nonneg.mpr h), ← Rat.intCast_natCast, Int.natAbs_of_nonneg h]
  · have h' : (z : ℚ) < 0 := by
      have := Rat.intCast_lt_intCast.mpr (show z < 0 by omega); simpa using this
    rw [abs_of_neg h', ← Rat.intCast_neg, ← Rat.intCast_natCast]
    congr 1; omega

/-- A bound on an integer's magnitude, read over the rationals. -/
theorem abs_intCast_le {z : ℤ} {B : ℕ} (h : z.natAbs ≤ B) : Rat.abs (z : ℚ) ≤ (B : ℚ) := by
  rw [abs_intCast]; exact Rat.natCast_le_natCast.mpr h

theorem mul_le_mul_abs {a b A B : ℚ} (ha : Rat.abs a ≤ A) (hb : Rat.abs b ≤ B) :
    Rat.abs (a * b) ≤ A * B := by
  rw [abs_mul]
  have hA : 0 ≤ A := Rat.le_trans (abs_nonneg a) ha
  have h1 := Rat.mul_le_mul_of_nonneg_right ha (abs_nonneg b)
  have h2 := Rat.mul_le_mul_of_nonneg_left hb hA
  exact Rat.le_trans h1 h2

/-! ## Sums -/

theorem natCast_succ (n : ℕ) : ((n + 1 : ℕ) : ℚ) = (n : ℚ) + 1 := by
  rw [Rat.natCast_add]; rfl

theorem sum_map_add (l : List α) (f g : α → ℚ) :
    (l.map fun a => f a + g a).sum = (l.map f).sum + (l.map g).sum := by
  induction l with
  | nil => simp <;> grind
  | cons a l ih => simp only [List.map_cons, List.sum_cons, ih]; grind

theorem sum_map_sub (l : List α) (f g : α → ℚ) :
    (l.map fun a => f a - g a).sum = (l.map f).sum - (l.map g).sum := by
  induction l with
  | nil => simp <;> grind
  | cons a l ih => simp only [List.map_cons, List.sum_cons, ih]; grind

theorem sum_map_mul_left (l : List α) (c : ℚ) (f : α → ℚ) :
    (l.map fun a => c * f a).sum = c * (l.map f).sum := by
  induction l with
  | nil => simp <;> grind
  | cons a l ih => simp only [List.map_cons, List.sum_cons, ih]; grind

theorem sum_map_mul_right (l : List α) (c : ℚ) (f : α → ℚ) :
    (l.map fun a => f a * c).sum = (l.map f).sum * c := by
  induction l with
  | nil => simp <;> grind
  | cons a l ih => simp only [List.map_cons, List.sum_cons, ih]; grind

theorem sum_map_zero (l : List α) : (l.map fun _ => (0 : ℚ)).sum = 0 := by
  induction l with
  | nil => simp <;> grind
  | cons a l ih => simp only [List.map_cons, List.sum_cons, ih]; grind

theorem sum_append_q (xs ys : List ℚ) : (xs ++ ys).sum = xs.sum + ys.sum := by
  induction xs with
  | nil => simp <;> grind
  | cons x xs ih => simp only [List.cons_append, List.sum_cons, ih]; grind

theorem sum_map_append (xs ys : List α) (f : α → ℚ) :
    ((xs ++ ys).map f).sum = (xs.map f).sum + (ys.map f).sum := by
  rw [List.map_append, sum_append_q]

/-- A sum splits into the terms that satisfy a predicate and the terms that do not. -/
theorem sum_filter_add (l : List α) (p : α → Bool) (f : α → ℚ) :
    (l.map f).sum = ((l.filter p).map f).sum + ((l.filter fun a => !p a).map f).sum := by
  induction l with
  | nil => simp <;> grind
  | cons a l ih =>
    cases hp : p a <;> simp only [List.map_cons, List.sum_cons, List.filter_cons, hp,
      Bool.not_false, Bool.not_true, ↓reduceIte, Bool.false_eq_true, ih] <;> grind

theorem sum_le_sum {l : List α} {f g : α → ℚ} (h : ∀ a ∈ l, f a ≤ g a) :
    (l.map f).sum ≤ (l.map g).sum := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.map_cons, List.sum_cons]
    have h1 := h a (by simp)
    have h2 := ih (fun b hb => h b (by simp [hb]))
    grind

theorem sum_le_length_mul {l : List α} {f : α → ℚ} {B : ℚ} (h : ∀ a ∈ l, f a ≤ B) :
    (l.map f).sum ≤ l.length * B := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.map_cons, List.sum_cons, List.length_cons]
    have h1 := h a (by simp)
    have h2 := ih (fun b hb => h b (by simp [hb]))
    rw [natCast_succ]
    grind

/-- A sum over two lists paired by `zipWith` is at most `(length of the first) · B` for terms
bounded by a nonnegative `B`. -/
theorem sum_zipWith_le {f : α → β → ℚ} {B : ℚ} (hB : 0 ≤ B) :
    ∀ (xs : List α) (ys : List β), (∀ a ∈ xs, ∀ b ∈ ys, f a b ≤ B) →
      (List.zipWith f xs ys).sum ≤ xs.length * B
  | [], _, _ => by simp
  | _ :: _, [], _ => by
    simp only [List.zipWith_nil_right, List.sum_nil]
    exact Rat.mul_nonneg Rat.natCast_nonneg hB
  | a :: xs, b :: ys, h => by
    simp only [List.zipWith_cons_cons, List.sum_cons, List.length_cons]
    have h1 := h a (by simp) b (by simp)
    have h2 := sum_zipWith_le hB xs ys (fun a' ha b' hb => h a' (by simp [ha]) b' (by simp [hb]))
    rw [natCast_succ]
    grind

theorem sum_nonneg {l : List α} {f : α → ℚ} (h : ∀ a ∈ l, 0 ≤ f a) : 0 ≤ (l.map f).sum := by
  have := sum_le_sum (l := l) (f := fun _ => (0 : ℚ)) (g := f) h
  rwa [sum_map_zero] at this

/-- A term of a sum of nonnegative terms is at most the sum. -/
theorem le_sum_of_mem {l : List α} {f : α → ℚ} (hnn : ∀ a ∈ l, 0 ≤ f a) {a : α} (ha : a ∈ l) :
    f a ≤ (l.map f).sum := by
  induction l with
  | nil => simp at ha
  | cons b l ih =>
    simp only [List.map_cons, List.sum_cons]
    have hrest := sum_nonneg (l := l) (f := f) (fun c hc => hnn c (by simp [hc]))
    rcases List.mem_cons.mp ha with rfl | ha
    · grind
    · have := ih (fun c hc => hnn c (by simp [hc])) ha
      have := hnn b (by simp)
      grind

theorem abs_sum_le (l : List α) (f : α → ℚ) :
    Rat.abs (l.map f).sum ≤ (l.map fun a => Rat.abs (f a)).sum := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.map_cons, List.sum_cons]
    have := abs_add_le (f a) (l.map f).sum
    grind

/-! ## Vectors and dot products

Vectors are lists. The dot product pairs entries with `zipWith`, so it ignores the excess of the
longer argument; the theorems state the length hypotheses they need. -/

/-- `Σᵢ xᵢ yᵢ` over the rationals. -/
def dot (x y : List ℚ) : ℚ := (List.zipWith (· * ·) x y).sum

/-- `Σᵢ xᵢ yᵢ` over the integers. -/
def dotZ (x y : List ℤ) : ℤ := (List.zipWith (· * ·) x y).sum

/-- An integer vector read as rationals. -/
def ofInts (x : List ℤ) : List ℚ := x.map fun z : ℤ => (z : ℚ)

/-- `Σᵢ |xᵢ yᵢ|`, the sum of the product magnitudes of an integer dot product, which the
exactness bound of a matrix multiplier limits. -/
def dotAbs (x y : List ℤ) : ℕ := (List.zipWith (fun a b => (a * b).natAbs) x y).sum

@[simp] theorem dot_nil_left (y : List ℚ) : dot [] y = 0 := by simp [dot]
@[simp] theorem dot_nil_right (x : List ℚ) : dot x [] = 0 := by simp [dot]
@[simp] theorem dot_cons (a b : ℚ) (x y : List ℚ) : dot (a :: x) (b :: y) = a * b + dot x y := by
  simp [dot]

@[simp] theorem dotZ_nil_left (y : List ℤ) : dotZ [] y = 0 := by simp [dotZ]
@[simp] theorem dotZ_nil_right (x : List ℤ) : dotZ x [] = 0 := by simp [dotZ]
@[simp] theorem dotZ_cons (a b : ℤ) (x y : List ℤ) :
    dotZ (a :: x) (b :: y) = a * b + dotZ x y := by simp [dotZ]

@[simp] theorem dotAbs_nil_left (y : List ℤ) : dotAbs [] y = 0 := by simp [dotAbs]
@[simp] theorem dotAbs_nil_right (x : List ℤ) : dotAbs x [] = 0 := by simp [dotAbs]
@[simp] theorem dotAbs_cons (a b : ℤ) (x y : List ℤ) :
    dotAbs (a :: x) (b :: y) = (a * b).natAbs + dotAbs x y := by simp [dotAbs]

@[simp] theorem ofInts_nil : ofInts [] = [] := rfl
@[simp] theorem ofInts_cons (z : ℤ) (x : List ℤ) : ofInts (z :: x) = (z : ℚ) :: ofInts x := rfl
@[simp] theorem ofInts_length (x : List ℤ) : (ofInts x).length = x.length := by simp [ofInts]

theorem dot_ofInts (x y : List ℤ) : dot (ofInts x) (ofInts y) = (dotZ x y : ℚ) := by
  induction x generalizing y with
  | nil => simp
  | cons a x ih =>
    cases y with
    | nil => simp
    | cons b y => simp [ih, Rat.intCast_add, Rat.intCast_mul]

theorem dot_comm (x y : List ℚ) : dot x y = dot y x := by
  induction x generalizing y with
  | nil => simp
  | cons a x ih =>
    cases y with
    | nil => simp
    | cons b y => simp only [dot_cons, ih]; grind

theorem dotZ_comm (x y : List ℤ) : dotZ x y = dotZ y x := by
  induction x generalizing y with
  | nil => simp
  | cons a x ih =>
    cases y with
    | nil => simp
    | cons b y => simp only [dotZ_cons, ih]; rw [Int.mul_comm]

theorem dotAbs_comm (x y : List ℤ) : dotAbs x y = dotAbs y x := by
  induction x generalizing y with
  | nil => simp
  | cons a x ih =>
    cases y with
    | nil => simp
    | cons b y => simp only [dotAbs_cons, ih]; rw [Int.mul_comm]

/-- `|Σ xᵢ yᵢ| ≤ Σ |xᵢ yᵢ|`. -/
theorem natAbs_dotZ_le (x y : List ℤ) : (dotZ x y).natAbs ≤ dotAbs x y := by
  induction x generalizing y with
  | nil => simp
  | cons a x ih =>
    cases y with
    | nil => simp
    | cons b y =>
      simp only [dotZ_cons, dotAbs_cons]
      have := Int.natAbs_add_le (a * b) (dotZ x y)
      have := ih y
      omega

/-- `Σ |xᵢ yᵢ| ≤ n · A · B` for entries bounded by `A` and `B`. -/
theorem dotAbs_le (x y : List ℤ) (A B : ℕ) (hx : ∀ a ∈ x, a.natAbs ≤ A)
    (hy : ∀ b ∈ y, b.natAbs ≤ B) : dotAbs x y ≤ x.length * (A * B) := by
  induction x generalizing y with
  | nil => simp
  | cons a x ih =>
    cases y with
    | nil => simp
    | cons b y =>
      simp only [dotAbs_cons, List.length_cons]
      have ha := hx a (by simp)
      have hb := hy b (by simp)
      have hab : (a * b).natAbs ≤ A * B := by
        rw [Int.natAbs_mul]; exact Nat.mul_le_mul ha hb
      have := ih y (fun c hc => hx c (by simp [hc])) (fun c hc => hy c (by simp [hc]))
      rw [Nat.succ_mul]
      omega

theorem dot_map_mul_left (c : ℚ) (x y : List ℚ) :
    dot (x.map fun a => c * a) y = c * dot x y := by
  induction x generalizing y with
  | nil => simp
  | cons a x ih =>
    cases y with
    | nil => simp
    | cons b y => simp only [List.map_cons, dot_cons, ih]; grind

theorem dot_map_mul_right (c : ℚ) (x y : List ℚ) :
    dot (x.map fun a => a * c) y = dot x y * c := by
  induction x generalizing y with
  | nil => simp
  | cons a x ih =>
    cases y with
    | nil => simp
    | cons b y => simp only [List.map_cons, dot_cons, ih]; grind

/-- Linearity in the first argument: `(x − z)·y = x·y − z·y` for equally long `x` and `z`. -/
theorem dot_zipWith_sub (x z y : List ℚ) (h : x.length = z.length) :
    dot (List.zipWith (· - ·) x z) y = dot x y - dot z y := by
  induction x generalizing z y with
  | nil => cases z <;> simp_all <;> grind
  | cons a x ih =>
    cases z with
    | nil => simp at h
    | cons c z =>
      cases y with
      | nil => simp <;> grind
      | cons b y =>
        simp only [List.zipWith_cons_cons, dot_cons]
        rw [ih z y (by simpa using h)]
        grind

/-- `|x·y| ≤ n · A · B` for entries bounded by `A` and `B`, with `n` the length of `x`. -/
theorem abs_dot_le (x y : List ℚ) (A B : ℚ) (hx : ∀ a ∈ x, Rat.abs a ≤ A)
    (hy : ∀ b ∈ y, Rat.abs b ≤ B) (hA : 0 ≤ A) (hB : 0 ≤ B) :
    Rat.abs (dot x y) ≤ x.length * (A * B) := by
  induction x generalizing y with
  | nil => simp
  | cons a x ih =>
    cases y with
    | nil =>
      simp only [dot_nil_right, abs_zero, List.length_cons]
      have := Rat.mul_nonneg hA hB
      have : (0 : ℚ) ≤ ((x.length + 1 : ℕ) : ℚ) := Rat.natCast_nonneg
      exact Rat.mul_nonneg this (Rat.mul_nonneg hA hB)
    | cons b y =>
      simp only [dot_cons, List.length_cons]
      have h1 := mul_le_mul_abs (hx a (by simp)) (hy b (by simp))
      have h2 := ih y (fun c hc => hx c (by simp [hc])) (fun c hc => hy c (by simp [hc]))
      have h3 := abs_add_le (a * b) (dot x y)
      rw [natCast_succ]
      grind

/-! ## Largest magnitude -/

/-- `max |xᵢ|`, zero for the empty vector. -/
def maxAbs (x : List ℚ) : ℚ := x.foldr (fun a m => max (Rat.abs a) m) 0

theorem maxAbs_nonneg (x : List ℚ) : 0 ≤ maxAbs x := by
  induction x with
  | nil => simp [maxAbs]
  | cons a x ih =>
    simp only [maxAbs, List.foldr_cons] at *
    have := abs_nonneg a
    grind

theorem abs_le_maxAbs {x : List ℚ} {a : ℚ} (h : a ∈ x) : Rat.abs a ≤ maxAbs x := by
  induction x with
  | nil => simp at h
  | cons b x ih =>
    simp only [maxAbs, List.foldr_cons] at *
    rcases List.mem_cons.mp h with h | h
    · subst h; grind
    · have := ih h; grind

theorem maxAbs_le {x : List ℚ} {B : ℚ} (hB : 0 ≤ B) (h : ∀ a ∈ x, Rat.abs a ≤ B) :
    maxAbs x ≤ B := by
  induction x with
  | nil => simpa [maxAbs] using hB
  | cons b x ih =>
    simp only [maxAbs, List.foldr_cons] at *
    have h1 := h b (by simp)
    have h2 := ih (fun a ha => h a (by simp [ha]))
    grind

/-- A vector whose largest magnitude is zero is zero. -/
theorem eq_zero_of_maxAbs {x : List ℚ} (h : maxAbs x = 0) : ∀ a ∈ x, a = 0 := by
  intro a ha
  have := abs_le_maxAbs ha
  rw [h] at this
  have := abs_nonneg a
  exact abs_eq_zero.mp (by grind)

end Ozaki
