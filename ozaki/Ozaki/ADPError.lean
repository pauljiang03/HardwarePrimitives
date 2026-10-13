import Ozaki.ADP
import Ozaki.Rounding
import Ozaki.Summation

/-! # ADP's emulated path: accuracy

ADP (`Ozaki/ADP.lean`) converts every row `x` of `A` (column `y` of `B`) to `W`-bit fixed point,
`N = ⌊a · 2^s⌋` with `s = W − 1 − exp(row max)`, computes the fixed-point product exactly, and
rounds it once to binary64. This file proves the accuracy of that path for one output entry,
independently of the matrix multiplier:

* **Binary64 exponents (§4 modeling choice).** `exp64 v` is the IEEE exponent component,
  `⌊log₂|v|⌋` but at least `−1022`; every binary64 value is `m · 2^(exp64 v − 52)` with an integer
  `m` (`OnGrid64`, `[D.1]`), and `|v| < 2^(exp64 v + 1)` (`abs_lt_exp64`, `[D.2]`).
* **Fixed point.** `0 ≤ a 2^s − N < 1` (`fixed_floor`, `[F.2]`), `N ∈ [−2^W, 2^W)`
  (`fixed_range`, `[F.1]`), and an entry whose lowest bit lies on the grid is converted exactly
  (`fixed_exact`); with `W = 53 + ESC + 1` that includes both factors of every dominant product
  (`dominant_exact`, `[F.3]`).
* **Each product.** With `W ≥ 54 + ESC`, every product's conversion error is at most
  `2^(F − 52)`, where `F = exp(z_r)` (`term_bound`, the funnel `[F.4]`, which checks
  `2^(F − 51)`).
* **P.1.** The exact fixed-point product is within `k 2^(F − 52)` of `x · y`
  (`fixedPoint_error`, `[P.1]` checks `k 2^(F − 51)`).
* **ESC.** For the coarsened ESC, `W ≥ 54 + ESC` covers the exact ESC (`escCoarse_ge`, `[X.5]`),
  and `F ≤ exp(x_p) + exp(y_q)` (`fExact_le`, `[X.1]`).
* **P.2, Grade A.** After one rounding with relative error `u = 2^-53` and absolute error `η`,
  `|C − x · y| ≤ (2k + 2) u Σ|xᵢyᵢ| + η`, hence `(4k + 1) u Σ|xᵢyᵢ| + η`, the paper's Grade-A
  bound (`emulated_gradeA`, `[P.2]`), for normal (or zero) inputs and `2ku ≤ 1`. The Z3 check
  `[P.2]` has no `η`: it never meets an underflowing result. -/

local notation "ℕ" => Nat
local notation "ℤ" => Int
local notation "ℚ" => Rat

namespace Ozaki.ADP

/-! ## Binary64 exponents -/

/-- The IEEE exponent component of a nonzero binary64 value: `⌊log₂|v|⌋`, at least `−1022`. -/
def exp64 (v : ℚ) : ℤ := max (floorLog2 (Rat.abs v)) (-1022)

/-- The exponent of an entry, `−∞` (`none`) for zero. -/
def expOf (v : ℚ) : Exp := if v = 0 then none else some (exp64 v)

/-- The exponents of a vector. -/
def expsOf (x : List ℚ) : List Exp := x.map expOf

/-- `v` lies on its own binary64 grid, `v = m · 2^(exp64 v − 52)` with an integer `m` (`[D.1]`). -/
def OnGrid64 (v : ℚ) : Prop := ∃ m : ℤ, v = m * 2 ^ (exp64 v - 52)

/-- A normal binary64 magnitude, or zero. -/
def Normal64 (v : ℚ) : Prop := v = 0 ∨ (2 : ℚ) ^ (-1022 : ℤ) ≤ Rat.abs v

theorem floor_zero : Rat.floor 0 = 0 := by decide

theorem lt_of_lt_of_le_q {a b c : ℚ} (h1 : a < b) (h2 : b ≤ c) : a < c := by grind

theorem mem_zipWith_of_mem_zip {f : α → β → γ} :
    ∀ {x : List α} {y : List β} {a : α} {b : β}, (a, b) ∈ List.zip x y → f a b ∈ List.zipWith f x y
  | [], _, _, _, h => by simp at h
  | _ :: _, [], _, _, h => by simp at h
  | c :: x, d :: y, a, b, h => by
    simp only [List.zip_cons_cons, List.mem_cons, Prod.mk.injEq] at h
    simp only [List.zipWith_cons_cons, List.mem_cons]
    rcases h with ⟨rfl, rfl⟩ | h
    · exact Or.inl rfl
    · exact Or.inr (mem_zipWith_of_mem_zip h)

theorem abs_pos_of_ne {v : ℚ} (hv : v ≠ 0) : 0 < Rat.abs v := by
  have := abs_nonneg v
  have : Rat.abs v ≠ 0 := fun h => hv (abs_eq_zero.mp h)
  grind

/-- `|v| < 2^(exp64 v + 1)` (`[D.2]`). -/
theorem abs_lt_exp64 {v : ℚ} (hv : v ≠ 0) : Rat.abs v < 2 ^ (exp64 v + 1) := by
  have h := (floorLog2_spec (abs_pos_of_ne hv)).2
  exact lt_of_lt_of_le_q h (two_pow_le (by unfold exp64; omega))

/-- A normal value has `2^(exp64 v) ≤ |v|` (`[D.2]`). -/
theorem exp64_le_abs {v : ℚ} (hv : v ≠ 0) (hn : Normal64 v) : (2 : ℚ) ^ exp64 v ≤ Rat.abs v := by
  rcases hn with h | h
  · exact absurd h hv
  have ⟨h1, h2⟩ := floorLog2_spec (abs_pos_of_ne hv)
  unfold exp64
  by_cases hc : -1022 ≤ floorLog2 (Rat.abs v)
  · rw [Int.max_eq_left hc]; exact h1
  · rw [Int.max_eq_right (by omega)]; exact h

/-- A grid integer `m · 2^n` with `n ≥ 0` is an integer. -/
theorem intCast_mul_two_pow_nat (m : ℤ) {n : ℤ} (hn : 0 ≤ n) :
    (m : ℚ) * 2 ^ n = ((m * 2 ^ n.toNat : ℤ) : ℚ) := by
  have : n = (n.toNat : ℤ) := by omega
  rw [this, two_pow_natCast, Rat.intCast_mul]
  simp only [Int.toNat_natCast, Rat.intCast_pow, Rat.intCast_ofNat, Rat.natCast_pow,
    Rat.natCast_ofNat]

/-! ## Fixed point -/

/-- Row-wise fixed point, `Nᵢ = ⌊xᵢ · 2^shift⌋`. -/
def fixedVec (shift : ℤ) (x : List ℚ) : List ℤ := x.map fun a => (a * 2 ^ shift).floor

/-- **Floor conversion** (`[F.2]`): `0 ≤ a 2^s − N < 1`. -/
theorem fixed_floor (a : ℚ) (s : ℤ) :
    0 ≤ a * 2 ^ s - ((a * 2 ^ s).floor : ℚ) ∧ a * 2 ^ s - ((a * 2 ^ s).floor : ℚ) < 1 := by
  have ⟨h1, h2⟩ := floor_frac (a * 2 ^ s)
  constructor <;> grind

/-- **The fixed-point range** (`[F.1]`): with `s = W − 1 − e` and `exp(a) ≤ e`,
`N ∈ [−2^W, 2^W)`. -/
theorem fixed_range {a : ℚ} {e : ℤ} (hae : a ≠ 0 → exp64 a ≤ e) (W : ℕ) :
    -(2 ^ W : ℤ) ≤ (a * 2 ^ ((W : ℤ) - 1 - e)).floor ∧ (a * 2 ^ ((W : ℤ) - 1 - e)).floor < 2 ^ W := by
  have hlt : Rat.abs (a * 2 ^ ((W : ℤ) - 1 - e)) < 2 ^ (W : ℤ) := by
    rw [abs_mul_two_pow]
    by_cases ha : a = 0
    · subst ha; rw [abs_zero, Rat.zero_mul]; exact two_pow_pos _
    · have h1 := abs_lt_exp64 ha
      have h2 : (2 : ℚ) ^ (exp64 a + 1) ≤ 2 ^ (e + 1) := two_pow_le (by have := hae ha; omega)
      have h3 := Rat.mul_lt_mul_of_pos_right (lt_of_lt_of_le_q h1 h2) (two_pow_pos ((W : ℤ) - 1 - e))
      rwa [← two_pow_add, show e + 1 + ((W : ℤ) - 1 - e) = W by omega] at h3
  rw [two_pow_natCast] at hlt
  have ⟨f1, f2⟩ := floor_frac (a * 2 ^ ((W : ℤ) - 1 - e))
  have hb := (abs_lt_iff _ _).mp hlt
  generalize (a * 2 ^ ((W : ℤ) - 1 - e)).floor = N at *
  generalize a * 2 ^ ((W : ℤ) - 1 - e) = t at *
  have c1 : (N : ℚ) < ((2 ^ W : ℕ) : ℚ) := lt_of_le_of_lt' f1 hb.2
  have c2 : -(((2 ^ W : ℕ) : ℚ)) < (N : ℚ) + 1 := lt_of_lt_of_le_q hb.1 (Rat.le_of_lt f2)
  have e1 : (((2 ^ W : ℕ) : ℤ) : ℚ) = ((2 ^ W : ℕ) : ℚ) := Rat.intCast_natCast _
  rw [← e1] at c1 c2
  have c2' : ((-((2 ^ W : ℕ) : ℤ) : ℤ) : ℚ) < ((N + 1 : ℤ) : ℚ) := by
    rw [Rat.intCast_neg, Rat.intCast_add, Rat.intCast_one]; exact c2
  have d1 := Rat.intCast_lt_intCast.mp c1
  have d2 := Rat.intCast_lt_intCast.mp c2'
  have : ((2 ^ W : ℕ) : ℤ) = (2 : ℤ) ^ W := by simp
  omega

/-- An entry whose lowest bit `2^(exp(a) − 52)` lies on the grid `2^(−s)` is converted exactly. -/
theorem fixed_exact {a : ℚ} (ha : OnGrid64 a) {s : ℤ} (hs : -s ≤ exp64 a - 52) :
    ((a * 2 ^ s).floor : ℚ) * 2 ^ (-s) = a := by
  obtain ⟨m, hm⟩ := ha
  have hint : a * 2 ^ s = ((m * 2 ^ (exp64 a - 52 + s).toNat : ℤ) : ℚ) := by
    rw [← intCast_mul_two_pow_nat m (show 0 ≤ exp64 a - 52 + s by omega)]
    conv => lhs; rw [hm]
    rw [Rat.mul_assoc, ← two_pow_add]
  rw [hint, Rat.floor_intCast, ← hint, Rat.mul_assoc, ← two_pow_add, show s + -s = 0 by omega,
    two_pow_zero, Rat.mul_one]

/-- **Full fidelity** (`[F.3]`, from `[Z.9]`): with `W = 53 + ESC + 1`, both factors of a dominant
product (`exp(a) + exp(b) = F`) are converted exactly. -/
theorem dominant_exact {a b : ℚ} (ha : OnGrid64 a) (hb : OnGrid64 b) {ep eq F ESC W : ℤ}
    (h1 : exp64 a ≤ ep) (h2 : exp64 b ≤ eq) (hF : F = exp64 a + exp64 b)
    (hE : ep + eq - F ≤ ESC) (hW : W = 53 + ESC + 1) :
    ((a * 2 ^ (W - 1 - ep)).floor : ℚ) * 2 ^ (-(W - 1 - ep)) = a ∧
      ((b * 2 ^ (W - 1 - eq)).floor : ℚ) * 2 ^ (-(W - 1 - eq)) = b := by
  have := full_fidelity ep eq (exp64 a) (exp64 b) F ESC W h1 h2 hF hE hW
  exact ⟨fixed_exact ha (by omega), fixed_exact hb (by omega)⟩

/-- The conversion of one entry: the error `d = a − ã` lies in `[0, 2^(e+1−W))`, `|a| ≤ 2^(e+1)`,
and either the entry is exact or `|a| ≤ 2^(e + 53 − W)`. -/
theorem entry_facts {a : ℚ} (ha : OnGrid64 a) {e : ℤ} (hae : a ≠ 0 → exp64 a ≤ e) (W : ℤ) :
    0 ≤ a - ((a * 2 ^ (W - 1 - e)).floor : ℚ) * 2 ^ (-(W - 1 - e)) ∧
    a - ((a * 2 ^ (W - 1 - e)).floor : ℚ) * 2 ^ (-(W - 1 - e)) < 2 ^ (e + 1 - W) ∧
    Rat.abs a ≤ 2 ^ (e + 1) ∧
    (a - ((a * 2 ^ (W - 1 - e)).floor : ℚ) * 2 ^ (-(W - 1 - e)) = 0 ∨
      Rat.abs a ≤ 2 ^ (e + 53 - W)) := by
  have hg := two_pow_pos (-(W - 1 - e))
  have ⟨f1, f2⟩ := fixed_floor a (W - 1 - e)
  have hd : a - ((a * 2 ^ (W - 1 - e)).floor : ℚ) * 2 ^ (-(W - 1 - e)) =
      (a * 2 ^ (W - 1 - e) - ((a * 2 ^ (W - 1 - e)).floor : ℚ)) * 2 ^ (-(W - 1 - e)) := by
    have : a * 2 ^ (W - 1 - e) * 2 ^ (-(W - 1 - e)) = a := by
      rw [Rat.mul_assoc, ← two_pow_add, show W - 1 - e + -(W - 1 - e) = 0 by omega, two_pow_zero,
        Rat.mul_one]
    grind
  have hge : -(W - 1 - e) = e + 1 - W := by omega
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hd]; exact Rat.mul_nonneg f1 (Rat.le_of_lt hg)
  · rw [hd, ← hge]
    have := Rat.mul_lt_mul_of_pos_right f2 hg
    grind
  · by_cases h0 : a = 0
    · subst h0; rw [abs_zero]; exact Rat.le_of_lt (two_pow_pos _)
    · exact Rat.le_of_lt (lt_of_lt_of_le_q (abs_lt_exp64 h0) (two_pow_le (by have := hae h0; omega)))
  · by_cases h0 : a = 0
    · subst h0; left; rw [Rat.zero_mul, floor_zero]; grind
    · by_cases hx : -(W - 1 - e) ≤ exp64 a - 52
      · left; rw [fixed_exact ha hx]; grind
      · right
        exact Rat.le_of_lt (lt_of_lt_of_le_q (abs_lt_exp64 h0) (two_pow_le (by omega)))

/-- `|a · d| ≤ A · D` from `|a| ≤ A` and `0 ≤ d ≤ D`. -/
theorem abs_mul_le_of {a d A D : ℚ} (ha : Rat.abs a ≤ A) (hd0 : 0 ≤ d) (hd : d ≤ D) :
    Rat.abs (a * d) ≤ A * D :=
  mul_le_mul_abs ha (by rw [abs_of_nonneg hd0]; exact hd)

/-- **One product** (`[F.4]`). If the conversion errors `da, db` lie in `[0, 2^(e+1−W))`,
`|a| ≤ 2^(e_p+1)`, `|b| ≤ 2^(e_q+1)`, each entry is exact or below `2^(e + 53 − W)`, and
`W ≥ 54 + (e_p + e_q − F)` with `F ≤ e_p + e_q`, then the product's error is at most `2^(F − 52)`. -/
theorem term_bound {a b da db : ℚ} {ep eq F W : ℤ} (hda0 : 0 ≤ da) (hda : da < 2 ^ (ep + 1 - W))
    (hdb0 : 0 ≤ db) (hdb : db < 2 ^ (eq + 1 - W))
    (ha : Rat.abs a ≤ 2 ^ (ep + 1)) (hb : Rat.abs b ≤ 2 ^ (eq + 1))
    (hae : da = 0 ∨ Rat.abs a ≤ 2 ^ (ep + 53 - W)) (hbe : db = 0 ∨ Rat.abs b ≤ 2 ^ (eq + 53 - W))
    (hF : F ≤ ep + eq) (hW : 54 + (ep + eq - F) ≤ W) :
    Rat.abs (a * b - (a - da) * (b - db)) ≤ 2 ^ (F - 52) := by
  have e : a * b - (a - da) * (b - db) = a * db + da * b - da * db := by grind
  have k1 : (2 : ℚ) ^ (ep + 1) * 2 ^ (eq + 1 - W) ≤ 2 ^ (F - 52) := by
    rw [← two_pow_add]; exact two_pow_le (by omega)
  have k2 : (2 : ℚ) ^ (ep + 1 - W) * 2 ^ (eq + 1) ≤ 2 ^ (F - 52) := by
    rw [← two_pow_add]; exact two_pow_le (by omega)
  rcases hae with ha0 | has
  · subst ha0
    rw [show a * b - (a - 0) * (b - db) = a * db by grind]
    exact Rat.le_trans (abs_mul_le_of ha hdb0 (Rat.le_of_lt hdb)) k1
  rcases hbe with hb0 | hbs
  · subst hb0
    rw [show a * b - (a - da) * (b - 0) = da * b by grind, Rat.mul_comm]
    exact Rat.le_trans (abs_mul_le_of hb hda0 (Rat.le_of_lt hda)) (by rw [Rat.mul_comm]; exact k2)
  -- both entries small: `|a| db + da |b| + da db ≤ 3 · 2^(ep+eq+54−2W) ≤ 2^(F − 52)`
  rw [e]
  have t1 := abs_mul_le_of has hdb0 (Rat.le_of_lt hdb)
  have t2 : Rat.abs (da * b) ≤ 2 ^ (eq + 53 - W) * 2 ^ (ep + 1 - W) := by
    rw [Rat.mul_comm da b]; exact abs_mul_le_of hbs hda0 (Rat.le_of_lt hda)
  have t3 : Rat.abs (da * db) ≤ 2 ^ (ep + 1 - W) * 2 ^ (eq + 1 - W) :=
    mul_le_mul_abs (by rw [abs_of_nonneg hda0]; exact Rat.le_of_lt hda)
      (by rw [abs_of_nonneg hdb0]; exact Rat.le_of_lt hdb)
  rw [← two_pow_add] at t1 t2 t3
  have p1 : (2 : ℚ) ^ (ep + 53 - W + (eq + 1 - W)) = 2 ^ (ep + eq + 54 - 2 * W) :=
    congrArg _ (by omega)
  have p2 : (2 : ℚ) ^ (eq + 53 - W + (ep + 1 - W)) = 2 ^ (ep + eq + 54 - 2 * W) :=
    congrArg _ (by omega)
  have p3 : (2 : ℚ) ^ (ep + 1 - W + (eq + 1 - W)) ≤ 2 ^ (ep + eq + 54 - 2 * W) := two_pow_le (by omega)
  have p4 : (2 : ℚ) ^ (ep + eq + 54 - 2 * W) * 4 ≤ 2 ^ (F - 52) := by
    rw [show (4 : ℚ) = 2 ^ (2 : ℤ) by decide, ← two_pow_add]; exact two_pow_le (by omega)
  have s1 := abs_add_le (a * db + da * b) (-(da * db))
  have s2 := abs_add_le (a * db) (da * b)
  rw [abs_neg, ← Rat.sub_eq_add_neg] at s1
  have hpos := two_pow_pos (ep + eq + 54 - 2 * W)
  grind

/-! ## The fixed-point product -/

/-- The converted value `ã = ⌊a 2^s⌋ 2^(−s)`. -/
def fixedValue (s : ℤ) (a : ℚ) : ℚ := ((a * 2 ^ s).floor : ℚ) * 2 ^ (-s)

theorem dot_fixedValue (sa sb : ℤ) :
    ∀ x y : List ℚ, dot (x.map (fixedValue sa)) (y.map (fixedValue sb)) =
      (dotZ (fixedVec sa x) (fixedVec sb y) : ℚ) * 2 ^ (-(sa + sb))
  | [], _ => by simp [fixedVec]
  | _ :: _, [] => by simp [fixedVec]
  | a :: x, b :: y => by
    simp only [List.map_cons, dot_cons, fixedVec, dotZ_cons] at *
    rw [dot_fixedValue sa sb x y]
    unfold fixedVec fixedValue
    rw [Rat.intCast_add, Rat.intCast_mul, Rat.add_mul, show -(sa + sb) = -sa + -sb by omega,
      two_pow_add]
    grind

/-- The conversion errors add up: `|x · y − x̃ · ỹ| ≤ k 2^(F − 52)`. -/
theorem dot_fixed_error {ep eq F W : ℤ} (hF : F ≤ ep + eq) (hW : 54 + (ep + eq - F) ≤ W) :
    ∀ (x y : List ℚ), x.length = y.length → (∀ a ∈ x, OnGrid64 a) → (∀ b ∈ y, OnGrid64 b) →
      (∀ a ∈ x, a ≠ 0 → exp64 a ≤ ep) → (∀ b ∈ y, b ≠ 0 → exp64 b ≤ eq) →
      Rat.abs (dot x y - dot (x.map (fixedValue (W - 1 - ep))) (y.map (fixedValue (W - 1 - eq)))) ≤
        x.length * 2 ^ (F - 52)
  | [], [], _, _, _, _, _ => by
    simp only [List.map_nil, dot_nil_left, List.length_nil]
    rw [show (0 : ℚ) - 0 = 0 by grind, abs_zero, show ((0 : ℕ) : ℚ) = 0 from rfl, Rat.zero_mul]
    exact Rat.le_refl
  | a :: x, b :: y, hlen, hx, hy, hex, hey => by
    have ih := dot_fixed_error hF hW x y (by simpa using hlen) (fun c hc => hx c (by simp [hc]))
      (fun c hc => hy c (by simp [hc])) (fun c hc => hex c (by simp [hc]))
      (fun c hc => hey c (by simp [hc]))
    obtain ⟨a1, a2, a3, a4⟩ := entry_facts (hx a (by simp)) (hex a (by simp)) W
    obtain ⟨b1, b2, b3, b4⟩ := entry_facts (hy b (by simp)) (hey b (by simp)) W
    have ht := term_bound a1 a2 b1 b2 a3 b3 a4 b4 hF hW
    simp only [List.map_cons, dot_cons, List.length_cons, natCast_succ]
    unfold fixedValue at ih ⊢
    have e : a * b + dot x y - ((a * 2 ^ (W - 1 - ep)).floor * 2 ^ (-(W - 1 - ep)) *
        ((b * 2 ^ (W - 1 - eq)).floor * 2 ^ (-(W - 1 - eq))) +
        dot (x.map fun a => ((a * 2 ^ (W - 1 - ep)).floor : ℚ) * 2 ^ (-(W - 1 - ep)))
          (y.map fun a => ((a * 2 ^ (W - 1 - eq)).floor : ℚ) * 2 ^ (-(W - 1 - eq)))) =
        (a * b - (a - (a - ((a * 2 ^ (W - 1 - ep)).floor : ℚ) * 2 ^ (-(W - 1 - ep)))) *
          (b - (b - ((b * 2 ^ (W - 1 - eq)).floor : ℚ) * 2 ^ (-(W - 1 - eq))))) +
        (dot x y - dot (x.map fun a => ((a * 2 ^ (W - 1 - ep)).floor : ℚ) * 2 ^ (-(W - 1 - ep)))
          (y.map fun a => ((a * 2 ^ (W - 1 - eq)).floor : ℚ) * 2 ^ (-(W - 1 - eq)))) := by grind
    rw [e]
    exact Rat.le_trans (abs_add_le _ _) (by grind)

/-- **P.1** (`[P.1]`): with `e_p, e_q` bounding the exponents of `x` and `y`, `F ≤ e_p + e_q` and
`W ≥ 54 + (e_p + e_q − F)`, the exact fixed-point product, rescaled, is within `k 2^(F − 52)` of
`x · y` (the Z3 check uses `k 2^(F − 51)`). -/
theorem fixedPoint_error {x y : List ℚ} (hlen : x.length = y.length) (hx : ∀ a ∈ x, OnGrid64 a)
    (hy : ∀ b ∈ y, OnGrid64 b) {ep eq F W : ℤ} (hep : ∀ a ∈ x, a ≠ 0 → exp64 a ≤ ep)
    (heq : ∀ b ∈ y, b ≠ 0 → exp64 b ≤ eq) (hF : F ≤ ep + eq) (hW : 54 + (ep + eq - F) ≤ W) :
    Rat.abs (dot x y - (dotZ (fixedVec (W - 1 - ep) x) (fixedVec (W - 1 - eq) y) : ℚ) *
      2 ^ (-((W - 1 - ep) + (W - 1 - eq)))) ≤ x.length * 2 ^ (F - 52) := by
  rw [← dot_fixedValue]
  exact dot_fixed_error hF hW x y hlen hx hy hep heq

/-! ## ESC -/

theorem expOf_ne {v : ℚ} (hv : v ≠ 0) : expOf v = some (exp64 v) := by simp [expOf, hv]

/-- `maxE` is attained. -/
theorem maxE_mem : ∀ {l : List Exp} {v : ℤ}, maxE l = some v → some v ∈ l
  | [], _, h => by simp [maxE] at h
  | a :: l, v, h => by
    change eMax a (maxE l) = some v at h
    cases a with
    | none => simp only [eMax] at h; exact List.mem_cons_of_mem _ (maxE_mem h)
    | some a =>
      cases hl : maxE l with
      | none => rw [hl] at h; simp only [eMax, Option.some.injEq] at h; subst h; simp
      | some m =>
        rw [hl] at h; simp only [eMax, Option.some.injEq] at h
        by_cases hm : a ≤ m
        · rw [Int.max_eq_right hm] at h; subst h; exact List.mem_cons_of_mem _ (maxE_mem hl)
        · rw [Int.max_eq_left (by omega)] at h; subst h; simp

/-- Every nonzero entry's exponent is at most the vector's largest. -/
theorem exp64_le_maxE {x : List ℚ} {ep : ℤ} (h : maxE (expsOf x) = some ep) :
    ∀ a ∈ x, a ≠ 0 → exp64 a ≤ ep := by
  intro a ha h0
  have := le_maxE (l := expsOf x) (e := expOf a) (List.mem_map_of_mem ha)
  rw [h, expOf_ne h0] at this
  exact this

/-- A vector with no exponent is zero. -/
theorem eq_zero_of_maxE_none {x : List ℚ} (h : maxE (expsOf x) = none) : ∀ a ∈ x, a = 0 := by
  intro a ha
  apply Classical.byContradiction; intro h0
  have := le_maxE (l := expsOf x) (e := expOf a) (List.mem_map_of_mem ha)
  rw [h, expOf_ne h0] at this
  exact this

/-- `exp(z_r)` is attained by a pair of nonzero entries. -/
theorem fExact_attained {x y : List ℚ} {F : ℤ} (h : fExact (expsOf x) (expsOf y) = some F) :
    ∃ a b, (a, b) ∈ List.zip x y ∧ a ≠ 0 ∧ b ≠ 0 ∧ F = exp64 a + exp64 b := by
  have hm := maxE_mem h
  unfold expsOf at hm
  rw [List.zipWith_map] at hm
  obtain ⟨a, b, hab, he⟩ := mem_zipWith_exists hm
  by_cases ha : a = 0
  · simp [expOf, ha, eAdd] at he
  by_cases hb : b = 0
  · simp [expOf, hb, eAdd] at he
  rw [expOf_ne ha, expOf_ne hb] at he
  simp only [eAdd, Option.some.injEq] at he
  exact ⟨a, b, hab, ha, hb, he⟩

/-- **ESC ≥ 0** (`[X.1]`): `F ≤ exp(x_p) + exp(y_q)`. -/
theorem fExact_le {x y : List ℚ} {ep eq F : ℤ} (hp : maxE (expsOf x) = some ep)
    (hq : maxE (expsOf y) = some eq) (h : fExact (expsOf x) (expsOf y) = some F) : F ≤ ep + eq := by
  obtain ⟨a, b, hab, ha, hb, rfl⟩ := fExact_attained h
  have := exp64_le_maxE hp a (List.of_mem_zip hab).1 ha
  have := exp64_le_maxE hq b (List.of_mem_zip hab).2 hb
  omega

/-- No exponent sum: every product has a zero factor. -/
theorem fExact_none {x y : List ℚ} (h : fExact (expsOf x) (expsOf y) = none) :
    ∀ ab ∈ List.zip x y, ab.1 = 0 ∨ ab.2 = 0 := by
  intro ⟨a, b⟩ hab
  apply Classical.byContradiction; intro hn
  simp only [not_or] at hn
  have hm : eAdd (expOf a) (expOf b) ∈ List.zipWith eAdd (expsOf x) (expsOf y) := by
    unfold expsOf; rw [List.zipWith_map]
    exact mem_zipWith_of_mem_zip hab
  have := le_maxE hm
  unfold fExact at h
  rw [h, expOf_ne hn.1, expOf_ne hn.2] at this
  exact this

/-- The coarsened ESC of one dot product (§4, §5.2): `exp(x_p) + exp(y_q) − est`, with the
coarsened estimate `est` over blocks of `n`; `0` for a zero row or column; `none` (unbounded,
the Z3 model's `ESC > ESC_CAP`) when the estimate is `−∞`. -/
def escCoarse (n : ℕ) (x y : List ℚ) : Option ℤ :=
  match maxE (expsOf x), maxE (expsOf y) with
  | some xp, some yq => (coarseEst n (expsOf x) (expsOf y)).map fun est => xp + yq - est
  | _, _ => some 0

/-- The exact ESC of one dot product: `exp(x_p) + exp(y_q) − exp(z_r)`, `0` without a nonzero
product. -/
def escExact (x y : List ℚ) : ℤ :=
  match maxE (expsOf x), maxE (expsOf y), fExact (expsOf x) (expsOf y) with
  | some xp, some yq, some F => xp + yq - F
  | _, _, _ => 0

/-- **The coarsened ESC is conservative** (`[X.5]`, from `[Z.6]`): it is at least the exact
ESC. -/
theorem escCoarse_ge {n : ℕ} {x y : List ℚ} (hlen : x.length = y.length) {c : ℤ}
    (h : escCoarse n x y = some c) : escExact x y ≤ c := by
  unfold escCoarse at h; unfold escExact
  have hl : (expsOf x).length = (expsOf y).length := by simp [expsOf, hlen]
  cases hp : maxE (expsOf x) with
  | none =>
    rw [hp] at h; simp only [Option.some.injEq] at h; subst h; simp
  | some xp =>
    cases hq : maxE (expsOf y) with
    | none =>
      rw [hp, hq] at h; simp only [Option.some.injEq] at h; subst h; simp
    | some yq =>
      rw [hp, hq] at h
      simp only at h
      cases he : coarseEst n (expsOf x) (expsOf y) with
      | none => rw [he] at h; simp at h
      | some est =>
        rw [he] at h; simp only [Option.map_some, Option.some.injEq] at h
        have hle := coarseEst_le n hl
        rw [he] at hle
        cases hf : fExact (expsOf x) (expsOf y) with
        | none => rw [hf] at hle; simp [eLe] at hle
        | some F =>
          rw [hf] at hle
          simp only [eLe] at hle
          simp only
          omega

/-- With `W ≥ 54 + c` for the coarsened ESC `c`, the exact ESC condition holds. -/
theorem width_ok {n : ℕ} {x y : List ℚ} (hlen : x.length = y.length) {c W : ℤ}
    (h : escCoarse n x y = some c) (hW : 54 + c ≤ W) {ep eq F : ℤ}
    (hp : maxE (expsOf x) = some ep) (hq : maxE (expsOf y) = some eq)
    (hf : fExact (expsOf x) (expsOf y) = some F) : 54 + (ep + eq - F) ≤ W := by
  have := escCoarse_ge hlen h
  unfold escExact at this
  rw [hp, hq, hf] at this
  simp only at this
  omega

/-! ## The emulated entry -/

/-- ADP's shift for a row: `W − 1 − exp(row max)`, `0` for a zero row. -/
def shiftOf (W : ℤ) (x : List ℚ) : ℤ :=
  match maxE (expsOf x) with
  | some e => W - 1 - e
  | none => 0

/-- The exact fixed-point product of one entry, rescaled: the value ADP rounds to binary64. -/
def fixedProduct (W : ℤ) (x y : List ℚ) : ℚ :=
  (dotZ (fixedVec (shiftOf W x) x) (fixedVec (shiftOf W y) y) : ℚ) *
    2 ^ (-(shiftOf W x + shiftOf W y))

theorem fixedVec_zero {s : ℤ} {x : List ℚ} (h : ∀ a ∈ x, a = 0) : ∀ z ∈ fixedVec s x, z = 0 := by
  intro z hz
  obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hz
  rw [h a ha]; simp [floor_zero]

theorem dotZ_zero_left : ∀ (x y : List ℤ), (∀ z ∈ x, z = 0) → dotZ x y = 0
  | [], _, _ => by simp
  | _ :: _, [], _ => by simp
  | a :: x, b :: y, h => by
    rw [dotZ_cons, h a (by simp), dotZ_zero_left x y (fun z hz => h z (by simp [hz]))]; simp

theorem dot_zero_left : ∀ (x y : List ℚ), (∀ a ∈ x, a = 0) → dot x y = 0
  | [], _, _ => by simp
  | _ :: _, [], _ => by simp
  | a :: x, b :: y, h => by
    rw [dot_cons, h a (by simp), dot_zero_left x y (fun z hz => h z (by simp [hz]))]; grind

/-- Products with a zero factor contribute nothing, before and after conversion. -/
theorem dot_pairs_zero (sa sb : ℤ) :
    ∀ (x y : List ℚ), (∀ ab ∈ List.zip x y, ab.1 = 0 ∨ ab.2 = 0) →
      dot x y = 0 ∧ dotZ (fixedVec sa x) (fixedVec sb y) = 0
  | [], _, _ => by simp [fixedVec]
  | _ :: _, [], _ => by simp [fixedVec]
  | a :: x, b :: y, h => by
    obtain ⟨ih1, ih2⟩ := dot_pairs_zero sa sb x y (fun ab hab => h ab (by simp [hab]))
    simp only [dot_cons, fixedVec, List.map_cons, dotZ_cons] at *
    rw [ih1, ih2]
    rcases h (a, b) (by simp) with h0 | h0 <;> simp only at h0 <;> subst h0 <;>
      exact ⟨by grind, by simp [floor_zero]⟩

/-- **The emulated entry, exactly** (`[P.1]`, both cases). If `escCoarse n x y = some c` and
`W ≥ 54 + c`: when some product is nonzero, the fixed-point product is within `k 2^(F − 52)` of
`x · y` for `F = exp(z_r)`; otherwise both are zero. -/
theorem fixedProduct_error {n : ℕ} {x y : List ℚ} (hlen : x.length = y.length)
    (hx : ∀ a ∈ x, OnGrid64 a) (hy : ∀ b ∈ y, OnGrid64 b) {c W : ℤ}
    (hc : escCoarse n x y = some c) (hW : 54 + c ≤ W) :
    (∀ F, fExact (expsOf x) (expsOf y) = some F →
      Rat.abs (dot x y - fixedProduct W x y) ≤ x.length * 2 ^ (F - 52)) ∧
    (fExact (expsOf x) (expsOf y) = none → fixedProduct W x y = dot x y) := by
  unfold fixedProduct
  constructor
  · intro F hf
    cases hp : maxE (expsOf x) with
    | none =>
      obtain ⟨a, b, hab, ha, _, _⟩ := fExact_attained hf
      exact absurd (eq_zero_of_maxE_none hp a (List.of_mem_zip hab).1) ha
    | some ep =>
      cases hq : maxE (expsOf y) with
      | none =>
        obtain ⟨a, b, hab, _, hb, _⟩ := fExact_attained hf
        exact absurd (eq_zero_of_maxE_none hq b (List.of_mem_zip hab).2) hb
      | some eq =>
        have hsx : shiftOf W x = W - 1 - ep := by simp [shiftOf, hp]
        have hsy : shiftOf W y = W - 1 - eq := by simp [shiftOf, hq]
        rw [hsx, hsy]
        exact fixedPoint_error hlen hx hy (exp64_le_maxE hp) (exp64_le_maxE hq) (fExact_le hp hq hf)
          (width_ok hlen hc hW hp hq hf)
  · intro hf
    obtain ⟨h1, h2⟩ := dot_pairs_zero (shiftOf W x) (shiftOf W y) x y (fExact_none hf)
    rw [h1, h2]; simp

/-! ## Grade A -/

/-- `|x · y| ≤ Σ|xᵢyᵢ|`. -/
theorem abs_dot_le_sum (x y : List ℚ) :
    Rat.abs (dot x y) ≤ ((List.zipWith (· * ·) x y).map Rat.abs).sum := by
  unfold dot
  have := abs_sum_le (List.zipWith (· * ·) x y) id
  simpa using this

/-- A dominant product of normal entries: `2^F ≤ Σ|xᵢyᵢ|`. -/
theorem two_pow_F_le {x y : List ℚ} (hnx : ∀ a ∈ x, Normal64 a) (hny : ∀ b ∈ y, Normal64 b)
    {F : ℤ} (hf : fExact (expsOf x) (expsOf y) = some F) :
    (2 : ℚ) ^ F ≤ ((List.zipWith (· * ·) x y).map Rat.abs).sum := by
  obtain ⟨a, b, hab, ha, hb, rfl⟩ := fExact_attained hf
  have h1 := exp64_le_abs ha (hnx a (List.of_mem_zip hab).1)
  have h2 := exp64_le_abs hb (hny b (List.of_mem_zip hab).2)
  have hm : a * b ∈ List.zipWith (· * ·) x y := mem_zipWith_of_mem_zip hab
  have hle := le_sum_of_mem (l := List.zipWith (· * ·) x y) (f := Rat.abs) (fun c _ => abs_nonneg c) hm
  rw [two_pow_add]
  refine Rat.le_trans ?_ hle
  rw [abs_mul]
  exact Rat.le_trans (Rat.mul_le_mul_of_nonneg_right h1 (Rat.le_of_lt (two_pow_pos _)))
    (Rat.mul_le_mul_of_nonneg_left h2 (abs_nonneg a))

/-- One rounding of a value `H` within `k 2^(F − 52)` of `x · y`, with `2^F ≤ S = Σ|xᵢyᵢ|` and
`2ku ≤ 1` (`u = 2^-53`), is within `(2k + 2) u S + η` of `x · y`. -/
theorem round_gradeA {rnd : ℚ → Option ℚ} {η : ℚ} (hr : RoundWithin rnd (2 ^ (-53 : ℤ)) η)
    {xy S H C : ℚ} {k : ℕ} {F : ℤ} (hxy : Rat.abs xy ≤ S)
    (hH : Rat.abs (xy - H) ≤ k * 2 ^ (F - 52)) (hS : (2 : ℚ) ^ F ≤ S)
    (hk : 2 * (k : ℚ) * 2 ^ (-53 : ℤ) ≤ 1) (hC : rnd H = some C) :
    Rat.abs (C - xy) ≤ (2 * k + 2) * 2 ^ (-53 : ℤ) * S + η := by
  have hu := two_pow_pos (-53 : ℤ)
  generalize hU : (2 : ℚ) ^ (-53 : ℤ) = u at *
  have h52 : (2 : ℚ) ^ (F - 52) = 2 * u * 2 ^ F := by
    rw [show F - 52 = (1 + -53) + F by omega, two_pow_add, two_pow_add, two_pow_one, hU]
  have hkn : (0 : ℚ) ≤ k := Rat.natCast_nonneg
  -- `|xy − H| ≤ 2ku S`
  have hH' : Rat.abs (xy - H) ≤ 2 * k * u * S := by
    rw [h52] at hH
    have := Rat.mul_le_mul_of_nonneg_left hS (show (0 : ℚ) ≤ k * (2 * u) by
      exact Rat.mul_nonneg hkn (by grind))
    grind
  have hround := hr H C hC
  have hHabs : Rat.abs H ≤ S + 2 * k * u * S := by
    have := abs_add_le xy (H - xy)
    rw [show xy + (H - xy) = H by grind, abs_sub_comm] at this
    grind
  have hSnn : 0 ≤ S := Rat.le_trans (abs_nonneg xy) hxy
  have m1 := Rat.mul_le_mul_of_nonneg_left hHabs (Rat.le_of_lt hu)
  -- `u · 2ku S ≤ u S`
  have m2 : u * (2 * k * u * S) ≤ u * S := by
    have := Rat.mul_le_mul_of_nonneg_right hk (Rat.mul_nonneg (Rat.le_of_lt hu) hSnn)
    grind
  have t := abs_add_le (C - H) (H - xy)
  rw [show C - H + (H - xy) = C - xy by grind] at t
  rw [abs_sub_comm] at hH'
  grind

/-- **Grade A** (`[P.2]`). Normal (or zero) binary64 entries, `W ≥ 54 + c` for the coarsened ESC
`c` of this dot product, `2ku ≤ 1`, and one rounding of the exact fixed-point product with
`RoundWithin rnd 2^-53 η`: the result is within `(4k + 1) u Σ|xᵢyᵢ| + η` of `x · y`
(`(2k + 2) u Σ|xᵢyᵢ| + η` in the proof). -/
theorem emulated_gradeA {rnd : ℚ → Option ℚ} {η : ℚ} (hr : RoundWithin rnd (2 ^ (-53 : ℤ)) η)
    {n : ℕ} {x y : List ℚ} (hlen : x.length = y.length)
    (hx : ∀ a ∈ x, OnGrid64 a) (hy : ∀ b ∈ y, OnGrid64 b)
    (hnx : ∀ a ∈ x, Normal64 a) (hny : ∀ b ∈ y, Normal64 b) {c W : ℤ}
    (hc : escCoarse n x y = some c) (hW : 54 + c ≤ W) (hk : 2 * (x.length : ℚ) * 2 ^ (-53 : ℤ) ≤ 1)
    {C : ℚ} (hC : rnd (fixedProduct W x y) = some C) :
    Rat.abs (C - dot x y) ≤
      (4 * x.length + 1) * 2 ^ (-53 : ℤ) * ((List.zipWith (· * ·) x y).map Rat.abs).sum + η := by
  have hxy := abs_dot_le_sum x y
  generalize hS : ((List.zipWith (· * ·) x y).map Rat.abs).sum = S at *
  have hSnn : 0 ≤ S := Rat.le_trans (abs_nonneg _) hxy
  have hu := two_pow_pos (-53 : ℤ)
  obtain ⟨hsome, hnone⟩ := fixedProduct_error (n := n) hlen hx hy hc hW
  -- `(2k + 2) u S ≤ (4k + 1) u S`: for `k = 0` the sum is empty
  have hmono : (2 * (x.length : ℚ) + 2) * 2 ^ (-53 : ℤ) * S ≤
      (4 * x.length + 1) * 2 ^ (-53 : ℤ) * S := by
    by_cases h0 : x.length = 0
    · have : S = 0 := by
        rw [← hS, List.length_eq_zero_iff.mp h0]; simp
      rw [this]; grind
    · have : (1 : ℚ) ≤ x.length := by
        have : 1 ≤ x.length := Nat.pos_of_ne_zero h0
        exact_mod_cast this
      have := Rat.mul_nonneg (Rat.le_of_lt hu) hSnn
      have := Rat.mul_le_mul_of_nonneg_right (show 2 * (x.length : ℚ) + 2 ≤ 4 * x.length + 1 by grind)
        this
      grind
  cases hf : fExact (expsOf x) (expsOf y) with
  | none =>
    rw [hnone hf] at hC
    have h := hr _ _ hC
    have := Rat.mul_le_mul_of_nonneg_left hxy (Rat.le_of_lt hu)
    have hkS : 0 ≤ (4 * (x.length : ℚ)) * 2 ^ (-53 : ℤ) * S :=
      Rat.mul_nonneg (Rat.mul_nonneg (by grind) (Rat.le_of_lt hu)) hSnn
    grind
  | some F =>
    have h := round_gradeA hr hxy (hsome F hf)
      (by rw [← hS]; exact two_pow_F_le hnx hny hf) hk hC
    exact Rat.le_trans h (by grind)

/-! ## Digits and block representatives -/

/-- **Floor digits reconstruct `N`** (`[U.2]`). -/
theorem floorDigits_value : ∀ (s : ℕ) (N : ℤ), 0 < s → digitValue (floorDigits s N) = N
  | 0, _, h => absurd h (by decide)
  | 1, N, _ => by simp [floorDigits, digitValue]
  | s + 2, N, _ => by
    simp only [floorDigits, digitValue]
    rw [floorDigits_value (s + 1) (N / 256) (by omega)]
    omega

/-- **Floor digits are bytes** (`[U.1]`): the low digits are unsigned bytes, and the lead digit is
a signed byte when `N ∈ [−2^(8s−1), 2^(8s−1))`. -/
theorem floorDigits_bytes : ∀ (s : ℕ) (N : ℤ), 0 < s →
    -128 * 256 ^ (s - 1) ≤ N → N < 128 * 256 ^ (s - 1) →
    (∀ d ∈ (floorDigits s N).dropLast, 0 ≤ d ∧ d ≤ 255) ∧
      ∀ d ∈ (floorDigits s N).getLast?, -128 ≤ d ∧ d ≤ 127
  | 0, _, h, _, _ => absurd h (by decide)
  | 1, N, _, h1, h2 => by
    simp only [floorDigits, List.dropLast_singleton, List.not_mem_nil, false_implies,
      implies_true, List.getLast?_singleton, Option.mem_def, Option.some.injEq, forall_eq',
      true_and]
    simp at h1 h2; omega
  | s + 2, N, _, h1, h2 => by
    have hP : (256 : ℤ) ^ (s + 1) = 256 * 256 ^ s := by rw [Int.pow_succ]; omega
    simp only [show s + 2 - 1 = s + 1 by omega, hP] at h1 h2
    obtain ⟨ih1, ih2⟩ := floorDigits_bytes (s + 1) (N / 256) (by omega)
      (by simp only [show s + 1 - 1 = s by omega]; omega)
      (by simp only [show s + 1 - 1 = s by omega]; omega)
    have hne : floorDigits (s + 1) (N / 256) ≠ [] := by
      cases s <;> simp [floorDigits]
    obtain ⟨b, l', hl⟩ := List.exists_cons_of_ne_nil hne
    simp only [floorDigits]
    rw [List.dropLast_cons_of_ne_nil hne, hl, List.getLast?_cons_cons]
    rw [hl] at ih1 ih2
    refine ⟨fun d hd => ?_, ih2⟩
    rcases List.mem_cons.mp hd with rfl | hd
    · omega
    · exact ih1 d hd

theorem minE_le : ∀ {bs : List Exp} {e : Exp}, e ∈ bs → eLe (minE bs) e
  | [], _, h => by simp at h
  | [a], e, h => by simp only [List.mem_singleton] at h; subst h; exact eLe_refl _
  | a :: a' :: l, e, h => by
    change eLe (eMin a (minE (a' :: l))) e
    rcases List.mem_cons.mp h with rfl | h
    · exact eLe_eMin_left _ _
    · exact eLe_trans (eLe_eMin_right _ _) (minE_le h)

/-- **Block representatives bound every member** (`[X.3]`): `Min ≤ e ≤ Max`. -/
theorem blockRep_bounds {bs : List Exp} {e : Exp} (h : e ∈ bs) :
    eLe (blockRep bs).2 e ∧ eLe e (blockRep bs).1 := ⟨minE_le h, le_maxE h⟩

end Ozaki.ADP
