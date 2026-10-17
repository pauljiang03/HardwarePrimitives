import Ozaki.Binary

/-! # Bounded integer arithmetic for correct rounding

The correctness proofs of the correctly rounded schemes compute in exact rationals. This file gives
the integer operations an implementation uses, on integers of bounded width, and proves them equal
to the specification:

* `fixedSum w`: addition in a `w`-bit two's-complement register that wraps at every step; it is the
  exact sum while the magnitudes total less than `2^(w−1)` (`fixedSum_eq`);
* `bitlen`, `cmpDy`: bit length, and the comparison of two dyadic numbers `A 2^a` and `K 2^b`
  through their top bit positions and one shift no longer than the operands (`cmpDy_spec`);
* `roundByCmp`: round to nearest even of a positive magnitude `a`, given only an oracle that
  compares `a` with dyadic numbers `K 2^h`, a guess `eH` of its exponent within one, and a guess of
  its integer part on a grid within one (`roundByCmp_spec`). It asks at most five questions. The
  oracle can be exact integer comparison (`roundExact`) or a sign oracle for a sum of terms
  (`Ozaki.SignOracle`);
* `roundExact`: round to nearest even of `N · 2^q` with integer operations only, equal to
  `roundRNE` for every `N` and `q` (`roundExact_eq`). Its left shifts are by at most `p` bits or
  the operands' width; right shifts only shrink. -/

local notation "ℕ" => Nat
local notation "ℤ" => Int
local notation "ℚ" => Rat

namespace Ozaki

/-! ## A fixed-width register -/

/-- Two's-complement wrap to `w` bits: the representative of `x` modulo `2^w` in
`[−2^(w−1), 2^(w−1))`. -/
def wrap (w : ℕ) (x : ℤ) : ℤ := (x + 2 ^ (w - 1)) % 2 ^ w - 2 ^ (w - 1)

theorem wrap_eq {w : ℕ} (hw : 0 < w) {x : ℤ} (h : x.natAbs < 2 ^ (w - 1)) : wrap w x = x := by
  unfold wrap
  obtain ⟨v, rfl⟩ : ∃ v, w = v + 1 := ⟨w - 1, by omega⟩
  simp only [Nat.add_sub_cancel] at h ⊢
  have hP : (2 : ℤ) ^ (v + 1) = 2 ^ v * 2 := Int.pow_succ 2 v
  have hc : ((2 ^ v : ℕ) : ℤ) = (2 : ℤ) ^ v := by simp
  rw [hP]
  generalize (2 : ℤ) ^ v = P at hc ⊢
  rw [Int.emod_eq_of_lt (by omega) (by omega)]
  omega

/-- Accumulate from `acc` in a `w`-bit register, wrapping at every addition. -/
def fixedSumFrom (w : ℕ) : ℤ → List ℤ → ℤ
  | acc, [] => acc
  | acc, z :: zs => fixedSumFrom w (wrap w (acc + z)) zs

/-- **A `w`-bit two's-complement accumulator.** -/
def fixedSum (w : ℕ) (zs : List ℤ) : ℤ := fixedSumFrom w 0 zs

theorem fixedSumFrom_eq {w : ℕ} (hw : 0 < w) : ∀ (zs : List ℤ) (acc : ℤ),
    acc.natAbs + (zs.map Int.natAbs).sum < 2 ^ (w - 1) → fixedSumFrom w acc zs = acc + zs.sum
  | [], acc, _ => by simp [fixedSumFrom]
  | z :: zs, acc, h => by
    simp only [List.map_cons, List.sum_cons] at h
    have hz := Int.natAbs_add_le acc z
    unfold fixedSumFrom
    rw [wrap_eq hw (by omega), fixedSumFrom_eq hw zs (acc + z) (by omega), List.sum_cons]
    omega

/-- **The register is exact while the magnitudes total less than `2^(w−1)`.** -/
theorem fixedSum_eq {w : ℕ} (hw : 0 < w) {zs : List ℤ}
    (h : (zs.map Int.natAbs).sum < 2 ^ (w - 1)) : fixedSum w zs = zs.sum := by
  unfold fixedSum
  rw [fixedSumFrom_eq hw zs 0 (by simpa using h)]
  simp

/-! ## Bit lengths -/

theorem lt_le_trans' {a b c : ℚ} (h1 : a < b) (h2 : b ≤ c) : a < c := by grind

theorem le_lt_trans' {a b c : ℚ} (h1 : a ≤ b) (h2 : b < c) : a < c := by grind

/-- The number of bits of `n`: `0` for `0`, otherwise `⌊log₂ n⌋ + 1`. -/
def bitlen (n : ℕ) : ℕ := if n = 0 then 0 else n.log2 + 1

theorem lt_two_pow_bitlen (n : ℕ) : n < 2 ^ bitlen n := by
  unfold bitlen
  split
  · rename_i h; subst h; exact Nat.two_pow_pos 0
  · exact Nat.lt_log2_self

theorem two_pow_bitlen_le {n : ℕ} (hn : n ≠ 0) : 2 ^ (bitlen n - 1) ≤ n := by
  unfold bitlen
  rw [if_neg hn]
  simpa using Nat.log2_self_le hn

theorem bitlen_pos {n : ℕ} (hn : n ≠ 0) : 1 ≤ bitlen n := by
  unfold bitlen; rw [if_neg hn]; omega

theorem bitlen_le_iff {n k : ℕ} : bitlen n ≤ k ↔ n < 2 ^ k := by
  unfold bitlen
  split
  · rename_i h; subst h
    exact ⟨fun _ => Nat.two_pow_pos k, fun _ => Nat.zero_le _⟩
  · rename_i hn
    rw [show n.log2 + 1 ≤ k ↔ n.log2 < k by omega]
    exact Nat.log2_lt hn

theorem bitlen_mono {a b : ℕ} (h : a ≤ b) : bitlen a ≤ bitlen b :=
  bitlen_le_iff.mpr (Nat.lt_of_le_of_lt h (lt_two_pow_bitlen _))

theorem natCast_lt_two_pow_bitlen (A : ℕ) : (A : ℚ) < 2 ^ ((bitlen A : ℕ) : ℤ) := by
  rw [two_pow_natCast]; exact_mod_cast lt_two_pow_bitlen A

theorem two_pow_bitlen_le_natCast {A : ℕ} (hA : A ≠ 0) :
    (2 : ℚ) ^ ((bitlen A : ℤ) - 1) ≤ A := by
  have h := two_pow_bitlen_le hA
  have hb := bitlen_pos hA
  rw [show ((bitlen A : ℤ) - 1) = ((bitlen A - 1 : ℕ) : ℤ) by omega, two_pow_natCast]
  exact_mod_cast h

/-- `A 2^a < 2^(a + bitlen A)`. -/
theorem natCast_mul_two_pow_lt (A : ℕ) (a : ℤ) :
    (A : ℚ) * 2 ^ a < 2 ^ (a + bitlen A) := by
  rw [two_pow_add, Rat.mul_comm (2 ^ a)]
  exact Rat.mul_lt_mul_of_pos_right (natCast_lt_two_pow_bitlen A) (two_pow_pos a)

/-- `2^(a + bitlen A − 1) ≤ A 2^a` for `A ≠ 0`. -/
theorem two_pow_le_natCast_mul {A : ℕ} (hA : A ≠ 0) (a : ℤ) :
    (2 : ℚ) ^ (a + bitlen A - 1) ≤ (A : ℚ) * 2 ^ a := by
  rw [show a + (bitlen A : ℤ) - 1 = a + ((bitlen A : ℤ) - 1) by omega, two_pow_add,
    Rat.mul_comm (2 ^ a)]
  exact Rat.mul_le_mul_of_nonneg_right (two_pow_bitlen_le_natCast hA) (Rat.le_of_lt (two_pow_pos a))

/-- `(A · 2^d : ℕ)` as a rational is `A · 2^d`. -/
theorem natCast_mul_pow (A d : ℕ) : ((A * 2 ^ d : ℕ) : ℚ) = (A : ℚ) * 2 ^ (d : ℤ) := by
  rw [Rat.natCast_mul, two_pow_natCast]

/-! ## Signs and comparison of dyadic numbers -/

/-- The sign of a rational, `−1`, `0` or `1`. -/
def sgnQ (x : ℚ) : ℤ := if x < 0 then -1 else if x = 0 then 0 else 1

/-- The comparison of two integers, `−1`, `0` or `1`. -/
def cmpZ (x y : ℤ) : ℤ := if x < y then -1 else if x = y then 0 else 1

theorem sgnQ_nonneg_iff (x : ℚ) : 0 ≤ sgnQ x ↔ 0 ≤ x := by
  unfold sgnQ
  by_cases h1 : x < 0
  · rw [if_pos h1]
    exact ⟨fun h => absurd h (by decide), fun h => absurd h (Rat.not_le.mpr h1)⟩
  · rw [if_neg h1]
    have : 0 ≤ x := Rat.not_lt.mp h1
    by_cases h2 : x = 0
    · rw [if_pos h2]; exact ⟨fun _ => this, fun _ => by decide⟩
    · rw [if_neg h2]; exact ⟨fun _ => this, fun _ => by decide⟩

theorem sgnQ_pos_iff (x : ℚ) : 0 < sgnQ x ↔ 0 < x := by
  unfold sgnQ
  by_cases h1 : x < 0
  · rw [if_pos h1]
    exact ⟨fun h => absurd h (by decide), fun h => absurd h (by grind)⟩
  · rw [if_neg h1]
    by_cases h2 : x = 0
    · rw [if_pos h2]; exact ⟨fun h => absurd h (by decide), fun h => absurd h (by grind)⟩
    · rw [if_neg h2]; exact ⟨fun _ => by grind, fun _ => by decide⟩

theorem sgnQ_eq_zero_iff (x : ℚ) : sgnQ x = 0 ↔ x = 0 := by
  unfold sgnQ
  by_cases h1 : x < 0
  · rw [if_pos h1]
    exact ⟨fun h => absurd h (by decide), fun h => absurd h (by grind)⟩
  · rw [if_neg h1]
    by_cases h2 : x = 0
    · rw [if_pos h2]; exact ⟨fun _ => h2, fun _ => rfl⟩
    · rw [if_neg h2]; exact ⟨fun h => absurd h (by decide), fun h => absurd h h2⟩

theorem sgnQ_eq_of_iff {x y : ℚ} (h1 : x < 0 ↔ y < 0) (h2 : x = 0 ↔ y = 0) : sgnQ x = sgnQ y := by
  unfold sgnQ
  by_cases a : x < 0
  · rw [if_pos a, if_pos (h1.mp a)]
  · rw [if_neg a, if_neg (fun h => a (h1.mpr h))]
    by_cases b : x = 0
    · rw [if_pos b, if_pos (h2.mp b)]
    · rw [if_neg b, if_neg (fun h => b (h2.mpr h))]

theorem sgnQ_mul_two_pow (y : ℚ) (c : ℤ) : sgnQ (y * 2 ^ c) = sgnQ y := by
  have hp := two_pow_pos c
  apply sgnQ_eq_of_iff
  · constructor
    · intro h; apply Classical.byContradiction; intro hn
      have := Rat.mul_le_mul_of_nonneg_right (Rat.not_lt.mp hn) (Rat.le_of_lt hp)
      rw [Rat.zero_mul] at this; grind
    · intro h; have := Rat.mul_lt_mul_of_pos_right h hp; rwa [Rat.zero_mul] at this
  · constructor
    · intro h; rcases Rat.mul_eq_zero.mp h with h | h
      · exact h
      · exact absurd h (Rat.ne_of_gt hp)
    · intro h; rw [h, Rat.zero_mul]

theorem sgnQ_intCast_sub (x y : ℤ) : sgnQ ((x : ℚ) - y) = cmpZ x y := by
  unfold sgnQ cmpZ
  by_cases h1 : x < y
  · have := Rat.intCast_lt_intCast.mpr h1
    rw [if_pos (by grind), if_pos h1]
  · rw [if_neg h1]
    by_cases h2 : x = y
    · subst h2
      rw [if_neg (by grind), if_pos (by grind), if_pos rfl]
    · have h3 : y < x := by omega
      have := Rat.intCast_lt_intCast.mpr h3
      rw [if_neg (by grind), if_neg h2, if_neg]
      intro h; apply h2; exact Rat.intCast_inj.mp (by grind)

/-- **Compare `A 2^a` with `K 2^b`** (`A K ≥ 0`): by the top bit positions, then, only when they are
equal, with one shift by at most the width of the operands. -/
def cmpDy (A : ℕ) (a : ℤ) (K : ℕ) (b : ℤ) : ℤ :=
  if A = 0 then (if K = 0 then 0 else -1)
  else if K = 0 then 1
  else if a + bitlen A < b + bitlen K then -1
  else if b + bitlen K < a + bitlen A then 1
  else if b ≤ a then cmpZ ((A <<< (a - b).toNat : ℕ) : ℤ) K
  else cmpZ A ((K <<< (b - a).toNat : ℕ) : ℤ)

theorem cmpDy_spec (A : ℕ) (a : ℤ) (K : ℕ) (b : ℤ) :
    cmpDy A a K b = sgnQ ((A : ℚ) * 2 ^ a - (K : ℚ) * 2 ^ b) := by
  have hpa := two_pow_pos a
  have hpb := two_pow_pos b
  unfold cmpDy
  by_cases hA : A = 0
  · subst hA
    have e0 : ((0 : ℕ) : ℚ) * 2 ^ a = 0 := by simp
    rw [if_pos rfl, e0]
    by_cases hK : K = 0
    · subst hK
      rw [if_pos rfl]
      have : (0 : ℚ) - ((0 : ℕ) : ℚ) * 2 ^ b = 0 := by
        rw [show ((0 : ℕ) : ℚ) = 0 from rfl, Rat.zero_mul]; grind
      rw [this]; unfold sgnQ; simp
    · rw [if_neg hK]
      have hK' : (0 : ℚ) < K := by exact_mod_cast Nat.pos_of_ne_zero hK
      have : (0 : ℚ) < K * 2 ^ b := by
        have := Rat.mul_lt_mul_of_pos_right hK' hpb; rwa [Rat.zero_mul] at this
      unfold sgnQ; rw [if_pos (by grind)]
  rw [if_neg hA]
  by_cases hK : K = 0
  · subst hK
    rw [if_pos rfl]
    have hA' : (0 : ℚ) < A := by exact_mod_cast Nat.pos_of_ne_zero hA
    have : (0 : ℚ) < A * 2 ^ a := by
      have := Rat.mul_lt_mul_of_pos_right hA' hpa; rwa [Rat.zero_mul] at this
    have e0 : (A : ℚ) * 2 ^ a - ((0 : ℕ) : ℚ) * 2 ^ b = A * 2 ^ a := by
      rw [show ((0 : ℕ) : ℚ) = 0 from rfl, Rat.zero_mul]; grind
    rw [e0]; unfold sgnQ; rw [if_neg (by grind), if_neg (by grind)]
  rw [if_neg hK]
  have uA := natCast_mul_two_pow_lt A a
  have lA := two_pow_le_natCast_mul hA a
  have uK := natCast_mul_two_pow_lt K b
  have lK := two_pow_le_natCast_mul hK b
  by_cases h1 : a + bitlen A < b + bitlen K
  · rw [if_pos h1]
    have : (2 : ℚ) ^ (a + bitlen A) ≤ 2 ^ (b + bitlen K - 1) := two_pow_le (by omega)
    unfold sgnQ; rw [if_pos (by grind)]
  rw [if_neg h1]
  by_cases h2 : b + bitlen K < a + bitlen A
  · rw [if_pos h2]
    have : (2 : ℚ) ^ (b + bitlen K) ≤ 2 ^ (a + bitlen A - 1) := two_pow_le (by omega)
    unfold sgnQ; rw [if_neg (by grind), if_neg (by grind)]
  rw [if_neg h2]
  by_cases h3 : b ≤ a
  · rw [if_pos h3, Nat.shiftLeft_eq, ← sgnQ_intCast_sub]
    have e : (A : ℚ) * 2 ^ a - K * 2 ^ b =
        ((((A * 2 ^ (a - b).toNat : ℕ) : ℤ) : ℚ) - ((K : ℤ) : ℚ)) * 2 ^ b := by
      rw [Rat.intCast_natCast, Rat.intCast_natCast, natCast_mul_pow]
      have : (2 : ℚ) ^ a = 2 ^ (((a - b).toNat : ℕ) : ℤ) * 2 ^ b := by
        rw [← two_pow_add]; congr 1; omega
      rw [this]; grind
    rw [e, sgnQ_mul_two_pow]
  · rw [if_neg h3, Nat.shiftLeft_eq, ← sgnQ_intCast_sub]
    have e : (A : ℚ) * 2 ^ a - K * 2 ^ b =
        (((A : ℤ) : ℚ) - (((K * 2 ^ (b - a).toNat : ℕ) : ℤ) : ℚ)) * 2 ^ a := by
      rw [Rat.intCast_natCast, Rat.intCast_natCast, natCast_mul_pow]
      have : (2 : ℚ) ^ b = 2 ^ (((b - a).toNat : ℕ) : ℤ) * 2 ^ a := by
        rw [← two_pow_add]; congr 1; omega
      rw [this]; grind
    rw [e, sgnQ_mul_two_pow]

/-! ## Exponent, integer part, nearest-even integer -/

theorem floorLog2_eq {a : ℚ} {e : ℤ} (h1 : 2 ^ e ≤ a) (h2 : a < 2 ^ (e + 1)) :
    floorLog2 a = e := by
  have hpos : 0 < a := lt_le_trans' (two_pow_pos e) h1
  obtain ⟨f1, f2⟩ := floorLog2_spec hpos
  have c1 : ¬ floorLog2 a + 1 ≤ e := fun h => by
    have := two_pow_le h; grind
  have c2 : ¬ e + 1 ≤ floorLog2 a := fun h => by
    have := two_pow_le h; grind
  omega

theorem floor_eq_of {t : ℚ} {F : ℤ} (h1 : (F : ℚ) ≤ t) (h2 : t < F + 1) : t.floor = F := by
  have a := Rat.le_floor_iff.mpr h1
  have hf := Rat.floor_le t
  have b : ((t.floor : ℤ) : ℚ) < ((F + 1 : ℤ) : ℚ) := by rw [Rat.intCast_add]; grind
  have := Rat.intCast_lt_intCast.mp b
  omega

theorem roundNearestEven_eq_of {t : ℚ} {F : ℤ} (h1 : (F : ℚ) ≤ t) (h2 : t < F + 1) :
    roundNearestEven t =
      if 1 < 2 * (t - F) ∨ (2 * (t - F) = 1 ∧ F % 2 = 1) then F + 1 else F := by
  unfold roundNearestEven
  rw [floor_eq_of h1 h2]

/-! ## Round to nearest even through comparisons

`cmp K h` answers the sign of `a − K 2^h`. -/

/-- The exponent of `a`, from a guess `eH` within one, with two comparisons. -/
def expByCmp (cmp : ℤ → ℤ → ℤ) (eH : ℤ) : ℤ :=
  if 0 ≤ cmp 1 (eH + 1) then eH + 1 else if 0 ≤ cmp 1 eH then eH else eH - 1

/-- The grid exponent of the format for exponent `e`. -/
def gridOf (p : ℕ) (emin e : ℤ) : ℤ := max e emin - ((p : ℤ) - 1)

/-- `⌊a / 2^g⌋`, from a guess `F0` within one, with two comparisons. -/
def intPartOf (cmp : ℤ → ℤ → ℤ) (F0 g : ℤ) : ℤ :=
  if 0 ≤ cmp (F0 + 1) g then F0 + 1 else if 0 ≤ cmp F0 g then F0 else F0 - 1

/-- The nearest integer to `a / 2^g`, ties to even, from its integer part `F`, with one
comparison of `a` with the midpoint `(2F + 1) 2^(g−1)`. -/
def dirOf (cmp : ℤ → ℤ → ℤ) (F g : ℤ) : ℤ :=
  let r := cmp (2 * F + 1) (g - 1)
  if 0 < r ∨ (r = 0 ∧ F % 2 = 1) then F + 1 else F

/-- **Round a positive magnitude to nearest even through comparisons.** `eH` is an exponent guess
with `2^(eH−1) ≤ a < 2^(eH+2)`, and `FH g` a guess of `⌊a / 2^g⌋` within one. Two comparisons
fix the exponent and hence the grid `g`, two more the integer part `F`, and one more the rounding
direction. Returns the rounded integer `M` and the grid `g`: the result is `M · 2^g`. -/
def roundByCmp (p : ℕ) (emin : ℤ) (cmp : ℤ → ℤ → ℤ) (eH : ℤ) (FH : ℤ → ℤ) : ℤ × ℤ :=
  let g := gridOf p emin (expByCmp cmp eH)
  (dirOf cmp (intPartOf cmp (FH g) g) g, g)

/-- The comparisons `roundByCmp` asks, for an exponent guess `eH`: `K < 2^(p+4)` and
`eH − p − 1 ≤ h ≤ max (eH + 1) (gridOf p emin (eH + 1))`. An oracle need only answer these. -/
def QueryOK (p : ℕ) (emin eH K h : ℤ) : Prop :=
  0 ≤ K ∧ K < 2 ^ (p + 4) ∧ eH - (p : ℤ) - 1 ≤ h ∧ h ≤ max (eH + 1) (gridOf p emin (eH + 1))

/-- An integer below `2^k` times `2^g`. -/
theorem lt_two_pow_of_mul {K g : ℤ} {k : ℕ} (h : (K : ℚ) * 2 ^ g < 2 ^ (g + k)) : K < 2 ^ k := by
  apply Classical.byContradiction; intro hn
  have hk : ((2 ^ k : ℤ) : ℚ) ≤ (K : ℚ) := Rat.intCast_le_intCast.mpr (by omega)
  rw [Rat.intCast_pow, show ((2 : ℤ) : ℚ) = 2 from rfl, ← Rat.zpow_natCast] at hk
  have := Rat.mul_le_mul_of_nonneg_right hk (Rat.le_of_lt (two_pow_pos g))
  rw [← two_pow_add, Int.add_comm] at this
  grind

section Spec

variable {a : ℚ} {cmp : ℤ → ℤ → ℤ}

theorem cmp_ge {K h : ℤ} (hc : cmp K h = sgnQ (a - (K : ℚ) * 2 ^ h)) :
    0 ≤ cmp K h ↔ (K : ℚ) * 2 ^ h ≤ a := by
  rw [hc, sgnQ_nonneg_iff]; constructor <;> intro <;> grind

theorem cmp_lt {K h : ℤ} (hc : cmp K h = sgnQ (a - (K : ℚ) * 2 ^ h)) (hn : ¬ 0 ≤ cmp K h) :
    a < (K : ℚ) * 2 ^ h := by
  apply Rat.not_le.mp; intro h'; exact hn ((cmp_ge hc).mpr h')

theorem expByCmp_spec {eH : ℤ} (hc1 : cmp 1 (eH + 1) = sgnQ (a - ((1 : ℤ) : ℚ) * 2 ^ (eH + 1)))
    (hc0 : cmp 1 eH = sgnQ (a - ((1 : ℤ) : ℚ) * 2 ^ eH))
    (hE1 : 2 ^ (eH - 1) ≤ a) (hE2 : a < 2 ^ (eH + 2)) :
    2 ^ expByCmp cmp eH ≤ a ∧ a < 2 ^ (expByCmp cmp eH + 1) ∧ eH - 1 ≤ expByCmp cmp eH ∧
      expByCmp cmp eH ≤ eH + 1 := by
  unfold expByCmp
  by_cases c1 : 0 ≤ cmp 1 (eH + 1)
  · rw [if_pos c1]
    have h := (cmp_ge hc1).mp c1
    refine ⟨by simpa using h, by rw [show eH + 1 + 1 = eH + 2 by omega]; exact hE2, by omega,
      by omega⟩
  · rw [if_neg c1]
    have hl := cmp_lt hc1 c1
    simp only [Rat.intCast_one, Rat.one_mul] at hl
    by_cases c2 : 0 ≤ cmp 1 eH
    · rw [if_pos c2]
      have h := (cmp_ge hc0).mp c2
      exact ⟨by simpa using h, hl, by omega, by omega⟩
    · rw [if_neg c2]
      have hl2 := cmp_lt hc0 c2
      simp only [Rat.intCast_one, Rat.one_mul] at hl2
      exact ⟨hE1, by rw [show eH - 1 + 1 = eH by omega]; exact hl2, by omega, by omega⟩

theorem intPartOf_spec (ha : 0 < a) {F0 g : ℤ}
    (hc1 : 0 ≤ F0 + 1 → cmp (F0 + 1) g = sgnQ (a - ((F0 + 1 : ℤ) : ℚ) * 2 ^ g))
    (hc0 : 0 ≤ F0 → cmp F0 g = sgnQ (a - (F0 : ℚ) * 2 ^ g))
    (hF1 : ((F0 : ℚ) - 1) * 2 ^ g ≤ a) (hF2 : a < ((F0 : ℚ) + 2) * 2 ^ g) :
    ((intPartOf cmp F0 g : ℤ) : ℚ) * 2 ^ g ≤ a ∧ a < ((intPartOf cmp F0 g : ℚ) + 1) * 2 ^ g ∧
      0 ≤ intPartOf cmp F0 g := by
  have hpg := two_pow_pos g
  have hF0m : -1 ≤ F0 := by
    apply Classical.byContradiction; intro hn
    have hle : (F0 : ℚ) + 2 ≤ 0 := by
      have : ((F0 : ℤ) : ℚ) ≤ ((-2 : ℤ) : ℚ) := Rat.intCast_le_intCast.mpr (by omega)
      simp at this; grind
    have := Rat.mul_le_mul_of_nonneg_right hle (Rat.le_of_lt hpg)
    rw [Rat.zero_mul] at this; grind
  have hc1' := hc1 (by omega)
  unfold intPartOf
  by_cases c1 : 0 ≤ cmp (F0 + 1) g
  · rw [if_pos c1]
    have h := (cmp_ge hc1').mp c1
    refine ⟨h, ?_, by omega⟩
    rw [Rat.intCast_add, Rat.intCast_one]; grind
  · rw [if_neg c1]
    have hl := cmp_lt hc1' c1
    rw [Rat.intCast_add, Rat.intCast_one] at hl
    have hF0n : 0 ≤ F0 := by
      apply Classical.byContradiction; intro hn
      have : F0 = -1 := by omega
      subst this; simp at hl; grind
    have hc0' := hc0 hF0n
    by_cases c2 : 0 ≤ cmp F0 g
    · rw [if_pos c2]
      exact ⟨(cmp_ge hc0').mp c2, hl, hF0n⟩
    · rw [if_neg c2]
      have hl2 := cmp_lt hc0' c2
      have hpos1 : 1 ≤ F0 := by
        apply Classical.byContradiction; intro hn
        have : F0 = 0 := by omega
        subst this; simp at hl2; grind
      refine ⟨?_, ?_, by omega⟩
      · rw [Rat.intCast_sub, Rat.intCast_one]; exact hF1
      · rw [Rat.intCast_sub, Rat.intCast_one]; grind

theorem dirOf_spec {F g : ℤ}
    (hc : cmp (2 * F + 1) (g - 1) = sgnQ (a - ((2 * F + 1 : ℤ) : ℚ) * 2 ^ (g - 1)))
    (h1 : (F : ℚ) * 2 ^ g ≤ a) (h2 : a < ((F : ℚ) + 1) * 2 ^ g) :
    roundNearestEven (a / 2 ^ g) = dirOf cmp F g := by
  have hpg := two_pow_pos g
  have hta : a / 2 ^ g * 2 ^ g = a := Rat.div_mul_cancel (two_pow_ne_zero g)
  generalize ht : a / 2 ^ g = t at hta
  have ht1 : (F : ℚ) ≤ t := by
    apply Classical.byContradiction; intro hn
    have := Rat.mul_lt_mul_of_pos_right (Rat.not_le.mp hn) hpg; grind
  have ht2 : t < (F : ℚ) + 1 := by
    apply Classical.byContradiction; intro hn
    have := Rat.mul_le_mul_of_nonneg_right (Rat.not_lt.mp hn) (Rat.le_of_lt hpg); grind
  rw [roundNearestEven_eq_of ht1 ht2]
  unfold dirOf
  simp only
  have hu : (2 : ℚ) ^ g = 2 * 2 ^ (g - 1) := by
    rw [show g = (g - 1) + 1 by omega, two_pow_succ]; simp only [Int.sub_add_cancel]; grind
  have hkey : a - ((2 * F + 1 : ℤ) : ℚ) * 2 ^ (g - 1) = (2 * (t - F) - 1) * 2 ^ (g - 1) := by
    rw [Rat.intCast_add, Rat.intCast_mul, Rat.intCast_one]
    rw [hu] at hta
    simp only [Rat.intCast_ofNat]
    grind
  have hr : cmp (2 * F + 1) (g - 1) = sgnQ (2 * (t - F) - 1) := by
    rw [hc, hkey, sgnQ_mul_two_pow]
  rw [hr]
  have hd : (1 < 2 * (t - F) ∨ (2 * (t - F) = 1 ∧ F % 2 = 1)) ↔
      (0 < sgnQ (2 * (t - F) - 1) ∨ (sgnQ (2 * (t - F) - 1) = 0 ∧ F % 2 = 1)) := by
    rw [sgnQ_pos_iff, sgnQ_eq_zero_iff]
    constructor
    · rintro (h | ⟨h, h'⟩)
      · left; grind
      · right; exact ⟨by grind, h'⟩
    · rintro (h | ⟨h, h'⟩)
      · left; grind
      · right; exact ⟨by grind, h'⟩
  by_cases c : 1 < 2 * (t - F) ∨ (2 * (t - F) = 1 ∧ F % 2 = 1)
  · rw [if_pos c, if_pos (hd.mp c)]
  · rw [if_neg c, if_neg (fun h => c (hd.mpr h))]

theorem gridOf_mono {p : ℕ} {emin e e' : ℤ} (h : e ≤ e') : gridOf p emin e ≤ gridOf p emin e' := by
  unfold gridOf; omega

/-- **Rounding through comparisons is round to nearest even.** The oracle need only answer the
comparisons of `QueryOK`. -/
theorem roundByCmp_spec {p : ℕ} {emin : ℤ} (ha : 0 < a) {eH : ℤ}
    (hcmp : ∀ K h, QueryOK p emin eH K h → cmp K h = sgnQ (a - (K : ℚ) * 2 ^ h))
    (hE1 : 2 ^ (eH - 1) ≤ a) (hE2 : a < 2 ^ (eH + 2)) {FH : ℤ → ℤ}
    (hF : ∀ g, eH - (p : ℤ) ≤ g → ((FH g : ℚ) - 1) * 2 ^ g ≤ a ∧ a < ((FH g : ℚ) + 2) * 2 ^ g) :
    rneMag p emin a = ((roundByCmp p emin cmp eH FH).1 : ℚ) * 2 ^ (roundByCmp p emin cmp eH FH).2 ∧
      0 ≤ (roundByCmp p emin cmp eH FH).1 := by
  have hp4 : (1 : ℤ) < 2 ^ (p + 4) := by
    have : (2 : ℤ) ^ (p + 4) = 2 ^ p * 16 := by rw [Int.pow_add]; rfl
    have : (0 : ℤ) < 2 ^ p := by
      have := Nat.two_pow_pos p
      have h2 : ((2 ^ p : ℕ) : ℤ) = (2 : ℤ) ^ p := by rw [Int.natCast_pow]; rfl
      omega
    omega
  have hgm : eH + 1 ≤ max (eH + 1) (gridOf p emin (eH + 1)) := Int.le_max_left _ _
  obtain ⟨he1, he2, heL, heU⟩ := expByCmp_spec (cmp := cmp)
    (hcmp 1 (eH + 1) ⟨by decide, hp4, by omega, hgm⟩)
    (hcmp 1 eH ⟨by decide, hp4, by omega, by omega⟩) hE1 hE2
  have hfl := floorLog2_eq he1 he2
  simp only [roundByCmp]
  generalize hE : expByCmp cmp eH = e at he1 he2 heL heU hfl
  generalize hG : gridOf p emin e = g
  have hgrid : rneGrid p emin a = g := by unfold rneGrid; rw [hfl, ← hG]; rfl
  have hgL : eH - (p : ℤ) ≤ g := by rw [← hG]; unfold gridOf; omega
  have hgU : g ≤ max (eH + 1) (gridOf p emin (eH + 1)) := by
    rw [← hG]; exact Int.le_trans (gridOf_mono heU) (Int.le_max_right _ _)
  have hpg := two_pow_pos g
  -- every integer compared is below `2^(p+2)` times `2^g`
  have hsmall : ∀ K : ℤ, (K : ℚ) * 2 ^ g ≤ a → K < 2 ^ (p + 2) := fun K hK =>
    lt_two_pow_of_mul (le_lt_trans' hK (lt_le_trans' hE2 (two_pow_le (by omega))))
  obtain ⟨hF1, hF2⟩ := hF g hgL
  have hF0b : FH g - 1 < 2 ^ (p + 2) := hsmall _ (by rw [Rat.intCast_sub, Rat.intCast_one]; exact hF1)
  have hp2 : (2 : ℤ) ^ (p + 4) = 2 ^ (p + 2) * 4 := by
    rw [show p + 4 = (p + 2) + 2 by omega, Int.pow_add]; rfl
  obtain ⟨hI1, hI2, hI0⟩ := intPartOf_spec (cmp := cmp) ha
    (fun h0 => hcmp _ _ ⟨h0, by omega, by omega, hgU⟩)
    (fun h0 => hcmp _ _ ⟨h0, by omega, by omega, hgU⟩) hF1 hF2
  generalize intPartOf cmp (FH g) g = F at hI1 hI2 hI0
  have hFb := hsmall F hI1
  have hdir := dirOf_spec (cmp := cmp)
    (hcmp _ _ ⟨by omega, by omega, by omega, by omega⟩) hI1 hI2
  refine ⟨?_, ?_⟩
  · unfold rneMag; rw [hgrid, hdir]
  · unfold dirOf; simp only; split <;> omega

end Spec

/-! ## Assembling the signed result -/

/-- The signed result `sgn · M · 2^g`, with the overflow test done by `cmpDy`. -/
def finishRNE (p : ℕ) (emax : ℤ) (sgn : ℤ) (Mg : ℤ × ℤ) : Option ℚ :=
  if cmpDy Mg.1.toNat Mg.2 (2 ^ p - 1) (emax - ((p : ℤ) - 1)) ≤ 0 then
    some ((sgn : ℚ) * Mg.1 * 2 ^ Mg.2)
  else none

theorem rneU_of_mag {p : ℕ} {emin : ℤ} {S : ℚ} {M g : ℤ}
    (hM : rneMag p emin (Rat.abs S) = (M : ℚ) * 2 ^ g) :
    rneU p emin S = (if S < 0 then (-1 : ℚ) else 1) * M * 2 ^ g := by
  unfold rneU
  split
  · rename_i h; rw [abs_of_neg h] at hM; rw [hM]; grind
  · rename_i h; rw [abs_of_nonneg (Rat.not_lt.mp h)] at hM; rw [hM]; grind

/-- **The signed rounding from the rounded magnitude.** -/
theorem roundRNE_eq_finish {p : ℕ} {emin emax : ℤ} {S : ℚ} {sgn M g : ℤ}
    (hsgn : (sgn : ℚ) = if S < 0 then -1 else 1) (hM : rneMag p emin (Rat.abs S) = (M : ℚ) * 2 ^ g)
    (hM0 : 0 ≤ M) : roundRNE p emin emax S = finishRNE p emax sgn (M, g) := by
  have hU := rneU_of_mag (p := p) (emin := emin) hM
  have hpg := two_pow_pos g
  have hMq : (0 : ℚ) ≤ M := by exact_mod_cast hM0
  have hn : (0 : ℚ) ≤ (M : ℚ) * 2 ^ g := Rat.mul_nonneg hMq (Rat.le_of_lt hpg)
  have habs : Rat.abs (rneU p emin S) = (M : ℚ) * 2 ^ g := by
    rw [hU]
    split
    · rw [show (-1 : ℚ) * M * 2 ^ g = -((M : ℚ) * 2 ^ g) by grind, abs_neg, abs_of_nonneg hn]
    · rw [show (1 : ℚ) * M * 2 ^ g = (M : ℚ) * 2 ^ g by grind, abs_of_nonneg hn]
  have hcmp := cmpDy_spec M.toNat g (2 ^ p - 1) (emax - ((p : ℤ) - 1))
  have hMn : ((M.toNat : ℕ) : ℚ) = M := by
    rw [← Rat.intCast_natCast, Int.toNat_of_nonneg hM0]
  rw [hMn] at hcmp
  unfold roundRNE finishRNE
  simp only
  rw [habs, hcmp, hU, ← hsgn]
  have hiff : sgnQ ((M : ℚ) * 2 ^ g - ((2 ^ p - 1 : ℕ) : ℚ) * 2 ^ (emax - ((p : ℤ) - 1))) ≤ 0 ↔
      (M : ℚ) * 2 ^ g ≤ maxFormat p emax := by
    unfold maxFormat
    generalize ((2 ^ p - 1 : ℕ) : ℚ) * 2 ^ (emax - ((p : ℤ) - 1)) = mf
    unfold sgnQ
    by_cases h1 : (M : ℚ) * 2 ^ g - mf < 0
    · rw [if_pos h1]; exact ⟨fun _ => by grind, fun _ => by decide⟩
    · rw [if_neg h1]
      by_cases h2 : (M : ℚ) * 2 ^ g - mf = 0
      · rw [if_pos h2]; exact ⟨fun _ => by grind, fun _ => by decide⟩
      · rw [if_neg h2]; exact ⟨fun h => absurd h (by decide), fun h => absurd h (by grind)⟩
  by_cases hc : (M : ℚ) * 2 ^ g ≤ maxFormat p emax
  · rw [if_pos hc, if_pos (hiff.mpr hc)]
  · rw [if_neg hc, if_neg (fun h => hc (hiff.mp h))]

theorem roundRNE_zero' (p : ℕ) (emin emax : ℤ) : roundRNE p emin emax 0 = some 0 := by
  unfold roundRNE
  rw [rneU_zero, abs_zero, if_pos]
  unfold maxFormat
  exact Rat.mul_nonneg Rat.natCast_nonneg (Rat.le_of_lt (two_pow_pos _))

theorem intCast_sign {N : ℤ} (hN : N ≠ 0) :
    ((N.sign : ℤ) : ℚ) = if (N : ℚ) < 0 then -1 else 1 := by
  by_cases h : N < 0
  · rw [Int.sign_eq_neg_one_of_neg h, if_pos (by exact_mod_cast h)]; rfl
  · have hp : 0 < N := by omega
    have : ((0 : ℤ) : ℚ) < (N : ℚ) := Rat.intCast_lt_intCast.mpr hp
    rw [Int.sign_eq_one_of_pos hp, if_neg (by simp at this; grind)]; rfl

theorem mul_two_pow_neg_iff (x : ℚ) (q : ℤ) : x * 2 ^ q < 0 ↔ x < 0 := by
  have hp := two_pow_pos q
  constructor
  · intro h; apply Classical.byContradiction; intro hn
    have := Rat.mul_le_mul_of_nonneg_right (Rat.not_lt.mp hn) (Rat.le_of_lt hp)
    rw [Rat.zero_mul] at this; grind
  · intro h; have := Rat.mul_lt_mul_of_pos_right h hp; rwa [Rat.zero_mul] at this

/-! ## Round to nearest even of `N · 2^q` with integer operations -/

/-- `⌊A · 2^(q − g)⌋` by one shift. -/
def shiftFloor (A : ℕ) (q g : ℤ) : ℤ :=
  if g ≤ q then ((A <<< (q - g).toNat : ℕ) : ℤ) else ((A >>> (g - q).toNat : ℕ) : ℤ)

theorem shiftFloor_spec (A : ℕ) (q g : ℤ) :
    (shiftFloor A q g : ℚ) * 2 ^ g ≤ (A : ℚ) * 2 ^ q ∧
      (A : ℚ) * 2 ^ q < ((shiftFloor A q g : ℚ) + 1) * 2 ^ g := by
  have hpg := two_pow_pos g
  unfold shiftFloor
  split
  · rename_i h
    rw [Nat.shiftLeft_eq, Rat.intCast_natCast, natCast_mul_pow]
    have e : (A : ℚ) * 2 ^ q = (A : ℚ) * 2 ^ (((q - g).toNat : ℕ) : ℤ) * 2 ^ g := by
      rw [Rat.mul_assoc, ← two_pow_add]; congr 2; omega
    rw [e]
    exact ⟨Rat.le_refl, by grind⟩
  · rename_i h
    rw [Nat.shiftRight_eq_div_pow, Rat.intCast_natCast]
    generalize hd : (g - q).toNat = d
    have hgq : g = q + d := by omega
    have hdm := Nat.div_add_mod A (2 ^ d)
    have hml := Nat.mod_lt A (Nat.two_pow_pos d)
    have hA : (A : ℚ) = ((2 ^ d : ℕ) : ℚ) * ((A / 2 ^ d : ℕ) : ℚ) + ((A % 2 ^ d : ℕ) : ℚ) := by
      rw [← Rat.natCast_mul, ← Rat.natCast_add, hdm]
    have hm : ((A % 2 ^ d : ℕ) : ℚ) < ((2 ^ d : ℕ) : ℚ) := by exact_mod_cast hml
    have hm0 : (0 : ℚ) ≤ ((A % 2 ^ d : ℕ) : ℚ) := Rat.natCast_nonneg
    have hg2 : (2 : ℚ) ^ g = ((2 ^ d : ℕ) : ℚ) * 2 ^ q := by
      rw [← two_pow_natCast, ← two_pow_add, hgq]; congr 1; omega
    rw [hg2, hA]
    have hpq := two_pow_pos q
    constructor
    · have := Rat.mul_le_mul_of_nonneg_right hm0 (Rat.le_of_lt hpq); grind
    · have := Rat.mul_lt_mul_of_pos_right hm hpq; grind

/-- **Round to nearest even of `N · 2^q`** with integer operations only: bit lengths, shifts and
the comparisons of `cmpDy`. -/
def roundExact (p : ℕ) (emin emax : ℤ) (N q : ℤ) : Option ℚ :=
  if N = 0 then some 0
  else finishRNE p emax N.sign
    (roundByCmp p emin (fun K h => cmpDy N.natAbs q K.toNat h)
      (q + bitlen N.natAbs - 1) (shiftFloor N.natAbs q))

/-- **Integer round to nearest even equals `roundRNE`**, for every `N` and `q`. -/
theorem roundExact_eq (p : ℕ) (emin emax : ℤ) (N q : ℤ) :
    roundExact p emin emax N q = roundRNE p emin emax ((N : ℚ) * 2 ^ q) := by
  unfold roundExact
  by_cases hN : N = 0
  · subst hN
    rw [if_pos rfl]
    have : ((0 : ℤ) : ℚ) * 2 ^ q = 0 := by simp
    rw [this, roundRNE_zero']
  rw [if_neg hN]
  have hA : N.natAbs ≠ 0 := by omega
  have hpq := two_pow_pos q
  have hS : Rat.abs ((N : ℚ) * 2 ^ q) = ((N.natAbs : ℕ) : ℚ) * 2 ^ q := by
    rw [abs_mul_two_pow, abs_intCast]
  have ha : 0 < ((N.natAbs : ℕ) : ℚ) * 2 ^ q := by
    have : (0 : ℚ) < ((N.natAbs : ℕ) : ℚ) := by exact_mod_cast Nat.pos_of_ne_zero hA
    have := Rat.mul_lt_mul_of_pos_right this hpq; rwa [Rat.zero_mul] at this
  obtain ⟨hmag, hM0⟩ := roundByCmp_spec (p := p) (emin := emin) ha
    (cmp := fun K h => cmpDy N.natAbs q K.toNat h)
    (fun K h ⟨hK, _⟩ => by
      show cmpDy N.natAbs q K.toNat h = _
      rw [cmpDy_spec]
      congr 2
      rw [← Rat.intCast_natCast, Int.toNat_of_nonneg hK])
    (eH := q + bitlen N.natAbs - 1)
    (Rat.le_trans (two_pow_le (by omega)) (two_pow_le_natCast_mul hA q))
    (lt_le_trans' (natCast_mul_two_pow_lt N.natAbs q) (two_pow_le (by omega)))
    (FH := shiftFloor N.natAbs q)
    (fun g _ => by
      obtain ⟨h1, h2⟩ := shiftFloor_spec N.natAbs q g
      have hpg := two_pow_pos g
      constructor
      · exact Rat.le_trans (Rat.mul_le_mul_of_nonneg_right (by grind) (Rat.le_of_lt hpg)) h1
      · exact lt_le_trans' h2 (Rat.mul_le_mul_of_nonneg_right (by grind) (Rat.le_of_lt hpg)))
  rw [← hS] at hmag
  symm
  apply roundRNE_eq_finish _ hmag hM0
  rw [intCast_sign hN]
  have hiff := mul_two_pow_neg_iff (N : ℚ) q
  by_cases h : (N : ℚ) < 0
  · rw [if_pos h, if_pos (hiff.mpr h)]
  · rw [if_neg h, if_neg (fun h' => h (hiff.mp h'))]

/-! ## Examples, checked by the kernel -/

/-- A wrapping register: `100 + 50` wraps in 8 bits, the final sum `90` does not. -/
example : fixedSum 8 [100, 50, -60] = 90 := by decide +kernel

/-- A tie: `5 · 2^-1 = 2.5` with two bits rounds to the even `2`. -/
example : roundExact 2 (-10) 10 5 (-1) = some 2 := by decide +kernel

example : roundExact 2 (-10) 10 5 (-1) = roundRNE 2 (-10) 10 ((5 : ℤ) * 2 ^ (-1 : ℤ)) := by
  decide +kernel

/-- Binary32: a normal, a subnormal, and the overflow threshold. -/
example : roundExact 24 (-126) 127 (2 ^ 25 + 3) (-3) =
    roundRNE 24 (-126) 127 (((2 ^ 25 + 3 : ℤ) : ℚ) * 2 ^ (-3 : ℤ)) := by decide +kernel

example : roundExact 24 (-126) 127 (-(2 ^ 25 + 4)) (-160) =
    roundRNE 24 (-126) 127 (((-(2 ^ 25 + 4) : ℤ) : ℚ) * 2 ^ (-160 : ℤ)) := by decide +kernel

example : roundExact 24 (-126) 127 (2 ^ 25 - 1) 103 = none ∧
    roundRNE 24 (-126) 127 (((2 ^ 25 - 1 : ℤ) : ℚ) * 2 ^ (103 : ℤ)) = none := by decide +kernel

end Ozaki
