import Ozaki.Ozaki1
import Ozaki.CRT

/-! # Ozaki-II: modular integer products

Ozaki, Uchino and Imamura (2025) replace slicing by modular arithmetic. For one output entry
`x · y`:

1. Scale `x` by `2^sₓ` so that `max|x|` lies in `(2^(P−1), 2^P]`, and truncate:
   `a = trunc(2^sₓ x)`, `|aᵢ| ≤ 2^P`; likewise `c = trunc(2^s_y y)`. This truncation is the only
   approximation of the scheme.
2. For each modulus `m` of a CRT basis, multiply the symmetric residues of `a` and `c` on the matrix
   multiplier: one low-precision product per modulus. With `m ≤ 2^(b+1)` the residues are `b`-bit
   integers, and the matrix multiplier is exact.
3. Reconstruct `a · c` from the residues of the products (`crt_eq`); this is exact when
   `2 k 2^(2P) < M`.
4. Scale back by `2^(−sₓ−s_y)` and round once.

Main results:

* `ozaki2_eq`: with an exact matrix multiplier and `2 k 2^(2P) < M`, Ozaki-II returns the single
  rounding of `2^(−sₓ−s_y) (a · c)`;
* `truncProduct_error`: `|x · y − 2^(−sₓ−s_y) (a · c)| ≤ Σᵢ (2^(−sₓ)|yᵢ| + 2^(−sₓ−s_y)|aᵢ|)`, the
  a-priori bound the Z3 model checks at runtime (`[S5.1]`);
* `truncProduct_error_normwise`: that is at most `8 k max|x| max|y| 2^(−P)`;
* `ozaki2_error`: with a rounding of relative error `u` and absolute error `η`, the result is
  within `u |C| + η` of `C = 2^(−sₓ−s_y) (a · c)`, and so within the bound above plus that of
  `x · y`.

As in the Z3 model, the residues and the reconstruction use exact integer arithmetic. -/

local notation "ℕ" => Nat
local notation "ℤ" => Int
local notation "ℚ" => Rat

namespace Ozaki

/-! ## Scaling -/

/-- The shift that puts `max|x|` in `(2^(P−1), 2^P]`: `P − ⌈log₂ max|x|⌉`, and `0` for a zero
vector. -/
def scaleShift (P : ℕ) (x : List ℚ) : ℤ := if maxAbs x = 0 then 0 else P - ceilLog2 (maxAbs x)

/-- `aᵢ = trunc(2^shift · xᵢ)`. -/
def scaleTrunc (shift : ℤ) (x : List ℚ) : List ℤ := x.map fun a => truncInt (a * 2 ^ shift)

theorem scaleTrunc_length (shift : ℤ) (x : List ℚ) : (scaleTrunc shift x).length = x.length := by
  simp [scaleTrunc]

/-- The scaled integers have magnitude at most `2^P`. -/
theorem scaleTrunc_bound (P : ℕ) (x : List ℚ) :
    ∀ z ∈ scaleTrunc (scaleShift P x) x, z.natAbs ≤ 2 ^ P := by
  intro z hz
  obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hz
  apply natAbs_truncInt_le
  unfold scaleShift
  split
  · rename_i h
    rw [eq_zero_of_maxAbs h a ha, Rat.zero_mul, abs_zero]
    exact Rat.natCast_nonneg
  · rename_i h
    have hpos : 0 < maxAbs x := by have := maxAbs_nonneg x; grind
    have hE := (ceilLog2_spec hpos).2
    rw [abs_mul_two_pow, ← two_pow_natCast]
    have h1 := Rat.mul_le_mul_of_nonneg_right (Rat.le_trans (abs_le_maxAbs ha) hE)
      (Rat.le_of_lt (two_pow_pos ((P : ℤ) - ceilLog2 (maxAbs x))))
    rw [← two_pow_add] at h1
    have : ceilLog2 (maxAbs x) + ((P : ℤ) - ceilLog2 (maxAbs x)) = P := by omega
    rwa [this] at h1

/-- `max|x| ≤ 2^(P − sₓ)`: the shift's exponent bounds every entry. -/
theorem abs_le_scaleShift (P : ℕ) (x : List ℚ) : ∀ a ∈ x, Rat.abs a ≤ 2 ^ ((P : ℤ) - scaleShift P x) := by
  intro a ha
  unfold scaleShift
  split
  · rename_i h
    rw [eq_zero_of_maxAbs h a ha, abs_zero]; exact Rat.le_of_lt (two_pow_pos _)
  · rename_i h
    have hpos : 0 < maxAbs x := by have := maxAbs_nonneg x; grind
    have : (P : ℤ) - ((P : ℤ) - ceilLog2 (maxAbs x)) = ceilLog2 (maxAbs x) := by omega
    rw [this]
    exact Rat.le_trans (abs_le_maxAbs ha) (ceilLog2_spec hpos).2

/-- One truncated product: `|xy − 2^(−s−t) a c| ≤ 2^(−s)|y| + 2^(−s−t)|a|` for
`a = trunc(2^s x)` and `c = trunc(2^t y)`. -/
theorem truncTerm_error (x y : ℚ) (s t : ℤ) :
    Rat.abs (x * y - 2 ^ (-(s + t)) * ((truncInt (x * 2 ^ s) : ℚ) * truncInt (y * 2 ^ t))) ≤
      2 ^ (-s) * Rat.abs y + 2 ^ (-(s + t)) * Rat.abs (truncInt (x * 2 ^ s) : ℚ) := by
  generalize ha : (truncInt (x * 2 ^ s) : ℚ) = a
  generalize hc : (truncInt (y * 2 ^ t) : ℚ) = c
  have hα := (truncInt_spec (x * 2 ^ s)).1
  have hβ := (truncInt_spec (y * 2 ^ t)).1
  rw [ha] at hα; rw [hc] at hβ
  generalize hal : x * 2 ^ s - a = α at hα
  generalize hbe : y * 2 ^ t - c = β at hβ
  have hs : (2 : ℚ) ^ s * 2 ^ (-s) = 1 := by rw [← two_pow_add, Int.add_right_neg, two_pow_zero]
  have ht : (2 : ℚ) ^ t * 2 ^ (-t) = 1 := by rw [← two_pow_add, Int.add_right_neg, two_pow_zero]
  have hst : (2 : ℚ) ^ (-(s + t)) = 2 ^ (-s) * 2 ^ (-t) := by rw [← two_pow_add]; congr 1; omega
  have hx : x = (a + α) * 2 ^ (-s) := by
    rw [← hal]; have : x * 2 ^ s * 2 ^ (-s) = x := by rw [Rat.mul_assoc, hs, Rat.mul_one]
    grind
  have hy : y = (c + β) * 2 ^ (-t) := by
    rw [← hbe]; have : y * 2 ^ t * 2 ^ (-t) = y := by rw [Rat.mul_assoc, ht, Rat.mul_one]
    grind
  have hdiff : x * y - 2 ^ (-(s + t)) * (a * c) =
      α * 2 ^ (-s) * y + a * 2 ^ (-s) * 2 ^ (-t) * β := by
    rw [hst]; rw [hx]; conv => lhs; rw [hy]
    conv => rhs; rw [hy]
    grind
  rw [hdiff]
  have h1 : Rat.abs (α * 2 ^ (-s) * y) ≤ 2 ^ (-s) * Rat.abs y := by
    rw [abs_mul, abs_mul, abs_two_pow]
    have := Rat.mul_le_mul_of_nonneg_right (Rat.le_of_lt hα)
      (Rat.mul_nonneg (Rat.le_of_lt (two_pow_pos (-s))) (abs_nonneg y))
    grind
  have h2 : Rat.abs (a * 2 ^ (-s) * 2 ^ (-t) * β) ≤ 2 ^ (-(s + t)) * Rat.abs a := by
    rw [abs_mul, abs_mul, abs_mul, abs_two_pow, abs_two_pow, hst]
    have := Rat.mul_le_mul_of_nonneg_left (Rat.le_of_lt hβ)
      (Rat.mul_nonneg (Rat.mul_nonneg (abs_nonneg a) (Rat.le_of_lt (two_pow_pos (-s))))
        (Rat.le_of_lt (two_pow_pos (-t))))
    grind
  have := abs_add_le (α * 2 ^ (-s) * y) (a * 2 ^ (-s) * 2 ^ (-t) * β)
  grind

/-- **Truncation error** (`[S5.1]` of the Z3 model):
`|x · y − 2^(−s−t) (a · c)| ≤ Σᵢ (2^(−s)|yᵢ| + 2^(−s−t)|aᵢ|)`. -/
theorem truncProduct_error (s t : ℤ) :
    ∀ (x y : List ℚ), x.length = y.length →
      Rat.abs (dot x y - 2 ^ (-(s + t)) * (dotZ (scaleTrunc s x) (scaleTrunc t y) : ℚ)) ≤
        (List.zipWith (fun a b => 2 ^ (-s) * Rat.abs b +
          2 ^ (-(s + t)) * Rat.abs (truncInt (a * 2 ^ s) : ℚ)) x y).sum
  | [], [], _ => by
    have h0 : dotZ (scaleTrunc s []) (scaleTrunc t []) = 0 := rfl
    rw [h0, Rat.intCast_zero, Rat.mul_zero, dot_nil_left]
    simp only [List.zipWith_nil_left, List.sum_nil]
    rw [show (0 : ℚ) - 0 = 0 by grind, abs_zero]; grind
  | [], _ :: _, h => by simp at h
  | _ :: _, [], h => by simp at h
  | a :: x, b :: y, h => by
    have ih := truncProduct_error s t x y (by simpa using h)
    simp only [scaleTrunc, List.map_cons, dotZ_cons, dot_cons, List.zipWith_cons_cons,
      List.sum_cons, Rat.intCast_add, Rat.intCast_mul] at ih ⊢
    have h1 := truncTerm_error a b s t
    have e : a * b + dot x y -
        2 ^ (-(s + t)) * ((truncInt (a * 2 ^ s) : ℚ) * (truncInt (b * 2 ^ t) : ℚ) +
          ((dotZ (x.map fun a => truncInt (a * 2 ^ s)) (y.map fun a => truncInt (a * 2 ^ t)) : ℤ) : ℚ)) =
        (a * b - 2 ^ (-(s + t)) * ((truncInt (a * 2 ^ s) : ℚ) * (truncInt (b * 2 ^ t) : ℚ))) +
        (dot x y - 2 ^ (-(s + t)) *
          ((dotZ (x.map fun a => truncInt (a * 2 ^ s)) (y.map fun a => truncInt (a * 2 ^ t)) : ℤ) : ℚ)) := by
      grind
    rw [e]
    have := abs_add_le (a * b - 2 ^ (-(s + t)) * ((truncInt (a * 2 ^ s) : ℚ) * (truncInt (b * 2 ^ t) : ℚ)))
      (dot x y - 2 ^ (-(s + t)) *
          ((dotZ (x.map fun a => truncInt (a * 2 ^ s)) (y.map fun a => truncInt (a * 2 ^ t)) : ℤ) : ℚ))
    grind

/-- **Truncation error, normwise.** With the shifts of Ozaki-II and nonzero `x` and `y`,
`|x · y − 2^(−sₓ−s_y) (a · c)| ≤ 2 k 2^(E + F − P) ≤ 8 k max|x| max|y| 2^(−P)`. -/
theorem truncProduct_error_normwise (P : ℕ) {x y : List ℚ} (hlen : x.length = y.length)
    (hx : maxAbs x ≠ 0) (hy : maxAbs y ≠ 0) :
    Rat.abs (dot x y - 2 ^ (-(scaleShift P x + scaleShift P y)) *
        (dotZ (scaleTrunc (scaleShift P x) x) (scaleTrunc (scaleShift P y) y) : ℚ)) ≤
      8 * x.length * maxAbs x * maxAbs y * 2 ^ (-(P : ℤ)) := by
  refine Rat.le_trans (truncProduct_error _ _ x y hlen) ?_
  have hEx := ceilLog2_spec (show 0 < maxAbs x by have := maxAbs_nonneg x; grind)
  have hEy := ceilLog2_spec (show 0 < maxAbs y by have := maxAbs_nonneg y; grind)
  have hsx : scaleShift P x = P - ceilLog2 (maxAbs x) := by unfold scaleShift; rw [if_neg hx]
  have hsy : scaleShift P y = P - ceilLog2 (maxAbs y) := by unfold scaleShift; rw [if_neg hy]
  generalize hE : ceilLog2 (maxAbs x) = E at *
  generalize hF : ceilLog2 (maxAbs y) = F at *
  -- each term is at most `2 · 2^(E + F − P)`
  have hterm : ∀ p1 ∈ x, ∀ p2 ∈ y,
      2 ^ (-scaleShift P x) * Rat.abs p2 + 2 ^ (-(scaleShift P x + scaleShift P y)) *
        Rat.abs (truncInt (p1 * 2 ^ scaleShift P x) : ℚ) ≤ 2 * 2 ^ (E + F - P) := by
    intro p1 hp1 p2 hp2
    have hb : Rat.abs p2 ≤ 2 ^ F := Rat.le_trans (abs_le_maxAbs hp2) hEy.2
    have ha : Rat.abs (truncInt (p1 * 2 ^ scaleShift P x) : ℚ) ≤ 2 ^ (P : ℤ) := by
      rw [two_pow_natCast]
      exact abs_intCast_le (scaleTrunc_bound P x _ (List.mem_map.mpr ⟨p1, hp1, rfl⟩))
    have h1 := Rat.mul_le_mul_of_nonneg_left hb (Rat.le_of_lt (two_pow_pos (-scaleShift P x)))
    have h2 := Rat.mul_le_mul_of_nonneg_left ha
      (Rat.le_of_lt (two_pow_pos (-(scaleShift P x + scaleShift P y))))
    rw [← two_pow_add] at h1 h2
    have e1 : -scaleShift P x + F = E + F - P := by omega
    have e2 : -(scaleShift P x + scaleShift P y) + P = E + F - P := by omega
    rw [e1] at h1; rw [e2] at h2
    grind
  have hsum : (List.zipWith (fun a b => 2 ^ (-scaleShift P x) * Rat.abs b +
      2 ^ (-(scaleShift P x + scaleShift P y)) * Rat.abs (truncInt (a * 2 ^ scaleShift P x) : ℚ))
      x y).sum ≤ x.length * (2 * 2 ^ (E + F - P)) :=
    sum_zipWith_le (by have := two_pow_pos (E + F - P); grind) x y hterm
  refine Rat.le_trans hsum ?_
  -- `2^(E+F−P) < 4 max|x| max|y| 2^(−P)`
  have h2x : (2 : ℚ) ^ E ≤ 2 * maxAbs x := by
    have : (2 : ℚ) ^ E = 2 ^ (E - 1) * 2 := by rw [← two_pow_succ, Int.sub_add_cancel]
    grind
  have h2y : (2 : ℚ) ^ F ≤ 2 * maxAbs y := by
    have : (2 : ℚ) ^ F = 2 ^ (F - 1) * 2 := by rw [← two_pow_succ, Int.sub_add_cancel]
    grind
  have hsplit : (2 : ℚ) ^ (E + F - P) = 2 ^ E * 2 ^ F * 2 ^ (-(P : ℤ)) := by
    rw [← two_pow_add, ← two_pow_add]; congr 1
  rw [hsplit]
  have hxy : (2 : ℚ) ^ E * 2 ^ F ≤ (2 * maxAbs x) * (2 * maxAbs y) := by
    have := mul_le_mul_abs (a := (2 : ℚ) ^ E) (b := 2 ^ F) (by rw [abs_two_pow]; exact h2x)
      (by rw [abs_two_pow]; exact h2y)
    rwa [abs_mul, abs_two_pow, abs_two_pow] at this
  have hP := two_pow_pos (-(P : ℤ))
  have := Rat.mul_le_mul_of_nonneg_right hxy (Rat.le_of_lt hP)
  have := Rat.mul_le_mul_of_nonneg_left this (show (0 : ℚ) ≤ 2 * x.length by
    have : (0 : ℚ) ≤ x.length := Rat.natCast_nonneg; grind)
  grind

/-! ## The scheme -/

/-- A rational that is an integer, as an integer. -/
def toInt? (v : ℚ) : Option ℤ := if v.den = 1 then some v.num else none

theorem toInt?_intCast (z : ℤ) : toInt? (z : ℚ) = some z := by
  simp [toInt?, Rat.den_intCast, Rat.num_intCast]

/-- The product of the residues of `a` and `c` modulo `m`, on the matrix multiplier, reduced modulo
`m`. -/
def residueProduct (mult : MatrixMultiplier) (m : ℕ) (a c : List ℤ) : Option ℤ := do
  let v ← mult (a.map fun z => symMod z m) (c.map fun z => symMod z m)
  let z ← toInt? v
  return z % (m : ℤ)

/-- **Ozaki-II** for one output entry `x · y`: scale and truncate to `P`-bit integers, one dot
product on the matrix multiplier per modulus, CRT reconstruction, one final rounding. -/
def ozaki2 (mult : MatrixMultiplier) (round : ℚ → Option ℚ) (B : CRTBasis) (P : ℕ) (x y : List ℚ) :
    Option ℚ := do
  let a := scaleTrunc (scaleShift P x) x
  let c := scaleTrunc (scaleShift P y) y
  let rs ← B.moduli.mapM fun m => residueProduct mult m a c
  round ((crt B rs : ℚ) * 2 ^ (-(scaleShift P x + scaleShift P y)))

theorem emod_sub_dvd (z m : ℤ) : m ∣ z % m - z := ⟨-(z / m), by rw [Int.emod_def, Int.mul_neg]; omega⟩

/-- Products of residues are congruent to the product. -/
theorem dvd_dotZ_symMod (m : ℕ) :
    ∀ a c : List ℤ, (m : ℤ) ∣ dotZ a c - dotZ (a.map fun z => symMod z m) (c.map fun z => symMod z m)
  | [], _ => by simp
  | _ :: _, [] => by simp
  | x :: a, z :: c => by
    simp only [List.map_cons, dotZ_cons]
    have hx := symMod_dvd x m
    have hz := symMod_dvd z m
    have ih := dvd_dotZ_symMod m a c
    have e : x * z + dotZ a c - (symMod x m * symMod z m +
        dotZ (a.map fun z => symMod z m) (c.map fun z => symMod z m)) =
        x * (z - symMod z m) + (x - symMod x m) * symMod z m +
          (dotZ a c - dotZ (a.map fun z => symMod z m) (c.map fun z => symMod z m)) := by
      rw [Int.mul_sub, Int.sub_mul]; omega
    rw [e]
    exact Int.dvd_add (Int.dvd_add (Int.dvd_trans hz (Int.dvd_mul_left x _))
      (Int.dvd_trans hx (Int.dvd_mul_right _ _))) ih

/-- With an exact matrix multiplier, each modulus returns the residue of `a · c`. -/
theorem residueProduct_eq {mult : MatrixMultiplier} {b bound : ℕ} (hmult : mult.ExactOn b bound) {m : ℕ}
    (hm : 0 < m) (hmb : m ≤ 2 ^ (b + 1)) {a c : List ℤ} (hlen : a.length = c.length)
    (hbound : a.length * (2 ^ b * 2 ^ b) ≤ bound) :
    residueProduct mult m a c = some
      (dotZ (a.map fun z => symMod z m) (c.map fun z => symMod z m) % (m : ℤ)) := by
  have hres : ∀ z : ℤ, (symMod z m).natAbs ≤ 2 ^ b := by
    intro z
    have := natAbs_symMod_le z hm
    rw [Nat.pow_succ] at hmb
    omega
  have hx : ∀ z ∈ a.map fun z => symMod z m, z.natAbs ≤ 2 ^ b := by
    intro z hz; obtain ⟨w, _, rfl⟩ := List.mem_map.mp hz; exact hres w
  have hy : ∀ z ∈ c.map fun z => symMod z m, z.natAbs ≤ 2 ^ b := by
    intro z hz; obtain ⟨w, _, rfl⟩ := List.mem_map.mp hz; exact hres w
  unfold residueProduct
  rw [hmult _ _ (by simpa using hlen) hx hy (by
    refine Nat.le_trans (dotAbs_le _ _ _ _ hx hy) ?_
    simpa using hbound)]
  simp [toInt?_intCast]

/-- **Exact reconstruction.** With a matrix multiplier exact on `b`-bit integers, moduli at most
`2^(b+1)`, and `2 k 2^(2P) < M`, Ozaki-II rounds `2^(−sₓ−s_y) (a · c)` once. -/
theorem ozaki2_eq {mult : MatrixMultiplier} {b bound : ℕ} (hmult : mult.ExactOn b bound)
    (round : ℚ → Option ℚ) {B : CRTBasis} (hB : B.Valid) (hmb : ∀ m ∈ B.moduli, m ≤ 2 ^ (b + 1))
    (P : ℕ) {x y : List ℚ} (hlen : x.length = y.length)
    (hbound : x.length * (2 ^ b * 2 ^ b) ≤ bound)
    (hrange : 2 * x.length * (2 ^ P * 2 ^ P) < B.modulus) :
    ozaki2 mult round B P x y =
      round ((dotZ (scaleTrunc (scaleShift P x) x) (scaleTrunc (scaleShift P y) y) : ℚ) *
        2 ^ (-(scaleShift P x + scaleShift P y))) := by
  have hpos := hB.2.1
  generalize ha : scaleTrunc (scaleShift P x) x = a
  generalize hc : scaleTrunc (scaleShift P y) y = c
  have hla : a.length = x.length := by rw [← ha, scaleTrunc_length]
  have hlc : c.length = y.length := by rw [← hc, scaleTrunc_length]
  have hrs : B.moduli.mapM (fun m => residueProduct mult m a c) = some (B.moduli.map fun m =>
      dotZ (a.map fun z => symMod z m) (c.map fun z => symMod z m) % (m : ℤ)) :=
    mapM_eq_some_map fun m hm => residueProduct_eq hmult (hpos m hm) (hmb m hm)
      (by rw [hla, hlc, hlen]) (by rw [hla]; exact hbound)
  have hcrt : crt B (B.moduli.map fun m =>
      dotZ (a.map fun z => symMod z m) (c.map fun z => symMod z m) % (m : ℤ)) = dotZ a c := by
    have hab : (dotZ a c).natAbs ≤ x.length * (2 ^ P * 2 ^ P) := by
      refine Nat.le_trans (natAbs_dotZ_le a c) ?_
      rw [← hla]
      exact dotAbs_le a c _ _ (by rw [← ha]; exact scaleTrunc_bound P x)
        (by rw [← hc]; exact scaleTrunc_bound P y)
    rw [Nat.mul_assoc] at hrange
    apply crt_eq hB (by simp)
    · intro j
      rcases j with ⟨j, hj⟩
      simp only [Fin.getElem_fin, List.getD_eq_getElem?_getD, List.getElem?_map,
        List.getElem?_eq_getElem hj, Option.map_some, Option.getD_some]
      have h1 := dvd_dotZ_symMod B.moduli[j] a c
      have h2 : ((B.moduli[j] : ℕ) : ℤ) ∣
          dotZ (a.map fun z => symMod z B.moduli[j]) (c.map fun z => symMod z B.moduli[j]) % B.moduli[j] -
          dotZ (a.map fun z => symMod z B.moduli[j]) (c.map fun z => symMod z B.moduli[j]) := by
        exact emod_sub_dvd _ _
      have : dotZ (a.map fun z => symMod z B.moduli[j]) (c.map fun z => symMod z B.moduli[j]) %
          B.moduli[j] - dotZ a c =
          (dotZ (a.map fun z => symMod z B.moduli[j]) (c.map fun z => symMod z B.moduli[j]) %
            B.moduli[j] - dotZ (a.map fun z => symMod z B.moduli[j])
              (c.map fun z => symMod z B.moduli[j])) -
          (dotZ a c - dotZ (a.map fun z => symMod z B.moduli[j])
            (c.map fun z => symMod z B.moduli[j])) := by omega
      rw [this]
      exact Int.dvd_sub h2 h1
    · omega
    · omega
  unfold ozaki2
  simp only [ha, hc, hrs, Option.bind_eq_bind, Option.bind_some, hcrt]

/-- **Ozaki-II error.** With an exact matrix multiplier and a rounding of relative error `u` and
absolute error `η`, the result `v` satisfies
`|v − x · y| ≤ u |C| + η + Σᵢ (2^(−sₓ)|yᵢ| + 2^(−sₓ−s_y)|aᵢ|)` with `C = 2^(−sₓ−s_y) (a · c)`. -/
theorem ozaki2_error {mult : MatrixMultiplier} {b bound : ℕ} (hmult : mult.ExactOn b bound)
    {round : ℚ → Option ℚ} {u η : ℚ} (hround : RoundWithin round u η)
    {B : CRTBasis} (hB : B.Valid) (hmb : ∀ m ∈ B.moduli, m ≤ 2 ^ (b + 1))
    (P : ℕ) {x y : List ℚ} (hlen : x.length = y.length)
    (hbound : x.length * (2 ^ b * 2 ^ b) ≤ bound)
    (hrange : 2 * x.length * (2 ^ P * 2 ^ P) < B.modulus) {v : ℚ}
    (hv : ozaki2 mult round B P x y = some v) :
    Rat.abs (v - dot x y) ≤
      u * Rat.abs ((dotZ (scaleTrunc (scaleShift P x) x) (scaleTrunc (scaleShift P y) y) : ℚ) *
        2 ^ (-(scaleShift P x + scaleShift P y))) + η +
      (List.zipWith (fun a b => 2 ^ (-scaleShift P x) * Rat.abs b +
          2 ^ (-(scaleShift P x + scaleShift P y)) *
            Rat.abs (truncInt (a * 2 ^ scaleShift P x) : ℚ)) x y).sum := by
  rw [ozaki2_eq hmult round hB hmb P hlen hbound hrange] at hv
  have h1 := hround _ v hv
  have h2 := truncProduct_error (scaleShift P x) (scaleShift P y) x y hlen
  have h3 := abs_add_le (v - (dotZ (scaleTrunc (scaleShift P x) x) (scaleTrunc (scaleShift P y) y) : ℚ) *
        2 ^ (-(scaleShift P x + scaleShift P y)))
    (2 ^ (-(scaleShift P x + scaleShift P y)) *
        (dotZ (scaleTrunc (scaleShift P x) x) (scaleTrunc (scaleShift P y) y) : ℚ) - dot x y)
  rw [abs_sub_comm _ (dot x y)] at h3
  have e : v - (dotZ (scaleTrunc (scaleShift P x) x) (scaleTrunc (scaleShift P y) y) : ℚ) *
        2 ^ (-(scaleShift P x + scaleShift P y)) +
      (2 ^ (-(scaleShift P x + scaleShift P y)) *
        (dotZ (scaleTrunc (scaleShift P x) x) (scaleTrunc (scaleShift P y) y) : ℚ) - dot x y) =
      v - dot x y := by grind
  rw [e] at h3
  grind

/-- `C = AB` entrywise with Ozaki-II; `A` by rows, `B` by rows. -/
def ozaki2Gemm (mult : MatrixMultiplier) (round : ℚ → Option ℚ) (B : CRTBasis) (P : ℕ)
    (A Bm : List (List ℚ)) : Option (List (List ℚ)) :=
  A.mapM fun x => (transpose Bm).mapM fun y => ozaki2 mult round B P x y

/-- The largest `P` with `2 k 2^(2P) < M`, searched up to `fuel`. -/
def ozaki2Bits (k M : ℕ) : ℕ → ℕ
  | 0 => 0
  | fuel + 1 => if 2 * k * (2 ^ (fuel + 1) * 2 ^ (fuel + 1)) < M then fuel + 1 else ozaki2Bits k M fuel

end Ozaki
