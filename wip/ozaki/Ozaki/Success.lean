import Ozaki.Ozaki2

/-! # The pipelines return a value

The Z3 models check at runtime that no NaN or infinity ever appears (`[H.1]` of both models). Here
the schemes return `none` exactly when a rounding overflows, so the statement is that they return
`some` value. A rounding or an addition that fails only out of range (`RoundSucceeds`,
`AddSucceeds`) never fails inside the pipelines when the inputs are not too large:

* `sumWith_isSome`: `n` additions of relative error `u` and absolute error `η` succeed whenever
  `(1 + u)^n Σ|tⱼ| + n (1 + u)^n η` is within range, since no partial sum exceeds that;
* `ozaki1_isSome`: with an exact matrix multiplier, Ozaki-I returns a value when
  `(1 + u)^n · n k 2^(E+F) + n (1 + u)^n η` is within range (`n = s(s+1)/2`, `E` and `F` the
  exponents of `x` and `y`);
* `ozaki2_isSome`: with an exact matrix multiplier and `2 k 2^(2P) < M`, Ozaki-II returns a value
  when `k 2^((P − sₓ) + (P − s_y))` is within range;
* `splitExp_le`, `scaleExp_le`: those exponents are at most `e` when every entry is at most `2^e`
  in magnitude. -/

local notation "ℕ" => Nat
local notation "ℤ" => Int
local notation "ℚ" => Rat

namespace Ozaki

/-- A rounding that returns a value for every input of magnitude at most `L`. -/
def RoundSucceeds (round : ℚ → Option ℚ) (L : ℚ) : Prop :=
  ∀ q, Rat.abs q ≤ L → ∃ v, round q = some v

/-- An addition that returns a value whenever the exact sum has magnitude at most `L`. -/
def AddSucceeds (add : ℚ → ℚ → Option ℚ) (L : ℚ) : Prop :=
  ∀ a b, Rat.abs (a + b) ≤ L → ∃ v, add a b = some v

theorem addOfRound_succeeds {round : ℚ → Option ℚ} {L : ℚ} (h : RoundSucceeds round L) :
    AddSucceeds (addOfRound round) L := fun a b hab => h (a + b) hab

/-- One step of the induction: from a computed value `c` within `e` of `a`, the remaining
additions succeed when `(1 + u)^n (e + T) + n (1 + u)^n η` is within range. -/
theorem sumWith_isSome_from {add : ℚ → ℚ → Option ℚ} {u η L : ℚ} (hu : 0 ≤ u) (hη : 0 ≤ η)
    (hadd : AddWithin add u η) (hs : AddSucceeds add L) :
    ∀ (ts : List ℚ) (c a e T : ℚ), Rat.abs (c - a) ≤ e →
      Rat.abs a + (ts.map Rat.abs).sum ≤ T →
      (1 + u) ^ ts.length * (e + T) + ts.length * (1 + u) ^ ts.length * η ≤ L →
      ∃ v, sumWith add c ts = some v := by
  intro ts
  induction ts with
  | nil => intro c _ _ _ _ _ _; exact ⟨c, rfl⟩
  | cons t ts ih =>
    intro c a e T hc hT hL
    simp only [List.map_cons, List.sum_cons] at hT
    have hrest := sum_nonneg (l := ts) (f := Rat.abs) (fun x _ => abs_nonneg x)
    have he0 : 0 ≤ e := Rat.le_trans (abs_nonneg _) hc
    have hT0 : 0 ≤ T := by have := abs_nonneg a; have := abs_nonneg t; grind
    have hct : Rat.abs (c + t) ≤ e + T := by
      have := abs_add_le (a + t) (c - a); have h : a + t + (c - a) = c + t := by grind
      rw [h] at this
      have := abs_add_le a t
      grind
    -- `e + T` is within range
    generalize hP : (1 + u) ^ ts.length = P at *
    have hP1 : (1 + u) ^ (ts.length + 1) = P * (1 + u) := by rw [Rat.pow_succ, hP]
    simp only [List.length_cons] at hL
    rw [hP1, natCast_succ] at hL
    have hPge : 1 ≤ P := by
      rw [← hP]
      clear hL hP hP1 ih
      induction ts.length with
      | zero => simp
      | succ n ihn =>
        rw [Rat.pow_succ]
        have := Rat.mul_le_mul_of_nonneg_left (show (1 : ℚ) ≤ 1 + u by grind)
          (show (0 : ℚ) ≤ (1 + u) ^ n by grind)
        grind
    have hn : (0 : ℚ) ≤ ts.length := Rat.natCast_nonneg
    have k0 : 0 ≤ P * u * (e + T) := Rat.mul_nonneg (Rat.mul_nonneg (by grind) hu) (by grind)
    have k1 : 0 ≤ ((ts.length : ℚ) + 1) * P * (1 + u) * η :=
      Rat.mul_nonneg (Rat.mul_nonneg (Rat.mul_nonneg (by grind) (by grind)) (by grind)) hη
    have k2 : 0 ≤ (P - 1) * (e + T) := Rat.mul_nonneg (by grind) (by grind)
    have hin : Rat.abs (c + t) ≤ L := by grind
    obtain ⟨c', hc'⟩ := hs c t hin
    -- the next starting error, as in `sumWith_error_from`
    have hstep := hadd c t c' hc'
    have he' : Rat.abs (c' - (a + t)) ≤ (1 + u) * e + u * T + η := by
      have h1 : c' - (a + t) = (c' - (c + t)) + (c - a) := by grind
      rw [h1]
      have h2 := abs_add_le (c' - (c + t)) (c - a)
      have h3 := Rat.mul_le_mul_of_nonneg_left hct hu
      grind
    have hT' : Rat.abs (a + t) + (ts.map Rat.abs).sum ≤ T := by
      have := abs_add_le a t; grind
    have hL' : P * ((1 + u) * e + u * T + η + T) + ts.length * P * η ≤ L := by
      have k3 : 0 ≤ ((ts.length : ℚ) + 1) * P * u * η :=
        Rat.mul_nonneg (Rat.mul_nonneg (Rat.mul_nonneg (by grind) (by grind)) hu) hη
      grind
    obtain ⟨v, hv⟩ := ih c' (a + t) _ T he' hT' hL'
    exact ⟨v, by simp only [sumWith, hc', Option.bind_some]; exact hv⟩

/-- **Summation succeeds.** `n` additions of relative error `u` and absolute error `η` that only
fail out of range succeed when `(1 + u)^n Σ|tⱼ| + n (1 + u)^n η ≤ L`. -/
theorem sumWith_isSome {add : ℚ → ℚ → Option ℚ} {u η L : ℚ} (hu : 0 ≤ u) (hη : 0 ≤ η)
    (hadd : AddWithin add u η) (hs : AddSucceeds add L) {ts : List ℚ}
    (hL : (1 + u) ^ ts.length * (ts.map Rat.abs).sum + ts.length * (1 + u) ^ ts.length * η ≤ L) :
    ∃ v, sumWith add 0 ts = some v :=
  sumWith_isSome_from hu hη hadd hs ts 0 0 0 ((ts.map Rat.abs).sum)
    (by rw [show (0 : ℚ) - 0 = 0 by grind, abs_zero]; grind)
    (by rw [abs_zero]; grind)
    (by rw [show (0 : ℚ) + (ts.map Rat.abs).sum = (ts.map Rat.abs).sum by grind]; exact hL)

/-- **Ozaki-I returns a value** (`[H.1]`). With a matrix multiplier exact on `b`-bit slices and
additions that fail only beyond `L`, the result exists when
`(1 + u)^n · n k 2^(E+F) + n (1 + u)^n η ≤ L`, where `n = s(s+1)/2` is the number of slice
products. -/
theorem ozaki1_isSome {mult : MatrixMultiplier} {add : ℚ → ℚ → Option ℚ} {b bound s : ℕ} {u η L : ℚ}
    (hmult : mult.ExactOn b bound) (hu : 0 ≤ u) (hη : 0 ≤ η) (hadd : AddWithin add u η)
    (hs : AddSucceeds add L) {x y : List ℚ} (hlen : x.length = y.length)
    (hbound : x.length * (2 ^ b * 2 ^ b) ≤ bound)
    (hL : (1 + u) ^ (trianglePairs s).length *
        ((trianglePairs s).length * (x.length * 2 ^ (splitExp b x + splitExp b y))) +
      (trianglePairs s).length * (1 + u) ^ (trianglePairs s).length * η ≤ L) :
    ∃ v, ozaki1 mult add b s x y = some v := by
  rw [ozaki1_eq_sumWith hmult add s hlen hbound]
  have hlenT : (exactTerms b s x y).length = (trianglePairs s).length := by simp [exactTerms]
  have hT : ((exactTerms b s x y).map Rat.abs).sum ≤
      (trianglePairs s).length * (x.length * 2 ^ (splitExp b x + splitExp b y)) := by
    unfold exactTerms
    rw [List.map_map]
    exact sum_le_length_mul (fun p hp => abs_exactTerm_le b s x y hp)
  apply sumWith_isSome hu hη hadd hs
  rw [hlenT]
  have hP : (0 : ℚ) ≤ (1 + u) ^ (trianglePairs s).length := Rat.pow_nonneg (by grind)
  have := Rat.mul_le_mul_of_nonneg_left hT hP
  grind

/-- The reconstructed product of Ozaki-II is at most `k 2^((P − sₓ) + (P − s_y))` in magnitude. -/
theorem abs_truncProduct_le (P : ℕ) (x y : List ℚ) :
    Rat.abs ((dotZ (scaleTrunc (scaleShift P x) x) (scaleTrunc (scaleShift P y) y) : ℚ) *
        2 ^ (-(scaleShift P x + scaleShift P y))) ≤
      x.length * 2 ^ ((P - scaleShift P x) + (P - scaleShift P y)) := by
  have hab : (dotZ (scaleTrunc (scaleShift P x) x) (scaleTrunc (scaleShift P y) y)).natAbs ≤
      x.length * (2 ^ P * 2 ^ P) := by
    refine Nat.le_trans (natAbs_dotZ_le _ _) ?_
    have := dotAbs_le _ _ _ _ (scaleTrunc_bound P x) (scaleTrunc_bound P y)
    rwa [scaleTrunc_length] at this
  rw [abs_mul, abs_two_pow, abs_intCast]
  have h1 : (((dotZ (scaleTrunc (scaleShift P x) x) (scaleTrunc (scaleShift P y) y)).natAbs : ℕ) : ℚ)
      ≤ x.length * (2 ^ (P : ℤ) * 2 ^ (P : ℤ)) := by
    rw [two_pow_natCast, ← Rat.natCast_mul, ← Rat.natCast_mul]
    exact Rat.natCast_le_natCast.mpr hab
  have h2 := Rat.mul_le_mul_of_nonneg_right h1
    (Rat.le_of_lt (two_pow_pos (-(scaleShift P x + scaleShift P y))))
  refine Rat.le_trans h2 ?_
  have he : (2 : ℚ) ^ (P : ℤ) * 2 ^ (P : ℤ) * 2 ^ (-(scaleShift P x + scaleShift P y)) =
      2 ^ ((P - scaleShift P x) + (P - scaleShift P y)) := by
    rw [← two_pow_add, ← two_pow_add]; congr 1; omega
  rw [Rat.mul_assoc, he]
  exact Rat.le_refl

/-- **Ozaki-II returns a value** (`[H.1]`). With a matrix multiplier exact on `b`-bit residues,
`2 k 2^(2P) < M`, and a rounding that fails only beyond `L`, the result exists when
`k 2^((P − sₓ) + (P − s_y)) ≤ L`. -/
theorem ozaki2_isSome {mult : MatrixMultiplier} {b bound : ℕ} (hmult : mult.ExactOn b bound)
    {round : ℚ → Option ℚ} {L : ℚ} (hr : RoundSucceeds round L) {B : CRTBasis} (hB : B.Valid)
    (hmb : ∀ m ∈ B.moduli, m ≤ 2 ^ (b + 1)) (P : ℕ) {x y : List ℚ} (hlen : x.length = y.length)
    (hbound : x.length * (2 ^ b * 2 ^ b) ≤ bound)
    (hrange : 2 * x.length * (2 ^ P * 2 ^ P) < B.modulus)
    (hL : x.length * (2 : ℚ) ^ ((P - scaleShift P x) + (P - scaleShift P y)) ≤ L) :
    ∃ v, ozaki2 mult round B P x y = some v := by
  rw [ozaki2_eq hmult round hB hmb P hlen hbound hrange]
  exact hr _ (Rat.le_trans (abs_truncProduct_le P x y) hL)

/-! ## Exponents from magnitudes -/

/-- If every entry is at most `2^e` in magnitude and `b − 1 ≤ e`, the slicing exponent `E` is at
most `e` (a zero vector has `E = b − 1`). -/
theorem splitExp_le (b : ℕ) {x : List ℚ} {e : ℤ} (hx : ∀ a ∈ x, Rat.abs a ≤ 2 ^ e)
    (hb : (b : ℤ) - 1 ≤ e) : splitExp b x ≤ e := by
  by_cases h0 : maxAbs x = 0
  · unfold splitExp sliceGrid; rw [if_pos h0]; omega
  · rw [(splitExp_spec b h0).1]
    have hpos : 0 < maxAbs x := by have := maxAbs_nonneg x; grind
    exact (ceilLog2_le_iff hpos e).mpr (maxAbs_le (Rat.le_of_lt (two_pow_pos e)) hx)

/-- If every entry is at most `2^e` in magnitude and `P ≤ e`, the exponent `P − sₓ` of Ozaki-II's
scaling is at most `e` (a zero vector has `sₓ = 0`). -/
theorem scaleExp_le (P : ℕ) {x : List ℚ} {e : ℤ} (hx : ∀ a ∈ x, Rat.abs a ≤ 2 ^ e)
    (hP : (P : ℤ) ≤ e) : (P : ℤ) - scaleShift P x ≤ e := by
  unfold scaleShift
  split
  · omega
  · rename_i h0
    have hpos : 0 < maxAbs x := by have := maxAbs_nonneg x; grind
    have := (ceilLog2_le_iff hpos e).mpr (maxAbs_le (Rat.le_of_lt (two_pow_pos e)) hx)
    omega

end Ozaki
