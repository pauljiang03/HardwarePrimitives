import Ozaki.Basic

/-! # Summation with a rounding addition

The Ozaki schemes add their scaled exact products in working precision. `sumWith add` is
left-to-right summation with a supplied addition (binary32 round to nearest in the hardware
instantiations), and `sumWith_error` is the classical bound for it: if every step returns the
exact sum up to a relative error `u` and an absolute error `η` (the subnormal range), then `n`
additions lose at most `((1 + u)^n − 1) · Σ|tⱼ| + n (1 + u)^n η`. -/

local notation "ℕ" => Nat
local notation "ℤ" => Int
local notation "ℚ" => Rat

namespace Ozaki

/-- Left-to-right summation from `acc`, each step with `add`; `none` if a step fails. -/
def sumWith (add : ℚ → ℚ → Option ℚ) : ℚ → List ℚ → Option ℚ
  | acc, [] => some acc
  | acc, t :: ts => (add acc t).bind fun s => sumWith add s ts

/-- Exact addition. -/
def exactAdd (a b : ℚ) : Option ℚ := some (a + b)

/-- Every step of `add` returns `a + b` up to a relative error `u` and an absolute error `η`. -/
def AddWithin (add : ℚ → ℚ → Option ℚ) (u η : ℚ) : Prop :=
  ∀ a b v, add a b = some v → Rat.abs (v - (a + b)) ≤ u * Rat.abs (a + b) + η

/-- A rounding to working precision returns `q` up to a relative error `u` and an absolute error
`η`; `none` signals overflow. -/
def RoundWithin (round : ℚ → Option ℚ) (u η : ℚ) : Prop :=
  ∀ q v, round q = some v → Rat.abs (v - q) ≤ u * Rat.abs q + η

/-- Addition of two working-precision values: the exact sum, rounded. -/
def addOfRound (round : ℚ → Option ℚ) (a b : ℚ) : Option ℚ := round (a + b)

theorem addOfRound_within {round : ℚ → Option ℚ} {u η : ℚ} (h : RoundWithin round u η) :
    AddWithin (addOfRound round) u η := fun a b v hv => h (a + b) v hv

theorem sumWith_exactAdd (acc : ℚ) (ts : List ℚ) : sumWith exactAdd acc ts = some (acc + ts.sum) := by
  induction ts generalizing acc with
  | nil => simp [sumWith] <;> grind
  | cons t ts ih => simp only [sumWith, exactAdd, Option.bind_some, ih, List.sum_cons]; grind

theorem exactAdd_within : AddWithin exactAdd 0 0 := by
  intro a b v h
  simp only [exactAdd, Option.some.injEq] at h
  subst h
  have : a + b - (a + b) = 0 := by grind
  rw [this, abs_zero]; grind

/-- One step of the induction: the error of the starting value grows by `(1 + u)`, and the step
adds `u T + η`. -/
theorem sumWith_error_from {add : ℚ → ℚ → Option ℚ} {u η : ℚ} (hu : 0 ≤ u) (hη : 0 ≤ η)
    (hadd : AddWithin add u η) :
    ∀ (ts : List ℚ) (c a e T v : ℚ), Rat.abs (c - a) ≤ e →
      Rat.abs a + (ts.map Rat.abs).sum ≤ T → sumWith add c ts = some v →
      Rat.abs (v - (a + ts.sum)) ≤
        (1 + u) ^ ts.length * e + ((1 + u) ^ ts.length - 1) * T +
          ts.length * (1 + u) ^ ts.length * η := by
  intro ts
  induction ts with
  | nil =>
    intro c a e T v hc _ hv
    simp only [sumWith, Option.some.injEq] at hv
    subst hv
    simp only [List.sum_nil, List.length_nil, Rat.pow_zero]
    have : c - (a + 0) = c - a := by grind
    rw [this]
    have h0 : ((0 : ℕ) : ℚ) = 0 := rfl
    rw [h0]
    grind
  | cons t ts ih =>
    intro c a e T v hc hT hv
    simp only [sumWith] at hv
    cases hs : add c t with
    | none => rw [hs] at hv; simp at hv
    | some c' =>
      rw [hs] at hv
      simp only [Option.bind_some] at hv
      simp only [List.map_cons, List.sum_cons] at hT
      have hrest := sum_nonneg (l := ts) (f := Rat.abs) (fun x _ => abs_nonneg x)
      have hat : Rat.abs (a + t) ≤ T := by have := abs_add_le a t; grind
      -- the new starting error
      have hstep := hadd c t c' hs
      have hct : Rat.abs (c + t) ≤ Rat.abs (a + t) + e := by
        have := abs_add_le (a + t) (c - a); have h : a + t + (c - a) = c + t := by grind
        rw [h] at this; grind
      have he' : Rat.abs (c' - (a + t)) ≤ (1 + u) * e + u * T + η := by
        have h1 : c' - (a + t) = (c' - (c + t)) + (c - a) := by grind
        rw [h1]
        have h2 := abs_add_le (c' - (c + t)) (c - a)
        have h3 := Rat.mul_le_mul_of_nonneg_left (Rat.le_trans hct (show Rat.abs (a + t) + e ≤ T + e
          by grind)) hu
        grind
      have hT' : Rat.abs (a + t) + (ts.map Rat.abs).sum ≤ T := by
        have := abs_add_le a t; grind
      have h := ih c' (a + t) _ T v he' hT' hv
      simp only [List.sum_cons, List.length_cons]
      have hsum : a + (t + ts.sum) = a + t + ts.sum := by grind
      rw [hsum]
      refine Rat.le_trans h ?_
      -- algebra with `P = (1 + u)^n`
      generalize hP : (1 + u) ^ ts.length = P at *
      have hP1 : (1 + u) ^ (ts.length + 1) = P * (1 + u) := by rw [Rat.pow_succ, hP]
      rw [hP1, natCast_succ]
      have hPnn : 0 ≤ P := by rw [← hP]; exact Rat.pow_nonneg (by grind)
      have hn : (0 : ℚ) ≤ ts.length := Rat.natCast_nonneg
      have k1 : 0 ≤ P * u * η := Rat.mul_nonneg (Rat.mul_nonneg hPnn hu) hη
      have k2 : 0 ≤ (ts.length : ℚ) * P * u * η :=
        Rat.mul_nonneg (Rat.mul_nonneg (Rat.mul_nonneg hn hPnn) hu) hη
      grind

/-- **Rounded summation.** `n` additions with relative error `u` and absolute error `η` lose at
most `((1 + u)^n − 1) Σ|tⱼ| + n (1 + u)^n η`. -/
theorem sumWith_error {add : ℚ → ℚ → Option ℚ} {u η : ℚ} (hu : 0 ≤ u) (hη : 0 ≤ η)
    (hadd : AddWithin add u η) {ts : List ℚ} {v : ℚ} (h : sumWith add 0 ts = some v) :
    Rat.abs (v - ts.sum) ≤
      ((1 + u) ^ ts.length - 1) * (ts.map Rat.abs).sum + ts.length * (1 + u) ^ ts.length * η := by
  have := sumWith_error_from hu hη hadd ts 0 0 0 ((ts.map Rat.abs).sum) v
    (by rw [show (0 : ℚ) - 0 = 0 by grind, abs_zero]; grind) (by rw [abs_zero]; grind) h
  have h0 : (0 : ℚ) + ts.sum = ts.sum := by grind
  rw [h0] at this
  grind

end Ozaki
