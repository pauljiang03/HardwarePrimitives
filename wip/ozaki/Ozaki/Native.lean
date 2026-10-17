import Ozaki.Summation

/-! # The native dot product

The Z3 models compare the Ozaki schemes with native GEMM in the working precision: every product
`xᵢyᵢ` is rounded, and the rounded products are added left to right with a rounded addition
(`acc = acc + A[i][t] * B[t][j]` from `acc = 0`, so the first addition only returns the first
product). `nativeDot round` is that computation for one output entry and any rounding `round`
(binary64 for ADP's fallback, binary32 for the Ozaki-I comparison).

`nativeDot_error` is the classical bound: with `RoundWithin round u η`, a length-`k` native dot
product is within `((1 + u)^k − 1) Σ|xᵢyᵢ| + 2k (1 + u)^k η` of `x · y`. Each product passes
through at most `k` roundings (its own and at most `k − 1` additions), so the relative part is
`γ_k = k u / (1 − k u)` (`pow_sub_one_le_gamma`, `nativeDot_error_gamma`): the bound ADP's runtime
check `[N.1]` and the Ozaki-I comparison `[M.1]` use. -/

local notation "ℕ" => Nat
local notation "ℤ" => Int
local notation "ℚ" => Rat

namespace Ozaki

/-- The native dot product: products rounded with `round`, the first rounded product starts the
accumulator, and the others are added left to right with `addOfRound round`; `0` for no
products. -/
def nativeDot (round : ℚ → Option ℚ) (x y : List ℚ) : Option ℚ :=
  match List.zipWith (· * ·) x y with
  | [] => some 0
  | z :: zs => (round z).bind fun p => (zs.mapM round).bind fun ps =>
      sumWith (addOfRound round) p ps

/-- Rounding a list term by term: the sum moves by at most `u Σ|zᵢ| + n η`, and the magnitudes
grow by at most that much. -/
theorem mapM_round_bounds {round : ℚ → Option ℚ} {u η : ℚ} (hr : RoundWithin round u η) :
    ∀ (zs ps : List ℚ), zs.mapM round = some ps →
      ps.length = zs.length ∧
      Rat.abs (ps.sum - zs.sum) ≤ u * (zs.map Rat.abs).sum + zs.length * η ∧
      (ps.map Rat.abs).sum ≤ (1 + u) * (zs.map Rat.abs).sum + zs.length * η
  | [], ps, h => by
    simp only [List.mapM_nil, pure, Option.some.injEq] at h
    subst h
    have h0 : ((0 : ℕ) : ℚ) = 0 := rfl
    refine ⟨rfl, ?_, ?_⟩
    · simp only [List.sum_nil, List.map_nil, List.length_nil]
      rw [show (0 : ℚ) - 0 = 0 by grind, abs_zero, h0]
      grind
    · simp only [List.sum_nil, List.map_nil, List.length_nil, h0]
      grind
  | z :: zs, ps, h => by
    rw [List.mapM_cons] at h
    cases hz : round z with
    | none => simp [hz] at h
    | some p =>
      cases hzs : zs.mapM round with
      | none => simp [hz, hzs] at h
      | some qs =>
        simp only [hz, hzs, Option.bind_eq_bind, Option.bind_some, pure,
          Option.some.injEq] at h
        subst h
        obtain ⟨hl, hs, ha⟩ := mapM_round_bounds hr zs qs hzs
        have hp := hr z p hz
        have h1 : Rat.abs (p + qs.sum - (z + zs.sum)) ≤ Rat.abs (p - z) + Rat.abs (qs.sum - zs.sum) := by
          have := abs_add_le (p - z) (qs.sum - zs.sum)
          rwa [show p - z + (qs.sum - zs.sum) = p + qs.sum - (z + zs.sum) by grind] at this
        have h2 : Rat.abs p ≤ Rat.abs z + Rat.abs (p - z) := by
          have := abs_add_le z (p - z); rwa [show z + (p - z) = p by grind] at this
        simp only [List.length_cons, List.sum_cons, List.map_cons, natCast_succ]
        refine ⟨by rw [hl], ?_, ?_⟩ <;> grind

/-- `(1 + u)^n ≥ 1` for `u ≥ 0`. -/
theorem one_le_pow_one_add {u : ℚ} (hu : 0 ≤ u) : ∀ n : ℕ, 1 ≤ (1 + u) ^ n
  | 0 => by rw [Rat.pow_zero]; exact Rat.le_refl
  | n + 1 => by
    rw [Rat.pow_succ]
    have ih := one_le_pow_one_add hu n
    have := Rat.mul_le_mul_of_nonneg_left (show (1 : ℚ) ≤ 1 + u by grind) (by grind : (0 : ℚ) ≤ (1 + u) ^ n)
    grind

/-- **The native dot product** (`[N.1]`, `[M.1]`). With `RoundWithin round u η`, a native dot
product of `k` products is within `((1 + u)^k − 1) Σ|xᵢyᵢ| + 2k (1 + u)^k η` of `x · y`. -/
theorem nativeDot_error {round : ℚ → Option ℚ} {u η : ℚ} (hu : 0 ≤ u) (hη : 0 ≤ η)
    (hr : RoundWithin round u η) {x y : List ℚ} {v : ℚ} (h : nativeDot round x y = some v) :
    Rat.abs (v - dot x y) ≤
      ((1 + u) ^ (List.zipWith (· * ·) x y).length - 1) *
          ((List.zipWith (· * ·) x y).map Rat.abs).sum +
        2 * (List.zipWith (· * ·) x y).length * (1 + u) ^ (List.zipWith (· * ·) x y).length * η := by
  unfold nativeDot at h
  unfold dot
  generalize List.zipWith (· * ·) x y = zl at h ⊢
  cases zl with
  | nil =>
    simp only [Option.some.injEq] at h
    subst h
    simp only [List.sum_nil, List.map_nil, List.length_nil, Rat.pow_zero]
    rw [show (0 : ℚ) - 0 = 0 by grind, abs_zero]
    have : ((0 : ℕ) : ℚ) = 0 := rfl
    grind
  | cons z zs =>
    cases hz : round z with
    | none => simp [hz] at h
    | some p =>
      cases hzs : zs.mapM round with
      | none => simp [hz, hzs] at h
      | some ps =>
        simp only [hz, hzs, Option.bind_some] at h
        obtain ⟨hl, hs, ha⟩ := mapM_round_bounds hr zs ps hzs
        have hp := hr z p hz
        have hsum := sumWith_error_from hu hη (addOfRound_within hr) ps p z
          (u * Rat.abs z + η) (Rat.abs z + (ps.map Rat.abs).sum) v hp (Rat.le_refl) h
        rw [hl] at hsum
        simp only [List.sum_cons, List.map_cons, List.length_cons]
        generalize hP : (1 + u) ^ zs.length = P at hsum
        have hP1 : (1 + u) ^ (zs.length + 1) = P * (1 + u) := by rw [Rat.pow_succ, hP]
        have hPge : 1 ≤ P := by rw [← hP]; exact one_le_pow_one_add hu _
        rw [hP1, natCast_succ]
        have htri : Rat.abs (v - (z + zs.sum)) ≤
            Rat.abs (v - (z + ps.sum)) + Rat.abs (ps.sum - zs.sum) := by
          have := abs_add_le (v - (z + ps.sum)) (ps.sum - zs.sum)
          rwa [show v - (z + ps.sum) + (ps.sum - zs.sum) = v - (z + zs.sum) by grind] at this
        have hn : (0 : ℚ) ≤ zs.length := Rat.natCast_nonneg
        have hZ := sum_nonneg (l := zs) (f := Rat.abs) (fun a _ => abs_nonneg a)
        have hA := abs_nonneg z
        -- `(P − 1) Σ|ps| ≤ (P − 1) ((1 + u) Σ|zs| + n η)`
        have k1 := Rat.mul_le_mul_of_nonneg_left ha (show (0 : ℚ) ≤ P - 1 by grind)
        have k2 : 0 ≤ P * u * Rat.abs z := Rat.mul_nonneg (Rat.mul_nonneg (by grind) hu) hA
        have k3 : 0 ≤ P * u * η := Rat.mul_nonneg (Rat.mul_nonneg (by grind) hu) hη
        have k4 : 0 ≤ (zs.length : ℚ) * P * u * η :=
          Rat.mul_nonneg (Rat.mul_nonneg (Rat.mul_nonneg hn (by grind)) hu) hη
        have k5 : 0 ≤ (zs.length : ℚ) * P * η := Rat.mul_nonneg (Rat.mul_nonneg hn (by grind)) hη
        have k6 : 0 ≤ P * u * (zs.map Rat.abs).sum := Rat.mul_nonneg (Rat.mul_nonneg (by grind) hu) hZ
        have k7 : 0 ≤ (zs.length : ℚ) * η := Rat.mul_nonneg hn hη
        have k8 : 0 ≤ P * η := Rat.mul_nonneg (by grind) hη
        have hD1 := abs_nonneg (v - (z + ps.sum))
        have hD2 := abs_nonneg (ps.sum - zs.sum)
        grind

/-- `(1 + u)^k (1 − k u) ≤ 1` for `u ≥ 0`. -/
theorem pow_mul_one_sub_le {u : ℚ} (hu : 0 ≤ u) : ∀ k : ℕ, (1 + u) ^ k * (1 - k * u) ≤ 1
  | 0 => by
    rw [Rat.pow_zero]; have : ((0 : ℕ) : ℚ) = 0 := rfl
    rw [this]; grind
  | k + 1 => by
    have ih := pow_mul_one_sub_le hu k
    rw [Rat.pow_succ, natCast_succ]
    have hP : 0 ≤ (1 + u) ^ k := Rat.pow_nonneg (by grind)
    -- `(1 + u)(1 − (k+1)u) = (1 − k u) − (k + 1) u² ≤ 1 − k u`
    have hk : (0 : ℚ) ≤ k := Rat.natCast_nonneg
    have hq : 0 ≤ ((k : ℚ) + 1) * u * u := Rat.mul_nonneg (Rat.mul_nonneg (by grind) hu) hu
    have e : (1 + u) ^ k * (1 + u) * (1 - ((k : ℚ) + 1) * u) =
        (1 + u) ^ k * (1 - k * u) - (1 + u) ^ k * (((k : ℚ) + 1) * u * u) := by grind
    rw [e]
    have := Rat.mul_nonneg hP hq
    grind

/-- `(1 + u)^k − 1 ≤ γ_k = k u / (1 − k u)` when `k u < 1`. -/
theorem pow_sub_one_le_gamma {u : ℚ} (hu : 0 ≤ u) {k : ℕ} (hk : k * u < 1) :
    (1 + u) ^ k - 1 ≤ k * u / (1 - k * u) := by
  have hpos : 0 < 1 - (k : ℚ) * u := by grind
  have h := pow_mul_one_sub_le hu k
  -- `((1 + u)^k − 1)(1 − k u) ≤ k u`
  have h2 : ((1 + u) ^ k - 1) * (1 - k * u) ≤ k * u := by grind
  have e : k * u / (1 - k * u) * (1 - k * u) = (k : ℚ) * u :=
    Rat.div_mul_cancel (Rat.ne_of_gt hpos)
  apply Classical.byContradiction
  intro hn
  have hlt : (k : ℚ) * u / (1 - k * u) < (1 + u) ^ k - 1 := Rat.not_le.mp hn
  have := Rat.mul_lt_mul_of_pos_right hlt hpos
  grind

/-- **The native dot product with `γ_k`** (`[N.1]`, `[M.1]`): for `k = |x| = |y|` products with
`k u < 1`, `|fl(x · y) − x · y| ≤ γ_k Σ|xᵢyᵢ| + 2k (1 + u)^k η`. -/
theorem nativeDot_error_gamma {round : ℚ → Option ℚ} {u η : ℚ} (hu : 0 ≤ u) (hη : 0 ≤ η)
    (hr : RoundWithin round u η) {x y : List ℚ} (hlen : x.length = y.length)
    (hk : x.length * u < 1) {v : ℚ} (h : nativeDot round x y = some v) :
    Rat.abs (v - dot x y) ≤
      x.length * u / (1 - x.length * u) * ((List.zipWith (· * ·) x y).map Rat.abs).sum +
        2 * x.length * (1 + u) ^ x.length * η := by
  have h1 := nativeDot_error hu hη hr h
  have hl : (List.zipWith (· * ·) x y).length = x.length := by simp [List.length_zipWith, hlen]
  rw [hl] at h1
  have hg := pow_sub_one_le_gamma hu hk
  have hS := sum_nonneg (l := List.zipWith (· * ·) x y) (f := Rat.abs) (fun a _ => abs_nonneg a)
  have := Rat.mul_le_mul_of_nonneg_right hg hS
  grind

end Ozaki
