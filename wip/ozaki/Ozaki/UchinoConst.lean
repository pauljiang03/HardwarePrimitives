import Ozaki.UchinoCRT
import Ozaki.SharpBounds

/-! # The closed-form bound of Uchino, Ozaki and Imamura's reconstruction

Uchino, Ozaki and Imamura (arXiv:2602.02549) bound the error of their binary64 reconstruction
(Algorithm 3) by the closed form of their Lemma 5,

  `R64 = (1 + 3u) 2^(1+⌈log₂ ρ⌉) (N + 2) u² ρ P + 3u |A'B'|`,

with `u = 2^-53`, `N` moduli, `ρ = Σ ⌊p_ℓ/2⌋` and `P` their product. `uchinoRecon_error` gives a
bound in the computed quantities; this file derives the closed form.

**The proof of their Lemma 5 has a gap.** Its final step writes the three nested roundings of
`fl(fma(−Q, P2, fma(−Q, P1, C1) + C2))` as factors `Δ₁, Δ₂, Δ₃ ∈ [1 − u, 1 + u]` (their (72),
which is right) and concludes `|D − C''| ≤ 3u |D|` for `D = C1 + C2 − (P1 + P2) Q` (their (73)).
That does not follow: the factors multiply the partial sums, not `D`, and the partial sums can be
much larger than `D`. `step73_fails` is a kernel-checked instance in binary64 where
`|D − C''| > 3u |D|`; it is not their configuration (there `P2 ≪ P1`), it shows that the
inference is invalid, not that `R64` is.

**R64 still holds**, because in their configuration the first fused multiply-add is exact:
`C1` and `P1 Q` lie on a common grid and their difference is below `2^53` grid steps
(`fma_exact_of_grid`). With that, the two remaining roundings lose at most
`(2u + u²) |D| + (1 + u) u |P2| |Q|` (`uchinoRecon_error_fma`), and the extra term, about
`u² ρ P`, fits in the slack their constant `N + 2` leaves over the `N + 1` the accumulation
needs (`uchino_R64`). The closed form here is theirs plus an explicit underflow term (their analysis
bars underflow), under the hypotheses `ρ ≥ 2`, `2ρ ≤ K = 2^(1+⌈log₂ ρ⌉)` and `N u ≤ 1/8`.

Two smaller differences from their proof:

* the low parts' dot product `C2` is bounded by Jeannerod and Rump's `(N u + (N − 1) u²)` with
  underflow (`nativeDot_error_jr_underflow`) instead of their Lemma 8's `N u`, which bars underflow;
* the double-double error `|P − P1 − P2|` is taken as `u |P − P1| + η` (one rounding), not their
  `u² P / 2`. -/

local notation "ℕ" => Nat
local notation "ℤ" => Int
local notation "ℚ" => Rat

namespace Ozaki

/-! ## The final reduction, and the gap in (73) -/

/-- Line 12 of Algorithm 3: `fl(fma(−Q, P2, fl(fma(−Q, P1, C1) + C2)))`, as in `uchinoRecon`. -/
def uchinoFinal (rnd : ℚ → Option ℚ) (P1 P2 C1 C2 : ℚ) (Q : ℤ) : Option ℚ := do
  let r1 ← rnd (-(Q : ℚ) * P1 + C1)
  let r2 ← rnd (r1 + C2)
  rnd (-(Q : ℚ) * P2 + r2)

/-- **Their step (73) fails.** With binary64 values `C1 = 1`, `C2 = 0`, `P1 = 2^-60`, `P2 = 1` and
`Q = 1`, the first rounding loses `2^-60` and the result is `0`, while
`D = C1 + C2 − (P1 + P2) Q = −2^-60`: the error is `2^-60`, not at most `3u |D| = 3 · 2^-113`. -/
theorem step73_fails :
    rne64 (2 ^ (-60 : ℤ)) = some (2 ^ (-60 : ℤ)) ∧ rne64 1 = some 1 ∧ rne64 0 = some 0 ∧
      uchinoFinal rne64 (2 ^ (-60 : ℤ)) 1 1 0 1 = some 0 ∧
      3 * 2 ^ (-53 : ℤ) * Rat.abs (1 + 0 - (2 ^ (-60 : ℤ) + 1) * ((1 : ℤ) : ℚ)) <
        Rat.abs (0 - (1 + 0 - (2 ^ (-60 : ℤ) + 1) * ((1 : ℤ) : ℚ))) := by
  decide +kernel

/-- **The first fused multiply-add is exact** when `C1` and `P1` lie on a common grid `2^g` and
`|C1 − Q P1| < 2^(p+g)`, as in their configuration. -/
theorem fma_exact_of_grid {p : ℕ} {emin emax g : ℤ} (hp : 0 < p) {C1 P1 : ℚ}
    (hC1 : GridMultiple g C1) (hP1 : GridMultiple g P1) (Q : ℤ)
    (hv : Rat.abs (-(Q : ℚ) * P1 + C1) < 2 ^ ((p : ℤ) + g)) (h1 : emin ≤ g + ((p : ℤ) - 1))
    (h2 : g + ((p : ℤ) - 1) ≤ emax) :
    roundRNE p emin emax (-(Q : ℚ) * P1 + C1) = some (-(Q : ℚ) * P1 + C1) := by
  have hQ : GridMultiple g (-(Q : ℚ) * P1) := by
    obtain ⟨z, hz⟩ := hP1
    exact ⟨-Q * z, by rw [hz, Rat.intCast_mul, Rat.intCast_neg]; grind⟩
  exact roundRNE_of_formatValue hp (formatValue_of_grid (gridMultiple_add hQ hC1) hv h1 h2)

/-! ## The reconstruction with an exact first fused multiply-add -/

/-- The bound on `|c − D|` in the computed quantities: the rounding of the low parts of the
weights, the dot product `C2` (Jeannerod and Rump's bound with underflow), and the double-double
error of `P1 + P2` times `|Q|`. -/
def uchinoT (u η : ℚ) (P : ℕ) (P1 : ℚ) (q G1 : ℤ) (w W : List ℤ) (s2 : List ℚ) : ℚ :=
  (List.zipWith (fun a r : ℤ => (u * Rat.abs ((a : ℚ) - weightHi G1 a) + η) * Rat.abs (r : ℚ)) w W).sum +
    (((List.zipWith (· * ·) s2 (ofInts W)).length * u +
        (((List.zipWith (· * ·) s2 (ofInts W)).length : ℚ) - 1) * u * u) *
        ((List.zipWith (· * ·) s2 (ofInts W)).map Rat.abs).sum +
      (List.zipWith (· * ·) s2 (ofInts W)).length *
        (1 + (((List.zipWith (· * ·) s2 (ofInts W)).length : ℚ) - 1) * u) * η) +
    Rat.abs (q : ℚ) * (u * Rat.abs ((P : ℚ) - P1) + η)

/-- **The reconstruction error when the first fused multiply-add is exact** (in IEEE round to
nearest even, `u = 2^-p`, `η = 2^(emin − p)`): with `T = uchinoT`, the two remaining roundings add
`(2u + u²) |D| + (1 + u) u |P2| |q|` and the underflow terms, so
`|C'' − c| ≤ (1 + u)² T + (2u + u²) |c| + (1 + u) u |q| |P2| + (2 + u) η`. -/
theorem uchinoRecon_error_fma {p : ℕ} {emin emax : ℤ} (hp : 0 < p) (hle : emin ≤ emax)
    {u η : ℚ} (hu : u = 2 ^ (-(p : ℤ))) (hη : η = 2 ^ (emin - p))
    {P : ℕ} (hP : 0 < P) {w W : List ℤ} (hw : ∀ a ∈ w, 0 ≤ a) {G1 : ℤ}
    (hfit : (List.zipWith (fun a r : ℤ => (((a * r).natAbs : ℕ) : ℚ)) w W).sum <
      2 ^ ((p : ℤ) + G1))
    (h1 : emin ≤ G1 + ((p : ℤ) - 1)) (h2 : G1 + ((p : ℤ) - 1) ≤ emax)
    {s2 : List ℚ}
    (hs2 : w.mapM (fun a : ℤ => roundRNE p emin emax ((a : ℚ) - weightHi G1 a)) = some s2)
    {P1 P2 Pinv : ℚ} (hP2 : roundRNE p emin emax ((P : ℚ) - P1) = some P2)
    {q c : ℤ} (hqc : dotZ w W = q * P + c)
    (hmargin : 2 * (Rat.abs (c : ℚ) + uchinoDelta u η P Pinv G1 w W) < P)
    (hr1 : roundRNE p emin emax (-(q : ℚ) * P1 + dot (w.map (weightHi G1)) (ofInts W)) =
      some (-(q : ℚ) * P1 + dot (w.map (weightHi G1)) (ofInts W)))
    {v : ℚ}
    (hv : uchinoRecon (roundRNE p emin emax) P1 P2 Pinv (w.map (weightHi G1)) s2 W = some v) :
    Rat.abs (v - c) ≤ (1 + u) ^ 2 * uchinoT u η P P1 q G1 w W s2 + (2 * u + u * u) * Rat.abs (c : ℚ) +
      (1 + u) * u * Rat.abs (q : ℚ) * Rat.abs P2 + (2 + u) * η := by
  have hround : RoundWithin (roundRNE p emin emax) u η := by rw [hu, hη]; exact roundRNE_within
  have hu0 : 0 ≤ u := by rw [hu]; exact Rat.le_of_lt (two_pow_pos _)
  have hη0 : 0 ≤ η := by rw [hη]; exact Rat.le_of_lt (two_pow_pos _)
  have hJ : JRAdd (FormatValue p emin emax) (roundRNE p emin emax) u := by
    rw [hu]; exact roundRNE_jrAdd hp hle
  have hC1 := nativeDot_exact hp (weightHi_products_level hw hfit h1 h2)
  have hacc := split_acc_error hround w s2 hs2 W
  unfold uchinoDelta at hmargin
  unfold uchinoT
  generalize dot (w.map (weightHi G1)) (ofInts W) = C1 at hC1 hacc hmargin hr1
  generalize hz2 : List.zipWith (· * ·) s2 (ofInts W) = z2
  have hd : ((dotZ w W : ℤ) : ℚ) = (q : ℚ) * P + c := by rw [hqc]; push_cast; rfl
  generalize ((dotZ w W : ℤ) : ℚ) = d at hacc hmargin hd
  unfold uchinoRecon at hv
  simp only [hC1, Option.bind_eq_bind, Option.bind_some] at hv
  cases hC2 : nativeDot (roundRNE p emin emax) s2 (ofInts W) with
  | none => simp [hC2] at hv
  | some C2 =>
  simp only [hC2, Option.bind_some] at hv
  cases hy : roundRNE p emin emax (Pinv * C1) with
  | none => simp [hy] at hv
  | some y =>
  simp only [hy, Option.bind_some] at hv
  -- `Q = q`
  have hPq : (0 : ℚ) < P := by exact_mod_cast hP
  have hyq : roundNearestEven y = q := by
    apply roundNearestEven_eq_of_lt_half
    have ey := hround _ _ hy
    have e : (P : ℚ) * (y - q) =
        P * (y - Pinv * C1) + (P * Pinv - 1) * C1 + (C1 - d) + c := by grind
    have hb : Rat.abs ((P : ℚ) * (y - q)) ≤
        P * (u * Rat.abs (Pinv * C1) + η) + Rat.abs (P * Pinv - 1) * Rat.abs C1 +
          Rat.abs (d - C1) + Rat.abs (c : ℚ) := by
      rw [e]
      have t1 := abs_add_le ((P : ℚ) * (y - Pinv * C1) + (P * Pinv - 1) * C1 + (C1 - d)) (c : ℚ)
      have t2 := abs_add_le ((P : ℚ) * (y - Pinv * C1) + (P * Pinv - 1) * C1) (C1 - d)
      have t3 := abs_add_le ((P : ℚ) * (y - Pinv * C1)) ((P * Pinv - 1) * C1)
      have m1 : Rat.abs ((P : ℚ) * (y - Pinv * C1)) ≤ P * (u * Rat.abs (Pinv * C1) + η) := by
        rw [abs_mul, abs_of_nonneg (Rat.le_of_lt hPq)]
        exact Rat.mul_le_mul_of_nonneg_left ey (Rat.le_of_lt hPq)
      have m2 : Rat.abs ((P * Pinv - 1) * C1) = Rat.abs (P * Pinv - 1) * Rat.abs C1 := abs_mul _ _
      have m3 : Rat.abs (C1 - d) = Rat.abs (d - C1) := abs_sub_comm _ _
      grind
    rw [abs_mul, abs_of_nonneg (Rat.le_of_lt hPq)] at hb
    have h3 : 2 * Rat.abs (y - q) * P < 1 * P := by grind
    exact Rat.lt_of_mul_lt_mul_right h3 (Rat.le_of_lt hPq)
  rw [hyq, hr1] at hv
  simp only [Option.bind_some] at hv
  cases hr2 : roundRNE p emin emax (-(q : ℚ) * P1 + C1 + C2) with
  | none => simp [hr2] at hv
  | some r2 =>
  simp only [hr2, Option.bind_some] at hv
  have eP2 := hround _ _ hP2
  have eC2 := nativeDot_error_jr_underflow hu0 hJ hround hC2
  rw [hz2] at eC2
  -- `|c − D|`
  generalize hD : C1 + C2 - (q : ℚ) * (P1 + P2) = D
  have hcD : Rat.abs ((c : ℚ) - D) ≤
      (List.zipWith (fun a r : ℤ => (u * Rat.abs ((a : ℚ) - weightHi G1 a) + η) *
          Rat.abs (r : ℚ)) w W).sum +
        ((z2.length * u + ((z2.length : ℚ) - 1) * u * u) * (z2.map Rat.abs).sum +
          z2.length * (1 + ((z2.length : ℚ) - 1) * u) * η) +
        Rat.abs (q : ℚ) * (u * Rat.abs ((P : ℚ) - P1) + η) := by
    have e : (c : ℚ) - D = ((d - C1 - dot s2 (ofInts W)) - (C2 - dot s2 (ofInts W))) -
        q * ((P : ℚ) - P1 - P2) := by grind
    rw [e]
    have t1 := abs_sub_le ((d - C1 - dot s2 (ofInts W)) - (C2 - dot s2 (ofInts W)))
      ((q : ℚ) * ((P : ℚ) - P1 - P2))
    have t2 := abs_sub_le (d - C1 - dot s2 (ofInts W)) (C2 - dot s2 (ofInts W))
    have t3 : Rat.abs ((q : ℚ) * ((P : ℚ) - P1 - P2)) ≤
        Rat.abs (q : ℚ) * (u * Rat.abs ((P : ℚ) - P1) + η) := by
      rw [abs_mul]
      refine Rat.mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
      rw [show (P : ℚ) - P1 - P2 = -(P2 - ((P : ℚ) - P1)) by grind, abs_neg]
      exact eP2
    grind
  generalize hT : (List.zipWith (fun a r : ℤ => (u * Rat.abs ((a : ℚ) - weightHi G1 a) + η) *
      Rat.abs (r : ℚ)) w W).sum +
        ((z2.length * u + ((z2.length : ℚ) - 1) * u * u) * (z2.map Rat.abs).sum +
          z2.length * (1 + ((z2.length : ℚ) - 1) * u) * η) +
        Rat.abs (q : ℚ) * (u * Rat.abs ((P : ℚ) - P1) + η) = T at hcD ⊢
  -- the second and third roundings
  have hE2 : Rat.abs (r2 - (-(q : ℚ) * P1 + C1 + C2)) ≤
      u * (Rat.abs D + Rat.abs (q : ℚ) * Rat.abs P2) + η := by
    have e2 := hround _ _ hr2
    have e : -(q : ℚ) * P1 + C1 + C2 = D + q * P2 := by grind
    rw [e] at e2 ⊢
    have := abs_add_le D (q * P2)
    rw [abs_mul] at this
    have := Rat.mul_le_mul_of_nonneg_left this hu0
    grind
  have hE3 : Rat.abs (v - (-(q : ℚ) * P2 + r2)) ≤
      u * (Rat.abs D + Rat.abs (r2 - (-(q : ℚ) * P1 + C1 + C2))) + η := by
    have e3 := hround _ _ hv
    have e : -(q : ℚ) * P2 + r2 = D + (r2 - (-(q : ℚ) * P1 + C1 + C2)) := by grind
    rw [e] at e3 ⊢
    have := abs_add_le D (r2 - (-(q : ℚ) * P1 + C1 + C2))
    have := Rat.mul_le_mul_of_nonneg_left this hu0
    grind
  have hvc : Rat.abs (v - c) ≤ T + Rat.abs (r2 - (-(q : ℚ) * P1 + C1 + C2)) +
      Rat.abs (v - (-(q : ℚ) * P2 + r2)) := by
    have e : v - c = (v - (-(q : ℚ) * P2 + r2)) + (r2 - (-(q : ℚ) * P1 + C1 + C2)) + (D - c) := by
      grind
    rw [e]
    have := abs_add_le ((v - (-(q : ℚ) * P2 + r2)) + (r2 - (-(q : ℚ) * P1 + C1 + C2))) (D - c)
    have := abs_add_le (v - (-(q : ℚ) * P2 + r2)) (r2 - (-(q : ℚ) * P1 + C1 + C2))
    have := abs_sub_comm D (c : ℚ)
    grind
  generalize Rat.abs (r2 - (-(q : ℚ) * P1 + C1 + C2)) = a2 at hE2 hE3 hvc
  have hDle : Rat.abs D ≤ Rat.abs (c : ℚ) + T := by
    have := abs_add_le (c : ℚ) (D - c)
    rw [show (c : ℚ) + (D - c) = D by grind, abs_sub_comm] at this
    grind
  have m1 := Rat.mul_le_mul_of_nonneg_left hE2 (show (0 : ℚ) ≤ 1 + u by grind)
  have m2 := Rat.mul_le_mul_of_nonneg_left hDle (show (0 : ℚ) ≤ 2 * u + u * u by
    have := Rat.mul_nonneg hu0 hu0; grind)
  have hsq : (1 + u) ^ 2 = 1 + 2 * u + u * u := by grind
  rw [hsq]
  grind

/-! ## The closed form -/

theorem sum_zipWith_weight_le {f : ℤ → ℚ} {M : ℚ} (hM : 0 ≤ M) :
    ∀ (w W : List ℤ), (∀ a ∈ w, f a ≤ M) →
      (List.zipWith (fun a r : ℤ => f a * Rat.abs (r : ℚ)) w W).sum ≤ M * absSum (ofInts W)
  | [], W, _ => by simpa using Rat.mul_nonneg hM (absSum_nonneg (ofInts W))
  | _ :: _, [], _ => by simp [absSum]
  | a :: w, r :: W, hw => by
    have ih := sum_zipWith_weight_le hM w W fun b hb => hw b (List.mem_cons_of_mem _ hb)
    have ha := Rat.mul_le_mul_of_nonneg_right (hw a List.mem_cons_self) (abs_nonneg (r : ℚ))
    simp only [List.zipWith_cons_cons, List.sum_cons, ofInts_cons]
    have e : absSum ((r : ℚ) :: ofInts W) = Rat.abs (r : ℚ) + absSum (ofInts W) := by
      simp [absSum]
    rw [e]
    grind

theorem sum_abs_zipWith_le {M : ℚ} (hM : 0 ≤ M) :
    ∀ (s : List ℚ) (W : List ℤ), (∀ a ∈ s, Rat.abs a ≤ M) →
      ((List.zipWith (· * ·) s (ofInts W)).map Rat.abs).sum ≤ M * absSum (ofInts W)
  | [], W, _ => by simpa using Rat.mul_nonneg hM (absSum_nonneg (ofInts W))
  | _ :: _, [], _ => by simp [absSum]
  | a :: s, r :: W, hs => by
    have ih := sum_abs_zipWith_le hM s W fun b hb => hs b (List.mem_cons_of_mem _ hb)
    have ha := Rat.mul_le_mul_of_nonneg_right (hs a List.mem_cons_self) (abs_nonneg (r : ℚ))
    simp only [ofInts_cons, List.zipWith_cons_cons, List.map_cons, List.sum_cons, abs_mul]
    have e : absSum ((r : ℚ) :: ofInts W) = Rat.abs (r : ℚ) + absSum (ofInts W) := by
      simp [absSum]
    rw [e]
    grind

/-- The arithmetic behind `uchino_R64`: with `ρ ≥ 2`, `K ≥ 2ρ`, `N ≥ 1` and `N u ≤ 1/8`, the
accumulation's `N + 1` and the two roundings' extra `2ρ + 1` fit in `(1 + 3u)(N + 2)`. -/
theorem uchino_R64_core {u K ρ N : ℚ} (hu0 : 0 ≤ u) (hN1 : 1 ≤ N) (hNu : N * u ≤ 1 / 8)
    (hρ : 2 ≤ ρ) (hK : 2 * ρ ≤ K) :
    (1 + u) ^ 2 * (K * ρ * (1 + (N + (N - 1) * u) * (1 + u)) + 2 * ρ + 1) ≤
      (1 + 3 * u) * ((N + 2) * (K * ρ)) := by
  have hρ0 : 0 ≤ ρ := by grind
  have hNu0 : (N - 1) * u ≥ 0 := Rat.mul_nonneg (by grind) hu0
  have hu8 : u ≤ 1 / 8 := by grind
  have huu : u * u ≤ u * (1 / 8) := Rat.mul_le_mul_of_nonneg_left hu8 hu0
  have hNuu : (N - 1) * u * u ≤ (1 / 8) * u := by
    have := Rat.mul_le_mul_of_nonneg_right (show (N - 1) * u ≤ 1 / 8 by grind) hu0; grind
  have hkr : 2 * ρ * ρ ≤ K * ρ := Rat.mul_le_mul_of_nonneg_right hK hρ0
  have hρρ : 2 * ρ ≤ ρ * ρ := Rat.mul_le_mul_of_nonneg_right hρ hρ0
  -- `g := 1 − (2N − 1) u − (N − 1) u² ≥ 47/64`
  have hg : (47 : ℚ) / 64 ≤ 1 - (2 * N - 1) * u - (N - 1) * u * u := by grind
  have hkr0 : 0 ≤ K * ρ := by grind
  have hkg := Rat.mul_le_mul_of_nonneg_left hg hkr0
  have hS : K * ρ * (1 + (N + (N - 1) * u) * (1 + u)) + 2 * ρ + 1 ≤ (N + 2) * (K * ρ) := by
    have e : K * ρ * (1 + (N + (N - 1) * u) * (1 + u)) =
        (N + 2) * (K * ρ) - K * ρ * (1 - (2 * N - 1) * u - (N - 1) * u * u) := by grind
    rw [e]; grind
  have hS0 : 0 ≤ K * ρ * (1 + (N + (N - 1) * u) * (1 + u)) + 2 * ρ + 1 := by
    have : 0 ≤ (N + (N - 1) * u) * (1 + u) := Rat.mul_nonneg (by grind) (by grind)
    have := Rat.mul_nonneg hkr0 (show 0 ≤ 1 + (N + (N - 1) * u) * (1 + u) by grind)
    grind
  have hsq : (1 + u) ^ 2 ≤ 1 + 3 * u := by
    have : (1 + u) ^ 2 = 1 + 2 * u + u * u := by grind
    rw [this]; grind
  calc (1 + u) ^ 2 * (K * ρ * (1 + (N + (N - 1) * u) * (1 + u)) + 2 * ρ + 1)
      ≤ (1 + 3 * u) * (K * ρ * (1 + (N + (N - 1) * u) * (1 + u)) + 2 * ρ + 1) :=
        Rat.mul_le_mul_of_nonneg_right hsq hS0
    _ ≤ (1 + 3 * u) * ((N + 2) * (K * ρ)) := Rat.mul_le_mul_of_nonneg_left hS (by grind)

/-- The underflow terms of `uchino_R64`, which their analysis bars. -/
def uchinoEta (u η N ρ : ℚ) : ℚ :=
  (1 + u) ^ 2 * (η * ρ + (N * u + (N - 1) * u * u) * η * ρ + N * (1 + (N - 1) * u) * η +
      (ρ + 1 / 2) * η) + (1 + u) * u * (ρ + 1 / 2) * η + (2 + u) * η

/-- **Their Lemma 5's closed form `R64`, with an underflow term**, for IEEE round to nearest even
(`u = 2^-p`, `η = 2^(emin − p)`), when the first fused multiply-add is exact (`hr1`; it is in their
configuration, `fma_exact_of_grid`). The hypotheses are their setting: weights `0 ≤ w_ℓ ≤ P`,
residues with `Σ|W_ℓ| ≤ ρ`, high parts within `K u P` of the weights (their (35), `K =
2^(1+⌈log₂ ρ⌉) ≥ 2ρ`), `|P − P1| ≤ u P`, `ρ ≥ 2`, and `N u ≤ 1/8` for the `N` moduli:
`|C'' − c| ≤ (1 + 3u) K (N + 2) u² ρ P + 3u |c| + uchinoEta`. -/
theorem uchino_R64 {p : ℕ} {emin emax : ℤ} (hp : 0 < p) (hle : emin ≤ emax)
    {u η : ℚ} (hu : u = 2 ^ (-(p : ℤ))) (hη : η = 2 ^ (emin - p))
    {P : ℕ} (hP : 0 < P) {w W : List ℤ} (hw : ∀ a ∈ w, 0 ≤ a) (hlen : w.length = W.length)
    {G1 : ℤ}
    (hfit : (List.zipWith (fun a r : ℤ => (((a * r).natAbs : ℕ) : ℚ)) w W).sum <
      2 ^ ((p : ℤ) + G1))
    (h1 : emin ≤ G1 + ((p : ℤ) - 1)) (h2 : G1 + ((p : ℤ) - 1) ≤ emax)
    {s2 : List ℚ}
    (hs2 : w.mapM (fun a : ℤ => roundRNE p emin emax ((a : ℚ) - weightHi G1 a)) = some s2)
    {P1 P2 Pinv : ℚ} (hP2 : roundRNE p emin emax ((P : ℚ) - P1) = some P2)
    {q c : ℤ} (hqc : dotZ w W = q * P + c)
    (hmargin : 2 * (Rat.abs (c : ℚ) + uchinoDelta u η P Pinv G1 w W) < P)
    (hr1 : roundRNE p emin emax (-(q : ℚ) * P1 + dot (w.map (weightHi G1)) (ofInts W)) =
      some (-(q : ℚ) * P1 + dot (w.map (weightHi G1)) (ofInts W)))
    {K ρ : ℚ} (hρ : 2 ≤ ρ) (hK : 2 * ρ ≤ K) (hWρ : absSum (ofInts W) ≤ ρ)
    (hwP : ∀ a ∈ w, (a : ℚ) ≤ P) (hs1 : ∀ a ∈ w, (a : ℚ) - weightHi G1 a ≤ K * u * P)
    (hP1 : Rat.abs ((P : ℚ) - P1) ≤ u * P) (hN1 : 1 ≤ w.length)
    (hNu : (w.length : ℚ) * u ≤ 1 / 8)
    {v : ℚ}
    (hv : uchinoRecon (roundRNE p emin emax) P1 P2 Pinv (w.map (weightHi G1)) s2 W = some v) :
    Rat.abs (v - c) ≤ (1 + 3 * u) * (K * (w.length + 2) * (u * u) * ρ * P) +
      3 * u * Rat.abs (c : ℚ) + uchinoEta u η w.length ρ := by
  have hfma := uchinoRecon_error_fma hp hle hu hη hP hw hfit h1 h2 hs2 hP2 hqc hmargin hr1 hv
  have hround : RoundWithin (roundRNE p emin emax) u η := by rw [hu, hη]; exact roundRNE_within
  have hu0 : 0 ≤ u := by rw [hu]; exact Rat.le_of_lt (two_pow_pos _)
  have hη0 : 0 ≤ η := by rw [hη]; exact Rat.le_of_lt (two_pow_pos _)
  have hPq : (0 : ℚ) < P := by exact_mod_cast hP
  have hP0 : (0 : ℚ) ≤ P := Rat.le_of_lt hPq
  have hρ0 : 0 ≤ ρ := by grind
  have hN1' : (1 : ℚ) ≤ w.length := by exact_mod_cast hN1
  generalize hN : (w.length : ℚ) = N at hNu hN1' ⊢
  -- the weights' parts
  have hsP : ∀ a ∈ w, Rat.abs ((a : ℚ) - weightHi G1 a) ≤ K * u * P := fun a ha => by
    rw [abs_of_nonneg (sub_weightHi_nonneg G1 a)]; exact hs1 a ha
  have hKuP : 0 ≤ K * u * P := by
    obtain ⟨a, ha⟩ := List.exists_mem_of_length_pos (show 0 < w.length by omega)
    exact Rat.le_trans (abs_nonneg _) (hsP a ha)
  -- `acc1`
  have hacc1 : (List.zipWith (fun a r : ℤ => (u * Rat.abs ((a : ℚ) - weightHi G1 a) + η) *
      Rat.abs (r : ℚ)) w W).sum ≤ (u * (K * u * P) + η) * ρ := by
    have := sum_zipWith_weight_le (f := fun a : ℤ => u * Rat.abs ((a : ℚ) - weightHi G1 a) + η)
      (M := u * (K * u * P) + η) (by have := Rat.mul_nonneg hu0 hKuP; grind) w W fun a ha => by
        have := Rat.mul_le_mul_of_nonneg_left (hsP a ha) hu0; grind
    have hM0 : 0 ≤ u * (K * u * P) + η := by have := Rat.mul_nonneg hu0 hKuP; grind
    exact Rat.le_trans this (Rat.mul_le_mul_of_nonneg_left hWρ hM0)
  -- the low parts and `z2`
  have hs2len : s2.length = w.length := mapM_length hs2
  have hs2b : ∀ s ∈ s2, Rat.abs s ≤ (1 + u) * (K * u * P) + η := by
    intro s hs
    obtain ⟨a, ha, hfa⟩ := mem_of_mapM hs2 s hs
    have e := hround _ _ hfa
    have h3 := hsP a ha
    have := abs_add_le (s - ((a : ℚ) - weightHi G1 a)) ((a : ℚ) - weightHi G1 a)
    rw [show s - ((a : ℚ) - weightHi G1 a) + ((a : ℚ) - weightHi G1 a) = s by grind] at this
    have := Rat.mul_le_mul_of_nonneg_left h3 hu0
    grind
  have hz2 : ((List.zipWith (· * ·) s2 (ofInts W)).map Rat.abs).sum ≤
      ((1 + u) * (K * u * P) + η) * ρ := by
    have hM0 : 0 ≤ (1 + u) * (K * u * P) + η := by
      have := Rat.mul_nonneg (show (0 : ℚ) ≤ 1 + u by grind) hKuP; grind
    exact Rat.le_trans (sum_abs_zipWith_le hM0 s2 W hs2b)
      (Rat.mul_le_mul_of_nonneg_left hWρ hM0)
  have hz2len : ((List.zipWith (· * ·) s2 (ofInts W)).length : ℚ) = N := by
    rw [List.length_zipWith, ofInts_length, hs2len, ← hlen, Nat.min_self, hN]
  -- `|q| ≤ ρ + 1/2`
  have hδ0 : 0 ≤ uchinoDelta u η P Pinv G1 w W := by
    unfold uchinoDelta
    have := Rat.mul_nonneg hu0 (abs_nonneg (Pinv * dot (w.map (weightHi G1)) (ofInts W)))
    have := Rat.mul_nonneg hP0 (show 0 ≤ u * Rat.abs (Pinv * dot (w.map (weightHi G1))
      (ofInts W)) + η by grind)
    have := Rat.mul_nonneg (abs_nonneg ((P : ℚ) * Pinv - 1))
      (abs_nonneg (dot (w.map (weightHi G1)) (ofInts W)))
    have := abs_nonneg ((dotZ w W : ℚ) - dot (w.map (weightHi G1)) (ofInts W))
    grind
  have hc : 2 * Rat.abs (c : ℚ) < P := by grind
  have hq : Rat.abs (q : ℚ) ≤ ρ + 1 / 2 := by
    have hdot : Rat.abs ((dotZ w W : ℤ) : ℚ) ≤ P * absSum (ofInts W) := by
      rw [← dot_ofInts]
      refine abs_dot_le_mul_absSum hP0 (ofInts w) (ofInts W) fun a ha => ?_
      obtain ⟨z, hz, rfl⟩ := List.mem_map.mp ha
      rw [abs_of_nonneg (by exact_mod_cast hw z hz)]
      exact hwP z hz
    have hd : ((dotZ w W : ℤ) : ℚ) = (q : ℚ) * P + c := by rw [hqc]; push_cast; rfl
    have hqP : Rat.abs (q : ℚ) * P ≤ (ρ + 1 / 2) * P := by
      have e : (q : ℚ) * P = ((dotZ w W : ℤ) : ℚ) - c := by grind
      have := abs_sub_le ((dotZ w W : ℤ) : ℚ) (c : ℚ)
      rw [← e, abs_mul, abs_of_nonneg hP0] at this
      have := Rat.mul_le_mul_of_nonneg_left hWρ hP0
      grind
    exact Rat.le_of_mul_le_mul_right hqP hPq
  -- `|P2|`
  have hP2b : Rat.abs P2 ≤ (1 + u) * (u * P) + η := by
    have e := hround _ _ hP2
    have := abs_add_le (P2 - ((P : ℚ) - P1)) ((P : ℚ) - P1)
    rw [show P2 - ((P : ℚ) - P1) + ((P : ℚ) - P1) = P2 by grind] at this
    have := Rat.mul_le_mul_of_nonneg_left hP1 hu0
    grind
  -- assemble
  unfold uchinoT at hfma
  rw [hz2len] at hfma
  generalize (List.zipWith (fun a r : ℤ => (u * Rat.abs ((a : ℚ) - weightHi G1 a) + η) *
    Rat.abs (r : ℚ)) w W).sum = A1 at hfma hacc1
  generalize ((List.zipWith (· * ·) s2 (ofInts W)).map Rat.abs).sum = Z at hfma hz2
  have hcoef : 0 ≤ N * u + (N - 1) * u * u := by
    have := Rat.mul_nonneg (Rat.mul_nonneg (show (0 : ℚ) ≤ N - 1 by grind) hu0) hu0
    have := Rat.mul_nonneg (show (0 : ℚ) ≤ N by grind) hu0
    grind
  have hJR := Rat.mul_le_mul_of_nonneg_left hz2 hcoef
  have hQ0 := abs_nonneg (q : ℚ)
  have hE : u * Rat.abs ((P : ℚ) - P1) + η ≤ u * (u * P) + η := by
    have := Rat.mul_le_mul_of_nonneg_left hP1 hu0; grind
  have hE0 : 0 ≤ u * (u * P) + η := by
    have := Rat.mul_nonneg hu0 (Rat.mul_nonneg hu0 hP0); grind
  have hQE : Rat.abs (q : ℚ) * (u * Rat.abs ((P : ℚ) - P1) + η) ≤ (ρ + 1 / 2) * (u * (u * P) + η) :=
    Rat.le_trans (Rat.mul_le_mul_of_nonneg_left hE hQ0) (Rat.mul_le_mul_of_nonneg_right hq hE0)
  have hT : A1 + ((N * u + (N - 1) * u * u) * Z + N * (1 + (N - 1) * u) * η) +
      Rat.abs (q : ℚ) * (u * Rat.abs ((P : ℚ) - P1) + η) ≤
      (u * (K * u * P) + η) * ρ + (N * u + (N - 1) * u * u) * (((1 + u) * (K * u * P) + η) * ρ) +
        N * (1 + (N - 1) * u) * η + (ρ + 1 / 2) * (u * (u * P) + η) := by grind
  have hT2 := Rat.mul_le_mul_of_nonneg_left hT (show (0 : ℚ) ≤ (1 + u) ^ 2 by
    have := Rat.mul_nonneg (show (0 : ℚ) ≤ 1 + u by grind) (show (0 : ℚ) ≤ 1 + u by grind)
    have e : (1 + u) ^ 2 = (1 + u) * (1 + u) := by grind
    rw [e]; exact this)
  have hP2e : (1 + u) * u * Rat.abs (q : ℚ) * Rat.abs P2 ≤
      (1 + u) * u * (ρ + 1 / 2) * ((1 + u) * (u * P) + η) := by
    have h0 : 0 ≤ (1 + u) * u := Rat.mul_nonneg (by grind) hu0
    have h1 := Rat.mul_le_mul_of_nonneg_left hP2b (Rat.mul_nonneg h0 hQ0)
    have h2 := Rat.mul_le_mul_of_nonneg_right (Rat.mul_le_mul_of_nonneg_left hq h0)
      (show 0 ≤ (1 + u) * (u * P) + η by
        have := Rat.mul_nonneg (show (0 : ℚ) ≤ 1 + u by grind) (Rat.mul_nonneg hu0 hP0); grind)
    grind
  have hc3 : (2 * u + u * u) * Rat.abs (c : ℚ) ≤ 3 * u * Rat.abs (c : ℚ) := by
    have hu1 : u ≤ 1 := by have := Rat.mul_le_mul_of_nonneg_right hN1' hu0; grind
    have : u * u ≤ u * 1 := Rat.mul_le_mul_of_nonneg_left hu1 hu0
    exact Rat.mul_le_mul_of_nonneg_right (by grind) (abs_nonneg _)
  have hcore := uchino_R64_core hu0 hN1' hNu hρ hK
  have hX : 0 ≤ u * u * P := Rat.mul_nonneg (Rat.mul_nonneg hu0 hu0) hP0
  have hcoreX := Rat.mul_le_mul_of_nonneg_right hcore hX
  unfold uchinoEta
  grind

end Ozaki
