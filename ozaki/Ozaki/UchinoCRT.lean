import Ozaki.AbdelfattahAcc

/-! # Ozaki-II with Uchino, Ozaki and Imamura's floating-point reconstruction

Uchino, Ozaki and Imamura, *Ozaki-II scheme: error analysis* (arXiv:2602.02549, §3.1, §3.3,
Algorithm 3, Lemmas 3–5), reconstruct the product from its residues in binary64 rather than
exactly. With moduli `p_ℓ`, `P = Π p_ℓ`, weights `w_ℓ = (P / p_ℓ) q_ℓ` and symmetric residues
`W_ℓ` (`|W_ℓ| ≤ ⌊p_ℓ/2⌋`), Algorithm 3 computes, in floating point:

* `C1 := fl(Σ s_ℓ1 W_ℓ)` with `s_ℓ1` the leading bits of `w_ℓ` down to a grid chosen so that every
  partial sum is exact (their (23) and Lemma 3);
* `C2 := fl(Σ s_ℓ2 W_ℓ)` with `s_ℓ2 := double(w_ℓ − s_ℓ1)`;
* `Q := round(fl(P_inv C1))` with `P_inv := double(1/P)`, the multiple of `P` (Lemma 4);
* `C'' := fl(fma(−Q, P2, fl(fma(−Q, P1, C1) + C2)))` with `P1 := double(P)`,
  `P2 := double(P − P1)` (Lemma 5).

Here, for the IEEE round to nearest even of any format (binary64 in particular):

* `weightHi` is the high part of a weight on the grid `2^G1` (truncation of `w_ℓ / 2^G1`), as
  their `s_ℓ1` (their grid is `2^⌈log₂ ρ⌉ u 2 ufp(r)`; any grid that makes the sum fit works);
* **`C1` is exact** (`nativeDot_exact`): products and partial sums are multiples of `2^G1` below
  `2^(p+G1)`, the condition of their Lemma 6;
* **`Q` is the right multiple** (`uchinoRecon_error`, via `roundNearestEven_eq_of_lt_half`)
  whenever `2(|c|/P + δ) < 1`, with `δ` the distance of `fl(P_inv C1)` from `Σ w_ℓ W_ℓ / P`,
  computed from the inputs (`uchinoDelta`), their Lemma 4 for given numbers;
* **the reconstruction error** (`uchinoRecon_error`): `|C'' − c| ≤ uchinoBound`, from the
  accumulation error of `C1 + C2` (their Lemma 3: the rounding of `s_ℓ2` and of the dot product
  `C2`), the double-double error `|P − P1 − P2|`, and the three roundings of the final step.

A difference from their proof of Lemma 5: their (42) writes the three nested roundings as
`(1 + δ₁)(1 + δ₂)(1 + δ₃)(C1 − P1 Q + C2 − P2 Q)`. For nested roundings the errors are relative to
the intermediate values, not to the final sum, so the bound here keeps them as such: each rounding
adds `u` times a bound on its argument (`|D| + |Q||P2| + |C2|` and the earlier errors) plus `η`.

* **End to end** (`ozaki2Uchino_error`). Ozaki-II scaled by any shifts `sₓ`, `s_y` (their scaling
  uses an approximate `log₂`, assumption (1); any shifts are allowed here, and the reconstruction
  range is a hypothesis, their Lemma 1's conclusion), residues on the engine, the floating-point
  reconstruction and one rounding of the scaled result: the error is the truncation bound plus
  `2^(−sₓ−s_y)` times the reconstruction error, through one rounding. The reconstruction error is
  supplied as a hypothesis for the residues the engine can produce, which `uchinoRecon_error`
  discharges for given numbers (`tests/OzakiTCTests/UchinoCRT.lean` checks an instance).

Not modelled: their single-precision computation of the shifts with `log2f` (assumption (1) and
Lemma 1), their exact choice of `β_ℓ` bits, and the binary32 variant (`P2 = 0`, `s_ℓ2 = 0`). -/

local notation "ℕ" => Nat
local notation "ℤ" => Int
local notation "ℚ" => Rat

namespace Ozaki

/-! ## Exact floating-point sums and dot products -/

theorem LevelExact.formatValue_of_mem {p : ℕ} {emin emax G : ℤ} {ts : List ℚ}
    (h : LevelExact p emin emax G ts) {a : ℚ} (ha : a ∈ ts) : FormatValue p emin emax a :=
  formatValue_of_grid (h.1 a ha)
    (lt_of_le_of_lt' (le_sum_of_mem (fun x _ => abs_nonneg x) ha) h.2.1) h.2.2.1 h.2.2.2

/-- **Left-to-right summation of an exact level is exact.** -/
theorem sumWith_exact {p : ℕ} {emin emax G : ℤ} (hp : 0 < p) :
    ∀ (acc : ℚ) (ts : List ℚ), LevelExact p emin emax G (acc :: ts) →
      sumWith (addOfRound (roundRNE p emin emax)) acc ts = some (acc + ts.sum)
  | acc, [], _ => by simp [sumWith, Rat.add_zero]
  | acc, t :: ts, h => by
    obtain ⟨hg, hs, h1, h2⟩ := h
    have hga : GridMultiple G acc := hg acc (by simp)
    have hgt : GridMultiple G t := hg t (by simp)
    simp only [List.map_cons, List.sum_cons] at hs
    have hts := sum_nonneg (l := ts) (f := Rat.abs) fun a _ => abs_nonneg a
    have hat := abs_add_le acc t
    have hfv : FormatValue p emin emax (acc + t) :=
      formatValue_of_grid (gridMultiple_add hga hgt) (by grind) h1 h2
    have hL : LevelExact p emin emax G ((acc + t) :: ts) := by
      refine ⟨fun x hx => ?_, ?_, h1, h2⟩
      · rcases List.mem_cons.mp hx with rfl | hx
        · exact gridMultiple_add hga hgt
        · exact hg x (by simp [hx])
      · simp only [List.map_cons, List.sum_cons]; grind
    simp only [sumWith, addOfRound]
    rw [roundRNE_of_formatValue hp hfv, Option.bind_some, sumWith_exact hp (acc + t) ts hL,
      List.sum_cons, Rat.add_assoc]

/-- **A floating-point dot product whose products form an exact level is exact.** -/
theorem nativeDot_exact {p : ℕ} {emin emax G : ℤ} (hp : 0 < p) {x y : List ℚ}
    (hL : LevelExact p emin emax G (List.zipWith (· * ·) x y)) :
    nativeDot (roundRNE p emin emax) x y = some (dot x y) := by
  unfold nativeDot dot
  generalize List.zipWith (· * ·) x y = zs at hL ⊢
  cases zs with
  | nil => rfl
  | cons z zs =>
    have hzs : zs.mapM (roundRNE p emin emax) = some zs := by
      have := mapM_eq_some_map (l := zs) (f := roundRNE p emin emax) (g := id) fun a ha =>
        roundRNE_of_formatValue hp (hL.formatValue_of_mem (List.mem_cons_of_mem z ha))
      simpa using this
    simp only
    rw [roundRNE_of_formatValue hp (hL.formatValue_of_mem List.mem_cons_self), Option.bind_some,
      hzs, Option.bind_some, sumWith_exact hp z zs hL, List.sum_cons]

/-! ## Splitting the weights -/

/-- **The high part of a weight**: `⌊w / 2^G⌋ 2^G`, its leading bits down to the grid `2^G`. -/
def weightHi (G : ℤ) (w : ℤ) : ℚ := ((((w : ℚ) / 2 ^ G).floor : ℤ) : ℚ) * 2 ^ G

theorem weightHi_grid (G w : ℤ) : GridMultiple G (weightHi G w) := ⟨_, rfl⟩

theorem weightHi_le (G w : ℤ) : weightHi G w ≤ w := by
  unfold weightHi
  have h := Rat.mul_le_mul_of_nonneg_right (Rat.floor_le ((w : ℚ) / 2 ^ G))
    (Rat.le_of_lt (two_pow_pos G))
  rwa [Rat.div_mul_cancel (two_pow_ne_zero G)] at h

theorem weightHi_nonneg {G w : ℤ} (hw : 0 ≤ w) : 0 ≤ weightHi G w := by
  unfold weightHi
  have h0 : (0 : ℚ) ≤ (w : ℚ) / 2 ^ G := by
    rw [div_two_pow]; exact Rat.mul_nonneg (by exact_mod_cast hw) (Rat.le_of_lt (two_pow_pos _))
  have hf : (0 : ℤ) ≤ ((w : ℚ) / 2 ^ G).floor := Rat.le_floor_iff.mpr (by simpa using h0)
  exact Rat.mul_nonneg (by exact_mod_cast hf) (Rat.le_of_lt (two_pow_pos G))

theorem sub_weightHi_lt (G w : ℤ) : (w : ℚ) - weightHi G w < 2 ^ G := by
  unfold weightHi
  have h := Rat.lt_floor_add_one ((w : ℚ) / 2 ^ G)
  rw [Rat.intCast_add, Rat.intCast_one] at h
  have h2 := Rat.mul_lt_mul_of_pos_right h (two_pow_pos G)
  rw [Rat.div_mul_cancel (two_pow_ne_zero G), Rat.add_mul, Rat.one_mul] at h2
  grind

theorem sub_weightHi_nonneg (G w : ℤ) : 0 ≤ (w : ℚ) - weightHi G w := by
  have := weightHi_le G w; grind

/-! ## Rounding to the nearest integer -/

/-- A value within less than `1/2` of an integer rounds to it. -/
theorem roundNearestEven_eq_of_lt_half {y : ℚ} {q : ℤ} (h : 2 * Rat.abs (y - q) < 1) :
    roundNearestEven y = q := by
  have hn := roundNearestEven_nearest y q
  have h5 : Rat.abs ((roundNearestEven y : ℚ) - q) < 1 := by
    have := abs_add_le ((roundNearestEven y : ℚ) - y) (y - q)
    rw [show (roundNearestEven y : ℚ) - y + (y - q) = (roundNearestEven y : ℚ) - q by grind,
      abs_sub_comm _ y] at this
    grind
  rw [← Rat.intCast_sub, abs_intCast] at h5
  have : (roundNearestEven y - q).natAbs < 1 := by exact_mod_cast h5
  omega

/-! ## The reconstruction -/

/-- **Algorithm 3 of Uchino, Ozaki and Imamura, lines 9–12**, with the rounding `rnd`: from the
residues `W`, the high parts `s1` and the rounded low parts `s2` of the weights, and the constants
`P1 ≈ P`, `P2 ≈ P − P1` and `P_inv ≈ 1/P`. -/
def uchinoRecon (rnd : ℚ → Option ℚ) (P1 P2 Pinv : ℚ) (s1 s2 : List ℚ) (W : List ℤ) :
    Option ℚ := do
  let C1 ← nativeDot rnd s1 (ofInts W)
  let C2 ← nativeDot rnd s2 (ofInts W)
  let y ← rnd (Pinv * C1)
  let r1 ← rnd (-(roundNearestEven y : ℚ) * P1 + C1)
  let r2 ← rnd (r1 + C2)
  rnd (-(roundNearestEven y : ℚ) * P2 + r2)

/-- The error bound of a floating-point dot product with products `zs` (`nativeDot_error`). -/
def dotErr (u η : ℚ) (zs : List ℚ) : ℚ :=
  ((1 + u) ^ zs.length - 1) * (zs.map Rat.abs).sum + 2 * zs.length * (1 + u) ^ zs.length * η

/-- `P` times the distance of `fl(P_inv C1)` from `Σ w_ℓ W_ℓ / P`, from the inputs: the rounding
of the product, the error of `P_inv`, and the part of the weights left out of `C1`. -/
def uchinoDelta (u η : ℚ) (P : ℕ) (Pinv : ℚ) (G1 : ℤ) (w W : List ℤ) : ℚ :=
  P * (u * Rat.abs (Pinv * dot (w.map (weightHi G1)) (ofInts W)) + η) +
    Rat.abs (P * Pinv - 1) * Rat.abs (dot (w.map (weightHi G1)) (ofInts W)) +
    Rat.abs ((dotZ w W : ℚ) - dot (w.map (weightHi G1)) (ofInts W))

/-- **The bound on the reconstruction error**: the accumulation error of `C1 + C2` (the rounding of
the low parts and of the dot product `C2`, their Lemma 3), the double-double error of
`P1 + P2`, and the three roundings of the final step, each relative to a bound on its argument. -/
def uchinoBound (u η : ℚ) (P : ℕ) (P1 P2 : ℚ) (q c G1 : ℤ) (w W : List ℤ) (s2 : List ℚ) : ℚ :=
  let z2 := List.zipWith (· * ·) s2 (ofInts W)
  let acc := (List.zipWith (fun a r : ℤ =>
      (u * Rat.abs ((a : ℚ) - weightHi G1 a) + η) * Rat.abs (r : ℚ)) w W).sum + dotErr u η z2
  let cD := acc + Rat.abs (q : ℚ) * (u * Rat.abs ((P : ℚ) - P1) + η)
  let A := Rat.abs (c : ℚ) + cD + Rat.abs (q : ℚ) * Rat.abs P2 + (z2.map Rat.abs).sum +
    dotErr u η z2
  let E1 := u * A + η
  let E2 := u * (A + E1) + η
  let E3 := u * (A + E1 + E2) + η
  cD + E1 + E2 + E3

theorem weightHi_products_grid (G : ℤ) :
    ∀ (w W : List ℤ), ∀ t ∈ List.zipWith (· * ·) (w.map (weightHi G)) (ofInts W), GridMultiple G t
  | [], _, t, ht => by simp at ht
  | _ :: _, [], t, ht => by simp [ofInts] at ht
  | a :: w, r :: W, t, ht => by
    simp only [ofInts, List.map_cons, List.zipWith_cons_cons, List.mem_cons] at ht
    rcases ht with rfl | ht
    · obtain ⟨z, hz⟩ := weightHi_grid G a
      exact ⟨z * r, by rw [hz, Rat.intCast_mul]; grind⟩
    · exact weightHi_products_grid G w W t (by simpa [ofInts] using ht)

theorem weightHi_products_abs_le (G : ℤ) :
    ∀ (w W : List ℤ), (∀ a ∈ w, 0 ≤ a) →
      ((List.zipWith (· * ·) (w.map (weightHi G)) (ofInts W)).map Rat.abs).sum ≤
        (List.zipWith (fun a r : ℤ => (((a * r).natAbs : ℕ) : ℚ)) w W).sum
  | [], _, _ => by simp
  | _ :: _, [], _ => by simp [ofInts]
  | a :: w, r :: W, hw => by
    have ha : 0 ≤ a := hw a (by simp)
    have ih := weightHi_products_abs_le G w W fun b hb => hw b (by simp [hb])
    simp only [ofInts, List.map_cons, List.zipWith_cons_cons, List.sum_cons] at ih ⊢
    have e : (((a * r).natAbs : ℕ) : ℚ) = (a : ℚ) * Rat.abs (r : ℚ) := by
      rw [abs_intCast, Int.natAbs_mul, Rat.natCast_mul]
      congr 1
      rw [← abs_intCast, abs_of_nonneg (by exact_mod_cast ha)]
    have hle : Rat.abs (weightHi G a * r) ≤ (a : ℚ) * Rat.abs (r : ℚ) := by
      rw [abs_mul, abs_of_nonneg (weightHi_nonneg ha)]
      exact Rat.mul_le_mul_of_nonneg_right (weightHi_le G a) (abs_nonneg _)
    grind

/-- The high parts' products form an exact level when `Σ w_ℓ |W_ℓ| < 2^(p+G1)`. -/
theorem weightHi_products_level {p : ℕ} {emin emax G : ℤ} {w W : List ℤ} (hw : ∀ a ∈ w, 0 ≤ a)
    (hfit : (List.zipWith (fun a r : ℤ => (((a * r).natAbs : ℕ) : ℚ)) w W).sum < 2 ^ ((p : ℤ) + G))
    (h1 : emin ≤ G + ((p : ℤ) - 1)) (h2 : G + ((p : ℤ) - 1) ≤ emax) :
    LevelExact p emin emax G (List.zipWith (· * ·) (w.map (weightHi G)) (ofInts W)) :=
  ⟨weightHi_products_grid G w W, lt_of_le_of_lt' (weightHi_products_abs_le G w W hw) hfit, h1, h2⟩

/-- **The accumulation error from splitting the weights**: `|Σ w W − Σ s1 W − Σ s2 W|` is at most
`Σ (u |w − s1| + η) |W|` when every `s2 = rnd(w − s1)`. -/
theorem split_acc_error {rnd : ℚ → Option ℚ} {u η : ℚ} (hround : RoundWithin rnd u η) {G : ℤ} :
    ∀ (w : List ℤ) (s2 : List ℚ),
      w.mapM (fun a : ℤ => rnd ((a : ℚ) - weightHi G a)) = some s2 →
      ∀ W : List ℤ,
        Rat.abs ((dotZ w W : ℚ) - dot (w.map (weightHi G)) (ofInts W) - dot s2 (ofInts W)) ≤
          (List.zipWith (fun a r : ℤ =>
            (u * Rat.abs ((a : ℚ) - weightHi G a) + η) * Rat.abs (r : ℚ)) w W).sum
  | [], s2, h, W => by
    simp only [List.mapM_nil, pure, Option.some.injEq] at h
    subst h
    simp only [dotZ_nil_left, List.map_nil, dot_nil_left, List.zipWith_nil_left, List.sum_nil]
    rw [show ((0 : ℤ) : ℚ) - 0 - 0 = 0 by simp; grind, abs_zero]; exact Rat.le_refl
  | a :: w, s2, h, W => by
    rw [List.mapM_cons] at h
    cases hs : rnd ((a : ℚ) - weightHi G a) with
    | none => simp [hs] at h
    | some s =>
      cases hr : w.mapM (fun a : ℤ => rnd ((a : ℚ) - weightHi G a)) with
      | none => simp [hs, hr] at h
      | some ss =>
        simp only [hs, hr, Option.bind_eq_bind, Option.bind_some, pure, Option.some.injEq] at h
        subst h
        cases W with
        | nil =>
          simp only [ofInts, List.map_nil, dotZ_nil_right, dot_nil_right, List.zipWith_nil_right,
            List.sum_nil]
          rw [show ((0 : ℤ) : ℚ) - 0 - 0 = 0 by simp; grind, abs_zero]; exact Rat.le_refl
        | cons r W =>
          have ih := split_acc_error hround w ss hr W
          have hrd := hround _ _ hs
          simp only [ofInts, List.map_cons, dotZ_cons, dot_cons, Rat.intCast_add, Rat.intCast_mul,
            List.zipWith_cons_cons, List.sum_cons] at ih ⊢
          generalize dot (w.map (weightHi G)) (List.map (fun z : ℤ => (z : ℚ)) W) = d1 at ih ⊢
          generalize dot ss (List.map (fun z : ℤ => (z : ℚ)) W) = d2 at ih ⊢
          generalize (dotZ w W : ℚ) = d0 at ih ⊢
          have e : (a : ℚ) * r + d0 - (weightHi G a * r + d1) - (s * r + d2) =
              ((a : ℚ) - weightHi G a - s) * r + (d0 - d1 - d2) := by grind
          rw [e]
          refine Rat.le_trans (abs_add_le _ _) ?_
          have h1 : Rat.abs (((a : ℚ) - weightHi G a - s) * r) ≤
              (u * Rat.abs ((a : ℚ) - weightHi G a) + η) * Rat.abs (r : ℚ) := by
            rw [abs_mul]
            refine Rat.mul_le_mul_of_nonneg_right ?_ (abs_nonneg _)
            rw [show (a : ℚ) - weightHi G a - s = -(s - ((a : ℚ) - weightHi G a)) by grind, abs_neg]
            exact hrd
          grind

/-- **The reconstruction error** (Lemmas 3–5 of Uchino, Ozaki and Imamura, for given numbers). If
`Σ w_ℓ W_ℓ = q P + c` and `2(|c| + δ) < P`, with `P δ` the distance `uchinoDelta`, then
`Q = q` and the reconstructed value is within `uchinoBound` of `c`. -/
theorem uchinoRecon_error {p : ℕ} {emin emax : ℤ} (hp : 0 < p) {u η : ℚ} (hu : 0 ≤ u)
    (hη : 0 ≤ η) (hround : RoundWithin (roundRNE p emin emax) u η)
    {P : ℕ} (hP : 0 < P) {w W : List ℤ} (hw : ∀ a ∈ w, 0 ≤ a) {G1 : ℤ}
    (hfit : (List.zipWith (fun a r : ℤ => (((a * r).natAbs : ℕ) : ℚ)) w W).sum <
      2 ^ ((p : ℤ) + G1))
    (h1 : emin ≤ G1 + ((p : ℤ) - 1)) (h2 : G1 + ((p : ℤ) - 1) ≤ emax)
    {s2 : List ℚ}
    (hs2 : w.mapM (fun a : ℤ => roundRNE p emin emax ((a : ℚ) - weightHi G1 a)) = some s2)
    {P1 P2 Pinv : ℚ} (hP2 : roundRNE p emin emax ((P : ℚ) - P1) = some P2)
    {q c : ℤ} (hqc : dotZ w W = q * P + c)
    (hmargin : 2 * (Rat.abs (c : ℚ) + uchinoDelta u η P Pinv G1 w W) < P)
    {v : ℚ}
    (hv : uchinoRecon (roundRNE p emin emax) P1 P2 Pinv (w.map (weightHi G1)) s2 W = some v) :
    Rat.abs (v - c) ≤ uchinoBound u η P P1 P2 q c G1 w W s2 := by
  have hC1 := nativeDot_exact hp (weightHi_products_level hw hfit h1 h2)
  have hacc := split_acc_error hround w s2 hs2 W
  unfold uchinoDelta at hmargin
  unfold uchinoBound
  dsimp only
  generalize dot (w.map (weightHi G1)) (ofInts W) = C1 at hC1 hacc hmargin
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
  rw [hyq] at hv
  cases hr1 : roundRNE p emin emax (-(q : ℚ) * P1 + C1) with
  | none => simp [hr1] at hv
  | some r1 =>
  simp only [hr1, Option.bind_some] at hv
  cases hr2 : roundRNE p emin emax (r1 + C2) with
  | none => simp [hr2] at hv
  | some r2 =>
  simp only [hr2, Option.bind_some] at hv
  -- the pieces
  have e1 := hround _ _ hr1
  have e2 := hround _ _ hr2
  have e3 := hround _ _ hv
  have eP2 := hround _ _ hP2
  have eC2 := nativeDot_error hu hη hround hC2
  rw [hz2] at eC2
  have hEC2 : Rat.abs (C2 - dot s2 (ofInts W)) ≤ dotErr u η z2 := by unfold dotErr; exact eC2
  have hpos2 : 0 ≤ dotErr u η z2 := Rat.le_trans (abs_nonneg _) hEC2
  have hC2le : Rat.abs C2 ≤ (z2.map Rat.abs).sum + dotErr u η z2 := by
    have := abs_add_le (C2 - dot s2 (ofInts W)) (dot s2 (ofInts W))
    rw [show C2 - dot s2 (ofInts W) + dot s2 (ofInts W) = C2 by grind] at this
    have hs := abs_listSum_le z2
    have hdz : dot s2 (ofInts W) = z2.sum := by rw [← hz2]; rfl
    rw [hdz] at this
    grind
  -- `|c − D|`
  generalize hD : C1 + C2 - (q : ℚ) * (P1 + P2) = D
  have hcD : Rat.abs ((c : ℚ) - D) ≤
      ((List.zipWith (fun a r : ℤ => (u * Rat.abs ((a : ℚ) - weightHi G1 a) + η) *
          Rat.abs (r : ℚ)) w W).sum + dotErr u η z2) +
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
  -- the three roundings
  generalize hcDv : ((List.zipWith (fun a r : ℤ => (u * Rat.abs ((a : ℚ) - weightHi G1 a) + η) *
      Rat.abs (r : ℚ)) w W).sum + dotErr u η z2) +
        Rat.abs (q : ℚ) * (u * Rat.abs ((P : ℚ) - P1) + η) = cD at hcD ⊢
  generalize hA : Rat.abs (c : ℚ) + cD + Rat.abs (q : ℚ) * Rat.abs P2 + (z2.map Rat.abs).sum +
    dotErr u η z2 = A
  have hDle : Rat.abs D ≤ Rat.abs (c : ℚ) + cD := by
    have := abs_add_le (c : ℚ) (D - c)
    rw [show (c : ℚ) + (D - c) = D by grind, abs_sub_comm] at this
    grind
  have hqP2 : Rat.abs ((q : ℚ) * P2) = Rat.abs (q : ℚ) * Rat.abs P2 := abs_mul _ _
  have hpos1 : 0 ≤ (z2.map Rat.abs).sum := sum_nonneg fun a _ => abs_nonneg a
  -- first rounding
  have ha1 : Rat.abs (-(q : ℚ) * P1 + C1) ≤ A := by
    have e : -(q : ℚ) * P1 + C1 = D + q * P2 - C2 := by grind
    rw [e]
    have := abs_sub_le (D + q * P2) C2
    have := abs_add_le D (q * P2)
    grind
  have hE1 : Rat.abs (r1 - (-(q : ℚ) * P1 + C1)) ≤ u * A + η := by
    have := Rat.mul_le_mul_of_nonneg_left ha1 hu; grind
  -- second rounding
  have ha2 : Rat.abs (r1 + C2) ≤ A + (u * A + η) := by
    have e : r1 + C2 = D + q * P2 + (r1 - (-(q : ℚ) * P1 + C1)) := by grind
    rw [e]
    have := abs_add_le (D + q * P2) (r1 - (-(q : ℚ) * P1 + C1))
    have := abs_add_le D (q * P2)
    have := abs_nonneg C2
    grind
  have hE2 : Rat.abs (r2 - (r1 + C2)) ≤ u * (A + (u * A + η)) + η := by
    have := Rat.mul_le_mul_of_nonneg_left ha2 hu; grind
  -- third rounding
  have ha3 : Rat.abs (-(q : ℚ) * P2 + r2) ≤ A + (u * A + η) + (u * (A + (u * A + η)) + η) := by
    have e : -(q : ℚ) * P2 + r2 =
        D + (r1 - (-(q : ℚ) * P1 + C1)) + (r2 - (r1 + C2)) := by grind
    rw [e]
    have := abs_add_le (D + (r1 - (-(q : ℚ) * P1 + C1))) (r2 - (r1 + C2))
    have := abs_add_le D (r1 - (-(q : ℚ) * P1 + C1))
    have := abs_nonneg ((q : ℚ) * P2)
    grind
  have hE3 : Rat.abs (v - (-(q : ℚ) * P2 + r2)) ≤
      u * (A + (u * A + η) + (u * (A + (u * A + η)) + η)) + η := by
    have := Rat.mul_le_mul_of_nonneg_left ha3 hu; grind
  -- together
  have e : v - c = (v - (-(q : ℚ) * P2 + r2)) + (r2 - (r1 + C2)) +
      (r1 - (-(q : ℚ) * P1 + C1)) + (D - c) := by grind
  rw [e]
  have := abs_add_le ((v - (-(q : ℚ) * P2 + r2)) + (r2 - (r1 + C2)) + (r1 - (-(q : ℚ) * P1 + C1)))
    (D - c)
  have := abs_add_le ((v - (-(q : ℚ) * P2 + r2)) + (r2 - (r1 + C2))) (r1 - (-(q : ℚ) * P1 + C1))
  have := abs_add_le (v - (-(q : ℚ) * P2 + r2)) (r2 - (r1 + C2))
  have := abs_sub_comm D (c : ℚ)
  grind

/-! ## Ozaki-II end to end -/

/-- With a valid basis, residues congruent to `c` give a weighted sum congruent to `c` modulo the
product of the moduli. -/
theorem crt_dvd {B : CRTBasis} (hB : B.Valid) {W : List ℤ} (hlen : W.length = B.moduli.length)
    {c : ℤ} (hres : ∀ j : Fin B.moduli.length, (B.moduli[j] : ℤ) ∣ W.getD j 0 - c) :
    (B.modulus : ℤ) ∣ dotZ B.weights W - c := by
  obtain ⟨hwl, _, hcop, hw⟩ := hB
  apply prod_dvd_of_pairwise_coprime B.moduli hcop
  intro m hm
  obtain ⟨j, hj, hjm⟩ := List.getElem_of_mem hm
  have hsel := dvd_dotZ_sub (B.moduli[j] : ℤ) B.weights W j (by rw [hwl, hlen])
    (by rw [hwl]; exact hj)
    (fun l hl => hw ⟨l, by rw [← hwl]; exact hl⟩ ⟨j, hj⟩ |> fun h => by
      simpa [Fin.ext_iff] using h)
  have hr := hres ⟨j, hj⟩
  rw [← hjm]
  have : dotZ B.weights W - c = (dotZ B.weights W - W.getD j 0) + (W.getD j 0 - c) := by omega
  rw [this]
  exact Int.dvd_add hsel hr

/-- **Ozaki-II with Uchino, Ozaki and Imamura's reconstruction**: the inputs scaled by any shifts
`sₓ`, `s_y` and truncated, one engine product per modulus, symmetric residues, the floating-point
reconstruction `uchinoRecon`, and one rounding of the scaled result. -/
def ozaki2Uchino (mult : MatrixMultiplier) (rnd : ℚ → Option ℚ) (B : CRTBasis) (G1 : ℤ) (P1 P2 Pinv : ℚ)
    (s2 : List ℚ) (sx sy : ℤ) (x y : List ℚ) : Option ℚ := do
  let a := scaleTrunc sx x
  let c := scaleTrunc sy y
  let rs ← B.moduli.mapM fun m => residueProduct mult m a c
  let C ← uchinoRecon rnd P1 P2 Pinv (B.weights.map (weightHi G1)) s2
    (List.zipWith (fun r m => symMod r m) rs B.moduli)
  rnd (C * 2 ^ (-(sx + sy)))

theorem zipWith_map_self {α β γ : Type} (f : α → β) (g : β → α → γ) :
    ∀ l : List α, List.zipWith g (l.map f) l = l.map fun a => g (f a) a
  | [] => rfl
  | a :: l => by simp only [List.map_cons, List.zipWith_cons_cons, zipWith_map_self f g l]

/-- **The error of Ozaki-II with a floating-point reconstruction.** If the reconstruction is
within `R` of the product `c` of the scaled integers for every residue vector the engine can
produce (symmetric residues congruent to `c`; `uchinoRecon_error` gives such an `R` for given
numbers), the result is within the truncation bound plus `2^(−sₓ−s_y) R`, through one rounding,
of `x · y`, for any shifts. -/
theorem ozaki2Uchino_error {mult : MatrixMultiplier} {b bound : ℕ} (hmult : mult.ExactOn b bound)
    {rnd : ℚ → Option ℚ} {u η : ℚ} (hu : 0 ≤ u) (hround : RoundWithin rnd u η)
    {B : CRTBasis} (hB : B.Valid) (hmb : ∀ m ∈ B.moduli, m ≤ 2 ^ (b + 1))
    {G1 : ℤ} {P1 P2 Pinv : ℚ} {s2 : List ℚ} (sx sy : ℤ) {x y : List ℚ}
    (hlen : x.length = y.length) (hbound : x.length * (2 ^ b * 2 ^ b) ≤ bound) {R : ℚ}
    (hrecon : ∀ W : List ℤ, W.length = B.moduli.length →
      (∀ pr ∈ W.zip B.moduli, 2 * pr.1.natAbs ≤ pr.2) →
      (B.modulus : ℤ) ∣ dotZ B.weights W - dotZ (scaleTrunc sx x) (scaleTrunc sy y) →
      ∀ C, uchinoRecon rnd P1 P2 Pinv (B.weights.map (weightHi G1)) s2 W = some C →
        Rat.abs (C - (dotZ (scaleTrunc sx x) (scaleTrunc sy y) : ℚ)) ≤ R)
    {v : ℚ} (hv : ozaki2Uchino mult rnd B G1 P1 P2 Pinv s2 sx sy x y = some v) :
    Rat.abs (v - dot x y) ≤
      u * (Rat.abs ((dotZ (scaleTrunc sx x) (scaleTrunc sy y) : ℚ) * 2 ^ (-(sx + sy))) +
          R * 2 ^ (-(sx + sy))) + η +
        R * 2 ^ (-(sx + sy)) + (2 ^ (-sx) * absSum y + 2 ^ (-sy) * absSum x) := by
  have hpos := hB.2.1
  generalize ha : scaleTrunc sx x = a at hrecon hv ⊢
  generalize hc : scaleTrunc sy y = c at hrecon hv ⊢
  have hla : a.length = x.length := by rw [← ha, scaleTrunc_length]
  have hlc : c.length = y.length := by rw [← hc, scaleTrunc_length]
  have hrs : B.moduli.mapM (fun m => residueProduct mult m a c) = some (B.moduli.map fun m =>
      dotZ (a.map fun z => symMod z m) (c.map fun z => symMod z m) % (m : ℤ)) :=
    mapM_eq_some_map fun m hm => residueProduct_eq hmult (hpos m hm) (hmb m hm)
      (by rw [hla, hlc, hlen]) (by rw [hla]; exact hbound)
  unfold ozaki2Uchino at hv
  simp only [ha, hc, hrs, Option.bind_eq_bind, Option.bind_some] at hv
  rw [zipWith_map_self] at hv
  generalize hW : (B.moduli.map fun m => symMod (dotZ (a.map fun z => symMod z m)
    (c.map fun z => symMod z m) % (m : ℤ)) m) = W at hv
  cases hC : uchinoRecon rnd P1 P2 Pinv (B.weights.map (weightHi G1)) s2 W with
  | none => simp [hC] at hv
  | some C =>
  simp only [hC, Option.bind_some] at hv
  -- the residues
  have hWlen : W.length = B.moduli.length := by rw [← hW, List.length_map]
  have hWb : ∀ pr ∈ W.zip B.moduli, 2 * pr.1.natAbs ≤ pr.2 := by
    rw [← hW]
    intro pr hpr
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hpr
    simp only [List.getElem_zip, List.getElem_map]
    exact natAbs_symMod_le _ (hpos _ (List.getElem_mem _))
  have hdvd : (B.modulus : ℤ) ∣ dotZ B.weights W - dotZ a c := by
    apply crt_dvd hB hWlen
    intro j
    rcases j with ⟨j, hj⟩
    rw [← hW]
    simp only [Fin.getElem_fin, List.getD_eq_getElem?_getD, List.getElem?_map,
      List.getElem?_eq_getElem hj, Option.map_some, Option.getD_some]
    generalize B.moduli[j] = m
    have h1 := dvd_dotZ_symMod m a c
    have h2 := emod_sub_dvd (dotZ (a.map fun z => symMod z m) (c.map fun z => symMod z m)) (m : ℤ)
    have h3 := symMod_dvd (dotZ (a.map fun z => symMod z m) (c.map fun z => symMod z m) % (m : ℤ)) m
    have e : symMod (dotZ (a.map fun z => symMod z m) (c.map fun z => symMod z m) % (m : ℤ)) m -
        dotZ a c =
        -((dotZ (a.map fun z => symMod z m) (c.map fun z => symMod z m) % (m : ℤ)) -
          symMod (dotZ (a.map fun z => symMod z m) (c.map fun z => symMod z m) % (m : ℤ)) m) +
        (dotZ (a.map fun z => symMod z m) (c.map fun z => symMod z m) % (m : ℤ) -
          dotZ (a.map fun z => symMod z m) (c.map fun z => symMod z m)) -
        (dotZ a c - dotZ (a.map fun z => symMod z m) (c.map fun z => symMod z m)) := by omega
    rw [e]
    exact Int.dvd_sub (Int.dvd_add (Int.dvd_neg.mpr h3) h2) h1
  have hR := hrecon W hWlen hWb hdvd C hC
  -- the rounding of the scaled result and the truncation
  have hr := hround _ _ hv
  have ht := truncProduct_error_mixed sx sy hlen
  rw [ha, hc] at ht
  have hS0 := two_pow_pos (-(sx + sy))
  generalize (2 : ℚ) ^ (-(sx + sy)) = S at hr ht hS0 ⊢
  have hS : 0 ≤ S := Rat.le_of_lt hS0
  have hCS : Rat.abs (C * S - (dotZ a c : ℚ) * S) ≤ R * S := by
    rw [show C * S - (dotZ a c : ℚ) * S = (C - dotZ a c) * S by grind, abs_mul,
      abs_of_nonneg hS]
    exact Rat.mul_le_mul_of_nonneg_right hR hS
  have hCS2 : Rat.abs (C * S) ≤ Rat.abs ((dotZ a c : ℚ) * S) + R * S := by
    have := abs_add_le (C * S - (dotZ a c : ℚ) * S) ((dotZ a c : ℚ) * S)
    rw [show C * S - (dotZ a c : ℚ) * S + (dotZ a c : ℚ) * S = C * S by grind] at this
    grind
  have hmul := Rat.mul_le_mul_of_nonneg_left hCS2 hu
  have e : v - dot x y = (v - C * S) + (C * S - (dotZ a c : ℚ) * S) +
      ((dotZ a c : ℚ) * S - dot x y) := by grind
  rw [e]
  have := abs_add_le ((v - C * S) + (C * S - (dotZ a c : ℚ) * S)) ((dotZ a c : ℚ) * S - dot x y)
  have := abs_add_le (v - C * S) (C * S - (dotZ a c : ℚ) * S)
  have := abs_sub_comm ((dotZ a c : ℚ) * S) (dot x y)
  rw [show S * (dotZ a c : ℚ) = (dotZ a c : ℚ) * S by grind] at ht
  grind

end Ozaki
