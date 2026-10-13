import OzakiTC.Rounding

/-! # The σ-trick in binary32

Ozaki-I computes each slice with three binary32 operations (Z3 model, steps 1c–1e):

  `hi = fl(fl(a + σ) − σ)`,  `lo = fl(a − hi)`,  `σ = 3 · 2^(g + 22)`.

Adding `σ` places `a` in `σ`'s binade `[2^(g+23), 2^(g+24))`, whose binary32 spacing is `2^g`, so
the first addition rounds `a` to the nearest multiple of `2^g`, ties to even; the subtraction of
`σ` is then exact, and so is `a − hi`.

`sigma_split` proves this for every binary32 value `a` with `|a| ≤ 2^(g + b)`, every grid
`−149 ≤ g ≤ 104`, and every slice width `b ≤ 21`, with IEEE binary32 addition (`add32`; `TensorCore`'s
correctly rounded `fp32Add` returns the same sums, `add32_of_fp32Add`): `hi = rne(a / 2^g) · 2^g`
and `lo = a − hi`, both binary32 values. This is the Z3
model's lemma `[Z.1]` (proved there for `|a| ≤ 1` and `b = 11`), for all exponents. Its
coefficient is `roundNearestEven`, the one `Ozaki.Split` uses, so the binary32 computation of a
slice is the slice of the scheme library (`sigma_slice`). -/

open TensorCore

namespace Ozaki.TC

/-- The σ-trick constant for the grid `2^g`. -/
def sigma (g : ℤ) : ℚ := 3 * pow2 (g + 22)

theorem rneInt_eq_roundNearestEven (t : ℚ) : rneInt t = roundNearestEven t := rfl

theorem roundNearestEven_eq_zero {t : ℚ} (h : 2 * Rat.abs t < 1) : roundNearestEven t = 0 := by
  have he := roundNearestEven_error t
  have h1 := abs_sub_le t (t - roundNearestEven t)
  have h2 : t - (t - roundNearestEven t) = roundNearestEven t := by grind
  rw [h2] at h1
  have h3 : Rat.abs ((roundNearestEven t : ℤ) : ℚ) < 1 := by grind
  rw [abs_intCast] at h3
  have : (roundNearestEven t).natAbs < 1 := by
    have := Rat.natCast_lt_natCast.mp (show (((roundNearestEven t).natAbs : ℕ) : ℚ) < ((1 : ℕ) : ℚ) by
      simpa using h3)
    exact this
  omega

/-- **First addition.** `fl(a + σ) = σ + rne(a / 2^g) · 2^g`. -/
theorem fp32Add_sigma {a : ℚ} {g : ℤ} {b : ℕ} (hb : b ≤ 21) (hg1 : -149 ≤ g) (hg2 : g ≤ 104)
    (ha : absQ a ≤ pow2 (g + b)) :
    fp32Add a (sigma g) = some (sigma g + roundNearestEven (a / pow2 g) * pow2 g) := by
  have hP := pow2_pos g
  have hsig : sigma g = 12582912 * pow2 g := by
    unfold sigma; rw [pow2_add]; have : pow2 22 = 4194304 := by decide +kernel
    rw [this]; grind
  have hab : pow2 (g + b) ≤ 2097152 * pow2 g := by
    have := pow2_le_of_le (show g + b ≤ g + 21 by omega)
    rw [pow2_add g 21, show pow2 21 = 2097152 by decide +kernel] at this; grind
  have ha' := (absQ_le_iff a _).mp ha
  -- `a + σ` lies in `[2^(g+23), 2^(g+24))`
  have hlo : pow2 (g + 23) ≤ a + sigma g := by
    rw [pow2_add, show pow2 23 = 8388608 by decide +kernel, hsig]; grind
  have hhi : a + sigma g < pow2 (g + 23 + 1) := by
    rw [pow2_add, pow2_add, show pow2 23 = 8388608 by decide +kernel, pow2_one, hsig]; grind
  have hpos : 0 < a + sigma g := by have := pow2_pos (g + 23); grind
  have hmax : absQ (a + sigma g) ≤ maxFinite32 := by
    rw [absQ_of_nonneg (Rat.le_of_lt hpos)]
    have h1 : a + sigma g ≤ 14680064 * pow2 g := by rw [hsig]; grind
    have h2 : pow2 g ≤ pow2 104 := pow2_le_of_le hg2
    have h3 : maxFinite32 = 16777215 * pow2 104 := by decide +kernel
    rw [h3]; grind
  obtain ⟨w, hw, hv, _⟩ := round32_nonzero_spec .nearestEven (a + sigma g)
    (Rat.ne_of_gt hpos) hmax
  unfold fp32Add; rw [hw]; simp only [Option.bind_some]; rw [hv]
  congr 1
  -- the rounded value
  have hmag : magnitudeExponent (a + sigma g) = g + 23 :=
    magnitudeExponent_eq_of_bounds _ _ hlo hhi
  have hnorm : normExp (a + sigma g) = g + 23 := by
    unfold normExp emin32; rw [hmag]; omega
  unfold signedRounded
  rw [if_neg (by grind), absQ_of_nonneg (Rat.le_of_lt hpos)]
  unfold magnitudeRounded roundedSignificand
  simp only [roundSignificand]
  rw [hnorm, show g + 23 - 23 = g by omega, rneInt_eq_roundNearestEven]
  have hdiv : (a + sigma g) / pow2 g = a / pow2 g + ((2 * 6291456 : ℤ) : ℚ) := by
    rw [hsig]
    have : (a + 12582912 * pow2 g) / pow2 g = a / pow2 g + 12582912 * pow2 g / pow2 g := by
      rw [Rat.div_def, Rat.div_def, Rat.div_def, Rat.add_mul]
    rw [this, Rat.mul_div_cancel (Rat.ne_of_gt hP)]; rfl
  rw [hdiv, roundNearestEven_add_even, hsig, Rat.intCast_add]
  grind

/-- `a − rne(a / 2^g) · 2^g` is a binary32 value for every binary32 value `a` and every grid
`2^g`. -/
theorem finiteValue32_sub_round {a : ℚ} (ha : FiniteValue32 a) (g : ℤ) :
    FiniteValue32 (a - roundNearestEven (a / pow2 g) * pow2 g) := by
  have ha0 := ha
  obtain ⟨k, e, he1, he2, hk, rfl⟩ := ha
  have hP := pow2_pos g
  by_cases hcoarse : g ≤ e - 23
  · -- `a` is a multiple of `2^g`: the rounding is exact and nothing is left
    have hint : (k : ℚ) * pow2 (e - 23) / pow2 g = ((k * 2 ^ (e - 23 - g).toNat : ℤ) : ℚ) := by
      have hn : pow2 (e - 23 - g) = (((2 : ℤ) ^ (e - 23 - g).toNat : ℤ) : ℚ) := by
        have h := pow2_natCast (e - 23 - g).toNat
        rw [show (((e - 23 - g).toNat : ℕ) : ℤ) = e - 23 - g by omega] at h
        rw [h, Rat.intCast_pow, Rat.natCast_pow]; rfl
      rw [Rat.div_def, Rat.mul_assoc, ← Rat.div_def, pow2_div, hn, Rat.intCast_mul]
    rw [hint, roundNearestEven_intCast, ← hint, Rat.div_mul_cancel (Rat.ne_of_gt hP)]
    have := grid_finiteValue32 0 0 (by omega) (by omega) (by decide)
    rwa [Rat.intCast_zero, Rat.zero_mul, show (k : ℚ) * pow2 (e - 23) - (k : ℚ) * pow2 (e - 23) = 0
      by grind] at *
  · by_cases hsmall : e ≤ g - 2
    · -- `|a| < 2^(g−1)`: the slice is zero and `a` is left
      have habs : 2 * absQ ((k : ℚ) * pow2 (e - 23) / pow2 g) < 1 := by
        rw [Rat.div_def, Rat.mul_assoc, ← Rat.div_def, pow2_div, absQ_mul_pos _ _ (pow2_pos _),
          absQ_intCast]
        have hk' : ((k.natAbs : ℤ) : ℚ) < 16777216 := by
          have := Rat.intCast_lt_intCast.mpr (show (k.natAbs : ℤ) < 16777216 by omega)
          rwa [Rat.intCast_ofNat] at this
        have hp : pow2 (e - 23 - g) ≤ pow2 (-25) := pow2_le_of_le (by omega)
        have h25 : pow2 (-25) * 16777216 = 1 / 2 := by decide +kernel
        have hnn : (0 : ℚ) ≤ ((k.natAbs : ℤ) : ℚ) := Rat.intCast_nonneg.mpr (by omega)
        have h1 := Rat.mul_le_mul_of_nonneg_left hp hnn
        have h2 := Rat.mul_lt_mul_of_pos_right hk' (pow2_pos (-25))
        generalize pow2 (e - 23 - g) = P at *
        generalize pow2 (-25) = Q at *
        generalize ((k.natAbs : ℤ) : ℚ) = N at *
        have h3 : 2 * (16777216 * Q) = 1 := by rw [Rat.mul_comm 16777216 Q, h25]; decide +kernel
        have h4 := lt_of_le_of_lt' h1 h2
        have h5 := Rat.mul_lt_mul_of_pos_left h4 (show (0 : ℚ) < 2 by decide)
        rw [h3] at h5; exact h5
      rw [roundNearestEven_eq_zero (by rw [← absQ_eq]; exact habs), Rat.intCast_zero, Rat.zero_mul,
        show (k : ℚ) * pow2 (e - 23) - 0 = (k : ℚ) * pow2 (e - 23) by grind]
      exact ha0
    · -- the common grid is `a`'s own: the remainder has at most 24 bits on it
      generalize hq : roundNearestEven ((k : ℚ) * pow2 (e - 23) / pow2 g) = q
      have herr := roundNearestEven_error ((k : ℚ) * pow2 (e - 23) / pow2 g)
      rw [hq, ← absQ_eq] at herr
      generalize hd : (g - (e - 23)).toNat = d
      have hdg : g = (e - 23) + d := by omega
      have hgrid : pow2 g = ((2 ^ d : ℕ) : ℚ) * pow2 (e - 23) := by
        rw [hdg, pow2_add, pow2_natCast, Rat.mul_comm]
      have hj : (k : ℚ) * pow2 (e - 23) - q * pow2 g = ((k - q * 2 ^ d : ℤ) : ℚ) * pow2 (e - 23) := by
        rw [hgrid, Rat.intCast_sub, Rat.intCast_mul, Rat.intCast_pow, Rat.intCast_ofNat,
          ← Rat.natCast_ofNat, ← Rat.natCast_pow]
        grind
      refine ⟨k - q * 2 ^ d, e, he1, he2, ?_, hj⟩
      · -- `|a − q 2^g| ≤ 2^(g−1)` gives a coefficient of at most `2^23`
        have hbound : absQ ((k : ℚ) * pow2 (e - 23) - q * pow2 g) ≤ pow2 (g - 1) := by
          have heq : (k : ℚ) * pow2 (e - 23) - q * pow2 g =
              ((k : ℚ) * pow2 (e - 23) / pow2 g - q) * pow2 g := by
            have := Rat.div_mul_cancel (a := (k : ℚ) * pow2 (e - 23)) (Rat.ne_of_gt hP)
            grind
          rw [heq, absQ_mul_pos _ _ hP]
          have h2 : pow2 g = 2 * pow2 (g - 1) := by
            rw [show g = (g - 1) + 1 by omega, pow2_succ]; grind
          have := Rat.mul_le_mul_of_nonneg_right herr (Rat.le_of_lt (pow2_pos (g - 1)))
          generalize absQ ((k : ℚ) * pow2 (e - 23) / pow2 g - q) = A at this ⊢
          rw [h2]; grind
        rw [hj, absQ_mul_pos _ _ (pow2_pos _), absQ_intCast] at hbound
        have hlim : pow2 (g - 1) ≤ 8388608 * pow2 (e - 23) := by
          have := pow2_le_of_le (show g - 1 ≤ (e - 23) + 23 by omega)
          rw [pow2_add, show pow2 23 = 8388608 by decide +kernel] at this; grind
        have hc : (((k - q * 2 ^ d).natAbs : ℤ) : ℚ) ≤ 8388608 := by
          have h := Rat.le_trans hbound hlim
          exact Rat.le_of_mul_le_mul_right h (pow2_pos _)
        have : ((k - q * 2 ^ d).natAbs : ℤ) ≤ 8388608 :=
          Rat.intCast_le_intCast.mp (by rw [Rat.intCast_ofNat]; exact hc)
        omega

/-- The first addition with IEEE binary32 addition. -/
theorem add32_sigma {a : ℚ} {g : ℤ} {b : ℕ} (hb : b ≤ 21) (hg1 : -149 ≤ g) (hg2 : g ≤ 104)
    (ha : absQ a ≤ pow2 (g + b)) :
    add32 a (sigma g) = some (sigma g + roundNearestEven (a / pow2 g) * pow2 g) :=
  add32_of_fp32Add (fp32Add_sigma hb hg1 hg2 ha)

/-- **The σ-trick** (`[Z.1]`, for every exponent and `b ≤ 21`). For a binary32 value `a` with
`|a| ≤ 2^(g+b)`, `hi = fl(fl(a + σ) − σ)` is `rne(a / 2^g) · 2^g` and `lo = fl(a − hi)` is
`a − hi`; every intermediate is a binary32 value. -/
theorem sigma_split {a : ℚ} (ha32 : FiniteValue32 a) {g : ℤ} {b : ℕ} (hb : b ≤ 21)
    (hg1 : -149 ≤ g) (hg2 : g ≤ 104) (ha : absQ a ≤ pow2 (g + b)) :
    ∃ s1 hi lo, add32 a (sigma g) = some s1 ∧ add32 s1 (-sigma g) = some hi ∧
      add32 a (-hi) = some lo ∧ hi = roundNearestEven (a / pow2 g) * pow2 g ∧ lo = a - hi ∧
      FiniteValue32 lo := by
  have hq : (roundNearestEven (a / pow2 g)).natAbs ≤ 2 ^ b := by
    apply natAbs_roundNearestEven_le
    rw [← absQ_eq, Rat.div_def, absQ_mul_pos _ _ (Rat.inv_pos.mpr (pow2_pos g)), ← Rat.div_def,
      ← pow2_natCast, div_le_iff (pow2_pos g), ← pow2_add]
    rwa [show ((b : ℕ) : ℤ) + g = g + b by omega]
  have hhi : FiniteValue32 ((roundNearestEven (a / pow2 g) : ℚ) * pow2 g) :=
    grid_finiteValue32 _ g hg1 hg2 (Nat.lt_of_le_of_lt hq
      (Nat.pow_lt_pow_right (by decide) (by omega)))
  refine ⟨_, _, _, add32_sigma hb hg1 hg2 ha, ?_, ?_, rfl, rfl,
    finiteValue32_sub_round ha32 g⟩
  · rw [add32_exact _ _ (by rw [show sigma g + (roundNearestEven (a / pow2 g) : ℚ) * pow2 g +
      -sigma g = (roundNearestEven (a / pow2 g) : ℚ) * pow2 g by grind]; exact hhi)]
    congr 1; grind
  · rw [add32_exact _ _ (by rw [← Rat.sub_eq_add_neg]; exact finiteValue32_sub_round ha32 g)]
    congr 1; grind

/-- **One slice of a binary32 vector.** With the slice's grid in range, the σ-trick computes the
slice of `Ozaki.Split` entry by entry, and what it leaves is again a binary32 vector. -/
theorem sigma_slice {b : ℕ} (hb : b ≤ 21) (prev : ℤ) {x : List ℚ}
    (hx : ∀ a ∈ x, FiniteValue32 a) (hg1 : -149 ≤ sliceGrid b prev x)
    (hg2 : sliceGrid b prev x ≤ 104) :
    (∀ a ∈ x, ∃ s1 hi lo, add32 a (sigma (sliceGrid b prev x)) = some s1 ∧
      add32 s1 (-sigma (sliceGrid b prev x)) = some hi ∧ add32 a (-hi) = some lo ∧
      hi = roundNearestEven (a / pow2 (sliceGrid b prev x)) * pow2 (sliceGrid b prev x) ∧
      lo = a - hi) ∧
    ∀ r ∈ sliceRest (sliceGrid b prev x) x, FiniteValue32 r := by
  constructor
  · intro a ha
    obtain ⟨s1, hi, lo, h1, h2, h3, h4, h5, _⟩ := sigma_split (hx a ha) hb hg1 hg2
      (by rw [absQ_eq]; exact abs_le_two_pow_sliceGrid b prev x a ha)
    exact ⟨s1, hi, lo, h1, h2, h3, h4, h5⟩
  · intro r hr
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hr
    exact finiteValue32_sub_round (hx a ha) _

/-- **Every residual of a binary32 vector is binary32.** So each slice of the split takes a binary32
vector, and `sigma_slice` computes it whenever its grid lies in `[−149, 104]`. -/
theorem splitFrom_binary32 (b : ℕ) :
    ∀ (s : ℕ) (prev : ℤ) (x : List ℚ), (∀ a ∈ x, FiniteValue32 a) →
      ∀ r ∈ (splitFrom b s prev x).2, FiniteValue32 r
  | 0, _, x, hx => by simpa [splitFrom] using hx
  | s + 1, prev, x, hx => by
    simp only [splitFrom]
    refine splitFrom_binary32 b s _ _ ?_
    intro r hr
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hr
    exact finiteValue32_sub_round (hx a ha) _

/-! ## The split in binary32 operations -/

/-- One entry of a slice computed as the Z3 model does: `hi = fl(fl(a + σ) − σ)`,
`lo = fl(a − hi)`, and the integer `hi / 2^g`. -/
def sigmaStep (g : ℤ) (a : ℚ) : Option (ℤ × ℚ) := do
  let s1 ← add32 a (sigma g)
  let hi ← add32 s1 (-sigma g)
  let lo ← add32 a (-hi)
  let q ← toInt? (hi / pow2 g)
  return (q, lo)

/-- The split computed with binary32 operations: each slice by `sigmaStep` on what the previous
slices left, with the same grids as `splitFrom`. -/
def splitFrom32 (b : ℕ) : ℕ → ℤ → List ℚ → Option (List Slice × List ℚ)
  | 0, _, x => some ([], x)
  | s + 1, prev, x => do
    let g := sliceGrid b prev x
    let steps ← x.mapM (sigmaStep g)
    let rest ← splitFrom32 b s g (steps.map (·.2))
    return (⟨g, steps.map (·.1)⟩ :: rest.1, rest.2)

/-- The split of `b`-bit slices computed with binary32 operations. -/
def split32 (b s : ℕ) (x : List ℚ) : Option (List Slice × List ℚ) := splitFrom32 b s b x

theorem sigmaStep_eq {a : ℚ} (ha32 : FiniteValue32 a) {g : ℤ} {b : ℕ} (hb : b ≤ 21)
    (hg1 : -149 ≤ g) (hg2 : g ≤ 104) (ha : absQ a ≤ pow2 (g + b)) :
    sigmaStep g a = some (roundNearestEven (a / pow2 g),
      a - roundNearestEven (a / pow2 g) * pow2 g) := by
  obtain ⟨s1, hi, lo, h1, h2, h3, rfl, rfl, _⟩ := sigma_split ha32 hb hg1 hg2 ha
  unfold sigmaStep
  rw [h1]; simp only [Option.bind_eq_bind, Option.bind_some]
  rw [h2]; simp only [Option.bind_some]
  rw [h3]; simp only [Option.bind_some]
  rw [Rat.mul_div_cancel (Rat.ne_of_gt (pow2_pos g)), toInt?_intCast]
  rfl

/-- **The binary32 split is the split.** For a binary32 vector whose slice grids all lie in
`[−149, 104]`, the slices computed with binary32 σ-trick operations are the slices of
`Ozaki.Split`, and so is the residual. -/
theorem splitFrom32_eq {b : ℕ} (hb : b ≤ 21) :
    ∀ (s : ℕ) (prev : ℤ) (x : List ℚ), (∀ a ∈ x, FiniteValue32 a) →
      (∀ sl ∈ (splitFrom b s prev x).1, -149 ≤ sl.grid ∧ sl.grid ≤ 104) →
      splitFrom32 b s prev x = some (splitFrom b s prev x)
  | 0, _, _, _, _ => rfl
  | s + 1, prev, x, hx, hg => by
    simp only [splitFrom, List.mem_cons, forall_eq_or_imp] at hg
    have hsteps : x.mapM (sigmaStep (sliceGrid b prev x)) = some (x.map fun a =>
        (roundNearestEven (a / pow2 (sliceGrid b prev x)),
          a - roundNearestEven (a / pow2 (sliceGrid b prev x)) * pow2 (sliceGrid b prev x))) :=
      mapM_eq_some_map fun a ha => sigmaStep_eq (hx a ha) hb hg.1.1 hg.1.2
        (by rw [absQ_eq]; exact abs_le_two_pow_sliceGrid b prev x a ha)
    have hrest : (x.map fun a => (roundNearestEven (a / pow2 (sliceGrid b prev x)),
        a - roundNearestEven (a / pow2 (sliceGrid b prev x)) * pow2 (sliceGrid b prev x))).map
          (·.2) = sliceRest (sliceGrid b prev x) x := by
      simp [sliceRest, List.map_map, Function.comp_def, pow2_eq]
    have hcoef : (x.map fun a => (roundNearestEven (a / pow2 (sliceGrid b prev x)),
        a - roundNearestEven (a / pow2 (sliceGrid b prev x)) * pow2 (sliceGrid b prev x))).map
          (·.1) = sliceCoeffs (sliceGrid b prev x) x := by
      simp [sliceCoeffs, List.map_map, Function.comp_def, pow2_eq]
    have ih := splitFrom32_eq hb s (sliceGrid b prev x) (sliceRest (sliceGrid b prev x) x)
      (fun r hr => by
        obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hr
        exact finiteValue32_sub_round (hx a ha) _) hg.2
    simp only [splitFrom32, hsteps, Option.bind_eq_bind, Option.bind_some, hrest, ih, hcoef]
    rfl

end Ozaki.TC
