import Ozaki.BoundedOzaki
import Ozaki.SignedZero

/-! # Ozaki-II's check in bounded integer arithmetic, and signed zeros for Ozaki-II

`ozaki2CRE` checks a rational enclosure: the reconstructed product `H` and the truncation bound
`B`, a rational computed from the inputs. Here the check is integer arithmetic of bounded width:

* **an integer enclosure** `H = N 2^q`, `B = K 2^c` (`enclVal`), tested by `enclosureTestB`: both ends
  rounded at the grid `min q c` with `roundExact` (`enclosureTestB_eq`); `roundingTestB` tries integer
  enclosures in turn, then a fallback (`roundingTestB_eq`);
* **a bound from the scaled integers** (`scaledBound_le`): when `x` and `y` are scaled by `2^sₓ`,
  `2^s_y` and rounded to integers `a`, `c` (truncated or floored), the bound of `dot_approx_error`
  is at most `K 2^(−sₓ−s_y)` with `K = [x drops bits] (Σ|cⱼ| + k) + [y drops bits] Σ|aᵢ|`
  (`boundK`): each entry loses less than one unit, nothing when no bits are dropped;
* **Ozaki-II's integer enclosure** (`ozaki2EnclosureB`): `N` the CRT reconstruction of the residue
  products, `q = −(sₓ + s_y)`, and `B = K 2^q` with `K` of the truncated integers (`ozaki2K`), so
  the enclosure contains `x · y` (`ozaki2EnclosureB_sound`);
* `ozaki2CRB`: the integer checks in turn, then Ozaki-I's bounded exact path. It is correctly
  rounded (`ozaki2CRB_eq`, binary64 and binary32 instances `ozaki2CRB64_eq`, `ozaki2CRB32_eq`).

**Widths** (`ozaki2EnclosureB_width`): `2|N| ≤ M`, `0 ≤ K ≤ k (2^(P+1) + 1)`, both on the grid `2^q`
(no alignment shift), so the integers `N ± K` that `roundExact` rounds are at most
`M/2 + k (2^(P+1) + 1)` in magnitude, whatever the inputs' exponents. `K` charges each truncation a
whole unit where the rational bound uses the largest actual loss, so the integer check can settle
fewer entries.

**Signed zeros.** `roundingTestSignedB` is `roundingTestSigned` on integer enclosures, with the sign of a
zero result read off the integer ends (`signB`) or, on the exact path, from the sign of the exact
sum computed by `signSum` (`ozaki1ExactFallbackBS`). `ozaki2CRS` (rational) and `ozaki2CRBS` (bounded)
return the IEEE-signed correctly rounded product `crSigned` (`ozaki2CRS_eq`, `ozaki2CRBS_eq`). -/

local notation "ℕ" => Nat
local notation "ℤ" => Int
local notation "ℚ" => Rat

namespace Ozaki

/-! ## Integer enclosures -/

/-- The values of an integer enclosure `(N, q, K, c)`: `H = N 2^q` and `B = K 2^c`. -/
def enclVal (e : ℤ × ℤ × ℤ × ℤ) : ℚ × ℚ := ((e.1 : ℚ) * 2 ^ e.2.1, (e.2.2.1 : ℚ) * 2 ^ e.2.2.2)

/-- The enclosure test on an integer enclosure: both ends rounded with `roundExact` at the grid
`min q c`. -/
def enclosureTestB (p : ℕ) (emin emax : ℤ) (e : ℤ × ℤ × ℤ × ℤ) : Option ℚ :=
  roundEnclosureB p emin emax e.1 e.2.1 e.2.2.1 e.2.2.2 0

theorem enclosureTestB_eq (p : ℕ) (emin emax : ℤ) (e : ℤ × ℤ × ℤ × ℤ) :
    enclosureTestB p emin emax e = roundEnclosure (roundRNE p emin emax) (enclVal e).1 (enclVal e).2 := by
  unfold enclosureTestB enclVal
  rw [roundEnclosureB_eq]
  rw [show ((((0 : ℕ) : ℚ)) : ℚ) = 0 from rfl, Rat.zero_mul, Rat.add_zero]

/-- Integer enclosures tried in turn (`none` for one that could not be computed), each by the
integer test, then the fallback. -/
def roundingTestB (p : ℕ) (emin emax : ℤ) : List (Option (ℤ × ℤ × ℤ × ℤ)) → Option ℚ → Option ℚ
  | [], exact => exact
  | e :: es, exact =>
    match e.bind (enclosureTestB p emin emax) with
    | some w => some w
    | none => roundingTestB p emin emax es exact

/-- `roundingTestB` is `roundingTest` with `rnd = roundRNE p emin emax` on the enclosures' values, when the
fallback is the rounding of `v`. -/
theorem roundingTestB_eq_roundingTest (p : ℕ) (emin emax : ℤ) {v : ℚ} :
    ∀ (es : List (Option (ℤ × ℤ × ℤ × ℤ))) (exact : Option ℚ), exact = roundRNE p emin emax v →
      roundingTestB p emin emax es exact =
        roundingTest (roundRNE p emin emax) (es.map (Option.map enclVal)) (some v)
  | [], exact, hex => by subst hex; rfl
  | e :: es, exact, hex => by
    have ih := roundingTestB_eq_roundingTest p emin emax es exact hex
    have he : e.bind (enclosureTestB p emin emax) =
        (Option.map enclVal e).bind fun q => roundEnclosure (roundRNE p emin emax) q.1 q.2 := by
      cases e <;> simp [enclosureTestB_eq]
    simp only [List.map_cons]
    unfold roundingTestB roundingTest
    rw [he]
    cases (Option.map enclVal e).bind fun q => roundEnclosure (roundRNE p emin emax) q.1 q.2 with
    | some w => rfl
    | none => exact ih

/-- **The integer check is correct rounding.** If every integer enclosure contains `v` and the
fallback is the rounding of `v`, `roundingTestB` returns the rounding of `v`. -/
theorem roundingTestB_eq {p : ℕ} {emin emax : ℤ} (hp : 0 < p) (hle : emin ≤ emax) {v : ℚ}
    (es : List (Option (ℤ × ℤ × ℤ × ℤ))) (exact : Option ℚ)
    (hes : ∀ e ∈ es, ∀ t, e = some t → Rat.abs (v - (enclVal t).1) ≤ (enclVal t).2)
    (hex : exact = roundRNE p emin emax v) :
    roundingTestB p emin emax es exact = roundRNE p emin emax v := by
  rw [roundingTestB_eq_roundingTest p emin emax es exact hex]
  apply roundingTest_eq (roundRNE_nearest hp hle) (roundRNE_intervals hp) _ _ _ rfl
  intro c hc H B hcB
  obtain ⟨e, he, rfl⟩ := List.mem_map.mp hc
  cases e with
  | none => simp at hcB
  | some t =>
    simp only [Option.map_some, Option.some.injEq] at hcB
    have := hes _ he t rfl
    rw [hcB] at this
    exact this

/-! ## Signed zeros on integer enclosures -/

/-- The sign bit an integer enclosure settles for its rounding `r`: the sign of a nonzero `r`; for
`r = 0`, the side of zero the integer ends lie on; none if they straddle zero. -/
def signB (e : ℤ × ℤ × ℤ × ℤ) (r : ℚ) : Option Bool :=
  let q0 := min e.2.1 e.2.2.2
  let H := e.1 * 2 ^ (e.2.1 - q0).toNat
  let B := e.2.2.1 * 2 ^ (e.2.2.2 - q0).toNat
  if r ≠ 0 then some (decide (r < 0))
  else if 0 < H - B then some false
  else if H + B < 0 then some true
  else none

theorem signB_eq (e : ℤ × ℤ × ℤ × ℤ) (r : ℚ) :
    signB e r = signFromEnclosure (enclVal e).1 (enclVal e).2 r := by
  obtain ⟨N, q, K, c⟩ := e
  have eq := pow_toNat_mul (Int.min_le_left q c)
  have ec := pow_toNat_mul (Int.min_le_right q c)
  have hp := two_pow_pos (min q c)
  have e1 : (((N * 2 ^ (q - min q c).toNat - K * 2 ^ (c - min q c).toNat : ℤ) : ℚ)) *
      2 ^ (min q c) = (N : ℚ) * 2 ^ q - (K : ℚ) * 2 ^ c := by
    simp only [Rat.intCast_sub, Rat.intCast_mul, intCast_two_pow]
    rw [← eq, ← ec]; grind
  have e2 : (((N * 2 ^ (q - min q c).toNat + K * 2 ^ (c - min q c).toNat : ℤ) : ℚ)) *
      2 ^ (min q c) = (N : ℚ) * 2 ^ q + (K : ℚ) * 2 ^ c := by
    simp only [Rat.intCast_add, Rat.intCast_mul, intCast_two_pow]
    rw [← eq, ← ec]; grind
  have i1 : (0 < N * 2 ^ (q - min q c).toNat - K * 2 ^ (c - min q c).toNat) ↔
      (0 : ℚ) < (N : ℚ) * 2 ^ q - (K : ℚ) * 2 ^ c := by
    rw [← e1, ← sgnQ_pos_iff, sgnQ_mul_two_pow, sgnQ_pos_iff]
    exact ⟨fun h => by exact_mod_cast h, fun h => by exact_mod_cast h⟩
  have i2 : (N * 2 ^ (q - min q c).toNat + K * 2 ^ (c - min q c).toNat < 0) ↔
      (N : ℚ) * 2 ^ q + (K : ℚ) * 2 ^ c < 0 := by
    rw [← e2, ← Rat.not_le, ← sgnQ_nonneg_iff, sgnQ_mul_two_pow, sgnQ_nonneg_iff, Rat.not_le]
    exact ⟨fun h => by exact_mod_cast h, fun h => by exact_mod_cast h⟩
  unfold signB signFromEnclosure enclVal
  simp only
  by_cases hr : r ≠ 0
  · rw [if_pos hr, if_pos hr]
  · rw [if_neg hr, if_neg hr]
    by_cases h1 : 0 < N * 2 ^ (q - min q c).toNat - K * 2 ^ (c - min q c).toNat
    · rw [if_pos h1, if_pos (i1.mp h1)]
    · rw [if_neg h1, if_neg (fun h => h1 (i1.mpr h))]
      by_cases h2 : N * 2 ^ (q - min q c).toNat + K * 2 ^ (c - min q c).toNat < 0
      · rw [if_pos h2, if_pos (i2.mp h2)]
      · rw [if_neg h2, if_neg (fun h => h2 (i2.mpr h))]

/-- The sign bit of a correctly rounded sum from the sign `σ ∈ {−1, 0, 1}` of the exact sum. -/
def signOfSgn (σ : ℤ) (z : Bool) : Bool := if σ = 0 then z else decide (σ < 0)

theorem signOfSgn_sgnQ (v : ℚ) (z : Bool) : signOfSgn (sgnQ v) z = sumNeg v z := by
  unfold signOfSgn sumNeg
  by_cases hv : v = 0
  · rw [if_pos ((sgnQ_eq_zero_iff v).mpr hv), if_pos hv]
  · rw [if_neg (fun h => hv ((sgnQ_eq_zero_iff v).mp h)), if_neg hv]
    have h : sgnQ v < 0 ↔ v < 0 := by
      rw [← Int.not_le, ← Rat.not_le, sgnQ_nonneg_iff]
    simp only [decide_eq_decide]
    exact h

/-- The signed check on integer enclosures: try them in order, accepting one whose ends round alike
and whose sign is settled; after the last, the fallback's rounding and the sign of the exact sum. -/
def roundingTestSignedB (p : ℕ) (emin emax : ℤ) :
    List (Option (ℤ × ℤ × ℤ × ℤ)) → Option (ℚ × ℤ) → Bool → Option Signed
  | [], exact, z => exact.map fun rs => ⟨rs.1, signOfSgn rs.2 z⟩
  | e :: es, exact, z =>
    match e.bind (fun t => (enclosureTestB p emin emax t).bind fun r =>
        (signB t r).map fun n => (⟨r, n⟩ : Signed)) with
    | some w => some w
    | none => roundingTestSignedB p emin emax es exact z

theorem roundingTestSignedB_eq_roundingTestSigned (p : ℕ) (emin emax : ℤ) {v : ℚ} (z : Bool) :
    ∀ (es : List (Option (ℤ × ℤ × ℤ × ℤ))) (exact : Option (ℚ × ℤ)),
      exact = (roundRNE p emin emax v).map (fun r => (r, sgnQ v)) →
      roundingTestSignedB p emin emax es exact z =
        roundingTestSigned (roundRNE p emin emax) (es.map (Option.map enclVal)) (some v) z
  | [], exact, hex => by
    subst hex
    unfold roundingTestSignedB roundingTestSigned
    simp only [Option.map_map]
    congr 1
    funext r
    simp only [Function.comp, signOfSgn_sgnQ]
  | e :: es, exact, hex => by
    have ih := roundingTestSignedB_eq_roundingTestSigned p emin emax z es exact hex
    have he : e.bind (fun t => (enclosureTestB p emin emax t).bind fun r =>
        (signB t r).map fun n => (⟨r, n⟩ : Signed)) =
        (Option.map enclVal e).bind (fun q => (roundEnclosure (roundRNE p emin emax) q.1 q.2).bind
          fun r => (signFromEnclosure q.1 q.2 r).map fun n => (⟨r, n⟩ : Signed)) := by
      cases e <;> simp [enclosureTestB_eq, signB_eq]
    simp only [List.map_cons]
    unfold roundingTestSignedB roundingTestSigned
    rw [he]
    cases (Option.map enclVal e).bind (fun q => (roundEnclosure (roundRNE p emin emax) q.1 q.2).bind
          fun r => (signFromEnclosure q.1 q.2 r).map fun n => (⟨r, n⟩ : Signed)) with
    | some w => rfl
    | none => exact ih

/-- **The signed integer check returns the correctly rounded value with the IEEE sign.** -/
theorem roundingTestSignedB_eq {p : ℕ} {emin emax : ℤ} (hp : 0 < p) (hle : emin ≤ emax) {v : ℚ}
    (z : Bool) (es : List (Option (ℤ × ℤ × ℤ × ℤ))) (exact : Option (ℚ × ℤ))
    (hes : ∀ e ∈ es, ∀ t, e = some t → Rat.abs (v - (enclVal t).1) ≤ (enclVal t).2)
    (hex : exact = (roundRNE p emin emax v).map (fun r => (r, sgnQ v))) :
    roundingTestSignedB p emin emax es exact z =
      (roundRNE p emin emax v).map fun r => ⟨r, sumNeg v z⟩ := by
  rw [roundingTestSignedB_eq_roundingTestSigned p emin emax z es exact hex]
  apply roundingTestSigned_eq (roundRNE_nearest hp hle) (roundRNE_intervals hp)
    (roundRNE_zero' p emin emax) z _ _ _ rfl
  intro c hc H B hcB
  obtain ⟨e, he, rfl⟩ := List.mem_map.mp hc
  cases e with
  | none => simp at hcB
  | some t =>
    simp only [Option.map_some, Option.some.injEq] at hcB
    have := hes _ he t rfl
    rw [hcB] at this
    exact this

/-! ## The bounded exact path with the sign of the exact sum -/

/-- Ozaki-I's bounded exact path, returning also the sign of the exact sum (`signSum` on the same
integer terms, with the same windows). -/
def ozaki1ExactFallbackBS (mult : MatrixMultiplier) (p : ℕ) (emin emax : ℤ) (b smax : ℕ) (x y : List ℚ) :
    Option (ℚ × ℤ) :=
  match (List.range' 1 smax).find? fun s => residualsVanish b s x y with
  | some s =>
    match (slicePairs (split b s x).1 (split b s y).1).mapM
        (fun pr => sliceProductInt mult pr.1 pr.2) with
    | some ts => (roundSum p emin emax (bitlen (ts.length + 1) + p + 4) ts).map fun r =>
        (r, signSum (bitlen (ts.length + 1) + p + 4) ts)
    | none => none
  | none => none

theorem ozaki1ExactFallbackBS_eq {mult : MatrixMultiplier} {b bound : ℕ} (hmult : mult.ExactOn b bound)
    (p : ℕ) (emin emax : ℤ) (smax : ℕ) {x y : List ℚ} (hlen : x.length = y.length)
    (hbound : x.length * (2 ^ b * 2 ^ b) ≤ bound)
    (hvanish : ∃ s ∈ List.range' 1 smax, residualsVanish b s x y = true) :
    ozaki1ExactFallbackBS mult p emin emax b smax x y =
      (roundRNE p emin emax (dot x y)).map fun r => (r, sgnQ (dot x y)) := by
  unfold ozaki1ExactFallbackBS
  obtain ⟨s, hs⟩ := Option.isSome_iff_exists.mp (List.find?_isSome.mpr hvanish)
  rw [hs]
  have hv := List.find?_some hs
  simp only [residualsVanish, Bool.and_eq_true, List.all_eq_true, beq_iff_eq] at hv
  simp only
  rw [mapM_eq_some_map (g := fun pr => exactSliceInt pr.1 pr.2) fun pr hpr =>
    sliceProductInt_exact hmult hlen hbound (mem_slicePairs hpr).1 (mem_slicePairs hpr).2]
  simp only
  have htsum : tsum ((slicePairs (split b s x).1 (split b s y).1).map
      fun pr => exactSliceInt pr.1 pr.2) = dot x y := by
    have hfull := ozaki1Full_eq hmult hlen hbound hv.1 hv.2
    unfold ozaki1Full at hfull
    rw [mapM_eq_some_map (f := fun pr : Slice × Slice => fullTerm mult pr.1 pr.2)
        (g := fun pr : Slice × Slice => tval (exactSliceInt pr.1 pr.2)) fun pr hpr => by
        unfold fullTerm
        rw [(multiplier_exact hmult hlen hbound (mem_slicePairs hpr).1 (mem_slicePairs hpr).2).1]
        unfold tval exactSliceInt; simp only [Option.map_some]; rw [Rat.mul_comm]] at hfull
    simp only [Option.map_some, Option.some.injEq] at hfull
    unfold tsum
    rw [List.map_map]
    exact hfull
  generalize hts : (slicePairs (split b s x).1 (split b s y).1).map
    (fun pr => exactSliceInt pr.1 pr.2) = ts at htsum
  have hbl := bitlen_mono (Nat.le_add_right ts.length 1)
  rw [roundSum_eq _ _ (by omega), signSum_eq (by omega), htsum]

/-! ## A dyadic bound from the scaled integers

Both Ozaki-II and ADP scale `x` by `2^sₓ` and round each entry to an integer `aᵢ = g(xᵢ 2^sₓ)`, `g`
truncation or floor, so `|xᵢ 2^sₓ − aᵢ| ≤ 1`; likewise `cⱼ` for `y`. The bound of
`dot_approx_error` for these approximations is then at most `K 2^(−sₓ−s_y)` with the integer
`K = [x drops bits] (Σ|cⱼ| + k) + [y drops bits] Σ|aᵢ|` (`scaledBound_le`): every entry loses less
than one unit, nothing when no bits are dropped, `Σ|y| ≤ (Σ|cⱼ| + k) 2^(−s_y)`, and
`Σ|x̃| = Σ|aᵢ| 2^(−sₓ)`. `K` is computed from the integers the engine multiplies. -/

theorem mem_zipWith_sub_map {x : List ℚ} {g : ℚ → ℚ} {d : ℚ}
    (h : d ∈ List.zipWith (· - ·) x (x.map g)) : ∃ a ∈ x, d = a - g a := by
  induction x with
  | nil => simp at h
  | cons a x ih =>
    simp only [List.map_cons, List.zipWith_cons_cons, List.mem_cons] at h
    rcases h with rfl | h
    · exact ⟨a, List.mem_cons_self, rfl⟩
    · obtain ⟨b, hb, rfl⟩ := ih h
      exact ⟨b, List.mem_cons_of_mem _ hb, rfl⟩

/-- Whether scaling `x` by `2^s` and rounding each entry to an integer with `g` drops anything. -/
def drops (g : ℚ → ℤ) (s : ℤ) (x : List ℚ) : Bool :=
  x.any fun t => decide ((g (t * 2 ^ s) : ℚ) ≠ t * 2 ^ s)

/-- The integer bound `K = [dx] (Σ|cⱼ| + k) + [dy] Σ|aᵢ|`. -/
def boundK (a c : List ℤ) (dx dy : Bool) (k : ℕ) : ℤ :=
  (if dx then (((c.map Int.natAbs).sum + k : ℕ) : ℤ) else 0) +
    (if dy then (((a.map Int.natAbs).sum : ℕ) : ℤ) else 0)

theorem absSum_cons (a : ℚ) (l : List ℚ) : absSum (a :: l) = Rat.abs a + absSum l := by
  simp [absSum]

theorem two_pow_mul_neg (s : ℤ) : (2 : ℚ) ^ s * 2 ^ (-s) = 1 := by
  rw [← two_pow_add, Int.add_right_neg, two_pow_zero]

theorem abs_sub_scaled_le {g : ℚ → ℤ} (hg : ∀ t, Rat.abs (t - g t) ≤ 1) (s : ℤ) (t : ℚ) :
    Rat.abs (t - (g (t * 2 ^ s) : ℚ) * 2 ^ (-s)) ≤ 2 ^ (-s) := by
  have hs := two_pow_mul_neg s
  have e : t - (g (t * 2 ^ s) : ℚ) * 2 ^ (-s) = (t * 2 ^ s - g (t * 2 ^ s)) * 2 ^ (-s) := by
    have : t * 2 ^ s * 2 ^ (-s) = t := by rw [Rat.mul_assoc, hs, Rat.mul_one]
    grind
  rw [e, abs_mul, abs_two_pow]
  have := Rat.mul_le_mul_of_nonneg_right (hg (t * 2 ^ s)) (Rat.le_of_lt (two_pow_pos (-s)))
  rwa [Rat.one_mul] at this

theorem abs_le_scaled {g : ℚ → ℤ} (hg : ∀ t, Rat.abs (t - g t) ≤ 1) (s : ℤ) (t : ℚ) :
    Rat.abs t ≤ (((g (t * 2 ^ s)).natAbs : ℚ) + 1) * 2 ^ (-s) := by
  have hs := two_pow_mul_neg s
  have e : t = (t * 2 ^ s) * 2 ^ (-s) := by rw [Rat.mul_assoc, hs, Rat.mul_one]
  have h1 : Rat.abs (t * 2 ^ s) ≤ ((g (t * 2 ^ s)).natAbs : ℚ) + 1 := by
    have := abs_add_le ((g (t * 2 ^ s) : ℤ) : ℚ) (t * 2 ^ s - g (t * 2 ^ s))
    rw [abs_intCast] at this
    have h2 := hg (t * 2 ^ s)
    have e2 : ((g (t * 2 ^ s) : ℤ) : ℚ) + (t * 2 ^ s - g (t * 2 ^ s)) = t * 2 ^ s := by grind
    rw [e2] at this
    grind
  have e' : Rat.abs t = Rat.abs (t * 2 ^ s) * 2 ^ (-s) := by
    conv => lhs; rw [e]
    rw [abs_mul, abs_two_pow]
  rw [e']
  exact Rat.mul_le_mul_of_nonneg_right h1 (Rat.le_of_lt (two_pow_pos (-s)))

theorem absSum_le_scaled {g : ℚ → ℤ} (hg : ∀ t, Rat.abs (t - g t) ≤ 1) (s : ℤ) :
    ∀ y : List ℚ, absSum y ≤
      ((((y.map fun t => g (t * 2 ^ s)).map Int.natAbs).sum : ℕ) + (y.length : ℚ)) * 2 ^ (-s)
  | [] => by
    show (0 : ℚ) ≤ _
    exact Rat.mul_nonneg (Rat.add_nonneg Rat.natCast_nonneg Rat.natCast_nonneg)
      (Rat.le_of_lt (two_pow_pos _))
  | t :: y => by
    have ih := absSum_le_scaled hg s y
    have h := abs_le_scaled hg s t
    rw [absSum_cons]
    simp only [List.map_cons, List.sum_cons, List.length_cons, Rat.natCast_add, natCast_succ]
    grind

theorem absSum_scaled (g : ℚ → ℤ) (s : ℤ) :
    ∀ x : List ℚ, absSum (x.map fun t => (g (t * 2 ^ s) : ℚ) * 2 ^ (-s)) =
      ((((x.map fun t => g (t * 2 ^ s)).map Int.natAbs).sum : ℕ) : ℚ) * 2 ^ (-s)
  | [] => by simp [absSum]
  | t :: x => by
    have ih := absSum_scaled g s x
    simp only [List.map_cons, List.sum_cons, Rat.natCast_add]
    rw [absSum_cons, ih, abs_mul, abs_two_pow, abs_intCast]
    grind

theorem maxAbs_scaled_le {g : ℚ → ℤ} (hg : ∀ t, Rat.abs (t - g t) ≤ 1) (s : ℤ) (x : List ℚ) :
    maxAbs (List.zipWith (· - ·) x (x.map fun t => (g (t * 2 ^ s) : ℚ) * 2 ^ (-s))) ≤
      if drops g s x then 2 ^ (-s) else 0 := by
  split
  · apply maxAbs_le (Rat.le_of_lt (two_pow_pos _))
    intro d hd
    obtain ⟨a, _, rfl⟩ := mem_zipWith_sub_map hd
    exact abs_sub_scaled_le hg s a
  · rename_i hd
    unfold drops at hd
    rw [Bool.not_eq_true, List.any_eq_false] at hd
    apply maxAbs_le Rat.le_refl
    intro d hmem
    obtain ⟨a, ha, rfl⟩ := mem_zipWith_sub_map hmem
    have hga : (g (a * 2 ^ s) : ℚ) = a * 2 ^ s := by
      have := hd a ha; simp at this; exact this
    rw [hga, Rat.mul_assoc, two_pow_mul_neg, Rat.mul_one, show a - a = (0 : ℚ) by grind, abs_zero]
    exact Rat.le_refl

/-- **The approximation bound from the scaled integers.** -/
theorem scaledBound_le {g : ℚ → ℤ} (hg : ∀ t, Rat.abs (t - g t) ≤ 1) (sx sy : ℤ)
    {x y : List ℚ} (hlen : x.length = y.length) :
    maxAbs (List.zipWith (· - ·) x (x.map fun t => (g (t * 2 ^ sx) : ℚ) * 2 ^ (-sx))) * absSum y +
        maxAbs (List.zipWith (· - ·) y (y.map fun t => (g (t * 2 ^ sy) : ℚ) * 2 ^ (-sy))) *
          absSum (x.map fun t => (g (t * 2 ^ sx) : ℚ) * 2 ^ (-sx)) ≤
      (boundK (x.map fun t => g (t * 2 ^ sx)) (y.map fun t => g (t * 2 ^ sy))
        (drops g sx x) (drops g sy y) x.length : ℚ) * 2 ^ (-(sx + sy)) := by
  have m1 := maxAbs_scaled_le hg sx x
  have m2 := maxAbs_scaled_le hg sy y
  have s1 := absSum_le_scaled hg sy y
  have s2 := absSum_scaled g sx x
  rw [← hlen] at s1
  rw [s2]
  have hpx := two_pow_pos (-sx)
  have hpy := two_pow_pos (-sy)
  have e : (2 : ℚ) ^ (-(sx + sy)) = 2 ^ (-sx) * 2 ^ (-sy) := by
    rw [← two_pow_add]; congr 1; omega
  rw [e]
  generalize hA : (((x.map fun t => g (t * 2 ^ sx)).map Int.natAbs).sum : ℕ) = A at *
  generalize hC : (((y.map fun t => g (t * 2 ^ sy)).map Int.natAbs).sum : ℕ) = C at *
  have he1 : 0 ≤ (if drops g sx x then (2 : ℚ) ^ (-sx) else 0) := by
    split
    · exact Rat.le_of_lt hpx
    · exact Rat.le_refl
  have hA0 : (0 : ℚ) ≤ (A : ℚ) * 2 ^ (-sx) := Rat.mul_nonneg Rat.natCast_nonneg (Rat.le_of_lt hpx)
  have a1 := Rat.mul_le_mul_of_nonneg_right m1 (absSum_nonneg y)
  have a2 := Rat.mul_le_mul_of_nonneg_left s1 he1
  have a3 := Rat.mul_le_mul_of_nonneg_right m2 hA0
  have key : (if drops g sx x then (2 : ℚ) ^ (-sx) else 0) *
        (((C : ℚ) + (x.length : ℚ)) * 2 ^ (-sy)) +
      (if drops g sy y then (2 : ℚ) ^ (-sy) else 0) * ((A : ℚ) * 2 ^ (-sx)) =
      (boundK (x.map fun t => g (t * 2 ^ sx)) (y.map fun t => g (t * 2 ^ sy))
        (drops g sx x) (drops g sy y) x.length : ℚ) * (2 ^ (-sx) * 2 ^ (-sy)) := by
    unfold boundK
    rw [hA, hC]
    cases drops g sx x <;> cases drops g sy y <;>
      simp only [Bool.false_eq_true, ↓reduceIte, Rat.intCast_add, Rat.intCast_natCast,
        Rat.intCast_zero, Rat.natCast_add] <;> grind
  rw [← key]
  have := Rat.le_trans a1 a2
  grind
/-! ## Ozaki-II's integer enclosure -/

/-- Ozaki-II's reconstructed integer product `a · c`: the residue products from the engine and the
CRT reconstruction. -/
def ozaki2Int (mult : MatrixMultiplier) (B : CRTBasis) (P : ℕ) (x y : List ℚ) : Option ℤ :=
  (B.moduli.mapM fun m =>
    residueProduct mult m (scaleTrunc (scaleShift P x) x) (scaleTrunc (scaleShift P y) y)).map
    (crt B)

theorem ozaki2_eq_int (mult : MatrixMultiplier) (round : ℚ → Option ℚ) (B : CRTBasis) (P : ℕ) (x y : List ℚ) :
    ozaki2 mult round B P x y = (ozaki2Int mult B P x y).bind fun N =>
      round ((N : ℚ) * 2 ^ (-(scaleShift P x + scaleShift P y))) := by
  unfold ozaki2 ozaki2Int
  simp only
  cases h : B.moduli.mapM fun m =>
    residueProduct mult m (scaleTrunc (scaleShift P x) x) (scaleTrunc (scaleShift P y) y) with
  | none => simp
  | some rs => simp

/-- Ozaki-II's integer bound: `K` of the truncated integers (`boundK`). -/
def ozaki2K (P : ℕ) (x y : List ℚ) : ℤ :=
  boundK (scaleTrunc (scaleShift P x) x) (scaleTrunc (scaleShift P y) y)
    (drops truncInt (scaleShift P x) x) (drops truncInt (scaleShift P y) y) x.length

/-- **Ozaki-II's integer enclosure**: `H = N 2^q` with `N` the reconstructed product and
`q = −(sₓ + s_y)`, and `B = K 2^q` on the same grid. -/
def ozaki2EnclosureB (mult : MatrixMultiplier) (B : CRTBasis) (P : ℕ) (x y : List ℚ) :
    Option (ℤ × ℤ × ℤ × ℤ) :=
  (ozaki2Int mult B P x y).map fun N =>
    (N, -(scaleShift P x + scaleShift P y), ozaki2K P x y, -(scaleShift P x + scaleShift P y))

theorem truncInt_close (t : ℚ) : Rat.abs (t - truncInt t) ≤ 1 :=
  Rat.le_of_lt (truncInt_spec t).1

/-- **The truncation bound is at most `K 2^q`.** -/
theorem ozaki2Bound_le (P : ℕ) {x y : List ℚ} (hlen : x.length = y.length) :
    ozaki2Bound P x y ≤ (ozaki2K P x y : ℚ) * 2 ^ (-(scaleShift P x + scaleShift P y)) := by
  have htv : ∀ z : List ℚ, truncVals P z =
      z.map fun a => (truncInt (a * 2 ^ scaleShift P z) : ℚ) * 2 ^ (-scaleShift P z) := by
    intro z; unfold truncVals scaleTrunc; rw [List.map_map]; rfl
  unfold ozaki2Bound ozaki2K
  rw [htv x, htv y]
  exact scaledBound_le truncInt_close _ _ hlen

/-- **Ozaki-II's integer enclosure contains `x · y`** on an exact engine with a valid basis. -/
theorem ozaki2EnclosureB_sound {mult : MatrixMultiplier} {b bound : ℕ} (hmult : mult.ExactOn b bound)
    {B : CRTBasis} (hB : B.Valid) (hmb : ∀ m ∈ B.moduli, m ≤ 2 ^ (b + 1)) (P : ℕ) {x y : List ℚ}
    (hlen : x.length = y.length) (hbound : x.length * (2 ^ b * 2 ^ b) ≤ bound)
    (hrange : 2 * x.length * (2 ^ P * 2 ^ P) < B.modulus) {t : ℤ × ℤ × ℤ × ℤ}
    (ht : ozaki2EnclosureB mult B P x y = some t) :
    Rat.abs (dot x y - (enclVal t).1) ≤ (enclVal t).2 := by
  unfold ozaki2EnclosureB at ht
  cases hN : ozaki2Int mult B P x y with
  | none => rw [hN] at ht; simp at ht
  | some N =>
    rw [hN, Option.map_some, Option.some.injEq] at ht
    subst ht
    have hval : ozaki2 mult some B P x y =
        some ((N : ℚ) * 2 ^ (-(scaleShift P x + scaleShift P y))) := by
      rw [ozaki2_eq_int, hN]; rfl
    have henc : ozaki2Enclosure mult B P x y =
        some ((N : ℚ) * 2 ^ (-(scaleShift P x + scaleShift P y)), ozaki2Bound P x y) := by
      unfold ozaki2Enclosure; rw [hval]; rfl
    exact Rat.le_trans (ozaki2Enclosure_sound hmult hB hmb P hlen hbound hrange henc)
      (ozaki2Bound_le P hlen)

theorem sum_natAbs_le_mul {a : List ℤ} {n : ℕ} (h : ∀ z ∈ a, z.natAbs ≤ n) :
    (a.map Int.natAbs).sum ≤ a.length * n := by
  induction a with
  | nil => simp
  | cons z a ih =>
    simp only [List.map_cons, List.sum_cons, List.length_cons]
    have h1 := h z List.mem_cons_self
    have h2 := ih fun w hw => h w (List.mem_cons_of_mem _ hw)
    rw [Nat.add_mul, Nat.one_mul]; omega

theorem boundK_le {a c : List ℤ} {dx dy : Bool} {k n : ℕ} (ha : a.length = k) (hc : c.length = k)
    (hna : ∀ z ∈ a, z.natAbs ≤ n) (hnc : ∀ z ∈ c, z.natAbs ≤ n) :
    0 ≤ boundK a c dx dy k ∧ (boundK a c dx dy k).natAbs ≤ k * (2 * n + 1) := by
  have h1 := sum_natAbs_le_mul hna
  have h2 := sum_natAbs_le_mul hnc
  rw [ha] at h1; rw [hc] at h2
  have hkn : k * (2 * n + 1) = 2 * (k * n) + k := by
    rw [Nat.mul_add, Nat.mul_one, Nat.mul_left_comm]
  rw [hkn]
  unfold boundK
  cases dx <;> cases dy <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> omega

/-- **The widths of Ozaki-II's integer enclosure**, independent of the exponents: `2|N| ≤ M`,
`0 ≤ K ≤ k (2^(P+1) + 1)`, the bound on `H`'s grid; so the integers `N ± K` the test rounds are at
most `M/2 + k (2^(P+1) + 1)` in magnitude. -/
theorem ozaki2EnclosureB_width {mult : MatrixMultiplier} {B : CRTBasis} {P : ℕ} {x y : List ℚ}
    (hM : 0 < B.modulus) (hlen : x.length = y.length) {t : ℤ × ℤ × ℤ × ℤ}
    (ht : ozaki2EnclosureB mult B P x y = some t) :
    2 * t.1.natAbs ≤ B.modulus ∧ t.2.2.2 = t.2.1 ∧ 0 ≤ t.2.2.1 ∧
      t.2.2.1.natAbs ≤ x.length * (2 * 2 ^ P + 1) ∧
      2 * (t.1 - t.2.2.1).natAbs ≤ B.modulus + 2 * (x.length * (2 * 2 ^ P + 1)) ∧
      2 * (t.1 + t.2.2.1).natAbs ≤ B.modulus + 2 * (x.length * (2 * 2 ^ P + 1)) := by
  unfold ozaki2EnclosureB ozaki2Int at ht
  cases hrs : B.moduli.mapM fun m =>
      residueProduct mult m (scaleTrunc (scaleShift P x) x) (scaleTrunc (scaleShift P y) y) with
  | none => rw [hrs] at ht; simp at ht
  | some rs =>
    rw [hrs] at ht
    simp only [Option.map_some, Option.some.injEq] at ht
    subst ht
    simp only
    have hN : 2 * (crt B rs).natAbs ≤ B.modulus := natAbs_symMod_le _ hM
    obtain ⟨hK0, hK⟩ := boundK_le (dx := drops truncInt (scaleShift P x) x)
      (dy := drops truncInt (scaleShift P y) y) (scaleTrunc_length _ x)
      (by rw [scaleTrunc_length, hlen]) (scaleTrunc_bound P x) (scaleTrunc_bound P y)
    unfold ozaki2K
    refine ⟨hN, trivial, hK0, hK, ?_, ?_⟩
    · have := Int.natAbs_sub_le (crt B rs) (boundK (scaleTrunc (scaleShift P x) x)
        (scaleTrunc (scaleShift P y) y) (drops truncInt (scaleShift P x) x)
        (drops truncInt (scaleShift P y) y) x.length)
      omega
    · have := Int.natAbs_add_le (crt B rs) (boundK (scaleTrunc (scaleShift P x) x)
        (scaleTrunc (scaleShift P y) y) (drops truncInt (scaleShift P x) x)
        (drops truncInt (scaleShift P y) y) x.length)
      omega

/-! ## Correctly rounded Ozaki-II in bounded integer arithmetic -/

/-- **Correctly rounded Ozaki-II with bounded registers**: the configurations `(basis, P)` in turn,
each checked on its integer enclosure, then Ozaki-I's bounded exact path. -/
def ozaki2CRB (mult : MatrixMultiplier) (p : ℕ) (emin emax : ℤ) (cfgs : List (CRTBasis × ℕ)) (b smax : ℕ)
    (x y : List ℚ) : Option ℚ :=
  roundingTestB p emin emax (cfgs.map fun c => ozaki2EnclosureB mult c.1 c.2 x y)
    (ozaki1ExactFallbackB mult p emin emax b smax x y)

/-- **Ozaki-II with bounded registers is correctly rounded** on an exact engine, for every input
whose exact path ends within `smax` slices. -/
theorem ozaki2CRB_eq {p : ℕ} {emin emax : ℤ} (hp : 0 < p) (hle : emin ≤ emax) {mult : MatrixMultiplier}
    {b bound : ℕ} (hmult : mult.ExactOn b bound) {cfgs : List (CRTBasis × ℕ)} {smax : ℕ}
    {x y : List ℚ}
    (hcfg : ∀ c ∈ cfgs, c.1.Valid ∧ (∀ m ∈ c.1.moduli, m ≤ 2 ^ (b + 1)) ∧
      2 * x.length * (2 ^ c.2 * 2 ^ c.2) < c.1.modulus)
    (hlen : x.length = y.length) (hbound : x.length * (2 ^ b * 2 ^ b) ≤ bound)
    (hvanish : ∃ s ∈ List.range' 1 smax, residualsVanish b s x y = true) :
    ozaki2CRB mult p emin emax cfgs b smax x y = roundRNE p emin emax (dot x y) := by
  apply roundingTestB_eq hp hle
  · intro e he t het
    obtain ⟨cfg, hmem, rfl⟩ := List.mem_map.mp he
    obtain ⟨hB, hmb, hrange⟩ := hcfg cfg hmem
    exact ozaki2EnclosureB_sound hmult hB hmb cfg.2 hlen hbound hrange het
  · rw [ozaki1ExactFallbackB_eq hmult p emin emax smax hlen hbound,
      ozaki1ExactFallback_eq hmult hlen hbound hvanish]
    rfl

/-- **Binary64 inputs**: correctly rounded to binary64 with bounded registers. -/
theorem ozaki2CRB64_eq {mult : MatrixMultiplier} {b bound : ℕ} (hmult : mult.ExactOn b bound)
    {cfgs : List (CRTBasis × ℕ)} {smax : ℕ} (hb : b ≤ 1025) (hsmax : 2098 < smax * (b + 1))
    {x y : List ℚ}
    (hcfg : ∀ c ∈ cfgs, c.1.Valid ∧ (∀ m ∈ c.1.moduli, m ≤ 2 ^ (b + 1)) ∧
      2 * x.length * (2 ^ c.2 * 2 ^ c.2) < c.1.modulus)
    (hlen : x.length = y.length) (hbound : x.length * (2 ^ b * 2 ^ b) ≤ bound)
    (hx : ∀ a ∈ x, Binary64Value a) (hy : ∀ a ∈ y, Binary64Value a) :
    ozaki2CRB mult 53 (-1022) 1023 cfgs b smax x y = rne64 (dot x y) :=
  ozaki2CRB_eq (by decide) (by decide) hmult hcfg hlen hbound (vanish64 hb hsmax hx hy)

/-- **Binary32 inputs**: correctly rounded to binary32 with bounded registers. -/
theorem ozaki2CRB32_eq {mult : MatrixMultiplier} {b bound : ℕ} (hmult : mult.ExactOn b bound)
    {cfgs : List (CRTBasis × ℕ)} {smax : ℕ} (hb : b ≤ 129) (hsmax : 277 < smax * (b + 1))
    {x y : List ℚ}
    (hcfg : ∀ c ∈ cfgs, c.1.Valid ∧ (∀ m ∈ c.1.moduli, m ≤ 2 ^ (b + 1)) ∧
      2 * x.length * (2 ^ c.2 * 2 ^ c.2) < c.1.modulus)
    (hlen : x.length = y.length) (hbound : x.length * (2 ^ b * 2 ^ b) ≤ bound)
    (hx : ∀ a ∈ x, Binary32Value a) (hy : ∀ a ∈ y, Binary32Value a) :
    ozaki2CRB mult 24 (-126) 127 cfgs b smax x y = rne32Q (dot x y) :=
  ozaki2CRB_eq (by decide) (by decide) hmult hcfg hlen hbound (vanish32Q hb hsmax hx hy)

/-! ## Signed zeros for Ozaki-II -/

theorem vals_length (xs : List Signed) : (vals xs).length = xs.length := by simp [vals]

theorem vals_all {xs : List Signed} {Q : ℚ → Prop} (h : ∀ a ∈ xs, Q a.val) : ∀ v ∈ vals xs, Q v := by
  intro v hv
  obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hv
  exact h a ha

/-- **Correctly rounded Ozaki-II with signed zeros**: Ozaki-II's enclosures, then Ozaki-I's exact
path, the sign of a zero result from the enclosure or the exact value. -/
def ozaki2CRS (mult : MatrixMultiplier) (rnd : ℚ → Option ℚ) (cfgs : List (CRTBasis × ℕ)) (b smax : ℕ)
    (xs ys : List Signed) : Option Signed :=
  roundingTestSigned rnd (cfgs.map fun c => ozaki2Enclosure mult c.1 c.2 (vals xs) (vals ys))
    (ozaki1ExactFallback mult b smax (vals xs) (vals ys)) (allNegZero xs ys)

theorem ozaki2CRS_eq {R : ℚ → Prop} {rnd : ℚ → Option ℚ} (h : RoundsToNearest R rnd)
    (hI : RoundsOnIntervals rnd) (h0 : rnd 0 = some 0) {mult : MatrixMultiplier} {b bound : ℕ}
    (hmult : mult.ExactOn b bound) {cfgs : List (CRTBasis × ℕ)} {smax : ℕ} {xs ys : List Signed}
    (hcfg : ∀ c ∈ cfgs, c.1.Valid ∧ (∀ m ∈ c.1.moduli, m ≤ 2 ^ (b + 1)) ∧
      2 * xs.length * (2 ^ c.2 * 2 ^ c.2) < c.1.modulus)
    (hlen : xs.length = ys.length) (hbound : xs.length * (2 ^ b * 2 ^ b) ≤ bound)
    (hvanish : ∃ s ∈ List.range' 1 smax, residualsVanish b s (vals xs) (vals ys) = true) :
    ozaki2CRS mult rnd cfgs b smax xs ys = crSigned rnd xs ys := by
  have hl : (vals xs).length = (vals ys).length := by rw [vals_length, vals_length, hlen]
  have hb : (vals xs).length * (2 ^ b * 2 ^ b) ≤ bound := by rw [vals_length]; exact hbound
  unfold ozaki2CRS crSigned
  apply roundingTestSigned_eq h hI h0 _ _ _ _ (ozaki1ExactFallback_eq hmult hl hb hvanish)
  intro c hc H Bd hcB
  obtain ⟨cfg, hmem, rfl⟩ := List.mem_map.mp hc
  obtain ⟨hB, hmb, hrange⟩ := hcfg cfg hmem
  exact ozaki2Enclosure_sound hmult hB hmb cfg.2 hl hb (by rw [vals_length]; exact hrange) hcB

/-- **Correctly rounded Ozaki-II with signed zeros and bounded registers.** -/
def ozaki2CRBS (mult : MatrixMultiplier) (p : ℕ) (emin emax : ℤ) (cfgs : List (CRTBasis × ℕ)) (b smax : ℕ)
    (xs ys : List Signed) : Option Signed :=
  roundingTestSignedB p emin emax (cfgs.map fun c => ozaki2EnclosureB mult c.1 c.2 (vals xs) (vals ys))
    (ozaki1ExactFallbackBS mult p emin emax b smax (vals xs) (vals ys)) (allNegZero xs ys)

theorem ozaki2CRBS_eq {p : ℕ} {emin emax : ℤ} (hp : 0 < p) (hle : emin ≤ emax) {mult : MatrixMultiplier}
    {b bound : ℕ} (hmult : mult.ExactOn b bound) {cfgs : List (CRTBasis × ℕ)} {smax : ℕ}
    {xs ys : List Signed}
    (hcfg : ∀ c ∈ cfgs, c.1.Valid ∧ (∀ m ∈ c.1.moduli, m ≤ 2 ^ (b + 1)) ∧
      2 * xs.length * (2 ^ c.2 * 2 ^ c.2) < c.1.modulus)
    (hlen : xs.length = ys.length) (hbound : xs.length * (2 ^ b * 2 ^ b) ≤ bound)
    (hvanish : ∃ s ∈ List.range' 1 smax, residualsVanish b s (vals xs) (vals ys) = true) :
    ozaki2CRBS mult p emin emax cfgs b smax xs ys = crSigned (roundRNE p emin emax) xs ys := by
  have hl : (vals xs).length = (vals ys).length := by rw [vals_length, vals_length, hlen]
  have hb : (vals xs).length * (2 ^ b * 2 ^ b) ≤ bound := by rw [vals_length]; exact hbound
  unfold ozaki2CRBS crSigned
  apply roundingTestSignedB_eq hp hle
  · intro e he t het
    obtain ⟨cfg, hmem, rfl⟩ := List.mem_map.mp he
    obtain ⟨hB, hmb, hrange⟩ := hcfg cfg hmem
    exact ozaki2EnclosureB_sound hmult hB hmb cfg.2 hl hb (by rw [vals_length]; exact hrange) het
  · exact ozaki1ExactFallbackBS_eq hmult p emin emax smax hl hb hvanish

end Ozaki
