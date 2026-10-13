import Ozaki.TruncatedSum
import Ozaki.Exact64
import Ozaki.SignOracle

/-! # Correctly rounded Ozaki-I with bounded registers

`ozaki1CRW` decides in exact rational arithmetic. Here every step after the engine is integer
arithmetic of bounded width, equal to it:

* the engine's slice products are integer terms `(v, gₜ + hᵤ)`, worth `v 2^(gₜ+hᵤ)`
  (`sliceProductInt`);
* **the check** (`ozaki1TestB`): each term rounded down to the window grid `q` by a shift, the
  results added in a two's-complement register of `W + bitlen (n (k + 2)) + 1` bits, which never
  wraps (`ozaki1TestB_register`); the bound `(s + 1) k 2^c + n 2^q` as integers at the grid
  `min q c`; both ends rounded with `roundExact`. It equals `roundEnclosure` of the window
  enclosure (`ozaki1TestB_eq`);
* **the exact path** (`ozaki1ExactFallbackB`): the `s²` slice products as integer terms, rounded by
  `roundSum` with windows of `bitlen (s² + 1) + p + 4` bits, equal to rounding the exact path's
  value (`ozaki1ExactFallbackB_eq`);
* `ozaki1CRB` is `ozaki1CRW` with `rnd = roundRNE p emin emax` (`ozaki1CRB_eq_CRW`), hence correctly
  rounded (`ozaki1CRB_eq`), for binary64 and binary32 inputs in particular (`ozaki1CRB64_eq`,
  `ozaki1CRB32_eq`).

No integer in it depends on the inputs' exponent range: window parts, window sums, residuals (each
at most a slice product, `sliceProductInt_natAbs_le`, at most the engine's budget) and query terms
are bounded by `W`, `p`, `b`, `s` and `k`; only exponents and the number of windows grow with it. -/

local notation "ℕ" => Nat
local notation "ℤ" => Int
local notation "ℚ" => Rat

namespace Ozaki

/-! ## Engine outputs as integer terms -/

/-- The engine's product of two slices as an integer term `(v, g + h)`, if the engine returned an
integer `v`. -/
def sliceProductInt (mult : MatrixMultiplier) (sl sl' : Slice) : Option (ℤ × ℤ) :=
  (mult sl.coeffs sl'.coeffs).bind fun v =>
    if v.den = 1 then some (v.num, sl.grid + sl'.grid) else none

theorem sliceProductInt_of_eq {mult : MatrixMultiplier} {sl sl' : Slice} {z : ℤ}
    (h : mult sl.coeffs sl'.coeffs = some (z : ℚ)) :
    sliceProductInt mult sl sl' = some (z, sl.grid + sl'.grid) := by
  unfold sliceProductInt
  rw [h, Option.bind_some, if_pos (Rat.den_intCast z), Rat.num_intCast]

/-- The exact integer term of two slices. -/
def exactSliceInt (sl sl' : Slice) : ℤ × ℤ := (dotZ sl.coeffs sl'.coeffs, sl.grid + sl'.grid)

theorem multiplier_exact {mult : MatrixMultiplier} {b bound s : ℕ} (hmult : mult.ExactOn b bound)
    {x y : List ℚ} (hlen : x.length = y.length) (hbound : x.length * (2 ^ b * 2 ^ b) ≤ bound)
    {sl sl' : Slice} (hsl : sl ∈ (split b s x).1) (hsl' : sl' ∈ (split b s y).1) :
    mult sl.coeffs sl'.coeffs = some (dotZ sl.coeffs sl'.coeffs : ℚ) ∧
      dotAbs sl.coeffs sl'.coeffs ≤ bound := by
  obtain ⟨_, hcx, _⟩ := split_length b s x
  obtain ⟨_, hcy, _⟩ := split_length b s y
  have hb : dotAbs sl.coeffs sl'.coeffs ≤ bound := by
    refine Nat.le_trans (dotAbs_le _ _ _ _ (split_coeff_bound b s x _ hsl)
      (split_coeff_bound b s y _ hsl')) ?_
    rw [hcx _ hsl]; exact hbound
  exact ⟨hmult _ _ (by rw [hcx _ hsl, hcy _ hsl', hlen]) (split_coeff_bound b s x _ hsl)
    (split_coeff_bound b s y _ hsl') hb, hb⟩

theorem sliceProductInt_exact {mult : MatrixMultiplier} {b bound s : ℕ} (hmult : mult.ExactOn b bound)
    {x y : List ℚ} (hlen : x.length = y.length) (hbound : x.length * (2 ^ b * 2 ^ b) ≤ bound)
    {sl sl' : Slice} (hsl : sl ∈ (split b s x).1) (hsl' : sl' ∈ (split b s y).1) :
    sliceProductInt mult sl sl' = some (exactSliceInt sl sl') :=
  sliceProductInt_of_eq (multiplier_exact hmult hlen hbound hsl hsl').1

/-- **Slice products are bounded by the engine's budget**, whatever the exponents. -/
theorem sliceProductInt_natAbs_le {mult : MatrixMultiplier} {b bound s : ℕ} (hmult : mult.ExactOn b bound)
    {x y : List ℚ} (hlen : x.length = y.length) (hbound : x.length * (2 ^ b * 2 ^ b) ≤ bound)
    {sl sl' : Slice} (hsl : sl ∈ (split b s x).1) (hsl' : sl' ∈ (split b s y).1) :
    (exactSliceInt sl sl').1.natAbs ≤ bound :=
  Nat.le_trans (natAbs_dotZ_le _ _) (multiplier_exact hmult hlen hbound hsl hsl').2

/-- The slice pair `(t, u)` of Ozaki-I as an integer term. -/
def pairInt (mult : MatrixMultiplier) (sx sy : List Slice) (p : ℕ × ℕ) : Option (ℤ × ℤ) :=
  sliceProductInt mult (sx.getD p.1 default) (sy.getD p.2 default)

/-- The exact integer term of the slice pair `(t, u)`. -/
def exactPairInt (sx sy : List Slice) (p : ℕ × ℕ) : ℤ × ℤ :=
  exactSliceInt (sx.getD p.1 default) (sy.getD p.2 default)

theorem tval_exactPairInt (sx sy : List Slice) (p : ℕ × ℕ) :
    tval (exactPairInt sx sy p) = exactTerm sx sy p := by
  unfold tval exactPairInt exactSliceInt exactTerm; simp only; rw [Rat.mul_comm]

theorem pairInt_exact {mult : MatrixMultiplier} {b bound s : ℕ} (hmult : mult.ExactOn b bound)
    {x y : List ℚ} (hlen : x.length = y.length) (hbound : x.length * (2 ^ b * 2 ^ b) ≤ bound)
    {p : ℕ × ℕ} (hp : p ∈ trianglePairs s) :
    pairInt mult (split b s x).1 (split b s y).1 p =
      some (exactPairInt (split b s x).1 (split b s y).1 p) := by
  obtain ⟨t, u⟩ := p
  have htu := mem_trianglePairs.mp hp
  obtain ⟨hlx, _, _⟩ := split_length b s x
  obtain ⟨hly, _, _⟩ := split_length b s y
  exact sliceProductInt_exact hmult hlen hbound (getD_mem (by omega)) (getD_mem (by omega))

/-! ## The window in integers -/

/-- `⌊z 2^(g − q)⌋`: a left shift, or an arithmetic right shift (floor division by `2^(q−g)`). -/
def floorPart (q : ℤ) (t : ℤ × ℤ) : ℤ :=
  if q ≤ t.2 then t.1 * 2 ^ (t.2 - q).toNat else t.1 / 2 ^ (q - t.2).toNat

theorem pow_toNat_mul {a b : ℤ} (h : b ≤ a) :
    (2 : ℚ) ^ (((a - b).toNat : ℕ) : ℤ) * 2 ^ b = 2 ^ a := by
  rw [← two_pow_add]; congr 1; omega

theorem floor_floorPart (q : ℤ) (t : ℤ × ℤ) : (tval t * 2 ^ (-q)).floor = floorPart q t := by
  obtain ⟨z, g⟩ := t
  unfold tval floorPart; simp only
  split
  · rename_i h
    have : (z : ℚ) * 2 ^ g * 2 ^ (-q) = ((z * 2 ^ (g - q).toNat : ℤ) : ℚ) := by
      rw [Rat.intCast_mul, intCast_two_pow, Rat.mul_assoc, ← two_pow_add]; congr 2; omega
    rw [this, Rat.floor_intCast]
  · rename_i h
    generalize hd : (q - g).toNat = d
    have hP : (0 : ℤ) < 2 ^ d := by
      have := Nat.two_pow_pos d
      have h2 : ((2 ^ d : ℕ) : ℤ) = (2 : ℤ) ^ d := by rw [Int.natCast_pow]; rfl
      omega
    have h1 := Int.ediv_mul_le z (b := 2 ^ d) (by omega)
    have h2 := Int.lt_ediv_add_one_mul_self z (b := 2 ^ d) hP
    generalize z / 2 ^ d = Q at h1 h2
    have hv : (z : ℚ) * 2 ^ g * 2 ^ (-q) * 2 ^ (d : ℤ) = z := by
      rw [Rat.mul_assoc, Rat.mul_assoc, ← two_pow_add, ← two_pow_add,
        show g + (-q + (d : ℤ)) = 0 by omega, two_pow_zero, Rat.mul_one]
    have hpd := two_pow_pos (d : ℤ)
    have h1' : ((Q : ℚ)) * 2 ^ (d : ℤ) ≤ z := by
      rw [← intCast_two_pow, ← Rat.intCast_mul]; exact Rat.intCast_le_intCast.mpr h1
    have h2' : (z : ℚ) < ((Q : ℚ) + 1) * 2 ^ (d : ℤ) := by
      rw [← intCast_two_pow, ← Rat.intCast_one, ← Rat.intCast_add, ← Rat.intCast_mul]
      exact Rat.intCast_lt_intCast.mpr h2
    generalize (z : ℚ) * 2 ^ g * 2 ^ (-q) = v at hv
    apply floor_eq_of
    · apply Classical.byContradiction; intro hn
      have := Rat.mul_lt_mul_of_pos_right (Rat.not_le.mp hn) hpd; grind
    · apply Classical.byContradiction; intro hn
      have := Rat.mul_le_mul_of_nonneg_right (Rat.not_lt.mp hn) (Rat.le_of_lt hpd); grind

theorem floorGrid_tval (q : ℤ) (t : ℤ × ℤ) : floorGrid q (tval t) = (floorPart q t : ℚ) * 2 ^ q := by
  unfold floorGrid; rw [floor_floorPart]

theorem truncatedSum_int (q : ℤ) (ts : List (ℤ × ℤ)) :
    truncatedSum q (ts.map tval) = (((ts.map (floorPart q)).sum : ℤ) : ℚ) * 2 ^ q := by
  induction ts with
  | nil => simp [truncatedSum]
  | cons t ts ih =>
    simp only [truncatedSum, List.map_cons, List.sum_cons] at ih ⊢
    rw [ih, floorGrid_tval, Rat.intCast_add, Rat.add_mul]

theorem abs_floor_le (v : ℚ) : Rat.abs ((v.floor : ℤ) : ℚ) ≤ Rat.abs v + 1 := by
  obtain ⟨f1, f2⟩ := floor_frac v
  rw [abs_le_iff]
  have := neg_abs_le v
  have := le_abs_self v
  constructor <;> grind

/-- A term below `k 2^(q + W)` in magnitude has a window part below `k 2^W + 2`. -/
theorem natAbs_floorPart_lt {q : ℤ} {W k : ℕ} {t : ℤ × ℤ}
    (h : Rat.abs (tval t) ≤ k * 2 ^ (q + W)) : (floorPart q t).natAbs < k * 2 ^ W + 2 := by
  have h1 := abs_floor_le (tval t * 2 ^ (-q))
  rw [floor_floorPart, abs_intCast, abs_mul_two_pow] at h1
  have h2 := Rat.mul_le_mul_of_nonneg_right h (Rat.le_of_lt (two_pow_pos (-q)))
  have h3 : (k : ℚ) * 2 ^ (q + W) * 2 ^ (-q) = ((k * 2 ^ W : ℕ) : ℚ) := by
    rw [Rat.mul_assoc, ← two_pow_add, show q + W + -q = ((W : ℕ) : ℤ) by omega, two_pow_natCast,
      Rat.natCast_mul]
  rw [h3] at h2
  have : (((floorPart q t).natAbs : ℕ) : ℚ) < ((k * 2 ^ W + 2 : ℕ) : ℚ) := by
    rw [Rat.natCast_add]; have : ((2 : ℕ) : ℚ) = 2 := rfl; grind
  exact_mod_cast this

/-! ## The enclosure test in integers -/

/-- **`roundEnclosure` in integers**: `H = N 2^q`, `B = K 2^c + n 2^q`, both ends rounded at the grid
`min q c` with `roundExact`. -/
def roundEnclosureB (p : ℕ) (emin emax : ℤ) (N q K c : ℤ) (n : ℕ) : Option ℚ :=
  let q0 := min q c
  let H := N * 2 ^ (q - q0).toNat
  let B := K * 2 ^ (c - q0).toNat + (n : ℤ) * 2 ^ (q - q0).toNat
  match roundExact p emin emax (H - B) q0, roundExact p emin emax (H + B) q0 with
  | some w, some w' => if w = w' then some w else none
  | _, _ => none

theorem roundEnclosureB_eq (p : ℕ) (emin emax N q K c : ℤ) (n : ℕ) :
    roundEnclosureB p emin emax N q K c n =
      roundEnclosure (roundRNE p emin emax) ((N : ℚ) * 2 ^ q) ((K : ℚ) * 2 ^ c + (n : ℚ) * 2 ^ q) := by
  have eq := pow_toNat_mul (Int.min_le_left q c)
  have ec := pow_toNat_mul (Int.min_le_right q c)
  have hn : (((n : ℤ)) : ℚ) = (n : ℚ) := Rat.intCast_natCast n
  have e1 : (((N * 2 ^ (q - min q c).toNat -
      (K * 2 ^ (c - min q c).toNat + (n : ℤ) * 2 ^ (q - min q c).toNat) : ℤ) : ℚ)) *
        2 ^ (min q c) = (N : ℚ) * 2 ^ q - ((K : ℚ) * 2 ^ c + (n : ℚ) * 2 ^ q) := by
    simp only [Rat.intCast_sub, Rat.intCast_add, Rat.intCast_mul, intCast_two_pow, hn]
    rw [← eq, ← ec]; grind
  have e2 : (((N * 2 ^ (q - min q c).toNat +
      (K * 2 ^ (c - min q c).toNat + (n : ℤ) * 2 ^ (q - min q c).toNat) : ℤ) : ℚ)) *
        2 ^ (min q c) = (N : ℚ) * 2 ^ q + ((K : ℚ) * 2 ^ c + (n : ℚ) * 2 ^ q) := by
    simp only [Rat.intCast_add, Rat.intCast_mul, intCast_two_pow, hn]
    rw [← eq, ← ec]; grind
  unfold roundEnclosureB roundEnclosure
  simp only
  rw [roundExact_eq, roundExact_eq, e1, e2]
  generalize roundRNE p emin emax ((N : ℚ) * 2 ^ q - ((K : ℚ) * 2 ^ c + (n : ℚ) * 2 ^ q)) = r1
  generalize roundRNE p emin emax ((N : ℚ) * 2 ^ q + ((K : ℚ) * 2 ^ c + (n : ℚ) * 2 ^ q)) = r2
  cases r1 <;> cases r2 <;> rfl

/-- **The bounded check for `s` slices**: the engine's slice products as integer terms, the window
sum in a `W + bitlen (n (k + 2)) + 1`-bit register, and the integer enclosure test. -/
def ozaki1TestB (mult : MatrixMultiplier) (p : ℕ) (emin emax : ℤ) (b s W : ℕ) (x y : List ℚ) :
    Option ℚ :=
  match (trianglePairs s).mapM (pairInt mult (split b s x).1 (split b s y).1) with
  | none => none
  | some ts =>
    roundEnclosureB p emin emax
      (fixedSum (W + bitlen (ts.length * (x.length + 2)) + 1)
        (ts.map (floorPart (truncationGrid b W x y))))
      (truncationGrid b W x y) (((s + 1) * x.length : ℕ) : ℤ)
      (splitExp b x + splitExp b y - s * (b + 1)) ts.length

theorem exactTerms_eq_map (b s : ℕ) (x y : List ℚ) :
    exactTerms b s x y =
      ((trianglePairs s).map (exactPairInt (split b s x).1 (split b s y).1)).map tval := by
  unfold exactTerms
  rw [List.map_map]
  exact List.map_congr_left fun p _ => (tval_exactPairInt _ _ p).symm

/-- **The window register never wraps**: the window parts of the `n` slice products add up, in
magnitude, below `2^(W + bitlen (n (k + 2)))`. -/
theorem ozaki1TestB_register (b s W : ℕ) (x y : List ℚ) :
    ((((trianglePairs s).map (exactPairInt (split b s x).1 (split b s y).1)).map
        (floorPart (truncationGrid b W x y))).map Int.natAbs).sum <
      2 ^ (W + bitlen ((trianglePairs s).length * (x.length + 2))) := by
  have hpart : ∀ z ∈ ((trianglePairs s).map (exactPairInt (split b s x).1 (split b s y).1)).map
      (floorPart (truncationGrid b W x y)), z.natAbs < x.length * 2 ^ W + 2 := by
    intro z hz
    obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hz
    obtain ⟨pr, hpr, rfl⟩ := List.mem_map.mp ht
    apply natAbs_floorPart_lt
    rw [tval_exactPairInt]
    have := abs_exactTerm_le b s x y hpr
    rw [show truncationGrid b W x y + (W : ℤ) = splitExp b x + splitExp b y by unfold truncationGrid; omega]
    exact this
  have h1 := sum_natAbs_le hpart
  simp only [List.length_map] at h1
  have h2 : x.length * 2 ^ W + 2 ≤ (x.length + 2) * 2 ^ W := by
    have := Nat.two_pow_pos W
    rw [Nat.add_mul]; omega
  have h3 := Nat.mul_le_mul_left (trianglePairs s).length h2
  rw [← Nat.mul_assoc] at h3
  have h4 := Nat.mul_lt_mul_of_pos_right
    (lt_two_pow_bitlen ((trianglePairs s).length * (x.length + 2))) (Nat.two_pow_pos W)
  rw [← Nat.pow_add, Nat.add_comm (bitlen _)] at h4
  omega

/-- **The bounded check is the enclosure test** on the window enclosure, with
`rnd = roundRNE p emin emax`. -/
theorem ozaki1TestB_eq {mult : MatrixMultiplier} {b bound : ℕ} (hmult : mult.ExactOn b bound)
    (p : ℕ) (emin emax : ℤ) (s W : ℕ) {x y : List ℚ} (hlen : x.length = y.length)
    (hbound : x.length * (2 ^ b * 2 ^ b) ≤ bound) :
    ozaki1TestB mult p emin emax b s W x y =
      (ozaki1TruncatedEnclosure mult b s W x y).bind
        fun e => roundEnclosure (roundRNE p emin emax) e.1 e.2 := by
  unfold ozaki1TestB ozaki1TruncatedEnclosure
  rw [mapM_eq_some_map fun _ hp => pairInt_exact hmult hlen hbound hp,
    ozaki1Terms_eq hmult s hlen hbound, Option.map_some, Option.bind_some]
  simp only
  rw [fixedSum_eq (by omega) (by
      rw [List.length_map, show ∀ a c : ℕ, a + c + 1 - 1 = a + c from fun _ _ => rfl]
      exact ozaki1TestB_register b s W x y),
    roundEnclosureB_eq, exactTerms_eq_map, truncatedSum_int, List.length_map, List.length_map]
  congr 2
  unfold ozaki1Bound
  rw [Rat.intCast_natCast, Rat.natCast_mul]
  all_goals simp only [List.length_map]

/-! ## The exact path in integers -/

/-- **The exact path with bounded registers**: the first slice count up to `smax` that leaves
nothing over, all `s²` slice products from the engine as integer terms, rounded by `roundSum` with
windows of `bitlen (s² + 1) + p + 4` bits. -/
def ozaki1ExactFallbackB (mult : MatrixMultiplier) (p : ℕ) (emin emax : ℤ) (b smax : ℕ) (x y : List ℚ) :
    Option ℚ :=
  match (List.range' 1 smax).find? fun s => residualsVanish b s x y with
  | some s =>
    match (slicePairs (split b s x).1 (split b s y).1).mapM
        (fun pr => sliceProductInt mult pr.1 pr.2) with
    | some ts => roundSum p emin emax (bitlen (ts.length + 1) + p + 4) ts
    | none => none
  | none => none

theorem mem_slicePairs {sx sy : List Slice} {pr : Slice × Slice} (h : pr ∈ slicePairs sx sy) :
    pr.1 ∈ sx ∧ pr.2 ∈ sy := by
  obtain ⟨sl, hsl, hp⟩ := List.mem_flatMap.mp h
  obtain ⟨sl', hsl', rfl⟩ := List.mem_map.mp hp
  exact ⟨hsl, hsl'⟩

theorem ozaki1ExactFallbackB_eq {mult : MatrixMultiplier} {b bound : ℕ} (hmult : mult.ExactOn b bound)
    (p : ℕ) (emin emax : ℤ) (smax : ℕ) {x y : List ℚ} (hlen : x.length = y.length)
    (hbound : x.length * (2 ^ b * 2 ^ b) ≤ bound) :
    ozaki1ExactFallbackB mult p emin emax b smax x y =
      (ozaki1ExactFallback mult b smax x y).bind (roundRNE p emin emax) := by
  unfold ozaki1ExactFallbackB ozaki1ExactFallback
  cases (List.range' 1 smax).find? fun s => residualsVanish b s x y with
  | none => rfl
  | some s =>
    simp only
    unfold ozaki1Full
    rw [mapM_eq_some_map (g := fun pr => exactSliceInt pr.1 pr.2) fun pr hpr =>
        sliceProductInt_exact hmult hlen hbound (mem_slicePairs hpr).1 (mem_slicePairs hpr).2,
      mapM_eq_some_map (f := fun pr : Slice × Slice => fullTerm mult pr.1 pr.2)
        (g := fun pr : Slice × Slice => tval (exactSliceInt pr.1 pr.2)) fun pr hpr => by
        unfold fullTerm
        rw [(multiplier_exact hmult hlen hbound (mem_slicePairs hpr).1 (mem_slicePairs hpr).2).1]
        unfold tval exactSliceInt; simp only [Option.map_some]; rw [Rat.mul_comm]]
    simp only [Option.map_some, Option.bind_some]
    rw [roundSum_eq _ _ (by omega)]
    unfold tsum
    rw [List.map_map]
    rfl

/-! ## The scheme -/

/-- **Correctly rounded Ozaki-I with bounded registers**: the bounded checks for the slice counts
`ss` in turn, then the bounded exact path. -/
def ozaki1CRB (mult : MatrixMultiplier) (p : ℕ) (emin emax : ℤ) (b W : ℕ) (ss : List ℕ) (smax : ℕ)
    (x y : List ℚ) : Option ℚ :=
  match ss with
  | [] => ozaki1ExactFallbackB mult p emin emax b smax x y
  | s :: ss =>
    match ozaki1TestB mult p emin emax b s W x y with
    | some w => some w
    | none => ozaki1CRB mult p emin emax b W ss smax x y

/-- **The bounded scheme is the rational one** with `rnd = roundRNE p emin emax`. -/
theorem ozaki1CRB_eq_CRW {mult : MatrixMultiplier} {b bound : ℕ} (hmult : mult.ExactOn b bound)
    (p : ℕ) (emin emax : ℤ) (W : ℕ) (smax : ℕ) {x y : List ℚ} (hlen : x.length = y.length)
    (hbound : x.length * (2 ^ b * 2 ^ b) ≤ bound) :
    ∀ ss : List ℕ, ozaki1CRB mult p emin emax b W ss smax x y =
      ozaki1CRW mult (roundRNE p emin emax) b W ss smax x y
  | [] => by
    unfold ozaki1CRB ozaki1CRW
    rw [ozaki1ExactFallbackB_eq hmult p emin emax smax hlen hbound]
    rfl
  | s :: ss => by
    have ih := ozaki1CRB_eq_CRW hmult p emin emax W smax hlen hbound ss
    unfold ozaki1CRW at ih ⊢
    unfold ozaki1CRB
    rw [ozaki1TestB_eq hmult p emin emax s W hlen hbound, List.map_cons]
    unfold roundingTest
    rw [← ih]
    cases (ozaki1TruncatedEnclosure mult b s W x y).bind
      (fun e => roundEnclosure (roundRNE p emin emax) e.1 e.2) <;> rfl

/-- **Correctly rounded Ozaki-I with bounded registers is correctly rounded**: on an exact engine,
for every input whose exact path ends within `smax` slices. -/
theorem ozaki1CRB_eq {p : ℕ} {emin emax : ℤ} (hp : 0 < p) (hle : emin ≤ emax) {mult : MatrixMultiplier}
    {b bound : ℕ} (hmult : mult.ExactOn b bound) (W : ℕ) (ss : List ℕ) {smax : ℕ}
    {x y : List ℚ} (hlen : x.length = y.length) (hbound : x.length * (2 ^ b * 2 ^ b) ≤ bound)
    (hvanish : ∃ s ∈ List.range' 1 smax, residualsVanish b s x y = true) :
    ozaki1CRB mult p emin emax b W ss smax x y = roundRNE p emin emax (dot x y) := by
  rw [ozaki1CRB_eq_CRW hmult p emin emax W smax hlen hbound ss]
  exact ozaki1CRW_eq (roundRNE_nearest hp hle) (roundRNE_intervals hp) hmult W ss hlen hbound
    hvanish

/-- **Binary64 inputs**: correctly rounded to binary64 with bounded registers, when
`smax (b + 1) > 2098`. -/
theorem ozaki1CRB64_eq {mult : MatrixMultiplier} {b bound : ℕ} (hmult : mult.ExactOn b bound) (W : ℕ)
    (ss : List ℕ) {smax : ℕ} (hb : b ≤ 1025) (hsmax : 2098 < smax * (b + 1)) {x y : List ℚ}
    (hlen : x.length = y.length) (hbound : x.length * (2 ^ b * 2 ^ b) ≤ bound)
    (hx : ∀ a ∈ x, Binary64Value a) (hy : ∀ a ∈ y, Binary64Value a) :
    ozaki1CRB mult 53 (-1022) 1023 b W ss smax x y = rne64 (dot x y) :=
  ozaki1CRB_eq (by decide) (by decide) hmult W ss hlen hbound (vanish64 hb hsmax hx hy)

/-- **Binary32 inputs**: correctly rounded to binary32 with bounded registers, when
`smax (b + 1) > 277`. -/
theorem ozaki1CRB32_eq {mult : MatrixMultiplier} {b bound : ℕ} (hmult : mult.ExactOn b bound) (W : ℕ)
    (ss : List ℕ) {smax : ℕ} (hb : b ≤ 129) (hsmax : 277 < smax * (b + 1)) {x y : List ℚ}
    (hlen : x.length = y.length) (hbound : x.length * (2 ^ b * 2 ^ b) ≤ bound)
    (hx : ∀ a ∈ x, Binary32Value a) (hy : ∀ a ∈ y, Binary32Value a) :
    ozaki1CRB mult 24 (-126) 127 b W ss smax x y = rne32Q (dot x y) :=
  ozaki1CRB_eq (by decide) (by decide) hmult W ss hlen hbound (vanish32Q hb hsmax hx hy)

/-- **The exact path's integer terms are bounded by the engine's budget**: every term handed to
`roundSum` has `|v| ≤ budget`, and `roundSum`'s own registers are bounded by its window, `p` and the
number of terms (`topDownSum_parts_lt`, `fixedSum_natAbs_le`, `query_natAbs_lt`). -/
theorem ozaki1ExactFallbackB_terms {mult : MatrixMultiplier} {b bound : ℕ} (hmult : mult.ExactOn b bound)
    {s : ℕ} {x y : List ℚ} (hlen : x.length = y.length)
    (hbound : x.length * (2 ^ b * 2 ^ b) ≤ bound) :
    (slicePairs (split b s x).1 (split b s y).1).mapM (fun pr => sliceProductInt mult pr.1 pr.2) =
        some ((slicePairs (split b s x).1 (split b s y).1).map fun pr => exactSliceInt pr.1 pr.2) ∧
      ∀ pr ∈ slicePairs (split b s x).1 (split b s y).1, (exactSliceInt pr.1 pr.2).1.natAbs ≤ bound :=
  ⟨mapM_eq_some_map fun _ hpr =>
      sliceProductInt_exact hmult hlen hbound (mem_slicePairs hpr).1 (mem_slicePairs hpr).2,
    fun _ hpr =>
      sliceProductInt_natAbs_le hmult hlen hbound (mem_slicePairs hpr).1 (mem_slicePairs hpr).2⟩

/-! ## Examples, checked by the kernel -/

/-- The window check settles `x · y` for a non-dyadic product with `4` slices and `W = 40`. -/
example : ozaki1TestB exactMultiplier 24 (-126) 127 8 4 40 [3, 5/4, -7/8] [1/2, 3, 2/3] =
    rne32Q (dot [3, 5/4, -7/8] [1/2, 3, 2/3]) := by decide +kernel

/-- A binary32 tie with a heavy cancellation, `2^40 + 1 + 2^-24 − 2^40`: two slices do not settle
it, and the bounded exact path rounds it to the even `1`. -/
example : ozaki1CRB exactMultiplier 24 (-126) 127 8 20 [2] 40 [2 ^ 40, 1, 2 ^ (-24 : ℤ), -(2 ^ 40)]
      [1, 1, 1, 1] = some 1 ∧
    rne32Q (dot [2 ^ 40, 1, 2 ^ (-24 : ℤ), -(2 ^ 40)] [1, 1, 1, 1]) = some 1 := by decide +kernel

end Ozaki
