import Ozaki.IEEEValue
import Ozaki.BoundedOzaki
import Ozaki.Native

/-! # Dot products with IEEE special values

**The specification** (`dotIEEE`). IEEE 754 recommends a dot-product reduction but leaves its order
of evaluation and the precision of its intermediate results to the implementation. A correctly
rounded dot product reads it as "exact, then round once", with IEEE's special cases:

* NaN if an input is NaN, a product is `Inf · 0`, or the products include `+Inf` and `−Inf`;
* otherwise `±Inf` if some product is infinite;
* otherwise the exact sum rounded to nearest even, `±Inf` when its rounding exceeds the largest
  finite value, and a zero result signed as in `crSigned`: the exact sum's sign when it is nonzero,
  and for an exact zero `−0` only when every product is `−0`.

**Correctly rounded schemes with special values** (`crIEEE`). Scan the inputs for special values;
if there are none, run a finite correctly rounded scheme, which returns the round to nearest even
of `x · y` or `none` on overflow, and sign its result: a nonzero result by its own sign, a zero
result or an overflow by the exact sum's sign, which a sign oracle supplies. `crIEEE_eq`: whenever
the scheme is correctly rounded and the oracle is right on the finite inputs, the wrapper meets the
specification for every input. `exactSignB` is such an oracle in bounded integer arithmetic: the
sign of the exact fallback's integer slice products by the top-down summation of `Ozaki.SignOracle`
(`exactSignB_eq`).

**The other versions** with special values, agreeing with the rational ones on finite results:
native dot products (`nativeDotIEEE`, products rounded and added left to right from `+0` with IEEE
operations, `nativeDotIEEE_fin`), plain Ozaki-I (`ozaki1IEEE`, the scaled slice products added with
IEEE addition, `ozaki1IEEE_fin`) and plain Ozaki-II (`ozaki2IEEE`, one IEEE rounding,
`ozaki2IEEE_fin`), each with the specification's special cases on special inputs. -/

local notation "ℕ" => Nat
local notation "ℤ" => Int
local notation "ℚ" => Rat

namespace Ozaki

variable {p : ℕ} {emin emax : ℤ}

/-! ## The specification -/

/-- The special result of a dot product: NaN when a product is NaN (a NaN input or `Inf · 0`) or the
products include `+Inf` and `−Inf`, `±Inf` when some product is infinite, `none` when every product
is finite. -/
def dotSpecial (xs ys : List FVal) : Option FVal :=
  let ps := List.zipWith mulX xs ys
  if ps.contains .nan then some .nan
  else if ps.contains (.inf false) && ps.contains (.inf true) then some .nan
  else if ps.contains (.inf false) then some (.inf false)
  else if ps.contains (.inf true) then some (.inf true)
  else none

/-- **The IEEE correctly rounded dot product**: the special cases of `dotSpecial`, otherwise the exact
sum rounded once to nearest even, `±Inf` on overflow, and the signed zero of `crSigned`. -/
def dotIEEE (p : ℕ) (emin emax : ℤ) (xs ys : List FVal) : FVal :=
  match dotSpecial xs ys with
  | some v => v
  | none =>
    match finParts xs, finParts ys with
    | some sx, some sy => roundF p emin emax (dot (vals sx) (vals sy)) (allNegZero sx sy)
    | _, _ => .nan

theorem finParts_map (sx : List Signed) : finParts (sx.map .fin) = some sx := by
  induction sx with
  | nil => rfl
  | cons s sx ih =>
    simp only [finParts, List.map_cons, List.mapM_cons, finPart] at ih ⊢
    rw [ih]; rfl

theorem dotSpecial_map : ∀ sx sy : List Signed, dotSpecial (sx.map .fin) (sy.map .fin) = none
  | [], _ => rfl
  | _ :: _, [] => rfl
  | s :: sx, t :: sy => by
    have ih := dotSpecial_map sx sy
    unfold dotSpecial at ih ⊢
    simp only [List.map_cons, List.zipWith_cons_cons, List.contains_cons] at ih ⊢
    simp only [mulX]
    split at ih <;> simp_all

/-- On finite inputs the specification is `crSigned` with the round to nearest even, and `±Inf` on
overflow. -/
theorem dotIEEE_fin (sx sy : List Signed) :
    dotIEEE p emin emax (sx.map .fin) (sy.map .fin) =
      match crSigned (roundRNE p emin emax) sx sy with
      | some w => .fin w
      | none => .inf (decide (dot (vals sx) (vals sy) < 0)) := by
  unfold dotIEEE
  rw [dotSpecial_map, finParts_map, finParts_map]
  simp only
  unfold roundF crSigned
  cases roundRNE p emin emax (dot (vals sx) (vals sy)) <;> rfl

/-! ## Correctly rounded schemes with special values -/

/-- The finite part of `crIEEE`: a nonzero result `r` signed by its own sign, a zero result by the
exact sum's sign `σ` (or by `z` when `σ = 0`), and an overflow (`none`) as the infinity of sign
`σ`. -/
def crFinite (r : Option ℚ) (σ : ℤ) (z : Bool) : FVal :=
  match r with
  | some r => if r = 0 then .fin ⟨0, if σ = 0 then z else decide (σ < 0)⟩
    else .fin ⟨r, decide (r < 0)⟩
  | none => .inf (decide (σ < 0))

/-- **A correctly rounded scheme with IEEE special values**: the special cases of `dotSpecial`,
otherwise the finite scheme's result, signed with the sign oracle `sgn` where its own sign does not
decide (`crFinite`). -/
def crIEEE (scheme : List ℚ → List ℚ → Option ℚ) (sgn : List ℚ → List ℚ → ℤ)
    (xs ys : List FVal) : FVal :=
  match dotSpecial xs ys with
  | some v => v
  | none =>
    match finParts xs, finParts ys with
    | some sx, some sy =>
      crFinite (scheme (vals sx) (vals sy)) (sgn (vals sx) (vals sy)) (allNegZero sx sy)
    | _, _ => .nan

theorem sgnQ_lt_zero_iff (q : ℚ) : sgnQ q < 0 ↔ q < 0 := by
  have := sgnQ_nonneg_iff q
  constructor
  · intro h; exact Rat.not_le.mp fun hq => absurd (this.mpr hq) (by omega)
  · intro h; exact Int.not_le.mp fun hs => absurd (this.mp hs) (Rat.not_le.mpr h)

/-- With the round to nearest even and the exact sign, `crFinite` is the IEEE rounding. -/
theorem crFinite_eq (hp : 0 < p) (hle : emin ≤ emax) (q : ℚ) (z : Bool) :
    crFinite (roundRNE p emin emax q) (sgnQ q) z = roundF p emin emax q z := by
  have hneg : decide (sgnQ q < 0) = decide (q < 0) := by
    simp only [decide_eq_decide]; exact sgnQ_lt_zero_iff q
  unfold crFinite roundF
  cases hr : roundRNE p emin emax q with
  | none => simp only; rw [hneg]
  | some r =>
    simp only
    by_cases hr0 : r = 0
    · subst hr0
      rw [if_pos rfl]
      unfold sumNeg
      by_cases hq : q = 0
      · rw [if_pos ((sgnQ_eq_zero_iff q).mpr hq), if_pos hq]
      · rw [if_neg (fun h => hq ((sgnQ_eq_zero_iff q).mp h)), if_neg hq, hneg]
    · rw [if_neg hr0]
      obtain ⟨hq0, hs⟩ :=
        sign_of_round (roundRNE_nearest hp hle) (roundRNE_zero' p emin emax) hr hr0
      unfold sumNeg; rw [if_neg hq0, hs]

/-- **Correctly rounded schemes meet the IEEE specification.** If on the finite parts of the inputs
the scheme returns the round to nearest even of `x · y` and the oracle its sign, the scheme with
special values returns `dotIEEE` for every input. -/
theorem crIEEE_eq (hp : 0 < p) (hle : emin ≤ emax) {scheme : List ℚ → List ℚ → Option ℚ}
    {sgn : List ℚ → List ℚ → ℤ} {xs ys : List FVal}
    (h : ∀ sx sy, finParts xs = some sx → finParts ys = some sy →
      scheme (vals sx) (vals sy) = roundRNE p emin emax (dot (vals sx) (vals sy)) ∧
        sgn (vals sx) (vals sy) = sgnQ (dot (vals sx) (vals sy))) :
    crIEEE scheme sgn xs ys = dotIEEE p emin emax xs ys := by
  unfold crIEEE dotIEEE
  cases dotSpecial xs ys with
  | some v => rfl
  | none =>
    simp only
    cases hx : finParts xs with
    | none => rfl
    | some sx =>
      cases hy : finParts ys with
      | none => rfl
      | some sy =>
        simp only
        obtain ⟨h1, h2⟩ := h sx sy hx hy
        rw [h1, h2, crFinite_eq hp hle]

/-! ## Inputs of a format -/

theorem finParts_cons {a : FVal} {xs : List FVal} {sx : List Signed}
    (h : finParts (a :: xs) = some sx) :
    ∃ s sx', a = .fin s ∧ finParts xs = some sx' ∧ sx = s :: sx' := by
  unfold finParts at h
  rw [List.mapM_cons] at h
  cases a with
  | fin s =>
    cases hr : xs.mapM finPart with
    | none => simp [finPart, hr] at h
    | some sx' =>
      simp only [finPart, hr, Option.bind_eq_bind, Option.bind_some, Option.pure_def,
        Option.some.injEq] at h
      exact ⟨s, sx', rfl, hr, h.symm⟩
  | inf n => simp [finPart] at h
  | nan => simp [finPart] at h

/-- The finite parts of a vector have its length. -/
theorem finParts_length : ∀ {xs : List FVal} {sx : List Signed}, finParts xs = some sx →
    (vals sx).length = xs.length
  | [], sx, h => by
    simp only [finParts, List.mapM_nil, Option.pure_def, Option.some.injEq] at h
    subst h; rfl
  | a :: xs, sx, h => by
    obtain ⟨s, sx', rfl, h', rfl⟩ := finParts_cons h
    have := finParts_length h'
    simp only [vals, List.length_map] at this ⊢
    simp [this]

/-- The finite parts of a vector of the format are values of the format. -/
theorem finParts_inFormat : ∀ {xs : List FVal} {sx : List Signed},
    (∀ a ∈ xs, a.InFormat p emin emax) → finParts xs = some sx →
    ∀ v ∈ vals sx, FormatValue p emin emax v
  | [], sx, _, h => by
    simp only [finParts, List.mapM_nil, Option.pure_def, Option.some.injEq] at h
    subst h; simp [vals]
  | a :: xs, sx, hx, h => by
    obtain ⟨s, sx', rfl, h', rfl⟩ := finParts_cons h
    intro v hv
    simp only [vals, List.map_cons, List.mem_cons] at hv
    rcases hv with rfl | hv
    · exact (hx _ List.mem_cons_self).1
    · exact finParts_inFormat (fun a ha => hx a (List.mem_cons_of_mem _ ha)) h' v hv

/-! ## The sign oracle in bounded arithmetic -/

/-- **The sign of `x · y` from the exact fallback**: at the first slice count up to `smax` that
leaves nothing over, the sign of the integer slice products of the matrix multiplier by the top-down
summation `signSum`; `0` if there is no such slice count or the matrix multiplier fails. -/
def exactSignB (mult : MatrixMultiplier) (b smax : ℕ) (x y : List ℚ) : ℤ :=
  match (List.range' 1 smax).find? fun s => residualsVanish b s x y with
  | some s =>
    match (slicePairs (split b s x).1 (split b s y).1).mapM
        (fun pr => sliceProductInt mult pr.1 pr.2) with
    | some ts => signSum (bitlen ts.length + 64) ts
    | none => 0
  | none => 0

/-- **The oracle is the exact sign** on any exact matrix multiplier, when the inputs leave nothing
over after at most `smax` slices. -/
theorem exactSignB_eq {mult : MatrixMultiplier} {b bound smax : ℕ} (hmult : mult.ExactOn b bound)
    {x y : List ℚ} (hlen : x.length = y.length) (hbound : x.length * (2 ^ b * 2 ^ b) ≤ bound)
    (hvanish : ∃ s ∈ List.range' 1 smax, residualsVanish b s x y = true) :
    exactSignB mult b smax x y = sgnQ (dot x y) := by
  have hex := ozaki1ExactFallback_eq hmult hlen hbound hvanish
  unfold ozaki1ExactFallback at hex
  unfold exactSignB
  cases hf : (List.range' 1 smax).find? fun s => residualsVanish b s x y with
  | none => rw [hf] at hex; simp at hex
  | some s =>
    rw [hf] at hex
    simp only at hex ⊢
    unfold ozaki1Full at hex
    rw [mapM_eq_some_map (g := fun pr => exactSliceInt pr.1 pr.2) fun pr hpr =>
        sliceProductInt_exact hmult hlen hbound (mem_slicePairs hpr).1 (mem_slicePairs hpr).2]
    rw [mapM_eq_some_map (f := fun pr : Slice × Slice => fullTerm mult pr.1 pr.2)
        (g := fun pr : Slice × Slice => tval (exactSliceInt pr.1 pr.2)) fun pr hpr => by
        unfold fullTerm
        rw [(multiplier_exact hmult hlen hbound (mem_slicePairs hpr).1 (mem_slicePairs hpr).2).1]
        unfold tval exactSliceInt; simp only [Option.map_some]; rw [Rat.mul_comm]] at hex
    simp only [Option.map_some, Option.some.injEq] at hex
    simp only
    rw [signSum_eq (by omega), ← hex]
    unfold tsum
    rw [List.map_map]
    rfl

/-- **`crIEEE` with the exact-fallback sign oracle, for inputs of a format**: the hypotheses of
`crIEEE_eq` from the finite scheme's theorem on vectors of the format whose length is the inputs'.
This is how every correctly rounded scheme is given special values. -/
theorem crIEEE_exactSign (hp : 0 < p) (hle : emin ≤ emax) {scheme : List ℚ → List ℚ → Option ℚ}
    {mult : MatrixMultiplier} {b smax : ℕ} (hmult : ∀ B, mult.ExactOn b B) {xs ys : List FVal}
    (hvanish : ∀ x y : List ℚ, (∀ a ∈ x, FormatValue p emin emax a) →
      (∀ a ∈ y, FormatValue p emin emax a) →
      ∃ s ∈ List.range' 1 smax, residualsVanish b s x y = true)
    (hscheme : ∀ x y : List ℚ, (∀ a ∈ x, FormatValue p emin emax a) →
      (∀ a ∈ y, FormatValue p emin emax a) → x.length = xs.length → y.length = xs.length →
      scheme x y = roundRNE p emin emax (dot x y))
    (hx : ∀ a ∈ xs, a.InFormat p emin emax) (hy : ∀ a ∈ ys, a.InFormat p emin emax)
    (hlen : xs.length = ys.length) :
    crIEEE scheme (exactSignB mult b smax) xs ys = dotIEEE p emin emax xs ys := by
  apply crIEEE_eq hp hle
  intro sx sy hsx hsy
  have hfx := finParts_inFormat hx hsx
  have hfy := finParts_inFormat hy hsy
  have hlx := finParts_length hsx
  have hly := finParts_length hsy
  exact ⟨hscheme _ _ hfx hfy hlx (by rw [hly, hlen]),
    exactSignB_eq (hmult _) (by rw [hlx, hly, hlen]) (Nat.le_refl _) (hvanish _ _ hfx hfy)⟩

/-! ## Native dot products with special values -/

/-- **The native dot product with IEEE operations**: each product rounded, then added left to right
to an accumulator that starts at `+0` (`acc = acc + x[i] * y[i]`). -/
def nativeDotIEEE (p : ℕ) (emin emax : ℤ) (xs ys : List FVal) : FVal :=
  (List.zipWith (mulF p emin emax) xs ys).foldl (addF p emin emax) (.fin ⟨0, false⟩)

/-- Adding finite values with IEEE addition follows `sumWith` with the round to nearest even. -/
theorem foldl_addF_fin : ∀ (acc : Signed) (ts : List Signed) {v : ℚ},
    sumWith (addOfRound (roundRNE p emin emax)) acc.val (ts.map Signed.val) = some v →
    ∃ n, (ts.map .fin).foldl (addF p emin emax) (.fin acc) = .fin ⟨v, n⟩
  | acc, [], v, h => by
    simp only [List.map_nil, sumWith, Option.some.injEq] at h
    subst h; exact ⟨acc.neg, rfl⟩
  | acc, t :: ts, v, h => by
    simp only [List.map_cons, sumWith, addOfRound] at h
    cases hr : roundRNE p emin emax (acc.val + t.val) with
    | none => simp [hr] at h
    | some r =>
      simp only [hr, Option.bind_some] at h
      simp only [List.map_cons, List.foldl_cons]
      rw [addF_fin, roundF_of_some hr]
      exact foldl_addF_fin ⟨r, _⟩ ts h

/-- Rounding a list of exact values whose roundings all succeed gives finite data. -/
theorem map_roundF_of_mapM : ∀ (zs : List (ℚ × Bool)) {ps : List ℚ},
    zs.mapM (fun z => roundRNE p emin emax z.1) = some ps →
    ∃ ss : List Signed, zs.map (fun z => roundF p emin emax z.1 z.2) = ss.map .fin ∧
      ss.map Signed.val = ps
  | [], ps, h => by
    simp only [List.mapM_nil, Option.pure_def, Option.some.injEq] at h
    subst h; exact ⟨[], rfl, rfl⟩
  | z :: zs, ps, h => by
    rw [List.mapM_cons] at h
    cases hr : roundRNE p emin emax z.1 with
    | none => simp [hr] at h
    | some r =>
      cases hrs : zs.mapM (fun z => roundRNE p emin emax z.1) with
      | none => simp [hr, hrs] at h
      | some rs =>
        simp only [hr, hrs, Option.bind_eq_bind, Option.bind_some, Option.pure_def,
          Option.some.injEq] at h
        subst h
        obtain ⟨ss, h1, h2⟩ := map_roundF_of_mapM zs hrs
        refine ⟨⟨r, sumNeg z.1 z.2⟩ :: ss, ?_, ?_⟩
        · simp only [List.map_cons, roundF_of_some hr, h1]
        · simp only [List.map_cons, h2]

/-- The products of two finite vectors, exactly, with the signs of the products. -/
def exactProds (sx sy : List Signed) : List (ℚ × Bool) :=
  List.zipWith (fun s t => (s.val * t.val, xor s.neg t.neg)) sx sy

theorem zipWith_mulF_map : ∀ (sx sy : List Signed),
    List.zipWith (mulF p emin emax) (sx.map .fin) (sy.map .fin) =
      (exactProds sx sy).map fun z => roundF p emin emax z.1 z.2
  | [], _ => rfl
  | _ :: _, [] => rfl
  | s :: sx, t :: sy => by
    simp only [List.map_cons, List.zipWith_cons_cons, exactProds] at *
    rw [zipWith_mulF_map sx sy, mulF_fin]; rfl

theorem zipWith_vals : ∀ (sx sy : List Signed),
    List.zipWith (· * ·) (vals sx) (vals sy) = (exactProds sx sy).map Prod.fst
  | [], _ => rfl
  | _ :: _, [] => rfl
  | s :: sx, t :: sy => by
    have ih := zipWith_vals sx sy
    simp only [vals, List.map_cons, List.zipWith_cons_cons, exactProds] at ih ⊢
    rw [ih]

/-- **Native dot products with IEEE operations agree with `nativeDot`**: whenever the rational
native dot product with the round to nearest even returns `v`, the IEEE one returns `v` with a sign
bit. So its error bound (`nativeDot_error`) applies. -/
theorem nativeDotIEEE_fin (hp : 0 < p) (hle : emin ≤ emax) {sx sy : List Signed} {v : ℚ}
    (h : nativeDot (roundRNE p emin emax) (vals sx) (vals sy) = some v) :
    ∃ n, nativeDotIEEE p emin emax (sx.map .fin) (sy.map .fin) = .fin ⟨v, n⟩ := by
  unfold nativeDotIEEE
  rw [zipWith_mulF_map]
  unfold nativeDot at h
  rw [zipWith_vals] at h
  cases hz : exactProds sx sy with
  | nil =>
    rw [hz] at h; simp only [List.map_nil, Option.some.injEq] at h
    subst h; exact ⟨false, rfl⟩
  | cons z zs =>
    rw [hz] at h
    simp only [List.map_cons] at h
    cases hr : roundRNE p emin emax z.1 with
    | none => simp [hr] at h
    | some r =>
      cases hrs : (zs.map Prod.fst).mapM (roundRNE p emin emax) with
      | none => simp [hr, hrs] at h
      | some rs =>
        simp only [hr, hrs, Option.bind_some] at h
        have hrs' : zs.mapM (fun z => roundRNE p emin emax z.1) = some rs := by
          rw [← hrs, List.mapM_map]; rfl
        obtain ⟨ss, h1, h2⟩ := map_roundF_of_mapM zs hrs'
        simp only [List.map_cons, List.foldl_cons]
        rw [roundF_of_some hr, h1]
        have hv := ((roundRNE_nearest hp hle) z.1 r hr).1
        rw [addF_posZero hp hv]
        refine foldl_addF_fin ⟨r, _⟩ ss ?_
        rw [h2]; exact h

/-! ## Plain Ozaki-I and Ozaki-II with special values -/

/-- **Ozaki-I with IEEE special values**: the specification's special cases, otherwise the matrix
multiplier's scaled slice products added left to right from `+0` with IEEE addition (`±Inf` on
overflow, signed zeros by IEEE addition). -/
def ozaki1IEEE (mult : MatrixMultiplier) (p : ℕ) (emin emax : ℤ) (b s : ℕ) (xs ys : List FVal) : FVal :=
  match dotSpecial xs ys with
  | some v => v
  | none =>
    match finParts xs, finParts ys with
    | some sx, some sy =>
      match (trianglePairs s).mapM (pairTerm mult (split b s (vals sx)).1 (split b s (vals sy)).1) with
      | some ts => (ts.map fun t => FVal.fin ⟨t, decide (t < 0)⟩).foldl (addF p emin emax)
          (.fin ⟨0, false⟩)
      | none => .nan
    | _, _ => .nan

/-- **Plain Ozaki-I with special values agrees with Ozaki-I** with IEEE addition on every finite
result. -/
theorem ozaki1IEEE_fin {mult : MatrixMultiplier} {b s : ℕ} {sx sy : List Signed} {v : ℚ}
    (h : ozaki1 mult (addOfRound (roundRNE p emin emax)) b s (vals sx) (vals sy) = some v) :
    ∃ n, ozaki1IEEE mult p emin emax b s (sx.map .fin) (sy.map .fin) = .fin ⟨v, n⟩ := by
  unfold ozaki1IEEE
  rw [dotSpecial_map, finParts_map, finParts_map]
  simp only
  unfold ozaki1 at h
  cases hts : (trianglePairs s).mapM (pairTerm mult (split b s (vals sx)).1 (split b s (vals sy)).1)
    with
  | none => rw [hts] at h; simp at h
  | some ts =>
    rw [hts] at h
    simp only [Option.bind_some] at h
    simp only
    have hmap : (ts.map fun t => FVal.fin ⟨t, decide (t < 0)⟩) =
        (ts.map fun t => (⟨t, decide (t < 0)⟩ : Signed)).map .fin := by
      rw [List.map_map]; rfl
    rw [hmap]
    refine foldl_addF_fin ⟨0, false⟩ _ ?_
    rw [List.map_map]
    have hid : (Signed.val ∘ fun t : ℚ => (⟨t, decide (t < 0)⟩ : Signed)) = id := rfl
    rw [hid, List.map_id]
    exact h

/-- The value Ozaki-II rounds: the reconstructed integer product, rescaled. -/
def ozaki2Value (mult : MatrixMultiplier) (B : CRTBasis) (P : ℕ) (x y : List ℚ) : Option ℚ := do
  let a := scaleTrunc (scaleShift P x) x
  let c := scaleTrunc (scaleShift P y) y
  let rs ← B.moduli.mapM fun m => residueProduct mult m a c
  pure ((crt B rs : ℚ) * 2 ^ (-(scaleShift P x + scaleShift P y)))

theorem ozaki2_eq_bind (mult : MatrixMultiplier) (round : ℚ → Option ℚ) (B : CRTBasis) (P : ℕ)
    (x y : List ℚ) : ozaki2 mult round B P x y = (ozaki2Value mult B P x y).bind round := by
  unfold ozaki2 ozaki2Value
  simp only [Option.bind_eq_bind, Option.pure_def]
  cases B.moduli.mapM fun m =>
    residueProduct mult m (scaleTrunc (scaleShift P x) x) (scaleTrunc (scaleShift P y) y) <;> rfl

/-- **Ozaki-II with IEEE special values**: the specification's special cases, otherwise one IEEE
rounding of the reconstructed product (`±Inf` on overflow; an exact zero is `−0` only when every
product is `−0`). -/
def ozaki2IEEE (mult : MatrixMultiplier) (p : ℕ) (emin emax : ℤ) (B : CRTBasis) (P : ℕ)
    (xs ys : List FVal) : FVal :=
  match dotSpecial xs ys with
  | some v => v
  | none =>
    match finParts xs, finParts ys with
    | some sx, some sy =>
      match ozaki2Value mult B P (vals sx) (vals sy) with
      | some q => roundF p emin emax q (allNegZero sx sy)
      | none => .nan
    | _, _ => .nan

/-- **Plain Ozaki-II with special values agrees with Ozaki-II** on every finite result. -/
theorem ozaki2IEEE_fin {mult : MatrixMultiplier} {B : CRTBasis} {P : ℕ} {sx sy : List Signed} {v : ℚ}
    (h : ozaki2 mult (roundRNE p emin emax) B P (vals sx) (vals sy) = some v) :
    ∃ n, ozaki2IEEE mult p emin emax B P (sx.map .fin) (sy.map .fin) = .fin ⟨v, n⟩ := by
  unfold ozaki2IEEE
  rw [dotSpecial_map, finParts_map, finParts_map]
  simp only
  rw [ozaki2_eq_bind] at h
  cases hq : ozaki2Value mult B P (vals sx) (vals sy) with
  | none => rw [hq] at h; simp at h
  | some q =>
    rw [hq] at h
    simp only [Option.bind_some] at h
    simp only
    rw [roundF_of_some h]
    exact ⟨_, rfl⟩

/-- Special inputs give the specification's special result, in every version. -/
theorem crIEEE_special {scheme : List ℚ → List ℚ → Option ℚ} {sgn : List ℚ → List ℚ → ℤ}
    {xs ys : List FVal} {v : FVal} (h : dotSpecial xs ys = some v) :
    crIEEE scheme sgn xs ys = v ∧ dotIEEE p emin emax xs ys = v := by
  unfold crIEEE dotIEEE; rw [h]; exact ⟨rfl, rfl⟩

end Ozaki
