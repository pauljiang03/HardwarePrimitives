import Ozaki.IEEEDot
import Ozaki.BoundedInt

/-! # IEEE special values for the integer pipelines

The integer pipelines (`ozaki1CRI`, `ozaki2CRJ`, `adpCRJ`) take their inputs as a binary format
stores them, integer pairs `(m, e)` worth `m · 2^e`. With special values the inputs are IEEE data in
that stored form (`IDatum`): a finite entry with its sign bit, `±Inf`, or NaN; `IDatum.toFVal`
reads one as the IEEE datum of `Ozaki.IEEEValue`.

`crIEEEI` is `crIEEE` for an integer scheme: the specification's special cases (decided on the
data's tags, signs and zero tests, through `dotSpecial` on the read data), otherwise the integer
scheme on the finite entries' pairs, signed with an integer sign oracle where its own sign does not
decide. `crIEEEI_eq`: whenever the scheme is correctly rounded and the oracle exact on the finite
entries, `crIEEEI` meets the IEEE specification `dotIEEE` on the read data, for every input.
`crIEEEI_exactSign` takes the oracle from the integer exact path (`exactSignI`, the jumping sign
oracle on the exact path's integer slice products) and needs only the scheme's correctness on
entries of the format. -/

local notation "ℕ" => Nat
local notation "ℤ" => Int
local notation "ℚ" => Rat

namespace Ozaki

/-- An IEEE datum as a binary format stores it: a finite entry `((m, e), sign bit)` worth `m 2^e`,
an infinity with its sign, or NaN. -/
inductive IDatum where
  | fin (a : SEntry)
  | inf (neg : Bool)
  | nan
  deriving DecidableEq, Repr

/-- The IEEE datum a stored datum denotes. -/
def IDatum.toFVal : IDatum → FVal
  | .fin a => .fin (toSigned a)
  | .inf n => .inf n
  | .nan => .nan

/-- A stored datum of the format: a finite entry is a value of the format. -/
def IDatum.InFormat (p : ℕ) (emin emax : ℤ) : IDatum → Prop
  | .fin a => FormatValue p emin emax (entryVal a.1)
  | _ => True

def finPartI : IDatum → Option SEntry
  | .fin a => some a
  | _ => none

/-- The finite entries of a vector, `none` if an entry is infinite or NaN. -/
def finPartsI (xs : List IDatum) : Option (List SEntry) := xs.mapM finPartI

theorem finParts_toFVal : ∀ xs : List IDatum,
    finParts (xs.map IDatum.toFVal) = (finPartsI xs).map (·.map toSigned)
  | [] => rfl
  | a :: xs => by
    have ih := finParts_toFVal xs
    unfold finParts at ih ⊢
    unfold finPartsI at ih ⊢
    rw [List.map_cons, List.mapM_cons, List.mapM_cons]
    cases a with
    | fin s =>
      simp only [IDatum.toFVal, finPart, finPartI, Option.bind_eq_bind, Option.bind_some, ih]
      cases xs.mapM finPartI <;> rfl
    | inf n => rfl
    | nan => rfl

theorem finPartsI_spec {p : ℕ} {emin emax : ℤ} : ∀ {xs : List IDatum} {sx : List SEntry},
    (∀ a ∈ xs, a.InFormat p emin emax) → finPartsI xs = some sx →
      sx.length = xs.length ∧ ∀ a ∈ sx, FormatValue p emin emax (entryVal a.1)
  | [], sx, _, h => by
    simp only [finPartsI, List.mapM_nil, Option.pure_def, Option.some.injEq] at h
    subst h; simp
  | a :: xs, sx, hx, h => by
    unfold finPartsI at h
    rw [List.mapM_cons] at h
    cases a with
    | inf n => simp [finPartI] at h
    | nan => simp [finPartI] at h
    | fin s =>
      cases hr : xs.mapM finPartI with
      | none => simp [finPartI, hr] at h
      | some sx' =>
        simp only [finPartI, hr, Option.bind_eq_bind, Option.bind_some, Option.pure_def,
          Option.some.injEq] at h
        subst h
        obtain ⟨hl, hf⟩ := finPartsI_spec (fun a ha => hx a (List.mem_cons_of_mem _ ha)) hr
        refine ⟨by simp [hl], fun a ha => ?_⟩
        rcases List.mem_cons.mp ha with rfl | ha
        · exact hx _ List.mem_cons_self
        · exact hf a ha

/-- **An integer correctly rounded scheme with IEEE special values.** -/
def crIEEEI (scheme : List (ℤ × ℤ) → List (ℤ × ℤ) → Option ℚ)
    (sgn : List (ℤ × ℤ) → List (ℤ × ℤ) → ℤ) (xs ys : List IDatum) : FVal :=
  match dotSpecial (xs.map IDatum.toFVal) (ys.map IDatum.toFVal) with
  | some v => v
  | none =>
    match finPartsI xs, finPartsI ys with
    | some sx, some sy =>
      crFinite (scheme (sx.map (·.1)) (sy.map (·.1))) (sgn (sx.map (·.1)) (sy.map (·.1)))
        (allNegZeroI sx sy)
    | _, _ => .nan

/-- **Integer correctly rounded schemes meet the IEEE specification.** -/
theorem crIEEEI_eq {p : ℕ} {emin emax : ℤ} (hp : 0 < p) (hle : emin ≤ emax)
    {scheme : List (ℤ × ℤ) → List (ℤ × ℤ) → Option ℚ} {sgn : List (ℤ × ℤ) → List (ℤ × ℤ) → ℤ}
    {xs ys : List IDatum}
    (h : ∀ sx sy, finPartsI xs = some sx → finPartsI ys = some sy →
      scheme (sx.map (·.1)) (sy.map (·.1)) =
          roundRNE p emin emax (dot (entryVals (sx.map (·.1))) (entryVals (sy.map (·.1)))) ∧
        sgn (sx.map (·.1)) (sy.map (·.1)) =
          sgnQ (dot (entryVals (sx.map (·.1))) (entryVals (sy.map (·.1))))) :
    crIEEEI scheme sgn xs ys = dotIEEE p emin emax (xs.map IDatum.toFVal) (ys.map IDatum.toFVal) := by
  unfold crIEEEI dotIEEE
  cases dotSpecial (xs.map IDatum.toFVal) (ys.map IDatum.toFVal) with
  | some v => rfl
  | none =>
    simp only
    rw [finParts_toFVal, finParts_toFVal]
    cases hx : finPartsI xs with
    | none => rfl
    | some sx =>
      cases hy : finPartsI ys with
      | none => rfl
      | some sy =>
        simp only [Option.map_some]
        obtain ⟨h1, h2⟩ := h sx sy hx hy
        rw [h1, h2, crFinite_eq hp hle, vals_toSigned, vals_toSigned, allNegZeroI_eq]

/-- **With the integer exact path as the sign oracle**: an integer scheme correctly rounded on
entries of the format, wrapped by `crIEEEI` with the sign from `exactSignI` on the same engine,
meets the IEEE specification for every input of the format. -/
theorem crIEEEI_exactSign {p : ℕ} {emin emax : ℤ} (hp : 0 < p) (hle : emin ≤ emax)
    {scheme : List (ℤ × ℤ) → List (ℤ × ℤ) → Option ℚ} {mult : MatrixMultiplier} {b smax : ℕ}
    (hmult : ∀ B, mult.ExactOn b B) {xs ys : List IDatum}
    (hvanish : ∀ x y : List (ℤ × ℤ), (∀ a ∈ x, FormatValue p emin emax (entryVal a)) →
      (∀ a ∈ y, FormatValue p emin emax (entryVal a)) →
      ∃ s ∈ List.range' 1 smax, vanishInt b s x y = true)
    (hscheme : ∀ x y : List (ℤ × ℤ), (∀ a ∈ x, FormatValue p emin emax (entryVal a)) →
      (∀ a ∈ y, FormatValue p emin emax (entryVal a)) → x.length = xs.length →
      y.length = xs.length → scheme x y = roundRNE p emin emax (dot (entryVals x) (entryVals y)))
    (hx : ∀ a ∈ xs, a.InFormat p emin emax) (hy : ∀ a ∈ ys, a.InFormat p emin emax)
    (hlen : xs.length = ys.length) :
    crIEEEI scheme (fun x y => (exactSignI mult b smax x y).getD 0) xs ys =
      dotIEEE p emin emax (xs.map IDatum.toFVal) (ys.map IDatum.toFVal) := by
  apply crIEEEI_eq hp hle
  intro sx sy hsx hsy
  obtain ⟨hlx, hfx⟩ := finPartsI_spec hx hsx
  obtain ⟨hly, hfy⟩ := finPartsI_spec hy hsy
  have hfx' : ∀ a ∈ sx.map (·.1), FormatValue p emin emax (entryVal a) := by
    intro a ha; obtain ⟨c, hc, rfl⟩ := List.mem_map.mp ha; exact hfx c hc
  have hfy' : ∀ a ∈ sy.map (·.1), FormatValue p emin emax (entryVal a) := by
    intro a ha; obtain ⟨c, hc, rfl⟩ := List.mem_map.mp ha; exact hfy c hc
  have hl : (sx.map (·.1)).length = (sy.map (·.1)).length := by simp [hlx, hly, hlen]
  refine ⟨hscheme _ _ hfx' hfy' (by simp [hlx]) (by simp [hly, hlen]), ?_⟩
  rw [exactSignI_eq (hmult _) hl (Nat.le_refl _) (hvanish _ _ hfx' hfy')]
  rfl

/-- Binary64 entries leave nothing over after at most `smax` integer slices, `smax (b+1) > 2098`. -/
theorem vanishInt64 {b smax : ℕ} (hb : b ≤ 1025) (hsmax : 2098 < smax * (b + 1))
    {x y : List (ℤ × ℤ)} (hx : ∀ a ∈ x, Binary64Value (entryVal a))
    (hy : ∀ a ∈ y, Binary64Value (entryVal a)) :
    ∃ s ∈ List.range' 1 smax, vanishInt b s x y = true :=
  (vanish64 hb hsmax (binary64_entries hx) (binary64_entries hy)).imp fun _ h =>
    ⟨h.1, by rw [vanishInt_eq]; exact h.2⟩

/-- Binary32 entries leave nothing over after at most `smax` integer slices, `smax (b+1) > 277`. -/
theorem vanishInt32 {b smax : ℕ} (hb : b ≤ 129) (hsmax : 277 < smax * (b + 1))
    {x y : List (ℤ × ℤ)} (hx : ∀ a ∈ x, Binary32Value (entryVal a))
    (hy : ∀ a ∈ y, Binary32Value (entryVal a)) :
    ∃ s ∈ List.range' 1 smax, vanishInt b s x y = true :=
  (vanish32Q hb hsmax (binary32_entries hx) (binary32_entries hy)).imp fun _ h =>
    ⟨h.1, by rw [vanishInt_eq]; exact h.2⟩

end Ozaki
