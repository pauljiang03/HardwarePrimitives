import Ozaki.BoundedOzaki2Int
import Ozaki.BoundedInt

/-! # Integer Ozaki-II with the jumping top-down summation, and with signed zeros

`ozaki2CRZ` (in `Ozaki.BoundedOzaki2Int`) takes its exact fallback through `ozaki1ExactFallbackZ`,
whose top-down summation (`roundSum`) visits one range per binade between the largest and the
smallest term: a number that grows with the inputs' exponent range. `ozaki2CRJ` takes the exact
fallback through `ozaki1ExactFallbackI` (in `Ozaki.BoundedInt`), whose top-down summation
(`roundSumJ`) jumps over empty gaps and visits at most `n · bitlen M + 1` ranges for `n` terms of
magnitude at most `M`, whatever their exponents (`rangesJ_le`; for the terms of the exact fallback,
`exactFallback_ranges`). The two pipelines return the same results (`ozaki2CRJ_eq_CRZ`), so
`ozaki2CRJ` is correctly rounded (`ozaki2CRJ_eq`, `ozaki2CRJ64_eq`, `ozaki2CRJ32_eq`); it is the
canonical integer Ozaki-II.

`ozaki2CRJS` adds IEEE's signed zeros on inputs with sign bits (`SEntry`): the integer enclosures
decide the sign when they lie on one side of zero (`roundingTestSignedB`), and otherwise the exact
fallback returns the rounded value with the sign of the exact sum from the jumping sign oracle
(`ozaki1ExactFallbackIS`, `ozaki1ExactFallbackIS_eq`); an exact zero is `−0` only when every product
is `−0` (`allNegZeroI`). It is `ozaki2CRBS` on the entries' signed values (`ozaki2CRJS_eq_CRBS`),
hence `crSigned` (`ozaki2CRJS_eq`, `ozaki2CRJS64_eq`, `ozaki2CRJS32_eq`). -/

local notation "ℕ" => Nat
local notation "ℤ" => Int
local notation "ℚ" => Rat

namespace Ozaki

/-! ## The exact fallback with the jumping top-down summation and the sign of the exact sum -/

/-- The integer exact fallback with the jumping top-down summation, returning the rounded value
together with the sign of the exact sum (`signSumJ` on the same integer terms and ranges). -/
def ozaki1ExactFallbackIS (mult : MatrixMultiplier) (p : ℕ) (emin emax : ℤ) (b smax : ℕ)
    (xs ys : List (ℤ × ℤ)) : Option (ℚ × ℤ) :=
  match (List.range' 1 smax).find? fun s => vanishInt b s xs ys with
  | some s =>
    match (slicePairs (splitInt b s xs).1 (splitInt b s ys).1).mapM
        (fun pr => sliceProductInt mult pr.1 pr.2) with
    | some ts => (roundSumJ p emin emax (bitlen (ts.length + 1) + p + 4) ts).map fun r =>
        (r, signSumJ (bitlen (ts.length + 1) + p + 4) ts)
    | none => none
  | none => none

/-- **The jumping exact fallback with its sign is the bounded one** on the entries' values. -/
theorem ozaki1ExactFallbackIS_eq (mult : MatrixMultiplier) (p : ℕ) (emin emax : ℤ) (b smax : ℕ)
    (xs ys : List (ℤ × ℤ)) :
    ozaki1ExactFallbackIS mult p emin emax b smax xs ys =
      ozaki1ExactFallbackBS mult p emin emax b smax (entryVals xs) (entryVals ys) := by
  unfold ozaki1ExactFallbackIS ozaki1ExactFallbackBS
  have hf : (fun s => vanishInt b s xs ys) =
      fun s => residualsVanish b s (entryVals xs) (entryVals ys) :=
    funext fun s => vanishInt_eq b s xs ys
  rw [hf]
  cases (List.range' 1 smax).find? fun s => residualsVanish b s (entryVals xs) (entryVals ys) with
  | none => rfl
  | some s =>
    simp only
    rw [(splitInt_eq b s xs).1, (splitInt_eq b s ys).1]
    cases (slicePairs (split b s (entryVals xs)).1 (split b s (entryVals ys)).1).mapM
        (fun pr => sliceProductInt mult pr.1 pr.2) with
    | none => rfl
    | some ts =>
      simp only
      have hbl := bitlen_mono (Nat.le_add_right ts.length 1)
      rw [roundSumJ_eq _ _ (by omega), roundSum_eq _ _ (by omega), signSumJ_eq (by omega),
        signSum_eq (by omega)]

/-- **The top-down summation of the exact fallback visits few ranges**: for its `s²` integer terms,
each at most the exactness bound of the matrix multiplier, the jumping top-down summation visits at
most `s² · bitlen bound + 1` ranges, whatever the inputs' exponents. -/
theorem exactFallback_ranges {mult : MatrixMultiplier} {b bound : ℕ} (hmult : mult.ExactOn b bound) (s W T : ℕ)
    {x y : List ℚ} (hlen : x.length = y.length) (hbound : x.length * (2 ^ b * 2 ^ b) ≤ bound) :
    rangesJ W T ((slicePairs (split b s x).1 (split b s y).1).map
      fun pr => exactSliceInt pr.1 pr.2) ≤ s * s * bitlen bound + 1 := by
  have hterms := (ozaki1ExactFallbackB_terms (s := s) hmult hlen hbound).2
  have h := rangesJ_le W T (M := bound) (ts := (slicePairs (split b s x).1 (split b s y).1).map
    fun pr => exactSliceInt pr.1 pr.2) (by
      intro t ht
      obtain ⟨pr, hpr, rfl⟩ := List.mem_map.mp ht
      exact hterms pr hpr)
  have hplen : (slicePairs (split b s x).1 (split b s y).1).length = s * s := by
    obtain ⟨hlx, _, _⟩ := split_length b s x
    obtain ⟨hly, _, _⟩ := split_length b s y
    unfold slicePairs
    rw [List.length_flatMap]
    simp only [List.length_map, hly]
    have hc : ∀ l : List Slice, (l.map fun _ => s).sum = l.length * s := by
      intro l; induction l with
      | nil => simp
      | cons a l ih => simp only [List.map_cons, List.sum_cons, ih, List.length_cons]; grind
    rw [hc, hlx]
  rw [List.length_map, hplen] at h
  exact h

/-! ## Correctly rounded Ozaki-II in integers with the jumping top-down summation -/

/-- **Correctly rounded Ozaki-II as an integer pipeline**: the integer enclosures of the
configurations in turn, then the integer exact fallback with the jumping top-down summation. -/
def ozaki2CRJ (mult : MatrixMultiplier) (p : ℕ) (emin emax : ℤ) (cfgs : List (CRTBasis × ℕ)) (b smax : ℕ)
    (xs ys : List (ℤ × ℤ)) : Option ℚ :=
  roundingTestB p emin emax (cfgs.map fun c => ozaki2EnclosureZ mult c.1 c.2 xs ys)
    (ozaki1ExactFallbackI mult p emin emax b smax xs ys)

/-- **The jumping pipeline returns what `ozaki2CRZ` returns.** -/
theorem ozaki2CRJ_eq_CRZ (mult : MatrixMultiplier) (p : ℕ) (emin emax : ℤ) (cfgs : List (CRTBasis × ℕ))
    (b smax : ℕ) (xs ys : List (ℤ × ℤ)) :
    ozaki2CRJ mult p emin emax cfgs b smax xs ys = ozaki2CRZ mult p emin emax cfgs b smax xs ys := by
  unfold ozaki2CRJ ozaki2CRZ
  rw [ozaki1ExactFallbackI_eq, ozaki1ExactFallbackZ_eq]

/-- **The jumping integer pipeline is correctly rounded.** -/
theorem ozaki2CRJ_eq {p : ℕ} {emin emax : ℤ} (hp : 0 < p) (hle : emin ≤ emax) {mult : MatrixMultiplier}
    {b bound : ℕ} (hmult : mult.ExactOn b bound) {cfgs : List (CRTBasis × ℕ)} {smax : ℕ}
    {xs ys : List (ℤ × ℤ)}
    (hcfg : ∀ c ∈ cfgs, c.1.Valid ∧ (∀ m ∈ c.1.moduli, m ≤ 2 ^ (b + 1)) ∧
      2 * xs.length * (2 ^ c.2 * 2 ^ c.2) < c.1.modulus)
    (hlen : xs.length = ys.length) (hbound : xs.length * (2 ^ b * 2 ^ b) ≤ bound)
    (hvanish : ∃ s ∈ List.range' 1 smax,
      residualsVanish b s (entryVals xs) (entryVals ys) = true) :
    ozaki2CRJ mult p emin emax cfgs b smax xs ys =
      roundRNE p emin emax (dot (entryVals xs) (entryVals ys)) := by
  rw [ozaki2CRJ_eq_CRZ]
  exact ozaki2CRZ_eq hp hle hmult hcfg hlen hbound hvanish

/-- **Binary64 inputs as integer pairs**: correctly rounded to binary64. -/
theorem ozaki2CRJ64_eq {mult : MatrixMultiplier} {b bound : ℕ} (hmult : mult.ExactOn b bound)
    {cfgs : List (CRTBasis × ℕ)} {smax : ℕ} (hb : b ≤ 1025) (hsmax : 2098 < smax * (b + 1))
    {xs ys : List (ℤ × ℤ)}
    (hcfg : ∀ c ∈ cfgs, c.1.Valid ∧ (∀ m ∈ c.1.moduli, m ≤ 2 ^ (b + 1)) ∧
      2 * xs.length * (2 ^ c.2 * 2 ^ c.2) < c.1.modulus)
    (hlen : xs.length = ys.length) (hbound : xs.length * (2 ^ b * 2 ^ b) ≤ bound)
    (hx : ∀ v ∈ entryVals xs, Binary64Value v) (hy : ∀ v ∈ entryVals ys, Binary64Value v) :
    ozaki2CRJ mult 53 (-1022) 1023 cfgs b smax xs ys = rne64 (dot (entryVals xs) (entryVals ys)) := by
  rw [ozaki2CRJ_eq_CRZ]
  exact ozaki2CRZ64_eq hmult hb hsmax hcfg hlen hbound hx hy

/-- **Binary32 inputs as integer pairs**: correctly rounded to binary32. -/
theorem ozaki2CRJ32_eq {mult : MatrixMultiplier} {b bound : ℕ} (hmult : mult.ExactOn b bound)
    {cfgs : List (CRTBasis × ℕ)} {smax : ℕ} (hb : b ≤ 129) (hsmax : 277 < smax * (b + 1))
    {xs ys : List (ℤ × ℤ)}
    (hcfg : ∀ c ∈ cfgs, c.1.Valid ∧ (∀ m ∈ c.1.moduli, m ≤ 2 ^ (b + 1)) ∧
      2 * xs.length * (2 ^ c.2 * 2 ^ c.2) < c.1.modulus)
    (hlen : xs.length = ys.length) (hbound : xs.length * (2 ^ b * 2 ^ b) ≤ bound)
    (hx : ∀ v ∈ entryVals xs, Binary32Value v) (hy : ∀ v ∈ entryVals ys, Binary32Value v) :
    ozaki2CRJ mult 24 (-126) 127 cfgs b smax xs ys = rne32Q (dot (entryVals xs) (entryVals ys)) := by
  rw [ozaki2CRJ_eq_CRZ]
  exact ozaki2CRZ32_eq hmult hb hsmax hcfg hlen hbound hx hy

/-! ## Signed zeros -/

/-- **Correctly rounded Ozaki-II in integers with signed zeros**: entries with their sign bits, the
signed integer rounding test on the integer enclosures, then the jumping exact fallback with the
sign of the exact sum. -/
def ozaki2CRJS (mult : MatrixMultiplier) (p : ℕ) (emin emax : ℤ) (cfgs : List (CRTBasis × ℕ)) (b smax : ℕ)
    (xs ys : List SEntry) : Option Signed :=
  roundingTestSignedB p emin emax
    (cfgs.map fun c => ozaki2EnclosureZ mult c.1 c.2 (xs.map (·.1)) (ys.map (·.1)))
    (ozaki1ExactFallbackIS mult p emin emax b smax (xs.map (·.1)) (ys.map (·.1))) (allNegZeroI xs ys)

/-- The signed integer pipeline is `ozaki2CRBS` on the entries' signed values. -/
theorem ozaki2CRJS_eq_CRBS (mult : MatrixMultiplier) (p : ℕ) (emin emax : ℤ) (cfgs : List (CRTBasis × ℕ))
    (b smax : ℕ) (xs ys : List SEntry) :
    ozaki2CRJS mult p emin emax cfgs b smax xs ys =
      ozaki2CRBS mult p emin emax cfgs b smax (xs.map toSigned) (ys.map toSigned) := by
  unfold ozaki2CRJS ozaki2CRBS
  rw [ozaki1ExactFallbackIS_eq, vals_toSigned, vals_toSigned, allNegZeroI_eq]
  congr 1
  apply List.map_congr_left
  intro c _
  exact ozaki2EnclosureZ_eq mult c.1 c.2 _ _

/-- **Signed correct rounding of Ozaki-II in integers**: the round to nearest even of `x · y` with
IEEE's sign for zero results. -/
theorem ozaki2CRJS_eq {p : ℕ} {emin emax : ℤ} (hp : 0 < p) (hle : emin ≤ emax) {mult : MatrixMultiplier}
    {b bound : ℕ} (hmult : mult.ExactOn b bound) {cfgs : List (CRTBasis × ℕ)} {smax : ℕ}
    {xs ys : List SEntry}
    (hcfg : ∀ c ∈ cfgs, c.1.Valid ∧ (∀ m ∈ c.1.moduli, m ≤ 2 ^ (b + 1)) ∧
      2 * xs.length * (2 ^ c.2 * 2 ^ c.2) < c.1.modulus)
    (hlen : xs.length = ys.length) (hbound : xs.length * (2 ^ b * 2 ^ b) ≤ bound)
    (hvanish : ∃ s ∈ List.range' 1 smax,
      residualsVanish b s (entryVals (xs.map (·.1))) (entryVals (ys.map (·.1))) = true) :
    ozaki2CRJS mult p emin emax cfgs b smax xs ys =
      crSigned (roundRNE p emin emax) (xs.map toSigned) (ys.map toSigned) := by
  rw [ozaki2CRJS_eq_CRBS]
  exact ozaki2CRBS_eq hp hle hmult (by simpa using hcfg) (by simp [hlen]) (by simpa using hbound)
    (by rw [vals_toSigned, vals_toSigned]; exact hvanish)

theorem entryVals_fst_of {xs : List SEntry} {Q : ℚ → Prop} (h : ∀ a ∈ xs, Q (entryVal a.1)) :
    ∀ v ∈ entryVals (xs.map (·.1)), Q v := by
  intro v hv
  simp only [entryVals, List.map_map, List.mem_map] at hv
  obtain ⟨a, ha, rfl⟩ := hv
  exact h a ha

/-- **Binary64 entries with signed zeros.** -/
theorem ozaki2CRJS64_eq {mult : MatrixMultiplier} {b bound : ℕ} (hmult : mult.ExactOn b bound)
    {cfgs : List (CRTBasis × ℕ)} {smax : ℕ} (hb : b ≤ 1025) (hsmax : 2098 < smax * (b + 1))
    {xs ys : List SEntry}
    (hcfg : ∀ c ∈ cfgs, c.1.Valid ∧ (∀ m ∈ c.1.moduli, m ≤ 2 ^ (b + 1)) ∧
      2 * xs.length * (2 ^ c.2 * 2 ^ c.2) < c.1.modulus)
    (hlen : xs.length = ys.length) (hbound : xs.length * (2 ^ b * 2 ^ b) ≤ bound)
    (hx : ∀ a ∈ xs, Binary64Value (entryVal a.1)) (hy : ∀ a ∈ ys, Binary64Value (entryVal a.1)) :
    ozaki2CRJS mult 53 (-1022) 1023 cfgs b smax xs ys =
      crSigned rne64 (xs.map toSigned) (ys.map toSigned) :=
  ozaki2CRJS_eq (by decide) (by decide) hmult hcfg hlen hbound
    (vanish64 hb hsmax (entryVals_fst_of hx) (entryVals_fst_of hy))

/-- **Binary32 entries with signed zeros.** -/
theorem ozaki2CRJS32_eq {mult : MatrixMultiplier} {b bound : ℕ} (hmult : mult.ExactOn b bound)
    {cfgs : List (CRTBasis × ℕ)} {smax : ℕ} (hb : b ≤ 129) (hsmax : 277 < smax * (b + 1))
    {xs ys : List SEntry}
    (hcfg : ∀ c ∈ cfgs, c.1.Valid ∧ (∀ m ∈ c.1.moduli, m ≤ 2 ^ (b + 1)) ∧
      2 * xs.length * (2 ^ c.2 * 2 ^ c.2) < c.1.modulus)
    (hlen : xs.length = ys.length) (hbound : xs.length * (2 ^ b * 2 ^ b) ≤ bound)
    (hx : ∀ a ∈ xs, Binary32Value (entryVal a.1)) (hy : ∀ a ∈ ys, Binary32Value (entryVal a.1)) :
    ozaki2CRJS mult 24 (-126) 127 cfgs b smax xs ys =
      crSigned rne32Q (xs.map toSigned) (ys.map toSigned) :=
  ozaki2CRJS_eq (by decide) (by decide) hmult hcfg hlen hbound
    (vanish32Q hb hsmax (entryVals_fst_of hx) (entryVals_fst_of hy))

end Ozaki
