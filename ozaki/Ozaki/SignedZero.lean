import Ozaki.TruncatedSum

/-! # Signed zeros

Values are rationals, which have one zero; IEEE formats have two. For a correctly rounded dot
product the sign of a zero result is fixed by IEEE's rules for multiplication and for a sum rounded
to nearest:

* a result that rounds to zero from a nonzero exact sum keeps the exact sum's sign (underflow);
* an exact sum of zero is `−0` only when every product is `−0`, the sign of a product being the
  exclusive or of its factors' signs, zeros included; otherwise it is `+0`.

`Signed` pairs a value with its sign bit, and `crSigned` is this specification: the round to
nearest of the exact sum, with the sign above. The enclosure check settles the sign as well when
the enclosure lies on one side of zero (`signFromEnclosure`), and the exact path knows it outright;
`roundingTestSigned_eq` proves the signed check returns `crSigned`. `ozaki1CRWS` is the correctly
rounded Ozaki-I with a window accumulator and signed zeros (`ozaki1CRWS_eq`). -/

local notation "ℕ" => Nat
local notation "ℤ" => Int
local notation "ℚ" => Rat

namespace Ozaki

/-- A floating-point value with its sign bit; for zero the bit tells `+0` from `−0`. -/
structure Signed where
  val : ℚ
  neg : Bool
  deriving DecidableEq, Repr

/-- The sign bit of a nonzero value is its sign. -/
def Signed.WellFormed (a : Signed) : Prop := a.val ≠ 0 → a.neg = decide (a.val < 0)

/-- The sign bit of a product: the exclusive or of the factors' sign bits. -/
def prodNeg (a b : Signed) : Bool := xor a.neg b.neg

/-- Every product is `−0` (and there is at least one). -/
def allNegZero (xs ys : List Signed) : Bool :=
  let ps := List.zipWith (fun a b => a.val * b.val == 0 && prodNeg a b) xs ys
  !ps.isEmpty && ps.all id

/-- The values of a signed vector. -/
def vals (xs : List Signed) : List ℚ := xs.map Signed.val

/-- The sign bit of a correctly rounded sum `v`: the sign of `v`, or for an exact zero the rule for
signed zeros. -/
def sumNeg (v : ℚ) (z : Bool) : Bool := if v = 0 then z else decide (v < 0)

/-- **The correctly rounded dot product with signed zeros.** -/
def crSigned (rnd : ℚ → Option ℚ) (xs ys : List Signed) : Option Signed :=
  (rnd (dot (vals xs) (vals ys))).map fun r =>
    ⟨r, sumNeg (dot (vals xs) (vals ys)) (allNegZero xs ys)⟩

/-- The sign bit an enclosure `[H − B, H + B]` settles for its rounding `r`: the sign of a nonzero
`r`; for `r = 0`, the side of zero the enclosure lies on; none if it contains zero. -/
def signFromEnclosure (H B r : ℚ) : Option Bool :=
  if r ≠ 0 then some (decide (r < 0))
  else if 0 < H - B then some false
  else if H + B < 0 then some true
  else none

/-- The signed check: try the enclosures in order, accepting one whose ends round alike and whose
sign is settled; after the last, the exact value. `z` is `allNegZero` of the inputs. -/
def roundingTestSigned (rnd : ℚ → Option ℚ) : List (Option (ℚ × ℚ)) → Option ℚ → Bool → Option Signed
  | [], exact, z => exact.bind fun v => (rnd v).map fun r => ⟨r, sumNeg v z⟩
  | c :: cs, exact, z =>
    match c.bind (fun p => (roundEnclosure rnd p.1 p.2).bind fun r =>
        (signFromEnclosure p.1 p.2 r).map fun n => (⟨r, n⟩ : Signed)) with
    | some w => some w
    | none => roundingTestSigned rnd cs exact z

/-- A rounding to nearest that fixes zero preserves the sign of a nonzero result. -/
theorem sign_of_round {R : ℚ → Prop} {rnd : ℚ → Option ℚ} (h : RoundsToNearest R rnd)
    (h0 : rnd 0 = some 0) {v r : ℚ} (hr : rnd v = some r) (hr0 : r ≠ 0) :
    v ≠ 0 ∧ decide (r < 0) = decide (v < 0) := by
  have hv0 : v ≠ 0 := by
    rintro rfl; rw [h0] at hr; cases hr; exact hr0 rfl
  refine ⟨hv0, ?_⟩
  rcases (show v < 0 ∨ 0 < v by grind) with hlt | hgt
  · have := round_monotone h (Rat.le_of_lt hlt) hr h0
    have hrl : r < 0 := by grind
    simp [hrl, hlt]
  · have := round_monotone h (Rat.le_of_lt hgt) h0 hr
    have hrg : ¬ r < 0 := by grind
    have hvg : ¬ v < 0 := by grind
    simp [hrg, hvg]

/-- **The signed check returns the correctly rounded value with the IEEE sign.** -/
theorem roundingTestSigned_eq {R : ℚ → Prop} {rnd : ℚ → Option ℚ} (h : RoundsToNearest R rnd)
    (hI : RoundsOnIntervals rnd) (h0 : rnd 0 = some 0) {v : ℚ} (z : Bool) :
    ∀ (cs : List (Option (ℚ × ℚ))) (exact : Option ℚ),
      (∀ c ∈ cs, ∀ H B, c = some (H, B) → Rat.abs (v - H) ≤ B) → exact = some v →
      roundingTestSigned rnd cs exact z = (rnd v).map fun r => ⟨r, sumNeg v z⟩
  | [], exact, _, hex => by subst hex; rfl
  | c :: cs, exact, hcs, hex => by
    unfold roundingTestSigned
    split
    · rename_i w hw
      cases c with
      | none => simp at hw
      | some p =>
        obtain ⟨H, B⟩ := p
        simp only [Option.bind_some] at hw
        have hv := hcs _ List.mem_cons_self H B rfl
        cases hre : roundEnclosure rnd H B with
        | none => simp [hre] at hw
        | some r =>
          simp only [hre, Option.bind_some] at hw
          have hrv := roundEnclosure_eq h hI hv hre
          rw [hrv, Option.map_some]
          cases hs : signFromEnclosure H B r with
          | none => simp [hs] at hw
          | some n =>
            simp only [hs, Option.map_some, Option.some.injEq] at hw
            subst hw
            congr 1
            simp only [Signed.mk.injEq, true_and]
            unfold signFromEnclosure at hs
            obtain ⟨h1, h2⟩ := (abs_le_iff _ _).mp hv
            by_cases hr0 : r ≠ 0
            · rw [if_pos hr0] at hs
              cases hs
              obtain ⟨hv0, hsign⟩ := sign_of_round h h0 hrv hr0
              unfold sumNeg; rw [if_neg hv0]; exact hsign
            · rw [if_neg hr0] at hs
              split at hs
              · cases hs
                have hvpos : 0 < v := by grind
                unfold sumNeg
                rw [if_neg (by grind)]
                simp; grind
              · split at hs
                · cases hs
                  have hvneg : v < 0 := by grind
                  unfold sumNeg
                  rw [if_neg (by grind)]
                  simp [hvneg]
                · cases hs
    · exact roundingTestSigned_eq h hI h0 z cs exact (fun c' hc' => hcs c' (List.mem_cons_of_mem _ hc')) hex

/-- **Correctly rounded Ozaki-I with a window accumulator and signed zeros.** -/
def ozaki1CRWS (mult : MatrixMultiplier) (rnd : ℚ → Option ℚ) (b W : ℕ) (ss : List ℕ) (smax : ℕ)
    (xs ys : List Signed) : Option Signed :=
  roundingTestSigned rnd (ss.map fun s => ozaki1TruncatedEnclosure mult b s W (vals xs) (vals ys))
    (ozaki1ExactFallback mult b smax (vals xs) (vals ys)) (allNegZero xs ys)

/-- **Signed correct rounding.** On an exact engine, `ozaki1CRWS` returns the correctly rounded
dot product with IEEE's sign for zero results. -/
theorem ozaki1CRWS_eq {R : ℚ → Prop} {rnd : ℚ → Option ℚ} (h : RoundsToNearest R rnd)
    (hI : RoundsOnIntervals rnd) (h0 : rnd 0 = some 0) {mult : MatrixMultiplier} {b bound : ℕ}
    (hmult : mult.ExactOn b bound) (W : ℕ) (ss : List ℕ) {smax : ℕ} {xs ys : List Signed}
    (hlen : xs.length = ys.length)
    (hbound : xs.length * (2 ^ b * 2 ^ b) ≤ bound)
    (hvanish : ∃ s ∈ List.range' 1 smax, residualsVanish b s (vals xs) (vals ys) = true) :
    ozaki1CRWS mult rnd b W ss smax xs ys = crSigned rnd xs ys := by
  have hl : (vals xs).length = (vals ys).length := by simp [vals, hlen]
  have hb : (vals xs).length * (2 ^ b * 2 ^ b) ≤ bound := by simpa [vals] using hbound
  unfold ozaki1CRWS crSigned
  apply roundingTestSigned_eq h hI h0 _ _ _ _ (ozaki1ExactFallback_eq hmult hl hb hvanish)
  intro c hc H B hcB
  obtain ⟨s, _, rfl⟩ := List.mem_map.mp hc
  exact ozaki1TruncatedEnclosure_sound hmult s W hl hb hcB

end Ozaki
