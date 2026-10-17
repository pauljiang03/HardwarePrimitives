import OzakiMC.Schemes
import OzakiMC.Scaling
import Ozaki.Correct

/-! # Correct rounding on the AMD matrix-core model

`MatrixCore`'s binary32 round to nearest even returns a nearest binary32 value
(`rne32_nearestEven`) and succeeds below the overflow threshold (`rne32_isSome_iff`), so it meets
the two conditions of the enclosure test (`round32Value_nearest`, `round32Value_intervals`). With
it, Ozaki-I and Ozaki-II on any matrix-core variant whose matrix multiplier is exact return the
binary32 round to nearest of `x · y` for every input (`mcOzaki1CR_eq`, `mcOzaki2CR_eq`).
MatrixCore's rounding follows IEEE overflow, TensorCore's fails above the largest finite value;
below it both return the binary32 round to nearest even of the same exact value. The any-`k`
variants of `OzakiMC.LongDot` use the shared `Ozaki.rne32Q` on both vendors. -/

open MatrixCore

namespace Ozaki.MC

/-- The finite binary32 values. -/
def IsValue32 (y : ℚ) : Prop := ∃ w, value32 w = some y

theorem round32Value_some {q v : ℚ} (h : round32Value q = some v) :
    ∃ w, rne32 q = some w ∧ value32 w = some v := by
  unfold round32Value at h
  cases hw : rne32 q with
  | none => simp [hw] at h
  | some w => rw [hw] at h; exact ⟨w, rfl, h⟩

/-- Binary32 round to nearest returns a nearest binary32 value. -/
theorem round32Value_nearest : RoundsToNearest IsValue32 round32Value := by
  intro q v h
  obtain ⟨w, hw, hv⟩ := round32Value_some h
  obtain ⟨d, hd, hnear, _⟩ := rne32_nearestEven hw
  rw [hv] at hd
  cases hd
  refine ⟨⟨w, hv⟩, fun y ⟨w', hy⟩ => ?_⟩
  have := hnear w' y hy
  rwa [absQ_eq, absQ_eq] at this

/-- Binary32 round to nearest succeeds on intervals (it fails only at and above the overflow
threshold). -/
theorem round32Value_intervals : RoundsOnIntervals round32Value := by
  intro a b q h1 h2 ha hb
  obtain ⟨va, hva⟩ := Option.isSome_iff_exists.mp ha
  obtain ⟨vb, hvb⟩ := Option.isSome_iff_exists.mp hb
  obtain ⟨wa, hwa, _⟩ := round32Value_some hva
  obtain ⟨wb, hwb, _⟩ := round32Value_some hvb
  have ra := (rne32_isSome_iff a).mp (by simp [hwa])
  have rb := (rne32_isSome_iff b).mp (by simp [hwb])
  rw [absQ_eq] at ra rb
  have hq : Rat.abs q < overflowThreshold32 := by
    rw [abs_lt_iff] at *; grind
  rw [← absQ_eq] at hq
  obtain ⟨w, hw⟩ := Option.isSome_iff_exists.mp ((rne32_isSome_iff q).mpr hq)
  obtain ⟨d, hd, _⟩ := rne32_nearestEven hw
  simp [round32Value, hw, hd]

/-- Correctly rounded Ozaki-I on a matrix-core variant: slice counts `ss` in turn, then the exact
product. -/
def mcOzaki1CR (P : Model) (b : ℕ) (ss : List ℕ) (x y : List ℚ) : Option ℚ :=
  ozaki1CR (mcMultiplier P) round32Value b ss x y

/-- Correctly rounded Ozaki-II on a matrix-core variant: configurations `(basis, P)` in turn, then
the exact product. -/
def mcOzaki2CR (P : Model) (cfgs : List (CRTBasis × ℕ)) (x y : List ℚ) : Option ℚ :=
  ozaki2CR (mcMultiplier P) round32Value cfgs x y

def mcOzaki1CRGemm (P : Model) (b : ℕ) (ss : List ℕ) (A B : List (List ℚ)) :
    Option (List (List ℚ)) :=
  A.mapM fun x => (transpose B).mapM fun y => mcOzaki1CR P b ss x y

def mcOzaki2CRGemm (P : Model) (cfgs : List (CRTBasis × ℕ)) (A B : List (List ℚ)) :
    Option (List (List ℚ)) :=
  A.mapM fun x => (transpose B).mapM fun y => mcOzaki2CR P cfgs x y

/-- **Ozaki-I on the matrix core, correctly rounded.** -/
theorem mcOzaki1CR_eq {P : Model} {b : ℕ} (hP : ExactMultiplier P b) (ss : List ℕ) {x y : List ℚ}
    (hlen : x.length = y.length) (hk : x.length * (2 ^ b * 2 ^ b) ≤ 2 ^ 24) :
    mcOzaki1CR P b ss x y = round32Value (dot x y) :=
  ozaki1CR_eq round32Value_nearest round32Value_intervals hP.exactOn ss hlen hk

/-- **Ozaki-II on the matrix core, correctly rounded.** -/
theorem mcOzaki2CR_eq {P : Model} {b : ℕ} (hP : ExactMultiplier P b) {cfgs : List (CRTBasis × ℕ)}
    {x y : List ℚ}
    (hcfg : ∀ c ∈ cfgs, c.1.Valid ∧ (∀ m ∈ c.1.moduli, m ≤ 2 ^ (b + 1)) ∧
      2 * x.length * (2 ^ c.2 * 2 ^ c.2) < c.1.modulus)
    (hlen : x.length = y.length) (hk : x.length * (2 ^ b * 2 ^ b) ≤ 2 ^ 24) :
    mcOzaki2CR P cfgs x y = round32Value (dot x y) :=
  ozaki2CR_eq round32Value_nearest round32Value_intervals hP.exactOn hcfg hlen hk

/-- The Z3 models' Ozaki-I configuration on CDNA 3 fp16, correctly rounded. -/
theorem cdna3F16_ozaki1CR_z3 (ss : List ℕ) {x y : List ℚ} (hlen : x.length = y.length)
    (hk : x.length = z3K) : mcOzaki1CR cdna3F16 11 ss x y = round32Value (dot x y) :=
  mcOzaki1CR_eq (cdna3F16_exactMultiplier (by decide)) ss hlen (by rw [hk]; decide)

/-! ## Entirely on the matrix core -/

theorem finiteValue32_gridMultiple {a : ℚ} (h : FiniteValue32 a) : GridMultiple (-149) a := by
  obtain ⟨k, e, he1, _, _, rfl⟩ := h
  refine ⟨k * ((2 ^ (e + 126).toNat : ℕ) : ℤ), ?_⟩
  rw [pow2_eq, Rat.intCast_mul, Rat.intCast_natCast, ← two_pow_natCast, Rat.mul_assoc,
    ← two_pow_add]
  congr 2; omega

theorem maxFinite32_lt_two_pow : maxFinite32 < (2 : ℚ) ^ (128 : ℤ) := by decide +kernel

theorem splitExp_le_128 {b : ℕ} (hb : b ≤ 129) {x : List ℚ} (hx : ∀ a ∈ x, FiniteValue32 a) :
    splitExp b x ≤ 128 := by
  by_cases hM : maxAbs x = 0
  · unfold splitExp sliceGrid; rw [if_pos hM]; omega
  · have hpos : 0 < maxAbs x := by have := maxAbs_nonneg x; grind
    rw [(splitExp_spec b hM).1]
    apply (ceilLog2_le_iff hpos 128).mpr
    refine maxAbs_le (Rat.le_of_lt (two_pow_pos _)) fun a ha => ?_
    exact Rat.le_of_lt (lt_of_le_of_lt' (finiteValue32_abs_le (hx a ha)) maxFinite32_lt_two_pow)

/-- Correctly rounded Ozaki-I with the exact fallback on matrix-core blocks as well. -/
def mcOzaki1CRE (P : Model) (b : ℕ) (ss : List ℕ) (smax : ℕ) (x y : List ℚ) : Option ℚ :=
  ozaki1CRE (mcMultiplier P) round32Value b ss smax x y

/-- **Ozaki-I on the matrix core, correctly rounded, with every slice product on matrix-core
blocks.** The slicing, the exact sum and the rounding test are exact arithmetic. -/
theorem mcOzaki1CRE_eq {P : Model} {b : ℕ} (hP : ExactMultiplier P b) (ss : List ℕ) {smax : ℕ}
    (hsmax : 277 < smax * (b + 1)) (hb : b ≤ 129) {x y : List ℚ}
    (hx : ∀ a ∈ x, FiniteValue32 a) (hy : ∀ a ∈ y, FiniteValue32 a)
    (hlen : x.length = y.length) (hk : x.length * (2 ^ b * 2 ^ b) ≤ 2 ^ 24) :
    mcOzaki1CRE P b ss smax x y = round32Value (dot x y) := by
  have hc : ((smax * (b + 1) : ℕ) : ℤ) = (smax : ℤ) * ((b : ℤ) + 1) := by simp
  have h277 : (277 : ℤ) < (smax : ℤ) * ((b : ℤ) + 1) := by rw [← hc]; omega
  have hpos : 0 < smax := by
    rcases Nat.eq_zero_or_pos smax with h | h
    · subst h; simp at hsmax
    · exact h
  have hex := splitExp_le_128 hb hx
  have hey := splitExp_le_128 hb hy
  exact ozaki1CRE_eq round32Value_nearest round32Value_intervals hP.exactOn ss hlen hk
    (residualsVanish_of_gridMultiple hpos (fun a ha => finiteValue32_gridMultiple (hx a ha))
      (fun a ha => finiteValue32_gridMultiple (hy a ha)) (by omega) (by omega))

end Ozaki.MC
