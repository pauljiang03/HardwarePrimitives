import TensorCore.Numerics.Binary.CorrectRounding
import TensorCore.Numerics.Sum
import TensorCore.Numerics.ScalarSum

/-! TC-EFT Lemma IV.7 and Theorem IV.8 for every well-formed IEEE-style format. -/

namespace TensorCore

theorem Format.finiteValue_abs_le (f : Format) {z : ℚ} (h : f.FiniteValue z) :
    absQ z ≤ f.maxFinite := by
  obtain ⟨k, e, _, he, hk, rfl⟩ := h
  rw [absQ_mul_pos _ _ (pow2_pos _), absQ_intCast]
  have hk' : ((k.natAbs : ℤ) : ℚ) ≤ ((2 ^ (f.mantissaBits + 1) - 1 : ℕ) : ℚ) := by
    rw [Rat.intCast_natCast]
    exact Rat.natCast_le_natCast.mpr (by omega)
  exact Rat.le_trans
    (Rat.mul_le_mul_of_nonneg_left (pow2_le_of_le (by omega))
      (Rat.intCast_nonneg.mpr (by omega)))
    (Rat.mul_le_mul_of_nonneg_right hk' (Rat.le_of_lt (pow2_pos _)))

/-- Correct rounding fixes a representable exact result (Lemma IV.7). -/
theorem roundBinary_exact_of_finite (f : Format) (hf : f.WellFormed) {s : ℚ}
    (h : f.FiniteValue s) :
    ∃ b, roundBinary f .nearestEven s = some b ∧ binaryValue f b = some s := by
  obtain ⟨b, hb, d, hd, hn, _⟩ := roundBinary_nearestEven_correct f hf s (f.finiteValue_abs_le h)
  have hz := hn s h
  have h0 : absQ (s - s) = 0 := by
    rw [show s - s = 0 by grind]; simp [absQ]
  rw [h0] at hz
  have hle := (absQ_le_iff _ _).mp hz
  have hds : d = s := by grind
  subst hds
  exact ⟨b, hb, hd⟩

/-- Scalar nearest-even addition on values, rejecting exact sums outside the finite range. -/
def binaryAdd (f : Format) (x y : ℚ) : Option ℚ :=
  (roundBinary f .nearestEven (x + y)).bind (binaryValue f)

theorem binaryAdd_exact (f : Format) (hf : f.WellFormed) (x y : ℚ)
    (h : f.FiniteValue (x + y)) : binaryAdd f x y = some (x + y) := by
  obtain ⟨b, hb, hv⟩ := roundBinary_exact_of_finite f hf h
  unfold binaryAdd
  rw [hb]
  exact hv

theorem grid_finiteValue (f : Format) (k ℓ : ℤ)
    (h1 : f.emin - f.mantissaBits ≤ ℓ) (h2 : ℓ ≤ f.emax - f.mantissaBits)
    (hk : k.natAbs < 2 ^ (f.mantissaBits + 1)) : f.FiniteValue ((k : ℚ) * pow2 ℓ) := by
  refine ⟨k, ℓ + f.mantissaBits, by omega, by omega, hk, ?_⟩
  rw [show ℓ + f.mantissaBits - f.mantissaBits = ℓ by omega]

theorem grid_finiteValue_of_range (f : Format) (hf : f.WellFormed) (k ℓ : ℤ)
    (h1 : f.emin - f.mantissaBits ≤ ℓ) (hk : k.natAbs < 2 ^ (f.mantissaBits + 1))
    (hr : absQ ((k : ℚ) * pow2 ℓ) ≤ f.maxFinite) : f.FiniteValue ((k : ℚ) * pow2 ℓ) := by
  by_cases h2 : ℓ ≤ f.emax - f.mantissaBits
  · exact grid_finiteValue f k ℓ h1 h2 hk
  · let g := f.emax - f.mantissaBits
    let n := (ℓ - g).toNat
    have hn : ℓ = g + (n : ℤ) := by dsimp [n, g]; omega
    have hv : (k : ℚ) * pow2 ℓ = ((k * (2 ^ n : ℕ) : ℤ) : ℚ) * pow2 g := by
      rw [hn, pow2_add, pow2_natCast, Rat.intCast_mul, Rat.intCast_natCast]
      grind
    rw [hv, absQ_mul_pos _ _ (pow2_pos _), absQ_intCast] at hr
    change (((k * (2 ^ n : ℕ)).natAbs : ℤ) : ℚ) * pow2 g ≤
      ((2 ^ (f.mantissaBits + 1) - 1 : ℕ) : ℚ) * pow2 g at hr
    have hcoeff := Rat.le_of_mul_le_mul_right hr (pow2_pos g)
    rw [Rat.intCast_natCast] at hcoeff
    have hcoeff' := Rat.natCast_le_natCast.mp hcoeff
    rw [hv]
    exact grid_finiteValue f _ g (by have := f.emin_le_emax hf; dsimp [g]; omega)
      (Int.le_refl _) (by omega)

def naiveSumBinaryFrom (f : Format) : ℚ → List ℚ → Option ℚ
  | acc, [] => some acc
  | acc, t :: ts => (binaryAdd f acc t).bind fun s => naiveSumBinaryFrom f s ts

def naiveSumBinary (f : Format) (ts : List ℚ) : Option ℚ := naiveSumBinaryFrom f 0 ts

theorem naiveSumBinaryFrom_exact (f : Format) (hf : f.WellFormed) (ℓ : ℤ)
    (h1 : f.emin - f.mantissaBits ≤ ℓ) (a : ℤ) (zs : List ℤ)
    (hbound : a.natAbs + magnitudeSum zs < 2 ^ (f.mantissaBits + 1))
    (hrange : ((a.natAbs + magnitudeSum zs : ℕ) : ℚ) * pow2 ℓ ≤ f.maxFinite) :
    naiveSumBinaryFrom f ((a : ℚ) * pow2 ℓ) (zs.map fun (z : ℤ) => (z : ℚ) * pow2 ℓ) =
      some (((a + sumZ zs : ℤ) : ℚ) * pow2 ℓ) := by
  induction zs generalizing a with
  | nil => simp [naiveSumBinaryFrom, sumZ]
  | cons z zs ih =>
    have hsum : (a : ℚ) * pow2 ℓ + (z : ℚ) * pow2 ℓ = ((a + z : ℤ) : ℚ) * pow2 ℓ := by
      rw [Rat.intCast_add]; grind
    have habs := Int.natAbs_add_le a z
    have hnext : (a + z).natAbs + magnitudeSum zs ≤ a.natAbs + magnitudeSum (z :: zs) := by
      simp only [magnitudeSum]; omega
    have hrnext : (((a + z).natAbs + magnitudeSum zs : ℕ) : ℚ) * pow2 ℓ ≤ f.maxFinite :=
      Rat.le_trans (Rat.mul_le_mul_of_nonneg_right (Rat.natCast_le_natCast.mpr hnext)
        (Rat.le_of_lt (pow2_pos _))) hrange
    have hrstep : absQ (((a + z : ℤ) : ℚ) * pow2 ℓ) ≤ f.maxFinite := by
      rw [absQ_mul_pos _ _ (pow2_pos _), absQ_intCast, Rat.intCast_natCast]
      exact Rat.le_trans (Rat.mul_le_mul_of_nonneg_right
        (Rat.natCast_le_natCast.mpr (Nat.le_add_right _ _)) (Rat.le_of_lt (pow2_pos _))) hrnext
    have hstep : binaryAdd f ((a : ℚ) * pow2 ℓ) ((z : ℚ) * pow2 ℓ) =
        some (((a + z : ℤ) : ℚ) * pow2 ℓ) := by
      rw [← hsum]
      apply binaryAdd_exact f hf
      rw [hsum]
      exact grid_finiteValue_of_range f hf _ ℓ h1 (by omega) hrstep
    have ih' := ih (a + z) (by omega) hrnext
    simp only [List.map_cons, naiveSumBinaryFrom, hstep, Option.bind_some, ih']
    rw [show a + z + sumZ zs = a + sumZ (z :: zs) by simp only [sumZ]; omega]

/-- Theorem IV.8, with its minimum-grid, coefficient and absolute-range conditions. -/
theorem naiveSumBinary_exact (f : Format) (hf : f.WellFormed) (ℓ : ℤ)
    (h1 : f.emin - f.mantissaBits ≤ ℓ) (zs : List ℤ)
    (hbound : magnitudeSum zs < 2 ^ (f.mantissaBits + 1))
    (hrange : (magnitudeSum zs : ℚ) * pow2 ℓ ≤ f.maxFinite) :
    naiveSumBinary f (zs.map fun (z : ℤ) => (z : ℚ) * pow2 ℓ) = some ((sumZ zs : ℚ) * pow2 ℓ) := by
  simpa [naiveSumBinary] using naiveSumBinaryFrom_exact f hf ℓ h1 0 zs
    (by simpa using hbound) (by simpa using hrange)

theorem coefficient_range_of_grid (f : Format) (ℓ : ℤ) (L : ℕ)
    (h2 : ℓ ≤ f.emax - f.mantissaBits) (hL : L < 2 ^ (f.mantissaBits + 1)) :
    (L : ℚ) * pow2 ℓ ≤ f.maxFinite := by
  have hL' : (L : ℚ) ≤ ((2 ^ (f.mantissaBits + 1) - 1 : ℕ) : ℚ) :=
    Rat.natCast_le_natCast.mpr (by omega)
  exact Rat.le_trans (Rat.mul_le_mul_of_nonneg_left (pow2_le_of_le h2) Rat.natCast_nonneg)
    (Rat.mul_le_mul_of_nonneg_right hL' (Rat.le_of_lt (pow2_pos _)))

/-- Table IV, FP64 instance: precision 53 and minimum grid `2^-1074`. -/
theorem naiveSum64_exact (ℓ : ℤ) (h1 : -1074 ≤ ℓ) (zs : List ℤ)
    (hbound : magnitudeSum zs < 2 ^ 53)
    (hrange : (magnitudeSum zs : ℚ) * pow2 ℓ ≤ fp64.maxFinite) :
    naiveSumBinary fp64 (zs.map fun (z : ℤ) => (z : ℚ) * pow2 ℓ) =
      some ((sumZ zs : ℚ) * pow2 ℓ) :=
  naiveSumBinary_exact fp64 (by decide) ℓ h1 zs hbound hrange

set_option maxRecDepth 4096 in
theorem binaryAdd_fp32 (x y : ℚ) : binaryAdd fp32 x y = fp32Add x y := rfl

theorem naiveSumBinaryFrom_fp32 (a : ℚ) (ts : List ℚ) :
    naiveSumBinaryFrom fp32 a ts = naiveSum32From a ts := by
  induction ts generalizing a with
  | nil => rfl
  | cons t ts ih =>
    simp only [naiveSumBinaryFrom, naiveSum32From, binaryAdd_fp32]
    congr 1
    funext s
    exact ih s

theorem naiveSumBinary_fp32 (ts : List ℚ) : naiveSumBinary fp32 ts = naiveSum32 ts :=
  naiveSumBinaryFrom_fp32 0 ts

/-- Theorem IV.8 in any summation order. -/
theorem naiveSumBinary_exact_perm (f : Format) (hf : f.WellFormed) (ℓ : ℤ)
    (h1 : f.emin - f.mantissaBits ≤ ℓ) (xs ys : List ℤ) (hperm : xs.Perm ys)
    (hbound : magnitudeSum xs < 2 ^ (f.mantissaBits + 1))
    (hrange : (magnitudeSum xs : ℚ) * pow2 ℓ ≤ f.maxFinite) :
    naiveSumBinary f (ys.map fun (z : ℤ) => (z : ℚ) * pow2 ℓ) =
      some ((sumZ xs : ℚ) * pow2 ℓ) := by
  rw [magnitudeSum_perm hperm] at hbound hrange
  rw [naiveSumBinary_exact f hf ℓ h1 ys hbound hrange, sumZ_perm hperm]

/-- Naive summation is exact when the summands fit within a bounded bit span. -/
theorem naiveSumBinary_exact_of_bitSpan (f : Format) (hf : f.WellFormed) (b ℓ : ℤ)
    (h1 : f.emin - f.mantissaBits ≤ ℓ) (zs : List ℤ)
    (hterm : ∀ z ∈ zs, absQ ((z : ℚ) * pow2 ℓ) < pow2 (b + 1))
    (hspan : b - ℓ + 1 + (ceilLog2 zs.length : ℤ) ≤ f.mantissaBits + 1)
    (hrange : (magnitudeSum zs : ℚ) * pow2 ℓ ≤ f.maxFinite) :
    naiveSumBinary f (zs.map fun (z : ℤ) => (z : ℚ) * pow2 ℓ) =
      some ((sumZ zs : ℚ) * pow2 ℓ) :=
  naiveSumBinary_exact f hf ℓ h1 zs (bitSpan_coefficient_bound zs b ℓ _ hterm hspan) hrange

def representableBinary (f : Format) (x : ℚ) : Bool :=
  (roundBinary f .nearestEven x).bind (binaryValue f) == some x

theorem representableBinary_finite (f : Format) (hf : f.WellFormed) {x : ℚ}
    (h : representableBinary f x = true) : f.FiniteValue x := by
  unfold representableBinary at h
  cases hr : roundBinary f .nearestEven x with
  | none => simp [hr] at h
  | some b =>
    simp only [hr, Option.bind_some, beq_iff_eq] at h
    unfold binaryValue at h
    cases hd : (classify f b).finite with
    | none => simp [hd] at h
    | some d =>
      simp only [hd, Option.map_some, Option.some.injEq] at h
      rw [← h]
      exact classifyNat_finiteValue f hf b.toNat d hd

end TensorCore
