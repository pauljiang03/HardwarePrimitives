import TensorCore.Numerics.CorrectRounding
import TensorCore.Numerics.Sum

/-! Correctly rounded FP32 addition on values, and exact naive summation on a common grid (TC-EFT Definition IV.6, Lemma IV.7, Theorem IV.8). -/

namespace TensorCore

/-- Value of a correctly rounded FP32 addition; `none` outside the finite range. -/
def fp32Add (x y : ℚ) : Option ℚ := (round32 .nearestEven (x + y)).bind value32

/-- Every finite FP32 value lies within `maxFinite32`. -/
theorem finiteValue32_abs_le {z : ℚ} (h : FiniteValue32 z) : absQ z ≤ maxFinite32 := by
  obtain ⟨k, e, _, he2, hk, rfl⟩ := h
  have hq := pow2_pos (e - 23)
  rw [absQ_mul_pos _ _ hq, absQ_intCast]
  have hk' : ((k.natAbs : ℤ) : ℚ) ≤ (16777215 : ℚ) := by
    have h1 : (k.natAbs : ℤ) ≤ 16777215 := by omega
    have h2 := Rat.intCast_le_intCast.mpr h1
    simpa using h2
  have hgrid : pow2 (e - 23) ≤ pow2 104 := pow2_le_of_le (by omega)
  have hnn : (0 : ℚ) ≤ ((k.natAbs : ℤ) : ℚ) := Rat.intCast_nonneg.mpr (by omega)
  have step : ((k.natAbs : ℤ) : ℚ) * pow2 (e - 23) ≤ 16777215 * pow2 104 :=
    calc ((k.natAbs : ℤ) : ℚ) * pow2 (e - 23)
        ≤ ((k.natAbs : ℤ) : ℚ) * pow2 104 := Rat.mul_le_mul_of_nonneg_left hgrid hnn
      _ ≤ 16777215 * pow2 104 :=
          Rat.mul_le_mul_of_nonneg_right hk' (Rat.le_of_lt (pow2_pos _))
  have hmax : maxFinite32 = (16777215 : ℚ) * pow2 104 := by decide +kernel
  rw [hmax]
  exact step

/-- Lemma IV.7: a representable exact result is returned exactly by nearest-even conversion. -/
theorem round32_exact_of_finite {s : ℚ} (h : FiniteValue32 s) :
    ∃ b : F32, round32 .nearestEven s = some b ∧ value32 b = some s := by
  obtain ⟨b, hb, d, hd, hnear, _⟩ := round32_nearestEven_correct s (finiteValue32_abs_le h)
  have hz := hnear s h
  have h0 : absQ (s - s) = 0 := by
    have hss : s - s = 0 := by grind
    rw [hss]; simp [absQ]
  rw [h0] at hz
  have hle := (absQ_le_iff _ _).mp hz
  have hds : d = s := by grind
  subst hds
  exact ⟨b, hb, hd⟩

theorem fp32Add_exact (x y : ℚ) (h : FiniteValue32 (x + y)) : fp32Add x y = some (x + y) := by
  obtain ⟨b, hb, hv⟩ := round32_exact_of_finite h
  unfold fp32Add
  rw [hb]
  exact hv

/-- An integer multiple of a grid between `2^-149` and `2^104` with fewer than 24 significant bits is a finite FP32 value. -/
theorem grid_finiteValue32 (k ℓ : ℤ) (h1 : -149 ≤ ℓ) (h2 : ℓ ≤ 104)
    (hk : k.natAbs < 2 ^ 24) : FiniteValue32 ((k : ℚ) * pow2 ℓ) := by
  refine ⟨k, ℓ + 23, by omega, by omega, hk, ?_⟩
  have he : ℓ + 23 - 23 = ℓ := by omega
  rw [he]

/-- Left-to-right correctly rounded FP32 summation from a starting value (Definition IV.6). -/
def naiveSum32From : ℚ → List ℚ → Option ℚ
  | acc, [] => some acc
  | acc, t :: ts => (fp32Add acc t).bind fun s => naiveSum32From s ts

def naiveSum32 (ts : List ℚ) : Option ℚ := naiveSum32From 0 ts

theorem naiveSum32From_exact (ℓ : ℤ) (h1 : -149 ≤ ℓ) (h2 : ℓ ≤ 104)
    (a : ℤ) (zs : List ℤ) (hbound : a.natAbs + magnitudeSum zs < 2 ^ 24) :
    naiveSum32From ((a : ℚ) * pow2 ℓ) (zs.map fun (z : ℤ) => (z : ℚ) * pow2 ℓ) =
      some (((a + sumZ zs : ℤ) : ℚ) * pow2 ℓ) := by
  induction zs generalizing a with
  | nil => simp [naiveSum32From, sumZ]
  | cons z zs ih =>
    have hsum : (a : ℚ) * pow2 ℓ + (z : ℚ) * pow2 ℓ = ((a + z : ℤ) : ℚ) * pow2 ℓ := by
      rw [Rat.intCast_add]; grind
    have habs := Int.natAbs_add_le a z
    simp only [magnitudeSum] at hbound
    have hstep : fp32Add ((a : ℚ) * pow2 ℓ) ((z : ℚ) * pow2 ℓ) =
        some (((a + z : ℤ) : ℚ) * pow2 ℓ) := by
      rw [← hsum]
      apply fp32Add_exact
      rw [hsum]
      exact grid_finiteValue32 _ _ h1 h2 (by omega)
    have ih' := ih (a + z) (by omega)
    simp only [List.map_cons, naiveSum32From, hstep, Option.bind_some, ih']
    have hs : a + z + sumZ zs = a + sumZ (z :: zs) := by simp only [sumZ]; omega
    rw [hs]

/-- Naive FP32 summation on one grid `2^ℓ` (`-149 ≤ ℓ ≤ 104`) is exact within a 24-bit coefficient bound (TC-EFT paper, Theorem IV.8). -/
theorem naiveSum32_exact (ℓ : ℤ) (h1 : -149 ≤ ℓ) (h2 : ℓ ≤ 104) (zs : List ℤ)
    (hbound : magnitudeSum zs < 2 ^ 24) :
    naiveSum32 (zs.map fun (z : ℤ) => (z : ℚ) * pow2 ℓ) = some ((sumZ zs : ℚ) * pow2 ℓ) := by
  have h := naiveSum32From_exact ℓ h1 h2 0 zs (by simpa using hbound)
  unfold naiveSum32
  simpa using h

/-- Executable representability: nearest-even conversion returns the value itself. -/
def representable32 (x : ℚ) : Bool := (round32 .nearestEven x).bind value32 == some x

theorem representable32_finite {x : ℚ} (h : representable32 x = true) : FiniteValue32 x := by
  unfold representable32 at h
  cases hr : round32 .nearestEven x with
  | none => simp [hr] at h
  | some b =>
    simp only [hr, Option.bind_some, beq_iff_eq] at h
    exact value32_finite b x h

end TensorCore
