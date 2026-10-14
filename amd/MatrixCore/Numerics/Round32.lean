import MatrixCore.Numerics.Format

/-! # Rounding to binary32

`fl{·}` of the paper: normalization followed by round-to-nearest, ties-to-even (RNE) into
binary32, with gradual underflow. A result that rounds beyond the largest finite value is an
overflow (`none`); the special-value layer reports it as an infinity. -/

namespace MatrixCore

/-- Nearest integer, ties to even. -/
def rneInt (t : ℚ) : ℤ :=
  if 1 < 2 * (t - t.floor) ∨ (2 * (t - t.floor) = 1 ∧ t.floor % 2 = 1) then t.floor + 1
  else t.floor

/-- Exponent of the binade in which a nonzero magnitude is rounded: `⌊log₂ a⌋`, but not below
binary32's minimum normal exponent `−126` (gradual underflow). Also the paper's
*subnormal-aware normalization*. -/
def normExp (a : ℚ) : ℤ := max (log2Floor a) (-126)

/-- binary32 word from a sign, an exponent `−126 ≤ e ≤ 127`, and an integer significand
`m < 2^24` with `23` mantissa bits (`m < 2^23` only for `e = −126`). -/
def encode32 (negative : Bool) (e : ℤ) (m : ℕ) : F32 :=
  BitVec.ofNat 32 ((if negative then 2147483648 else 0) +
    (if m < 8388608 then m else (e + 127).toNat * 8388608 + (m - 8388608)))

/-- RNE significand and exponent of a nonzero magnitude, before the exponent-range check;
the significand `2^24` is carried into the next binade. -/
def rneFields (a : ℚ) : ℤ × ℕ :=
  let e := normExp a
  let k := rneInt (a / pow2 (e - 23))
  if k = 16777216 then (e + 1, 8388608) else (e, k.toNat)

/-- `fl{x}`: binary32 RNE. `none` exactly when the rounded magnitude exceeds the finite range. -/
def rne32 (x : ℚ) : Option F32 :=
  if x = 0 then some 0
  else
    let (e, m) := rneFields (absQ x)
    if e > 127 then none else some (encode32 (decide (x < 0)) e m)

/-- Largest finite binary32 magnitude, `(2 − 2^-23)·2^127`. -/
def maxFinite32 : ℚ := 16777215 * pow2 104

/-- RNE overflows at and above `maxFinite32 + 2^103 = 2^128 − 2^103`. -/
def overflowThreshold32 : ℚ := pow2 128 - pow2 103

/-- A binary32 word whose exponent field is zero and mantissa nonzero. -/
def isSubnormal32 (w : F32) : Bool :=
  w.toNat / 8388608 % 256 == 0 && w.toNat % 8388608 != 0

/-- Keep only the sign bit. -/
def signedZero32 (w : F32) : F32 := BitVec.ofNat 32 (w.toNat / 2147483648 % 2 * 2147483648)

/-- `fl{x}` with optional flushing of subnormal results to a zero of the same sign (CDNA 2). -/
def fl32 (ftz : Bool) (x : ℚ) : Option F32 :=
  match rne32 x with
  | none => none
  | some w => some (if ftz && isSubnormal32 w then signedZero32 w else w)

/-! ## Nearest integer -/

theorem rneInt_cases (t : ℚ) :
    (rneInt t = t.floor + 1 ∧
      (1 < 2 * (t - t.floor) ∨ (2 * (t - t.floor) = 1 ∧ t.floor % 2 = 1))) ∨
    (rneInt t = t.floor ∧
      ¬(1 < 2 * (t - t.floor) ∨ (2 * (t - t.floor) = 1 ∧ t.floor % 2 = 1))) := by
  unfold rneInt; split <;> simp [*]

theorem intCast_le_or_succ_le (j k : ℤ) : (j : ℚ) ≤ k ∨ (k : ℚ) + 1 ≤ j := by
  by_cases h : j ≤ k
  · exact Or.inl (Rat.intCast_le_intCast.mpr h)
  · right
    have : k + 1 ≤ j := by omega
    have h' := Rat.intCast_le_intCast.mpr this
    simpa [Rat.intCast_add, Rat.intCast_one] using h'

/-- The selected integer is within one half. -/
theorem rneInt_dist (t : ℚ) : 2 * absQ (t - rneInt t) ≤ 1 := by
  have h := floor_bounds t
  rcases rneInt_cases t with ⟨hk, hc⟩ | ⟨hk, hc⟩ <;> rw [hk] <;>
    (try simp only [Rat.intCast_add, Rat.intCast_one]) <;> unfold absQ <;> split <;> grind

/-- The selected integer is at least as close as every integer. -/
theorem rneInt_nearest (t : ℚ) (j : ℤ) : absQ (t - rneInt t) ≤ absQ (t - j) := by
  have h := floor_bounds t
  have hj := intCast_le_or_succ_le j t.floor
  rcases rneInt_cases t with ⟨hk, hc⟩ | ⟨hk, hc⟩ <;> rw [hk] <;>
    (try simp only [Rat.intCast_add, Rat.intCast_one]) <;> unfold absQ <;> split <;> split <;>
    grind

/-- An equally close different integer forces a tie, which selects an even integer. -/
theorem rneInt_tie_even (t : ℚ) (j : ℤ) (htie : absQ (t - j) = absQ (t - rneInt t))
    (hne : j ≠ rneInt t) : rneInt t % 2 = 0 := by
  have h := floor_bounds t
  have hj := intCast_le_or_succ_le j t.floor
  have hj2 := intCast_le_or_succ_le (t.floor + 1) j
  simp only [Rat.intCast_add, Rat.intCast_one] at hj2
  rcases rneInt_cases t with ⟨hk, hc⟩ | ⟨hk, hc⟩ <;> rw [hk] at htie hne ⊢
  · have hne' : (j : ℚ) ≠ (t.floor : ℚ) + 1 := by
      intro he
      apply hne
      have : (j : ℚ) = ((t.floor + 1 : ℤ) : ℚ) := by
        simpa [Rat.intCast_add, Rat.intCast_one] using he
      exact Rat.intCast_inj.mp this
    simp only [Rat.intCast_add, Rat.intCast_one] at htie
    have hf : 2 * (t - t.floor) = 1 := by
      unfold absQ at htie; split at htie <;> split at htie <;> grind
    rcases hc with hc | ⟨_, hodd⟩
    · exfalso; rw [hf] at hc; exact Rat.lt_irrefl hc
    · omega
  · have hne' : (j : ℚ) ≠ (t.floor : ℚ) := fun he => hne (Rat.intCast_inj.mp he)
    have hf : 2 * (t - t.floor) = 1 := by
      unfold absQ at htie; split at htie <;> split at htie <;> grind
    have : ¬ (t.floor % 2 = 1) := fun hodd => hc (Or.inr ⟨hf, hodd⟩)
    omega

theorem rneInt_nonneg {t : ℚ} (h : 0 ≤ t) : 0 ≤ rneInt t := by
  have : (0 : ℤ) ≤ t.floor := Rat.le_floor_iff.mpr (by simpa using h)
  rcases rneInt_cases t with ⟨hk, _⟩ | ⟨hk, _⟩ <;> omega

/-- RNE of a value below an integer bound `n` is at most `n`. -/
theorem rneInt_le_of_lt {t : ℚ} {n : ℤ} (h : t < n) : rneInt t ≤ n := by
  have hf : t.floor < n := Rat.floor_lt_iff.mpr h
  rcases rneInt_cases t with ⟨hk, _⟩ | ⟨hk, _⟩ <;> omega

/-- RNE of a value at least an integer bound `n` is at least `n`. -/
theorem le_rneInt_of_le {t : ℚ} {n : ℤ} (h : (n : ℚ) ≤ t) : n ≤ rneInt t := by
  have hf : n ≤ t.floor := Rat.le_floor_iff.mpr h
  rcases rneInt_cases t with ⟨hk, _⟩ | ⟨hk, _⟩ <;> omega

/-- RNE of an integer is itself. -/
theorem rneInt_intCast (k : ℤ) : rneInt (k : ℚ) = k := by
  unfold rneInt
  rw [Rat.floor_intCast]
  have : 2 * ((k : ℚ) - k) = 0 := by grind
  rw [this]
  have h1 : ¬ ((1 : ℚ) < 0) := by decide
  have h2 : ¬ ((0 : ℚ) = 1) := by decide
  simp [h1, h2]

end MatrixCore
