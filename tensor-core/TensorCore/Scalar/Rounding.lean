import TensorCore.Scalar.Precision

/-! Total IEEE binary rounding under default non-stop handling. -/

namespace TensorCore.IEEE

/-- Finite conversion returns the proven result for an input within the format's range. -/
def finiteBits (f : BinaryFormat) (mode : BinaryRoundingMode) (x : ℚ)
    (hr : absQ x ≤ f.layout.maxFinite) : Word f :=
  (roundBinary f.layout mode x).get ((roundBinary_isSome_iff _ _ _).mpr ⟨f.valid, hr⟩)

theorem finiteBits_eq (f : BinaryFormat) (mode : BinaryRoundingMode) (x : ℚ)
    (hr : absQ x ≤ f.layout.maxFinite) :
    roundBinary f.layout mode x = some (finiteBits f mode x hr) := by
  exact (Option.some_get _).symm

theorem finiteBits_correct (f : BinaryFormat) (mode : BinaryRoundingMode) (x : ℚ)
    (hr : absQ x ≤ f.layout.maxFinite) :
    BinaryRoundSpec f.layout mode x (finiteBits f mode x hr) := by
  obtain ⟨b, hb, hs⟩ := roundBinary_correct f.layout f.valid mode x hr
  have he := Option.some.inj (hb.symm.trans (finiteBits_eq f mode x hr))
  simpa [← he] using hs

def overflowToInfinity (mode : BinaryRoundingMode) (negative : Bool) : Bool :=
  match mode with
  | .nearestEven => true
  | .truncate => false
  | .towardNegative => negative
  | .towardPositive => !negative

def tiny (f : BinaryFormat) (cfg : Context) (m u : ℚ) : Bool :=
  let a := match cfg.tininess with
    | .beforeRounding => m
    | .afterRounding => u
  decide (0 < a ∧ a < pow2 f.layout.emin)

def round (f : BinaryFormat) (cfg : Context) (zeroSign : Bool) (x : ℚ) : Result f :=
  if x = 0 then ⟨zero f zeroSign, {}⟩ else
  let negative := decide (x < 0)
  let m := absQ x
  let u := precisionMagnitude f.layout cfg.mode negative m
  if hr : m ≤ f.layout.maxFinite then
    let b := finiteBits f cfg.mode x hr
    let inexact := decide (binaryValue f.layout b ≠ some x)
    ⟨b, { inexact, underflow := tiny f cfg m u && inexact }⟩
  else
    let overflow := decide (f.layout.maxFinite < u)
    ⟨if overflow && overflowToInfinity cfg.mode negative then infinity f negative
      else maxFiniteWord f negative,
     { overflow, inexact := true }⟩

/-- IEEE rounding specification: precision optimality, result bits, sign, and exception flags. -/
def RoundSpec (f : BinaryFormat) (cfg : Context) (zeroSign : Bool) (x : ℚ)
    (r : Result f) : Prop :=
  if x = 0 then r.bits = zero f zeroSign ∧ r.flags = {} else
  ∃ u : ℚ, PrecisionRound f.layout cfg.mode (decide (x < 0)) (absQ x) u ∧
    if absQ x ≤ f.layout.maxFinite then
      BinaryRoundSpec f.layout cfg.mode x r.bits ∧
      sign f r.bits = decide (x < 0) ∧
      r.flags.invalid = false ∧ r.flags.divideByZero = false ∧ r.flags.overflow = false ∧
      (r.flags.inexact = true ↔ binaryValue f.layout r.bits ≠ some x) ∧
      (r.flags.underflow = true ↔ tiny f cfg (absQ x) u = true ∧ r.flags.inexact = true)
    else
      (r.flags.overflow = true ↔ f.layout.maxFinite < u) ∧
      r.flags.invalid = false ∧ r.flags.divideByZero = false ∧ r.flags.underflow = false ∧
      r.flags.inexact = true ∧
      r.bits = if f.layout.maxFinite < u ∧ overflowToInfinity cfg.mode (decide (x < 0)) = true
        then infinity f (decide (x < 0)) else maxFiniteWord f (decide (x < 0))

/-- Rounding meets `RoundSpec` for every rational input, with no success premise. -/
theorem round_correct (f : BinaryFormat) (cfg : Context) (zeroSign : Bool) (x : ℚ) :
    RoundSpec f cfg zeroSign x (round f cfg zeroSign x) := by
  by_cases hz : x = 0
  · simp [RoundSpec, round, hz]
  · simp only [RoundSpec, round, hz, ↓reduceIte]
    refine ⟨precisionMagnitude f.layout cfg.mode (decide (x < 0)) (absQ x),
      precisionMagnitude_correct _ _ _ _ (absQ_nonneg x), ?_⟩
    split
    · rename_i hr
      dsimp only
      have hs := roundBinary_sign f.layout cfg.mode x (finiteBits f cfg.mode x hr)
        (finiteBits_eq f cfg.mode x hr)
      exact ⟨finiteBits_correct f cfg.mode x hr, hs, rfl, rfl, rfl,
        by simp, by simp⟩
    · dsimp only
      simp

/-- IEEE rounding and finite binary conversion agree for nonzero inputs within the format's range. -/
theorem round_agrees_finite (f : BinaryFormat) (cfg : Context) (s : Bool) (x : ℚ)
    (hx : x ≠ 0) (hr : absQ x ≤ f.layout.maxFinite) :
    roundBinary f.layout cfg.mode x = some (round f cfg s x).bits := by
  simpa [round, hx, hr] using finiteBits_eq f cfg.mode x hr

theorem round_zero (f : BinaryFormat) (cfg : Context) (s : Bool) :
    round f cfg s 0 = ⟨zero f s, {}⟩ := by simp [round]

theorem round_no_invalid (f : BinaryFormat) (cfg : Context) (s : Bool) (x : ℚ) :
    (round f cfg s x).flags.invalid = false ∧
    (round f cfg s x).flags.divideByZero = false := by
  by_cases hz : x = 0 <;> by_cases hr : absQ x ≤ f.layout.maxFinite <;> simp [round, hz, hr]

theorem round_overflow_inexact (f : BinaryFormat) (cfg : Context) (s : Bool) (x : ℚ) :
    (round f cfg s x).flags.overflow = true → (round f cfg s x).flags.inexact = true := by
  by_cases hz : x = 0 <;> by_cases hr : absQ x ≤ f.layout.maxFinite <;> simp [round, hz, hr]

theorem round_underflow_inexact (f : BinaryFormat) (cfg : Context) (s : Bool) (x : ℚ) :
    (round f cfg s x).flags.underflow = true → (round f cfg s x).flags.inexact = true := by
  by_cases hz : x = 0 <;> by_cases hr : absQ x ≤ f.layout.maxFinite <;> simp [round, hz, hr]

/-- Overflow is flagged exactly when unbounded-exponent rounding exceeds `maxFinite`. -/
theorem round_overflow_iff (f : BinaryFormat) (cfg : Context) (s : Bool) (x : ℚ) :
    (round f cfg s x).flags.overflow = true ↔
      f.layout.maxFinite < precisionMagnitude f.layout cfg.mode (decide (x < 0)) (absQ x) := by
  by_cases hz : x = 0
  · have hp := maxFinite_positive f
    simp [round, hz, precisionMagnitude, absQ, Rat.not_lt.mpr (Rat.le_of_lt hp)]
  · by_cases hr : absQ x ≤ f.layout.maxFinite
    · have hu := precisionMagnitude_le_max f.layout f.valid cfg.mode (decide (x < 0))
        (absQ x) (absQ_nonneg x) hr
      simp [round, hz, hr, Rat.not_lt.mpr hu]
    · simp [round, hz, hr]

end TensorCore.IEEE
