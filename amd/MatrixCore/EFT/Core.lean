import MatrixCore.EFT.Sum32

/-! # Splitting a block at a cut-off bit

Every term is split at a cut-off bit `2^q` into a high and a low part; the exact sum is the sum of
the high parts plus the low parts. A fast FP32 path, guarded by a bit-span check, and an exact
fallback round it once. -/

namespace MatrixCore

/-- How a term is split at the cut-off: magnitude truncation, or RD. -/
inductive SplitRule where
  | trunc
  | rd
  deriving Repr, DecidableEq

def SplitRule.high : SplitRule → ℚ → ℤ → ℚ
  | .trunc, x, q => truncGrid x q
  | .rd, x, q => rdGrid x q

/-- The terms of one block (`c`, then the products) with their split rules, and the cut-off `q`. -/
structure EftSplit where
  q : ℤ
  terms : List (SplitRule × ℚ)
  deriving Repr, DecidableEq

namespace EftSplit

def highs (s : EftSplit) : List ℚ := s.terms.map fun t => t.1.high t.2 s.q

/-- The low parts: the bits of every term below the cut-off. -/
def lows (s : EftSplit) : List ℚ := s.terms.map fun t => t.2 - t.1.high t.2 s.q

/-- `H`, the sum of the high parts. -/
def H (s : EftSplit) : ℚ := sumQ s.highs

/-- The exact sum `S` of the terms. -/
def exact (s : EftSplit) : ℚ := sumQ (s.terms.map Prod.snd)

/-- The overlap `εₒ = D − H`. -/
def overlap (s : EftSplit) (D : ℚ) : ℚ := D - s.H

end EftSplit

/-! ## The fast path and its guard -/

def trailingZerosAux : ℕ → ℕ → ℕ
  | 0, _ => 0
  | fuel + 1, n => if n ≠ 0 ∧ n % 2 = 0 then trailingZerosAux fuel (n / 2) + 1 else 0

def lowestBitExp (x : ℚ) : ℤ :=
  (trailingZerosAux x.num.natAbs x.num.natAbs : ℤ) - (x.den.log2 : ℤ)

namespace EftSplit

def lowBit (s : EftSplit) : ℤ :=
  s.lows.foldl (fun e x => if x = 0 then e else min e (lowestBitExp x)) s.q

def lowCoeffs (s : EftSplit) : List ℤ := s.lows.map fun e => (e / pow2 s.lowBit).floor

/-- The fast-path check: the low parts fit 24 bits above their lowest bit; `εₒ` and `H` are FP32. -/
def guard (s : EftSplit) (D : ℚ) : Bool :=
  decide (-149 ≤ s.lowBit) &&
  (s.lows == s.lowCoeffs.map fun (z : ℤ) => (z : ℚ) * pow2 s.lowBit) &&
  decide (magnitudeSum s.lowCoeffs < 2 ^ 24) &&
  decide ((magnitudeSum s.lowCoeffs : ℚ) * pow2 s.lowBit < pow2 128) &&
  representable32 (s.overlap D) && representable32 s.H

/-- The fast path: FP32 sum of the low parts, `D − εₒ` in FP32, and one rounded FP32 addition. -/
def fastPath (s : EftSplit) (D : ℚ) : Option F32 :=
  (naiveSum32 s.lows).bind fun e => (fp32Add D (-s.overlap D)).bind fun h => rne32 (h + e)

/-- The exact fallback: `D − εₒ + Σ low parts` in exact arithmetic, rounded once. -/
def exactPath (s : EftSplit) (D : ℚ) : Option F32 := rne32 (D - s.overlap D + sumQ s.lows)

end EftSplit

/-- Outcome of the correction: fast path, exact fallback, or an exact sum beyond the FP32 range. -/
inductive EftResult where
  | fast (bits : F32)
  | exact (bits : F32)
  | outOfRange
  deriving Repr, DecidableEq

def EftResult.bits : EftResult → Option F32
  | .fast b => some b
  | .exact b => some b
  | .outOfRange => none

/-- The correction: the fast path when the guard holds, otherwise the exact fallback. -/
def EftSplit.run (s : EftSplit) (D : ℚ) : EftResult :=
  if s.guard D then
    match s.fastPath D with
    | some b => .fast b
    | none => .outOfRange
  else
    match s.exactPath D with
    | some b => .exact b
    | none => .outOfRange

/-! ## Correctness -/

namespace EftSplit

theorem high_onGrid (r : SplitRule) (x : ℚ) (q : ℤ) : OnGrid (r.high x q) q := by
  cases r
  · exact truncGrid_onGrid x q
  · exact rdGrid_onGrid x q

theorem low_abs_lt (r : SplitRule) (x : ℚ) (q : ℤ) : absQ (x - r.high x q) < pow2 q := by
  cases r
  · exact (truncGrid_bounds x q).2.1
  · have := rdGrid_bounds x q
    show absQ (x - rdGrid x q) < pow2 q
    rw [absQ_lt_iff]; constructor <;> grind

theorem lows_abs_lt (s : EftSplit) : ∀ e ∈ s.lows, absQ e < pow2 s.q := by
  intro e he
  simp only [lows, List.mem_map] at he
  obtain ⟨t, _, rfl⟩ := he
  exact low_abs_lt t.1 t.2 s.q

theorem H_onGrid (s : EftSplit) : OnGrid s.H s.q := by
  apply onGrid_sumQ
  intro v hv
  simp only [highs, List.mem_map] at hv
  obtain ⟨t, _, rfl⟩ := hv
  exact high_onGrid t.1 t.2 s.q

theorem exact_eq (s : EftSplit) : s.exact = s.H + sumQ s.lows := by
  unfold exact H highs lows
  rw [← sumQ_map_add]
  congr 1
  apply List.map_congr_left
  intro t _
  grind

/-- `S = D − εₒ + Σ εᵢ`, for any `D`. -/
theorem recovery (s : EftSplit) (D : ℚ) : s.exact = D - s.overlap D + sumQ s.lows := by
  rw [exact_eq]; unfold overlap; grind

/-- The overlap is the error of `D` plus the low parts: `εₒ = (D − S) + Σ εᵢ`. -/
theorem overlap_eq (s : EftSplit) (D : ℚ) : s.overlap D = (D - s.exact) + sumQ s.lows := by
  rw [exact_eq]; unfold overlap; grind

theorem sumQ_lows_abs_le (s : EftSplit) : absQ (sumQ s.lows) ≤ s.terms.length * pow2 s.q := by
  refine Rat.le_trans (absQ_sumQ_le _) ?_
  have := sumQ_map_le s.lows absQ (pow2 s.q) (fun e he => Rat.le_of_lt (s.lows_abs_lt e he))
  simpa [lows] using this

theorem exactPath_eq (s : EftSplit) (D : ℚ) : s.exactPath D = rne32 s.exact := by
  rw [exactPath, ← recovery]

/-- Under the guard, every FP32 step of the fast path but the last is exact. -/
theorem fastPath_sound (s : EftSplit) (D : ℚ) (h : s.guard D = true) :
    naiveSum32 s.lows = some (sumQ s.lows) ∧ fp32Add D (-s.overlap D) = some s.H ∧
      s.fastPath D = rne32 s.exact := by
  unfold guard at h
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h
  obtain ⟨⟨⟨⟨⟨h1, hgrid⟩, hmag⟩, hrange⟩, _⟩, hH⟩ := h
  have hsum : naiveSum32 s.lows = some (sumQ s.lows) := by
    rw [hgrid, naiveSum32_exact _ h1 _ hmag hrange, sumQ_map_intCast_mul]
  have hsub : fp32Add D (-s.overlap D) = some s.H := by
    have hr : D + -s.overlap D = s.H := by unfold overlap; grind
    rw [← hr]
    exact fp32Add_exact (by rw [hr]; exact representable32_finite hH)
  refine ⟨hsum, hsub, ?_⟩
  unfold fastPath
  rw [hsum, Option.bind_some, hsub, Option.bind_some, exact_eq]

/-- Whichever path runs, the result is RNE of the exact sum, for any `D`. -/
theorem run_bits (s : EftSplit) (D : ℚ) : (s.run D).bits = rne32 s.exact := by
  unfold run
  split
  · rename_i hg
    rw [← (fastPath_sound s D hg).2.2]
    cases s.fastPath D <;> rfl
  · rw [← exactPath_eq]
    cases s.exactPath D <;> rfl

/-- The fast path is taken exactly when the guard holds and the rounded sum is finite. -/
theorem run_fast_iff (s : EftSplit) (D : ℚ) :
    (∃ b, s.run D = .fast b) ↔ s.guard D = true ∧ (rne32 s.exact).isSome = true := by
  unfold run
  constructor
  · rintro ⟨b, hb⟩
    split at hb
    · rename_i hg
      refine ⟨hg, ?_⟩
      rw [← (fastPath_sound s D hg).2.2]
      split at hb
      · rename_i b' hb'; rw [hb']; rfl
      · cases hb
    · split at hb <;> cases hb
  · rintro ⟨hg, hs⟩
    rw [if_pos hg, (fastPath_sound s D hg).2.2]
    obtain ⟨b, hb⟩ := Option.isSome_iff_exists.mp hs
    exact ⟨b, by rw [hb]⟩

/-- A value is returned exactly when RNE of the exact sum is finite. -/
theorem run_isSome_iff (s : EftSplit) (D : ℚ) :
    (s.run D).bits.isSome = true ↔ absQ s.exact < overflowThreshold32 := by
  rw [run_bits]; exact rne32_isSome_iff _

end EftSplit

end MatrixCore
