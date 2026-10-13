import TensorCore.EFT.Defs
import TensorCore.Numerics.ScalarSum
import TensorCore.TC.StageResiduals
import TensorCore.Numerics.Truncation
import TensorCore.Numerics.Sum

/-! Exact sum recovery and the scalar fast-path check. -/

namespace TensorCore

/-- Lemma IV.1: every low component is strictly below the extraction grid. -/
theorem lowPart_bound (t : BlockTrace) :
    ∀ e ∈ t.lowParts, absQ e < pow2 t.extractionExponent := by
  intro e he
  simp only [BlockTrace.lowParts, List.mem_map] at he
  obtain ⟨x, _, rfl⟩ := he
  exact (alignment_residual x.value t.extractionExponent).2

/-- Theorem IV.5, overlap form: `S = D − ε_o + Σ εᵢ`. -/
theorem overlap_recovery (t : BlockTrace) :
    t.block.exactDot = t.output.value - t.overlap + sumQ t.lowParts := by
  have h := sum_stage_residuals (t.block.terms.map DenormalizedProduct.value)
    (fun x => truncGrid x t.extractionExponent)
  rw [terms_value] at h
  simp only [List.map_map, Function.comp_def] at h
  change t.block.exactDot = sumQ t.coarse + sumQ t.lowParts at h
  unfold BlockTrace.overlap BlockTrace.retainedSum
  grind

/-! Lemma IV.3 rests on one fact about nested grids: truncating to a fine grid equals truncating to a coarser grid and then truncating the remainder to the fine grid. -/

/-- Lemma IV.3, summed: the aligned accumulator is `H + Σ φ(εᵢ)`. -/
theorem accumulator_eq_retained (t : BlockTrace) :
    t.block.accumulator = t.retainedSum + sumQ t.retainedLowParts := by
  have hτ : ∃ τ : ℕ, t.extractionExponent = t.block.alignGridExponent + τ := by
    refine ⟨(t.extractionExponent - t.block.alignGridExponent).toNat, ?_⟩
    unfold BlockTrace.extractionExponent
    omega
  obtain ⟨τ, hτ⟩ := hτ
  rw [accumulator_value]
  unfold BlockTrace.retainedSum BlockTrace.retainedLowParts BlockTrace.lowParts BlockTrace.coarse
  rw [List.map_map]
  have hsplit : (fun x : DenormalizedProduct => truncGrid x.value t.block.alignGridExponent) =
      fun x => truncGrid x.value t.extractionExponent +
        truncGrid (x.value - truncGrid x.value t.extractionExponent) t.block.alignGridExponent := by
    funext x
    rw [hτ]
    exact truncGrid_split x.value t.block.alignGridExponent τ
  rw [hsplit, sumQ_map_add]
  rfl

/-- Lemma IV.4: `ε_o = Σ φ(εᵢ) − r_out`. -/
theorem overlap_eq_retained_sub_outputResidual (t : BlockTrace) :
    t.overlap = sumQ t.retainedLowParts - t.outputResidual := by
  have h := accumulator_eq_retained t
  unfold BlockTrace.overlap BlockTrace.outputResidual
  grind

/-- Number of trailing zero bits of `n` (`0` for `n = 0`), by structural recursion on fuel. -/
def trailingZeroBitsAux : ℕ → ℕ → ℕ
  | 0, _ => 0
  | fuel + 1, n => if n ≠ 0 ∧ n % 2 = 0 then trailingZeroBitsAux fuel (n / 2) + 1 else 0

def trailingZeroBits (n : ℕ) : ℕ := trailingZeroBitsAux n n

/-- Exponent of the lowest set bit of a nonzero dyadic rational: `x = odd · 2^(lowestBitExp x)`. -/
def lowestBitExp (x : ℚ) : ℤ := (trailingZeroBits x.num.natAbs : ℤ) - (x.den.log2 : ℤ)

/-- Lowest bit actually set in any low part, capped at the extraction grid; zeros are ignored. -/
def BlockTrace.lowestLowBitExp (t : BlockTrace) : ℤ :=
  t.lowParts.foldl (fun e x => if x = 0 then e else min e (lowestBitExp x)) t.extractionExponent

/-- Integer coefficients `zᵢ = εᵢ / 2^ℓ`. -/
def BlockTrace.lowBits (t : BlockTrace) : List ℤ :=
  let q := pow2 t.lowestLowBitExp
  t.lowParts.map fun e => (e / q).floor


def BlockTrace.scalarPredicate (t : BlockTrace) : Bool :=
  let ℓ := t.lowestLowBitExp
  let q := pow2 ℓ
  let zs := t.lowBits
  decide (-149 ≤ ℓ) && decide (ℓ ≤ 104) &&
  (t.lowParts == zs.map fun (z : ℤ) => (z : ℚ) * q) &&
  decide (magnitudeSum zs < 2 ^ 24) &&
  representable32 t.output.value && representable32 t.overlap &&
  representable32 t.retainedSum &&
  decide (absQ (t.retainedSum + sumQ t.lowParts) ≤ maxFinite32)

/-- Named checks for each condition of the scalar predicate. -/
def BlockTrace.scalarChecks (t : BlockTrace) : List (String × Bool) :=
  let ℓ := t.lowestLowBitExp
  let q := pow2 ℓ
  let zs := t.lowBits
  [("lowest_bit_min", decide (-149 ≤ ℓ)),
   ("lowest_bit_max", decide (ℓ ≤ 104)),
   ("low_bits_on_grid", t.lowParts == zs.map fun (z : ℤ) => (z : ℚ) * q),
   ("low_bits_sum_below_2pow24", decide (magnitudeSum zs < 2 ^ 24)),
   ("D_fits_fp32", representable32 t.output.value),
   ("overlap_fits_fp32", representable32 t.overlap),
   ("H_fits_fp32", representable32 t.retainedSum),
   ("final_range", decide (absQ (t.retainedSum + sumQ t.lowParts) ≤ maxFinite32))]

/-- Diagnostic conjunction is exactly the public predicate, including every guard. -/
theorem scalarChecks_all (t : BlockTrace) :
    (t.scalarChecks.all fun c => c.2) = t.scalarPredicate := by
  simp [BlockTrace.scalarChecks, BlockTrace.scalarPredicate, Bool.and_assoc]

/-- Unchecked diagnostic implementation of Algorithm 1, scalar branch. -/
def BlockTrace.scalarCorrectedUnchecked (t : BlockTrace) : Option F32 :=
  (naiveSum32 t.lowParts).bind fun etot =>
    (fp32Add t.output.value (-t.overlap)).bind fun h =>
      round32 .nearestEven (h + etot)

/-- Safe public scalar correction: reject unless the sufficient predicate holds. -/
def BlockTrace.scalarCorrected (t : BlockTrace) : Option F32 :=
  if t.scalarPredicate then t.scalarCorrectedUnchecked else none

/-- The scalar EFT: the scalar branch when its predicate holds, and `none` otherwise. -/
def BlockTrace.scalarTcEft (t : BlockTrace) : Option F32 := t.scalarCorrected

theorem retained_add_low (t : BlockTrace) :
    t.retainedSum + sumQ t.lowParts = t.block.exactDot := by
  have h := overlap_recovery t
  unfold BlockTrace.overlap at h
  grind

/-- Theorem IV.9 and Lemma IV.10 applied: under the predicate, the scalar branch computes exactly `RN(S)`. -/
theorem scalarCorrectedUnchecked_eq (t : BlockTrace) (h : t.scalarPredicate = true) :
    t.scalarCorrectedUnchecked = round32 .nearestEven t.block.exactDot := by
  unfold BlockTrace.scalarPredicate at h
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, hgrid⟩, hmag⟩, _⟩, _⟩, hH⟩, _⟩ := h
  have hsum : naiveSum32 t.lowParts = some (sumQ t.lowParts) := by
    rw [hgrid, naiveSum32_exact _ h1 h2 _ hmag, sum_coefficients]
  have hsub : fp32Add t.output.value (-t.overlap) = some (t.output.value + -t.overlap) := by
    apply fp32Add_exact
    have hr : t.output.value + -t.overlap = t.retainedSum := by
      unfold BlockTrace.overlap; grind
    rw [hr]
    exact representable32_finite hH
  unfold BlockTrace.scalarCorrectedUnchecked
  rw [hsum, hsub]
  simp only [Option.bind_some]
  congr 1
  have := overlap_recovery t
  grind

/-- Under the scalar predicate, public correction equals nearest-even rounding of the exact dot product. -/
theorem scalarCorrected_eq (t : BlockTrace) (h : t.scalarPredicate = true) :
    t.scalarCorrected = round32 .nearestEven t.block.exactDot := by
  unfold BlockTrace.scalarCorrected
  rw [if_pos h, scalarCorrectedUnchecked_eq t h]

/-- Public scalar correction returns `none` when its sufficient predicate fails. -/
theorem scalarCorrected_rejects (t : BlockTrace) (h : t.scalarPredicate = false) :
    t.scalarCorrected = none := by simp [BlockTrace.scalarCorrected, h]

/-- Corollary IV.11: the scalar branch returns the correctly rounded exact dot product. -/
theorem scalarCorrected_correct (t : BlockTrace) (h : t.scalarPredicate = true) :
    ∃ b, t.scalarCorrected = some b ∧ NearestEven32 t.block.exactDot b := by
  rw [scalarCorrected_eq t h]
  apply round32_nearestEven_correct
  unfold BlockTrace.scalarPredicate at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  rw [← retained_add_low]
  exact h.2

/-- Whenever the scalar EFT returns a result, it is the correctly rounded exact sum. -/
theorem scalarTcEft_correct (t : BlockTrace) (b : F32) (h : t.scalarTcEft = some b) :
    NearestEven32 t.block.exactDot b := by
  unfold BlockTrace.scalarTcEft BlockTrace.scalarCorrected at h
  split at h
  · rename_i hp
    obtain ⟨b', hb', hn⟩ := scalarCorrected_correct t hp
    simp only [BlockTrace.scalarCorrected, if_pos hp] at hb'
    rw [hb'] at h
    cases Option.some.inj h
    exact hn
  · contradiction

/-- The scalar EFT succeeds exactly when its predicate holds. -/
theorem scalarTcEft_isSome_iff (t : BlockTrace) : (t.scalarTcEft).isSome = true ↔ t.scalarPredicate = true := by
  unfold BlockTrace.scalarTcEft BlockTrace.scalarCorrected
  constructor
  · intro h
    split at h
    · assumption
    · simp at h
  · intro hp
    rw [if_pos hp]
    obtain ⟨b, hb, _⟩ := scalarCorrected_correct t hp
    simp only [BlockTrace.scalarCorrected, if_pos hp] at hb
    rw [hb]
    rfl

/-- Under the predicate, the scalar EFT and the exact-rational reference return the same bits. -/
theorem scalarTcEft_eq_corrected (t : BlockTrace) (h : t.scalarPredicate = true) :
    t.scalarTcEft = t.corrected := by
  unfold BlockTrace.scalarTcEft BlockTrace.scalarCorrected
  rw [if_pos h, scalarCorrectedUnchecked_eq t h, corrected_eq_round_exactDot]

/-- On a successful encoded-input evaluation, a scalar EFT result correctly rounds the independent ideal sum. -/
theorem evalBlock_scalarTcEft_correct {p : Model} {x : BlockInput p} {t : BlockTrace} {z : ℚ}
    {b : F32} (h : evalBlock x = .ok t) (hz : exactDot x = some z) (hb : t.scalarTcEft = some b) :
    NearestEven32 z b := by
  simp only [exactDot, evalBlock_prepared h, Option.map_some] at hz
  rw [← Option.some.inj hz]
  exact scalarTcEft_correct t b hb

end TensorCore
