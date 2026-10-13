import OzakiTC.Int8
import Ozaki.ADPError
import Ozaki.Native

/-! # ADP on the INT8 matrix multiplier (a 32-bit wrapping register over exact integer products)

The whole of NVIDIA's ADP (Schwarz et al., arXiv:2511.13778; the Z3 model `ozaki-NVIDIA/adp.py`)
for binary64 GEMM on the INT8 matrix multiplier of `OzakiTC/Int8.lean`:

1. **Scan (§5.1).** Decode every binary64 word (`value64`, TensorCore's `binaryValue fp64`); an
   Inf or NaN sends the product to native FP64 (`ADPPath.nativeNonfinite`).
2. **ESC (§4, §5.2).** The coarsened ESC of every dot product (`ADP.escCoarse`, blocks of
   `cfg.block`, zeros as `−∞`); the matrix ESC is the largest (`matrixEsc`, `[X.6]`). An
   unbounded estimate (the Z3 model's `ESC > ESC_CAP`) falls back to native FP64.
3. **Width and slices.** `W = 53 + ESC + 1` (`[B.1]`) and the fewest remapped slices that hold
   `W` bits (`slicesNeeded`, `[B.2]`).
4. **Heuristic (§5.3).** Emulate only when `s² ≤ cfg.speedRatio` (`[G.3]`), else native FP64.
5. **Emulation.** Row-wise fixed point with shift `W − 1 − exp(row max)`, `s` remapped slices,
   all `s²` INT8 products in TC-EFT's 32-bit register, exact recombination, and one binary64
   round to nearest (`emulEntry`, through `int8Ozaki`).

Native FP64 is `nativeDot fp64Round`: products and running sums rounded to binary64, as Python's
`acc = acc + A[i][t] * B[t][j]`. Every binary64 rounding is IEEE's round to nearest even
(`fp64Round`, `Ozaki.rne64`); TensorCore's (`fp64RoundTC`) computes the same value up to the
largest finite value and differs only in overflow (`OzakiTC.IEEE`).

The results:

* `fp64Round_within`: binary64 rounding loses at most `2^-53 |q| + 2^-1075`.
* `value64_onGrid`, `value64_bound` (`[D.1]`–`[D.3]`): every decoded value is `m 2^(exp(v) − 52)`
  with `|m| < 2^53`.
* `emulEntry_eq` (`[E.3]`, `[R.1]`): an emulated entry is the binary64 rounding of the exact
  fixed-point product.
* `emulEntry_gradeA` (`[P.2]`) and `nativeEntry_error` (`[N.1]`); `adp_accuracy` combines them
  for the whole routine: every entry of every result meets the Grade-A bound of its path.
* `adp_nonfinite_iff` (`[G.2]`), `adp_emulated_finite` (`[G.1]`), `adp_emulated_slices` (`[G.3]`).

Overflow is IEEE's, as in the Z3 model (`[R.2]`): a binary64 rounding fails exactly when the rounded
magnitude exceeds the largest finite value (`fp64Round_none_iff`); `adp` returns no values where
the Z3 model returns `±Inf`. -/

open TensorCore

namespace Ozaki.TC

/-! ## Binary64 values and rounding -/

/-- The value of a binary64 word, `none` for Inf and NaN. -/
def value64 (w : BitVec 64) : Option ℚ := binaryValue fp64 w

/-- TensorCore's binary64 round to nearest even, as a value; `none` above the largest finite
value. -/
def fp64RoundTC (q : ℚ) : Option ℚ := (roundBinary fp64 .nearestEven q).bind (binaryValue fp64)

/-- **Binary64 round to nearest even**, IEEE's: `Ozaki.rne64`; `none` exactly when the rounded
magnitude exceeds the largest finite value. -/
def fp64Round (q : ℚ) : Option ℚ := rne64 q

theorem fp64_wellFormed : fp64.WellFormed := by decide

/-- Rounding a positive magnitude to nearest even in a well-formed format loses at most
`2^-(p+1) m + 2^(emin − p − 1)`, `p` the stored mantissa bits. -/
theorem binaryMagnitude_error (f : Format) (hf : f.WellFormed) (negative : Bool) {m : ℚ}
    (hm : 0 < m) (hr : m ≤ f.maxFinite) :
    Rat.abs (binaryMagnitudeRounded f .nearestEven negative m - m) ≤
      2 ^ (-((f.mantissaBits : ℤ) + 1)) * m + 2 ^ (f.emin - f.mantissaBits - 1) := by
  obtain ⟨_, _, _, hlow⟩ := binaryNormExp_bounds f hf m hm hr
  generalize hE : binaryNormExp f m = e at *
  have hg := pow2_pos (e - f.mantissaBits)
  have hdist := rneInt_dist_le_half (m / pow2 (e - f.mantissaBits))
  rw [absQ_eq] at hdist
  have heq : binaryMagnitudeRounded f .nearestEven negative m - m =
      ((rneInt (m / pow2 (e - f.mantissaBits)) : ℚ) - m / pow2 (e - f.mantissaBits)) *
        pow2 (e - f.mantissaBits) := by
    unfold binaryMagnitudeRounded
    rw [hE, binaryCoefficient_nearestEven]
    have : m / pow2 (e - f.mantissaBits) * pow2 (e - f.mantissaBits) = m :=
      Rat.div_mul_cancel (Rat.ne_of_gt hg)
    grind
  rw [heq, abs_mul, abs_of_nonneg (Rat.le_of_lt hg), abs_sub_comm]
  have hhalf : Rat.abs (m / pow2 (e - f.mantissaBits) - rneInt (m / pow2 (e - f.mantissaBits))) *
      pow2 (e - f.mantissaBits) ≤ pow2 (e - f.mantissaBits - 1) := by
    have h2 : pow2 (e - f.mantissaBits) = 2 * pow2 (e - f.mantissaBits - 1) := by
      rw [show e - f.mantissaBits = (e - f.mantissaBits - 1) + 1 by omega, pow2_succ]; grind
    have := Rat.mul_le_mul_of_nonneg_right hdist (Rat.le_of_lt (pow2_pos (e - f.mantissaBits - 1)))
    generalize Rat.abs (m / pow2 (e - f.mantissaBits) - rneInt (m / pow2 (e - f.mantissaBits))) = A
      at this ⊢
    rw [h2]; grind
  refine Rat.le_trans hhalf ?_
  have hm0 : (0 : ℚ) ≤ 2 ^ (-((f.mantissaBits : ℤ) + 1)) * m :=
    Rat.mul_nonneg (Rat.le_of_lt (two_pow_pos _)) (Rat.le_of_lt hm)
  have hη : (0 : ℚ) ≤ 2 ^ (f.emin - f.mantissaBits - 1) := Rat.le_of_lt (two_pow_pos _)
  rcases hlow with hlow | hlow
  · have : pow2 (e - f.mantissaBits - 1) ≤ 2 ^ (-((f.mantissaBits : ℤ) + 1)) * m := by
      rw [show e - f.mantissaBits - 1 = -((f.mantissaBits : ℤ) + 1) + e by omega, pow2_add]
      exact Rat.mul_le_mul_of_nonneg_left hlow (Rat.le_of_lt (pow2_pos _))
    grind
  · subst hlow
    have : pow2 (f.emin - f.mantissaBits - 1) = 2 ^ (f.emin - f.mantissaBits - 1) := rfl
    rw [this]
    grind

/-- TensorCore's binary64 rounding error: `|fl(q) − q| ≤ 2^-53 |q| + 2^-1075`. -/
theorem fp64RoundTC_within : RoundWithin fp64RoundTC (2 ^ (-53 : ℤ)) (2 ^ (-1075 : ℤ)) := by
  intro q v h
  unfold fp64RoundTC at h
  cases hw : roundBinary fp64 .nearestEven q with
  | none => simp [hw] at h
  | some w =>
    simp only [hw, Option.bind_some] at h
    by_cases hq : q = 0
    · subst hq
      rw [roundBinary_zero fp64 fp64_wellFormed] at hw
      cases Option.some.inj hw
      rw [binaryValue_zero fp64 fp64_wellFormed] at h
      cases Option.some.inj h
      rw [show (0 : ℚ) - 0 = 0 by grind, abs_zero]
      have := two_pow_pos (-1075 : ℤ); have := abs_nonneg (0 : ℚ)
      grind
    · obtain ⟨_, hr⟩ := roundBinary_range hw
      obtain ⟨b, hb, hv, _⟩ := roundBinary_nonzero_spec fp64 fp64_wellFormed .nearestEven q hq hr
      rw [hw] at hb; cases Option.some.inj hb
      rw [hv] at h; cases Option.some.inj h
      have hpos : 0 < absQ q := absQ_pos_of_ne_zero q hq
      have herr := binaryMagnitude_error fp64 fp64_wellFormed (decide (q < 0)) hpos hr
      have e1 : (2 : ℚ) ^ (-(((fp64.mantissaBits : ℕ) : ℤ) + 1)) = 2 ^ (-53 : ℤ) := rfl
      have e2 : (2 : ℚ) ^ (fp64.emin - (fp64.mantissaBits : ℕ) - 1) = 2 ^ (-1075 : ℤ) := rfl
      rw [e1, e2] at herr
      rw [absQ_eq] at herr
      unfold binarySignedRounded
      split
      · rename_i hneg
        have hd : decide (q < 0) = true := by simp [hneg]
        rw [hd, abs_of_neg hneg] at herr
        rw [absQ_of_neg hneg, abs_of_neg hneg]
        have : -binaryMagnitudeRounded fp64 .nearestEven true (-q) - q =
            -(binaryMagnitudeRounded fp64 .nearestEven true (-q) - -q) := by grind
        rw [this, abs_neg]; exact herr
      · rename_i hnn
        have hq0 : 0 ≤ q := by grind
        have hd : decide (q < 0) = false := by simp [hnn]
        rw [hd, abs_of_nonneg hq0] at herr
        rw [absQ_of_nonneg hq0, abs_of_nonneg hq0]
        exact herr

/-- TensorCore's binary64 rounding fails exactly above the largest finite value. -/
theorem fp64RoundTC_none_iff (q : ℚ) : fp64RoundTC q = none ↔ fp64.maxFinite < Rat.abs q := by
  have hs := roundBinary_isSome_iff fp64 .nearestEven q
  rw [absQ_eq] at hs
  constructor
  · intro h
    unfold fp64RoundTC at h
    cases hw : roundBinary fp64 .nearestEven q with
    | none =>
      rw [hw] at hs
      simp only [Option.isSome_none, Bool.false_eq_true, false_iff, not_and] at hs
      exact Rat.not_le.mp (hs fp64_wellFormed)
    | some w =>
      exfalso
      obtain ⟨_, hr⟩ := roundBinary_range hw
      by_cases hq : q = 0
      · subst hq
        rw [roundBinary_zero fp64 fp64_wellFormed] at hw
        cases Option.some.inj hw
        rw [roundBinary_zero fp64 fp64_wellFormed] at h
        change binaryValue fp64 0 = none at h
        rw [binaryValue_zero fp64 fp64_wellFormed] at h
        exact absurd h (by simp)
      · obtain ⟨b, hb, hv, _⟩ := roundBinary_nonzero_spec fp64 fp64_wellFormed .nearestEven q hq hr
        rw [hb] at h; simp [hv] at h
  · intro h
    have hn : ¬ (roundBinary fp64 .nearestEven q).isSome = true := by
      rw [hs]; intro ⟨_, hr⟩; exact Rat.not_le.mpr h hr
    unfold fp64RoundTC
    cases hw : roundBinary fp64 .nearestEven q with
    | none => rfl
    | some w => rw [hw] at hn; simp at hn

/-- **Binary64 rounding error.** `|fl(q) − q| ≤ 2^-53 |q| + 2^-1075` whenever `fl(q)` is finite. -/
theorem fp64Round_within : RoundWithin fp64Round (2 ^ (-53 : ℤ)) (2 ^ (-1075 : ℤ)) := rne64_within

theorem fp64_maxFinite_eq_maxFormat : fp64.maxFinite = maxFormat 53 1023 := by decide +kernel

/-- **Overflow** (`[R.2]`): binary64 rounding fails exactly when the rounded magnitude exceeds the
largest finite value, as in IEEE; never at or below the largest finite value. -/
theorem fp64Round_none_iff (q : ℚ) :
    fp64Round q = none ↔ fp64.maxFinite < Rat.abs (rneU 53 (-1022) q) := by
  have h := roundRNE_isSome_iff (p := 53) (emin := -1022) (emax := 1023) (q := q)
  rw [fp64_maxFinite_eq_maxFormat]
  unfold fp64Round rne64
  cases hr : roundRNE 53 (-1022) 1023 q with
  | none =>
    rw [hr] at h; simp only [Option.isSome_none, Bool.false_eq_true, false_iff] at h
    exact ⟨fun _ => Rat.not_le.mp h, fun _ => rfl⟩
  | some v =>
    rw [hr] at h; simp only [Option.isSome_some, true_iff] at h
    exact ⟨fun h' => (by cases h'), fun h' => absurd h (Rat.not_le.mpr h')⟩

/-- Binary64 rounding succeeds up to the largest finite value. -/
theorem fp64Round_isSome {q : ℚ} (hq : Rat.abs q ≤ fp64.maxFinite) : (fp64Round q).isSome = true :=
  rne64_isSome (by rw [← fp64_maxFinite_eq_maxFormat]; exact hq)

/-! ## Decoding (`[D.1]`–`[D.3]`) -/

theorem floorLog2_le_of_lt {m : ℚ} (hm : 0 < m) {e : ℤ} (h : m < 2 ^ (e + 1)) : floorLog2 m ≤ e := by
  have h1 := (floorLog2_spec hm).1
  have := two_pow_lt_iff.mp (lt_of_le_of_lt' h1 h)
  omega

/-- A finite binary64 value `k 2^(e−52)`: its exponent is at most `e`. -/
theorem exp64_le_of_finite {v : ℚ} (hv : v ≠ 0) {k e : ℤ} (he : -1022 ≤ e) (hk : k.natAbs < 2 ^ 53)
    (hval : v = (k : ℚ) * 2 ^ (e - 52)) : ADP.exp64 v ≤ e := by
  unfold ADP.exp64
  have hlt : Rat.abs v < 2 ^ (e + 1) := by
    rw [hval, abs_mul_two_pow, abs_intCast]
    have : ((k.natAbs : ℕ) : ℚ) < ((2 ^ 53 : ℕ) : ℚ) := Rat.natCast_lt_natCast.mpr hk
    rw [← two_pow_natCast] at this
    have := Rat.mul_lt_mul_of_pos_right this (two_pow_pos (e - 52))
    rwa [← two_pow_add, show ((53 : ℕ) : ℤ) + (e - 52) = e + 1 by omega] at this
  have := floorLog2_le_of_lt (ADP.abs_pos_of_ne hv) hlt
  omega

/-- **Decoding** (`[D.1]`, `[D.3]`): every finite binary64 value is `m · 2^(exp(v) − 52)` with an
integer `m`, and `|m| < 2^53`. -/
theorem value64_onGrid {w : BitVec 64} {v : ℚ} (h : value64 w = some v) : ADP.OnGrid64 v := by
  unfold value64 binaryValue at h
  cases hd : (classify fp64 w).finite with
  | none => rw [hd] at h; simp at h
  | some d =>
    rw [hd] at h; simp only [Option.map_some, Option.some.injEq] at h
    obtain ⟨k, e, he1, _, hk, hval⟩ := classifyNat_finiteValue fp64 fp64_wellFormed _ d hd
    rw [h] at hval
    by_cases hv : v = 0
    · exact ⟨0, by rw [hv]; simp⟩
    · have he : -1022 ≤ e := he1
      have hval' : v = (k : ℚ) * 2 ^ (e - 52) := hval
      have hle := exp64_le_of_finite hv he hk hval'
      refine ⟨k * 2 ^ (e - ADP.exp64 v).toNat, ?_⟩
      rw [← ADP.intCast_mul_two_pow_nat k (show 0 ≤ e - ADP.exp64 v by omega), Rat.mul_assoc,
        ← two_pow_add, show e - ADP.exp64 v + (ADP.exp64 v - 52) = e - 52 by omega]
      exact hval'

/-- **Decoding** (`[D.2]`, `[D.3]`): `|v| < 2^(exp(v) + 1)`, so the integer `m` has `|m| < 2^53`. -/
theorem value64_bound {w : BitVec 64} {v : ℚ} (_h : value64 w = some v) (hv : v ≠ 0) :
    Rat.abs v < 2 ^ (ADP.exp64 v + 1) := ADP.abs_lt_exp64 hv

/-! ## Width and slice count (`[B.1]`, `[B.2]`) -/

/-- `W = 53 + ESC + 1` (`[B.1]`): the mantissa, the ESC padding, and one bit for the product of
two mantissas below `4`. -/
def adpWidth (esc : ℤ) : ℕ := (53 + esc + 1).toNat

/-- The first `s` from `start` (within `fuel` tries) whose remapped slices hold `W` bits. -/
def slicesFrom (W : ℕ) : ℕ → ℕ → ℕ
  | s, 0 => s
  | s, fuel + 1 => if ADP.remapFits W s then s else slicesFrom W (s + 1) fuel

/-- The fewest remapped slices that hold every integer in `[−2^W, 2^W)`. -/
def slicesNeeded (W : ℕ) : ℕ := slicesFrom W 1 (W + 1)

theorem remapFits_iff {W s : ℕ} :
    ADP.remapFits W s = true ↔ ADP.remapLo s ≤ -(2 ^ W : ℤ) ∧ (2 ^ W - 1 : ℤ) ≤ ADP.remapHi s := by
  unfold ADP.remapFits; simp

/-- `W + 1` remapped slices always hold `W` bits. -/
theorem remapFits_succ (W : ℕ) : ADP.remapFits W (W + 1) = true := by
  rw [remapFits_iff]
  have h1 : 255 * 256 ^ W ≤ 256 ^ (W + 1) - 1 := by
    rw [Nat.pow_succ]; have := Nat.one_le_pow W 256 (by decide); omega
  have h2 : 256 ^ W ≤ (256 ^ (W + 1) - 1) / 255 := (Nat.le_div_iff_mul_le (by decide)).mpr (by omega)
  have h3 : 2 ^ W ≤ 256 ^ W := Nat.pow_le_pow_left (by decide) W
  have h4 : ((2 : ℤ) ^ W) ≤ (((256 ^ (W + 1) - 1) / 255 : ℕ) : ℤ) := by
    have : 2 ^ W ≤ (256 ^ (W + 1) - 1) / 255 := Nat.le_trans h3 h2
    exact_mod_cast this
  unfold ADP.remapLo ADP.remapHi
  generalize (((256 ^ (W + 1) - 1) / 255 : ℕ) : ℤ) = D at h4 ⊢
  have : (0 : ℤ) ≤ 2 ^ W := Int.pow_nonneg (by decide)
  omega

theorem slicesFrom_spec (W : ℕ) : ∀ fuel s, s ≤ slicesFrom W s fuel ∧
    (∀ t, s ≤ t → t < slicesFrom W s fuel → ADP.remapFits W t = false) ∧
    (ADP.remapFits W (slicesFrom W s fuel) = true ∨ slicesFrom W s fuel = s + fuel)
  | 0, s => ⟨Nat.le_refl _, fun t h1 h2 => by simp [slicesFrom] at h2; omega,
      Or.inr (by simp [slicesFrom])⟩
  | fuel + 1, s => by
    unfold slicesFrom
    split
    · rename_i h; exact ⟨Nat.le_refl _, fun t h1 h2 => by omega, Or.inl h⟩
    · rename_i h
      obtain ⟨a, b, c⟩ := slicesFrom_spec W fuel (s + 1)
      refine ⟨by omega, fun t h1 h2 => ?_, by rcases c with c | c; exact Or.inl c; right; omega⟩
      by_cases ht : t = s
      · subst ht; simpa using h
      · exact b t (by omega) h2

/-- **The slice count is the minimum** (`[B.2]`): `slicesNeeded W` slices hold `W` bits and no
smaller positive count does. -/
theorem slicesNeeded_spec (W : ℕ) : 1 ≤ slicesNeeded W ∧ ADP.remapFits W (slicesNeeded W) = true ∧
    ∀ t, 1 ≤ t → t < slicesNeeded W → ADP.remapFits W t = false := by
  obtain ⟨a, b, c⟩ := slicesFrom_spec W (W + 1) 1
  unfold slicesNeeded
  refine ⟨a, ?_, b⟩
  rcases c with c | c
  · exact c
  · have := b (W + 1) (by omega) (by omega)
    rw [remapFits_succ] at this; exact absurd this (by decide)

/-! ## The matrix ESC (`[X.6]`) -/

/-- The larger of two estimates, `none` (unbounded) absorbing. -/
def maxOpt (acc e : Option ℤ) : Option ℤ := acc.bind fun a => e.map fun b => max a b

/-- The matrix ESC: the largest coarsened ESC over all dot products, `none` if one is
unbounded. -/
def matrixEsc (n : ℕ) (A cols : List (List ℚ)) : Option ℤ :=
  (A.flatMap fun x => cols.map fun y => ADP.escCoarse n x y).foldl maxOpt (some 0)

theorem foldl_maxOpt : ∀ (l : List (Option ℤ)) (acc : Option ℤ) (m : ℤ), l.foldl maxOpt acc = some m →
    (∃ a, acc = some a ∧ a ≤ m) ∧ ∀ e ∈ l, ∃ c, e = some c ∧ c ≤ m
  | [], acc, m, h => by simp only [List.foldl_nil] at h; subst h; exact ⟨⟨m, rfl, Int.le_refl _⟩, by simp⟩
  | e :: l, acc, m, h => by
    simp only [List.foldl_cons] at h
    obtain ⟨⟨a, ha, ham⟩, hl⟩ := foldl_maxOpt l (maxOpt acc e) m h
    cases acc with
    | none => simp [maxOpt] at ha
    | some a0 =>
      cases e with
      | none => simp [maxOpt] at ha
      | some c =>
        simp only [maxOpt, Option.bind_some, Option.map_some, Option.some.injEq] at ha
        subst ha
        refine ⟨⟨a0, rfl, by omega⟩, fun e he => ?_⟩
        rcases List.mem_cons.mp he with rfl | he
        · exact ⟨c, rfl, by omega⟩
        · exact hl e he

/-- **The matrix ESC bounds every dot product's** (`[X.6]`). -/
theorem matrixEsc_ge {n : ℕ} {A cols : List (List ℚ)} {m : ℤ} (h : matrixEsc n A cols = some m) :
    ∀ x ∈ A, ∀ y ∈ cols, ∃ c, ADP.escCoarse n x y = some c ∧ c ≤ m := by
  intro x hx y hy
  obtain ⟨_, hl⟩ := foldl_maxOpt _ _ m h
  exact hl _ (List.mem_flatMap.mpr ⟨x, hx, List.mem_map_of_mem hy⟩)

/-! ## One emulated entry -/

/-- One emulated entry: fixed point with ADP's shifts, `s` remapped slices on the INT8 matrix
multiplier, exact recombination, and binary64 round to nearest. -/
def emulEntry (W s : ℕ) (x y : List ℚ) : Option ℚ :=
  int8Ozaki s (ADP.shiftOf W x) (ADP.shiftOf W y) x y

/-- Every fixed-point integer of a row fits `s` remapped slices when `remapFits W s`. -/
theorem fixed_in_remap {W s : ℕ} (hfit : ADP.remapFits W s = true) (x : List ℚ) :
    ∀ z ∈ toFixed (ADP.shiftOf W x) x, ADP.remapLo s ≤ z ∧ z ≤ ADP.remapHi s := by
  obtain ⟨hlo, hhi⟩ := remapFits_iff.mp hfit
  have hp : (0 : ℤ) < 2 ^ W := Int.pow_pos (by decide)
  intro z hz
  obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hz
  unfold ADP.shiftOf
  cases hm : ADP.maxE (ADP.expsOf x) with
  | none =>
    rw [ADP.eq_zero_of_maxE_none hm a ha]
    simp only [Rat.zero_mul, ADP.floor_zero]
    omega
  | some e =>
    simp only
    have := ADP.fixed_range (e := e) (ADP.exp64_le_maxE hm a ha) W
    omega

/-- **Operands of the matrix multiplier** (`[E.1]`): the 8-bit two's-complement pattern of a signed
byte encodes it. -/
theorem int8_pattern {d : ℤ} (h1 : -128 ≤ d) (h2 : d ≤ 127) : (BitVec.ofInt 8 d).toInt = d := by
  have key : ∀ i : Fin 256, (BitVec.ofInt 8 ((i : ℤ) - 128)).toInt = (i : ℤ) - 128 := by
    decide +kernel
  have := key ⟨(d + 128).toNat, by omega⟩
  simp only at this
  rwa [show (((d + 128).toNat : ℕ) : ℤ) - 128 = d by omega] at this

/-- **An emulated entry** (`[E.3]`, `[R.1]`): all INT8 slice products are exact and the result is
the binary64 rounding of the exact fixed-point product. -/
theorem emulEntry_eq {W s : ℕ} (hs : 0 < s) (hfit : ADP.remapFits W s = true) {x y : List ℚ}
    (hk : x.length * (128 * 128) < 2 ^ 31) :
    emulEntry W s x y = fp64Round (ADP.fixedProduct W x y) := by
  unfold emulEntry
  rw [int8Ozaki_eq hs _ _ (fixed_in_remap hfit x) (fixed_in_remap hfit y) hk]
  rfl

theorem two_k_u_le {k : ℕ} (hk : k * (128 * 128) < 2 ^ 31) : 2 * (k : ℚ) * 2 ^ (-53 : ℤ) ≤ 1 := by
  have hk' : k ≤ 2 ^ 52 := by omega
  have e52 : (2 : ℚ) ^ (52 : ℤ) = ((2 ^ 52 : ℕ) : ℚ) := two_pow_natCast 52
  have : (k : ℚ) ≤ 2 ^ (52 : ℤ) := by
    rw [e52]; exact Rat.natCast_le_natCast.mpr hk'
  have hu := two_pow_pos (-53 : ℤ)
  have e : 2 * (2 : ℚ) ^ (52 : ℤ) * 2 ^ (-53 : ℤ) = 1 := by
    rw [Rat.mul_assoc, ← two_pow_add, show (52 : ℤ) + -53 = -1 by omega]
    have := two_pow_neg_mul (1 : ℤ); rw [two_pow_one] at this; rw [Rat.mul_comm]; exact this
  have := Rat.mul_le_mul_of_nonneg_right (Rat.mul_le_mul_of_nonneg_left this (by decide : (0 : ℚ) ≤ 2))
    (Rat.le_of_lt hu)
  grind

/-- **P.1 for an emulated entry** (`[P.1]`): `|C − x · y| ≤ k 2^(F − 51) + 2^-53 |H| + 2^-1075`,
with `H` the exact fixed-point product and `F = exp(z_r)` (the Z3 check uses `2^-53 |C|`). -/
theorem emulEntry_P1 {W s : ℕ} (hs : 0 < s) (hfit : ADP.remapFits W s = true) {n : ℕ}
    {x y : List ℚ} (hlen : x.length = y.length) (hx : ∀ a ∈ x, ADP.OnGrid64 a)
    (hy : ∀ b ∈ y, ADP.OnGrid64 b) {c : ℤ} (hc : ADP.escCoarse n x y = some c)
    (hW : 54 + c ≤ (W : ℤ)) (hk : x.length * (128 * 128) < 2 ^ 31) {F : ℤ}
    (hF : ADP.fExact (ADP.expsOf x) (ADP.expsOf y) = some F) {C : ℚ} (hC : emulEntry W s x y = some C) :
    Rat.abs (C - dot x y) ≤ x.length * 2 ^ (F - 51) +
      (2 ^ (-53 : ℤ) * Rat.abs (ADP.fixedProduct W x y) + 2 ^ (-1075 : ℤ)) := by
  rw [emulEntry_eq hs hfit hk] at hC
  have h1 := (ADP.fixedProduct_error hlen hx hy hc hW).1 F hF
  have h2 := fp64Round_within _ _ hC
  have h3 : (x.length : ℚ) * 2 ^ (F - 52) ≤ x.length * 2 ^ (F - 51) :=
    Rat.mul_le_mul_of_nonneg_left (two_pow_le (by omega)) Rat.natCast_nonneg
  have t := abs_add_le (C - ADP.fixedProduct W x y) (ADP.fixedProduct W x y - dot x y)
  rw [show C - ADP.fixedProduct W x y + (ADP.fixedProduct W x y - dot x y) = C - dot x y by grind,
    abs_sub_comm (ADP.fixedProduct W x y)] at t
  grind

/-- **Grade A for an emulated entry** (`[P.2]`). Normal (or zero) binary64 entries, `W ≥ 54 + c`
for the coarsened ESC `c` of this dot product, and `s` slices that hold `W` bits:
`|C − x · y| ≤ (4k + 1) 2^-53 Σ|xᵢyᵢ| + 2^-1075`. -/
theorem emulEntry_gradeA {W s : ℕ} (hs : 0 < s) (hfit : ADP.remapFits W s = true) {n : ℕ}
    {x y : List ℚ} (hlen : x.length = y.length) (hx : ∀ a ∈ x, ADP.OnGrid64 a)
    (hy : ∀ b ∈ y, ADP.OnGrid64 b) (hnx : ∀ a ∈ x, ADP.Normal64 a) (hny : ∀ b ∈ y, ADP.Normal64 b)
    {c : ℤ} (hc : ADP.escCoarse n x y = some c) (hW : 54 + c ≤ (W : ℤ))
    (hk : x.length * (128 * 128) < 2 ^ 31) {C : ℚ} (hC : emulEntry W s x y = some C) :
    Rat.abs (C - dot x y) ≤
      (4 * x.length + 1) * 2 ^ (-53 : ℤ) * ((List.zipWith (· * ·) x y).map Rat.abs).sum +
        2 ^ (-1075 : ℤ) := by
  rw [emulEntry_eq hs hfit hk] at hC
  exact ADP.emulated_gradeA fp64Round_within hlen hx hy hnx hny hc hW (two_k_u_le hk) hC

/-- **Native FP64** (`[N.1]`): `|C − x · y| ≤ γ_k Σ|xᵢyᵢ| + 2k (1 + 2^-53)^k 2^-1075`. -/
theorem nativeEntry_error {x y : List ℚ} (hlen : x.length = y.length)
    (hk : x.length * (128 * 128) < 2 ^ 31) {C : ℚ} (hC : nativeDot fp64Round x y = some C) :
    Rat.abs (C - dot x y) ≤
      x.length * 2 ^ (-53 : ℤ) / (1 - x.length * 2 ^ (-53 : ℤ)) *
          ((List.zipWith (· * ·) x y).map Rat.abs).sum +
        2 * x.length * (1 + 2 ^ (-53 : ℤ)) ^ x.length * 2 ^ (-1075 : ℤ) := by
  have h2 := two_k_u_le hk
  have hu := two_pow_pos (-53 : ℤ)
  have hn : (0 : ℚ) ≤ x.length := Rat.natCast_nonneg
  have hku : (x.length : ℚ) * 2 ^ (-53 : ℤ) < 1 := by
    have := Rat.mul_nonneg hn (Rat.le_of_lt hu); grind
  exact nativeDot_error_gamma (Rat.le_of_lt hu) (Rat.le_of_lt (two_pow_pos _)) fp64Round_within
    hlen hku hC

/-! ## The routine (§5) -/

/-- ADP's configuration: the coarsening block length and the speed ratio of the heuristic. -/
structure ADPConfig where
  block : ℕ := 2
  speedRatio : ℕ := 100
  deriving Repr

/-- The path ADP takes. -/
inductive ADPPath where
  | nativeNonfinite
  | nativeSlow
  | emulated
  deriving Repr, DecidableEq

/-- Decode a binary64 matrix; `none` if some entry is Inf or NaN. -/
def decodeMatrix64 (A : List (List (BitVec 64))) : Option (List (List ℚ)) :=
  A.mapM (·.mapM value64)

/-- Native FP64 GEMM, `A` by rows and `B` by columns. -/
def nativeGemm64 (A cols : List (List ℚ)) : Option (List (List ℚ)) :=
  A.mapM fun x => cols.mapM fun y => nativeDot fp64Round x y

/-- **ADP** (§5) for `C = AB`, `A` and `B` by rows of binary64 words: the path taken and the
values of `C` (none on the non-finite path, or if a value overflows). -/
def adp (cfg : ADPConfig) (A B : List (List (BitVec 64))) : ADPPath × Option (List (List ℚ)) :=
  match decodeMatrix64 A, decodeMatrix64 B with
  | some Aq, some Bq =>
    match matrixEsc cfg.block Aq (transpose Bq) with
    | none => (.nativeSlow, nativeGemm64 Aq (transpose Bq))
    | some esc =>
      if slicesNeeded (adpWidth esc) * slicesNeeded (adpWidth esc) ≤ cfg.speedRatio then
        (.emulated, Aq.mapM fun x => (transpose Bq).mapM fun y =>
          emulEntry (adpWidth esc) (slicesNeeded (adpWidth esc)) x y)
      else (.nativeSlow, nativeGemm64 Aq (transpose Bq))
  | _, _ => (.nativeNonfinite, none)

/-- **The scan** (`[G.2]`): ADP falls back for non-finite inputs exactly when some entry is Inf
or NaN. -/
theorem adp_nonfinite_iff (cfg : ADPConfig) (A B : List (List (BitVec 64))) :
    (adp cfg A B).1 = .nativeNonfinite ↔ decodeMatrix64 A = none ∨ decodeMatrix64 B = none := by
  unfold adp
  cases hA : decodeMatrix64 A <;> cases hB : decodeMatrix64 B <;> simp only [reduceCtorEq,
    or_self, or_true, true_or]
  split
  · simp
  · split <;> simp

/-- **Emulation sees only finite inputs and is economic** (`[G.1]`, `[G.3]`, `[B.1]`). -/
theorem adp_emulated {cfg : ADPConfig} {A B : List (List (BitVec 64))}
    (h : (adp cfg A B).1 = .emulated) :
    ∃ Aq Bq esc, decodeMatrix64 A = some Aq ∧ decodeMatrix64 B = some Bq ∧
      matrixEsc cfg.block Aq (transpose Bq) = some esc ∧
      slicesNeeded (adpWidth esc) * slicesNeeded (adpWidth esc) ≤ cfg.speedRatio := by
  unfold adp at h
  cases hA : decodeMatrix64 A <;> cases hB : decodeMatrix64 B <;> simp only [hA, hB,
    reduceCtorEq] at h
  rename_i Aq Bq
  cases he : matrixEsc cfg.block Aq (transpose Bq) with
  | none => simp [he] at h
  | some esc =>
    simp only [he] at h
    split at h
    · rename_i hs; exact ⟨Aq, Bq, esc, rfl, rfl, he, hs⟩
    · simp at h

/-! ## Accuracy of the whole routine -/

theorem mapM_some_index {f : α → Option β} :
    ∀ (l : List α) (r : List β), l.mapM f = some r →
      r.length = l.length ∧ ∀ i (h1 : i < l.length) (h2 : i < r.length), f l[i] = some r[i]
  | [], r, h => by simp only [List.mapM_nil, pure, Option.some.injEq] at h; subst h; simp
  | a :: l, r, h => by
    rw [List.mapM_cons] at h
    cases ha : f a with
    | none => simp [ha] at h
    | some b =>
      cases hl : l.mapM f with
      | none => simp [ha, hl] at h
      | some bs =>
        simp only [ha, hl, Option.bind_eq_bind, Option.bind_some, pure, Option.some.injEq] at h
        subst h
        obtain ⟨h1, h2⟩ := mapM_some_index l bs hl
        refine ⟨by simp [h1], fun i hi1 hi2 => ?_⟩
        cases i with
        | zero => simpa using ha
        | succ i => simpa using h2 i (by simpa using hi1) (by simpa using hi2)

theorem mapM_some_mem {f : α → Option β} {l : List α} {r : List β} (h : l.mapM f = some r) :
    ∀ b ∈ r, ∃ a ∈ l, f a = some b := by
  intro b hb
  obtain ⟨hlen, hidx⟩ := mapM_some_index l r h
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hb
  exact ⟨l[i], List.getElem_mem _, hidx i (by omega) hi⟩

/-- Entries of columns are entries of rows. -/
theorem mem_transpose : ∀ (rows : List (List ℚ)) (y : List ℚ), y ∈ transpose rows →
    ∀ b ∈ y, ∃ r ∈ rows, b ∈ r
  | [], _, h, _, _ => by simp [transpose] at h
  | [r], y, h, b, hb => by
    simp only [transpose, List.mem_map] at h
    obtain ⟨a, ha, rfl⟩ := h
    simp only [List.mem_singleton] at hb; subst hb
    exact ⟨r, by simp, ha⟩
  | r :: r' :: rs, y, h, b, hb => by
    simp only [transpose] at h
    obtain ⟨a, y', hm, rfl⟩ := ADP.mem_zipWith_exists h
    have hm' := List.of_mem_zip hm
    rcases List.mem_cons.mp hb with rfl | hb
    · exact ⟨r, by simp, hm'.1⟩
    · obtain ⟨r0, hr0, hb0⟩ := mem_transpose (r' :: rs) y' hm'.2 b hb
      exact ⟨r0, List.mem_cons_of_mem _ hr0, hb0⟩

/-- Decoded entries lie on the binary64 grid. -/
theorem decode_onGrid {A : List (List (BitVec 64))} {Aq : List (List ℚ)}
    (h : decodeMatrix64 A = some Aq) : ∀ x ∈ Aq, ∀ a ∈ x, ADP.OnGrid64 a := by
  intro x hx a ha
  obtain ⟨row, _, hrow⟩ := mapM_some_mem h x hx
  obtain ⟨w, _, hw⟩ := mapM_some_mem hrow a ha
  exact value64_onGrid hw

/-- **ADP's accuracy** (`[P.2]`, `[N.1]`). If ADP returns values `C` for `A` and `B` (decoded
`Aq`, `Bq`; `cols` the columns of `Bq`), with matching inner dimensions, normal (or zero) entries
and `k · 2^14 < 2^31`, then `C` has one row per row of `A` and one entry per column, and every
entry meets the Grade-A bound `(4k + 1) u Σ|xᵢyᵢ| + 2^-1075` on the emulated path and the native
bound `γ_k Σ|xᵢyᵢ| + 2k (1 + u)^k 2^-1075` on the native path (`u = 2^-53`). -/
theorem adp_accuracy {cfg : ADPConfig} {A B : List (List (BitVec 64))} {path : ADPPath}
    {C : List (List ℚ)} (h : adp cfg A B = (path, some C)) {Aq Bq : List (List ℚ)}
    (hA : decodeMatrix64 A = some Aq) (hB : decodeMatrix64 B = some Bq)
    (hshape : ∀ x ∈ Aq, ∀ y ∈ transpose Bq, x.length = y.length)
    (hnA : ∀ x ∈ Aq, ∀ a ∈ x, ADP.Normal64 a) (hnB : ∀ r ∈ Bq, ∀ b ∈ r, ADP.Normal64 b)
    (hk : ∀ x ∈ Aq, x.length * (128 * 128) < 2 ^ 31) :
    C.length = Aq.length ∧ ∀ i (hi : i < Aq.length) (hiC : i < C.length),
      C[i].length = (transpose Bq).length ∧
      ∀ j (hj : j < (transpose Bq).length) (hjC : j < C[i].length),
        (path = .emulated → Rat.abs (C[i][j] - dot Aq[i] (transpose Bq)[j]) ≤
          (4 * Aq[i].length + 1) * 2 ^ (-53 : ℤ) *
            ((List.zipWith (· * ·) Aq[i] (transpose Bq)[j]).map Rat.abs).sum + 2 ^ (-1075 : ℤ)) ∧
        (path = .nativeSlow → Rat.abs (C[i][j] - dot Aq[i] (transpose Bq)[j]) ≤
          Aq[i].length * 2 ^ (-53 : ℤ) / (1 - Aq[i].length * 2 ^ (-53 : ℤ)) *
            ((List.zipWith (· * ·) Aq[i] (transpose Bq)[j]).map Rat.abs).sum +
          2 * Aq[i].length * (1 + 2 ^ (-53 : ℤ)) ^ Aq[i].length * 2 ^ (-1075 : ℤ)) := by
  have gA := decode_onGrid hA
  have gB := decode_onGrid hB
  have gcol : ∀ y ∈ transpose Bq, ∀ b ∈ y, ADP.OnGrid64 b := fun y hy b hb => by
    obtain ⟨r, hr, hbr⟩ := mem_transpose Bq y hy b hb; exact gB r hr b hbr
  have ncol : ∀ y ∈ transpose Bq, ∀ b ∈ y, ADP.Normal64 b := fun y hy b hb => by
    obtain ⟨r, hr, hbr⟩ := mem_transpose Bq y hy b hb; exact hnB r hr b hbr
  -- the entry function of the path taken
  have key : ∀ (f : List ℚ → List ℚ → Option ℚ),
      Aq.mapM (fun x => (transpose Bq).mapM fun y => f x y) = some C →
      (∀ x ∈ Aq, ∀ y ∈ transpose Bq, ∀ c, f x y = some c →
        (path = .emulated → Rat.abs (c - dot x y) ≤ (4 * x.length + 1) * 2 ^ (-53 : ℤ) *
            ((List.zipWith (· * ·) x y).map Rat.abs).sum + 2 ^ (-1075 : ℤ)) ∧
        (path = .nativeSlow → Rat.abs (c - dot x y) ≤
          x.length * 2 ^ (-53 : ℤ) / (1 - x.length * 2 ^ (-53 : ℤ)) *
            ((List.zipWith (· * ·) x y).map Rat.abs).sum +
          2 * x.length * (1 + 2 ^ (-53 : ℤ)) ^ x.length * 2 ^ (-1075 : ℤ))) →
      C.length = Aq.length ∧ ∀ i (hi : i < Aq.length) (hiC : i < C.length),
        C[i].length = (transpose Bq).length ∧
        ∀ j (hj : j < (transpose Bq).length) (hjC : j < C[i].length),
          (path = .emulated → Rat.abs (C[i][j] - dot Aq[i] (transpose Bq)[j]) ≤
            (4 * Aq[i].length + 1) * 2 ^ (-53 : ℤ) *
              ((List.zipWith (· * ·) Aq[i] (transpose Bq)[j]).map Rat.abs).sum + 2 ^ (-1075 : ℤ)) ∧
          (path = .nativeSlow → Rat.abs (C[i][j] - dot Aq[i] (transpose Bq)[j]) ≤
            Aq[i].length * 2 ^ (-53 : ℤ) / (1 - Aq[i].length * 2 ^ (-53 : ℤ)) *
              ((List.zipWith (· * ·) Aq[i] (transpose Bq)[j]).map Rat.abs).sum +
            2 * Aq[i].length * (1 + 2 ^ (-53 : ℤ)) ^ Aq[i].length * 2 ^ (-1075 : ℤ)) := by
    intro f hC hf
    obtain ⟨hl, hrows⟩ := mapM_some_index Aq C hC
    refine ⟨hl, fun i hi hiC => ?_⟩
    have hrow := hrows i hi hiC
    obtain ⟨hl2, hents⟩ := mapM_some_index (transpose Bq) C[i] hrow
    refine ⟨hl2, fun j hj hjC => ?_⟩
    exact hf Aq[i] (List.getElem_mem _) (transpose Bq)[j] (List.getElem_mem _) _ (hents j hj hjC)
  unfold adp at h
  rw [hA, hB] at h
  simp only at h
  cases he : matrixEsc cfg.block Aq (transpose Bq) with
  | none =>
    rw [he] at h; simp only [Prod.mk.injEq] at h
    obtain ⟨rfl, hC⟩ := h
    refine key (fun x y => nativeDot fp64Round x y) hC ?_
    intro x hx y hy c hc
    exact ⟨fun h => absurd h (by decide),
      fun _ => nativeEntry_error (hshape x hx y hy) (hk x hx) hc⟩
  | some esc =>
    rw [he] at h
    simp only at h
    split at h
    · simp only [Prod.mk.injEq] at h
      obtain ⟨rfl, hC⟩ := h
      refine key _ hC ?_
      intro x hx y hy c hc
      refine ⟨fun _ => ?_, fun h => absurd h (by decide)⟩
      obtain ⟨c0, hc0, hle⟩ := matrixEsc_ge he x hx y hy
      obtain ⟨hs1, hfit, _⟩ := slicesNeeded_spec (adpWidth esc)
      have hW : 54 + c0 ≤ ((adpWidth esc : ℕ) : ℤ) := by unfold adpWidth; omega
      exact emulEntry_gradeA hs1 hfit (hshape x hx y hy) (gA x hx) (gcol y hy) (hnA x hx)
        (ncol y hy) hc0 hW (hk x hx) hc
    · simp only [Prod.mk.injEq] at h
      obtain ⟨rfl, hC⟩ := h
      refine key (fun x y => nativeDot fp64Round x y) hC ?_
      intro x hx y hy c hc
      exact ⟨fun h => absurd h (by decide),
        fun _ => nativeEntry_error (hshape x hx y hy) (hk x hx) hc⟩

end Ozaki.TC
