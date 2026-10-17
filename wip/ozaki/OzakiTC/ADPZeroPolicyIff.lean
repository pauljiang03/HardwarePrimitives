import OzakiTC.ADPZeroPolicyShapes
import OzakiTC.ADPIEEE

/-! # When an unsafe zero policy breaks Grade A: a sufficient and a necessary condition

ADP with an unsafe zero policy (`adpPolicy`) computes one ESC `e` for the whole matrix and converts
every row and column to fixed point of width `W = adpWidth e`. `adpPolicy_masked_gradeA` shows that
Grade A holds when `e` is at least the paper's matrix ESC. Here the condition is sharpened to one
entry, and complemented by a converse, both stated on the exponent pattern of the inputs (which
entries are zero, and the exponent of each nonzero entry), the only thing the ESC and the width
depend on.

* **Sufficient** (`adpPolicy_entry_gradeA`): in a run that emulates with matrix ESC `e`, an entry
  meets Grade A whenever `escExact(x, y) ≤ e` (so `54 + escExact(x, y) ≤ W`), the exact ESC of its
  own dot product, for every input with that pattern (normal or zero entries, `k · 2^14 < 2^31`).
  This is ADP's own argument (`emulated_gradeA`) with the exact ESC in place of the coarsened one
  (`emulated_gradeA_exactESC`); `adpPolicy_masked_gradeA` is the special case `e ≥` the paper's
  matrix ESC.
* **Necessary** (`adpPolicy_unmasked_fails_left`, `adpPolicy_unmasked_fails_right`): if some
  product `xₜyₜ` of the entry has a factor whose fixed-point conversion drops `D ≥ 1` of its 53
  significand bits (for `xₜ`, `D = exp(x_max) − exp(xₜ) + 53 − W`), and
  `(8k + 4) 2^-53 P + 2^-1074 < 2^(exp(xₜ) + exp(yₜ) − 53 + min(D, 53))` with
  `P = Σ 2^(exp(xᵢ) + exp(yᵢ))` over the nonzero products, then there are binary64 inputs with the
  same exponent pattern on which the run takes the same path with the same width and that entry
  breaks Grade A. The inputs replace every nonzero entry by the positive power of two with its
  exponent, except that the deficient factor's exponent gets the value `2^e + 2^(e + D − 53)`,
  which loses half a fixed-point unit (or `2^e`, lost entirely, when `D ≥ 53`). The hypotheses
  besides the pattern condition are the run's own (it emulates, `k · 2^14 < 2^31`) and entries below
  `2^500`, which keep every constructed result finite (`adpPolicy_mapped`).

**The gap.** For the dominant product (`exp(xₜ) + exp(yₜ) = F`), `54 + escExact ≤ W` means
`exp(x_max) − exp(xₜ) + exp(y_max) − exp(yₜ) + 54 ≤ W`: no factor loses a bit, with one bit to
spare. The necessary condition needs one factor to lose `D` bits with
`2^D > (8k + 4) P / 2^F + 2^(−1021 − F)`, about `log₂(8k + 4) + log₂(P / 2^F) ≤ log₂((8k + 4) k)`
bits. Undecided are the patterns in between: a factor that loses fewer bits than that; losses
spread over both factors of a product, each below the threshold; non-dominant products whose loss
the tolerance `(4k + 1) u Σ|xᵢyᵢ|` absorbs; and widths with `W < 54 + escExact` but no loss at
all. There Grade A can hold or fail depending on the significands. -/

open TensorCore

namespace Ozaki.TC

open ADP

/-! ## Sufficient: the exact ESC of the entry -/

/-- `fixedProduct_error` with the exact ESC in place of the coarsened one. -/
theorem fixedProduct_error_exactESC {x y : List ℚ} (hlen : x.length = y.length)
    (hx : ∀ a ∈ x, OnGrid64 a) (hy : ∀ b ∈ y, OnGrid64 b) {W : ℤ}
    (hW : 54 + escExact x y ≤ W) :
    (∀ F, fExact (expsOf x) (expsOf y) = some F →
      Rat.abs (dot x y - fixedProduct W x y) ≤ x.length * 2 ^ (F - 52)) ∧
    (fExact (expsOf x) (expsOf y) = none → fixedProduct W x y = dot x y) := by
  unfold fixedProduct
  constructor
  · intro F hf
    cases hp : maxE (expsOf x) with
    | none =>
      obtain ⟨a, b, hab, ha, _, _⟩ := fExact_attained hf
      exact absurd (eq_zero_of_maxE_none hp a (List.of_mem_zip hab).1) ha
    | some ep =>
      cases hq : maxE (expsOf y) with
      | none =>
        obtain ⟨a, b, hab, _, hb, _⟩ := fExact_attained hf
        exact absurd (eq_zero_of_maxE_none hq b (List.of_mem_zip hab).2) hb
      | some eq =>
        have hsx : shiftOf W x = W - 1 - ep := by simp [shiftOf, hp]
        have hsy : shiftOf W y = W - 1 - eq := by simp [shiftOf, hq]
        rw [hsx, hsy]
        have hw : 54 + (ep + eq - F) ≤ W := by
          unfold escExact at hW; rw [hp, hq, hf] at hW; simpa using hW
        exact fixedPoint_error hlen hx hy (exp64_le_maxE hp) (exp64_le_maxE hq) (fExact_le hp hq hf)
          hw
  · intro hf
    obtain ⟨h1, h2⟩ := dot_pairs_zero (shiftOf W x) (shiftOf W y) x y (fExact_none hf)
    rw [h1, h2]; simp

/-- **Grade A from the exact ESC.** `emulated_gradeA` with `W ≥ 54 + escExact x y`, the exact ESC
of this dot product, which depends only on the exponent pattern. -/
theorem emulated_gradeA_exactESC {rnd : ℚ → Option ℚ} {η : ℚ}
    (hr : RoundWithin rnd (2 ^ (-53 : ℤ)) η) {x y : List ℚ} (hlen : x.length = y.length)
    (hx : ∀ a ∈ x, OnGrid64 a) (hy : ∀ b ∈ y, OnGrid64 b)
    (hnx : ∀ a ∈ x, Normal64 a) (hny : ∀ b ∈ y, Normal64 b) {W : ℤ}
    (hW : 54 + escExact x y ≤ W) (hk : 2 * (x.length : ℚ) * 2 ^ (-53 : ℤ) ≤ 1)
    {C : ℚ} (hC : rnd (fixedProduct W x y) = some C) :
    Rat.abs (C - dot x y) ≤
      (4 * x.length + 1) * 2 ^ (-53 : ℤ) * ((List.zipWith (· * ·) x y).map Rat.abs).sum + η := by
  have hxy := abs_dot_le_sum x y
  generalize hS : ((List.zipWith (· * ·) x y).map Rat.abs).sum = S at *
  have hSnn : 0 ≤ S := Rat.le_trans (abs_nonneg _) hxy
  have hu := two_pow_pos (-53 : ℤ)
  obtain ⟨hsome, hnone⟩ := fixedProduct_error_exactESC hlen hx hy hW
  have hmono : (2 * (x.length : ℚ) + 2) * 2 ^ (-53 : ℤ) * S ≤
      (4 * x.length + 1) * 2 ^ (-53 : ℤ) * S := by
    by_cases h0 : x.length = 0
    · have : S = 0 := by
        rw [← hS, List.length_eq_zero_iff.mp h0]; simp
      rw [this]; grind
    · have : (1 : ℚ) ≤ x.length := by
        have : 1 ≤ x.length := Nat.pos_of_ne_zero h0
        exact_mod_cast this
      have := Rat.mul_nonneg (Rat.le_of_lt hu) hSnn
      have := Rat.mul_le_mul_of_nonneg_right
        (show 2 * (x.length : ℚ) + 2 ≤ 4 * x.length + 1 by grind) this
      grind
  cases hf : fExact (expsOf x) (expsOf y) with
  | none =>
    rw [hnone hf] at hC
    have h := hr _ _ hC
    have := Rat.mul_le_mul_of_nonneg_left hxy (Rat.le_of_lt hu)
    have hkS : 0 ≤ (4 * (x.length : ℚ)) * 2 ^ (-53 : ℤ) * S :=
      Rat.mul_nonneg (Rat.mul_nonneg (by grind) (Rat.le_of_lt hu)) hSnn
    grind
  | some F =>
    have h := round_gradeA hr hxy (hsome F hf)
      (by rw [← hS]; exact two_pow_F_le hnx hny hf) hk hC
    exact Rat.le_trans h (by grind)

/-- **Sufficient, per entry.** If ADP with any zero policy emulates with matrix ESC `e`, an entry
whose own exact ESC is at most `e` meets Grade A, whatever the significands, on normal or zero
entries with `k · 2^14 < 2^31`. -/
theorem adpPolicy_entry_gradeA {cfg : ADPConfig} {pol : ZeroPolicy}
    {A B : List (List (BitVec 64))} {C : List (List ℚ)}
    (h : adpPolicy cfg pol A B = (.emulated, some C)) {Aq Bq : List (List ℚ)}
    (hA : decodeMatrix64 A = some Aq) (hB : decodeMatrix64 B = some Bq) {e : ℤ}
    (he : matrixEscPolicy pol cfg.block Aq (transpose Bq) = some e)
    {i j : ℕ} (hi : i < Aq.length) (hj : j < (transpose Bq).length)
    (hlen : Aq[i].length = (transpose Bq)[j].length)
    (hnx : ∀ a ∈ Aq[i], Normal64 a) (hny : ∀ b ∈ (transpose Bq)[j], Normal64 b)
    (hk : Aq[i].length * (128 * 128) < 2 ^ 31)
    (hW : escExact Aq[i] (transpose Bq)[j] ≤ e) :
    ∃ (hiC : i < C.length) (hjC : j < C[i].length),
      gradeAEntry Aq[i] (transpose Bq)[j] C[i][j] = true := by
  have gA := decode_onGrid hA
  have gB := decode_onGrid hB
  have hx := List.getElem_mem (l := Aq) hi
  have hy := List.getElem_mem (l := transpose Bq) hj
  have gcol : ∀ b ∈ (transpose Bq)[j], ADP.OnGrid64 b := fun b hb => by
    obtain ⟨r, hr, hbr⟩ := mem_transpose Bq _ hy b hb; exact gB r hr b hbr
  unfold adpPolicy at h
  rw [hA, hB] at h
  simp only at h
  rw [he] at h
  simp only at h
  split at h
  · simp only [Prod.mk.injEq] at h
    obtain ⟨_, hC⟩ := h
    obtain ⟨hl, hrows⟩ := mapM_some_index Aq C hC
    have hiC : i < C.length := by omega
    obtain ⟨hl2, hents⟩ := mapM_some_index (transpose Bq) C[i] (hrows i hi hiC)
    have hjC : j < C[i].length := by omega
    refine ⟨hiC, hjC, ?_⟩
    obtain ⟨hs1, hfit, _⟩ := slicesNeeded_spec (adpWidth e)
    have hW' : 54 + escExact Aq[i] (transpose Bq)[j] ≤ ((adpWidth e : ℕ) : ℤ) := by
      unfold adpWidth; omega
    have hent := hents j hj hjC
    rw [emulEntry_eq hs1 hfit hk] at hent
    have hg := emulated_gradeA_exactESC fp64Round_within hlen (gA _ hx) gcol hnx hny hW'
      (two_k_u_le hk) hent
    unfold gradeAEntry
    exact decide_eq_true hg
  · simp at h

/-! ## Inputs with a given exponent pattern -/

/-- The positive power of two with the exponent of `v`; zero stays zero. -/
def pow2Of (v : ℚ) : ℚ := if v = 0 then 0 else 2 ^ exp64 v

/-- A value with exponent `e` whose fixed-point conversion, when it drops `D` of the 53 significand
bits (`1 ≤ D ≤ 52`), loses half a unit of the fixed-point grid: `2^e + 2^(e + D − 53)`. For
`D ≥ 53` the power `2^e`, which is lost entirely. -/
def lossyOf (e D : ℤ) : ℚ := if D ≤ 52 then 2 ^ e + 2 ^ (e + D - 53) else 2 ^ e

/-- Every nonzero entry with exponent `e` becomes `lossyOf e D`, every other nonzero entry its power
of two. -/
def lossyMap (e D : ℤ) (v : ℚ) : ℚ :=
  if v = 0 then 0 else if exp64 v = e then lossyOf e D else 2 ^ exp64 v

theorem exp64_ge (v : ℚ) : -1022 ≤ exp64 v := by unfold exp64; omega

theorem exp64_of_bounds {v : ℚ} {e : ℤ} (he : -1022 ≤ e) (h1 : (2 : ℚ) ^ e ≤ Rat.abs v)
    (h2 : Rat.abs v < 2 ^ (e + 1)) : exp64 v = e := by
  unfold exp64; rw [floorLog2_eq h1 h2]; omega

theorem exp64_two_pow {e : ℤ} (he : -1022 ≤ e) : exp64 ((2 : ℚ) ^ e) = e := by
  have hp := two_pow_pos e
  apply exp64_of_bounds he <;> rw [abs_of_nonneg (Rat.le_of_lt hp)]
  · exact Rat.le_refl
  · exact two_pow_lt (by omega)

theorem lossyOf_bounds (e : ℤ) {D : ℤ} (hD : 1 ≤ D) :
    (2 : ℚ) ^ e ≤ lossyOf e D ∧ lossyOf e D < 2 ^ (e + 1) := by
  have he := two_pow_pos e
  have h2 : (2 : ℚ) ^ (e + 1) = 2 ^ e + 2 ^ e := by rw [two_pow_add, two_pow_one]; grind
  unfold lossyOf
  split
  · have hl := two_pow_pos (e + D - 53)
    have hlt : (2 : ℚ) ^ (e + D - 53) < 2 ^ e := two_pow_lt (by omega)
    constructor <;> grind
  · constructor <;> grind

theorem exp64_lossyOf {e D : ℤ} (he : -1022 ≤ e) (hD : 1 ≤ D) : exp64 (lossyOf e D) = e := by
  obtain ⟨h1, h2⟩ := lossyOf_bounds e hD
  have hpos : 0 ≤ lossyOf e D := Rat.le_trans (Rat.le_of_lt (two_pow_pos e)) h1
  apply exp64_of_bounds he <;> rw [abs_of_nonneg hpos]
  · exact h1
  · exact h2

theorem lossyOf_ne_zero (e : ℤ) {D : ℤ} (hD : 1 ≤ D) : lossyOf e D ≠ 0 := by
  have := (lossyOf_bounds e hD).1; have := two_pow_pos e; grind

theorem expOf_pow2Of (v : ℚ) : expOf (pow2Of v) = expOf v := by
  unfold pow2Of
  by_cases hv : v = 0
  · simp [hv]
  · rw [if_neg hv, expOf_ne (Rat.ne_of_gt (two_pow_pos _)), expOf_ne hv,
      exp64_two_pow (exp64_ge v)]

theorem expOf_lossyMap {e D : ℤ} (hD : 1 ≤ D) (v : ℚ) : expOf (lossyMap e D v) = expOf v := by
  unfold lossyMap
  by_cases hv : v = 0
  · simp [hv]
  · rw [if_neg hv, expOf_ne hv]
    split
    · rename_i h
      rw [expOf_ne (lossyOf_ne_zero e hD), exp64_lossyOf (by rw [← h]; exact exp64_ge v) hD, h]
    · rw [expOf_ne (Rat.ne_of_gt (two_pow_pos _)), exp64_two_pow (exp64_ge v)]

theorem expsOf_map {f : ℚ → ℚ} (hf : ∀ v, expOf (f v) = expOf v) (x : List ℚ) :
    expsOf (x.map f) = expsOf x := by
  unfold expsOf; rw [List.map_map]; exact List.map_congr_left (fun v _ => hf v)

/-- A decoded binary64 word is a binary64 value. -/
theorem value64_binary64 {w : BitVec 64} {v : ℚ} (h : value64 w = some v) : Binary64Value v :=
  fp64_binary64 (binaryValue_finiteValue fp64_wellFormed h)

theorem decode_binary64 {A : List (List (BitVec 64))} {Aq : List (List ℚ)}
    (h : decodeMatrix64 A = some Aq) : ∀ x ∈ Aq, ∀ a ∈ x, Binary64Value a := by
  intro x hx a ha
  obtain ⟨row, _, hrow⟩ := mapM_some_mem h x hx
  obtain ⟨w, _, hw⟩ := mapM_some_mem hrow a ha
  exact value64_binary64 hw

theorem exp64_le_of_abs_lt {v : ℚ} (hv : v ≠ 0) {E : ℤ} (h : Rat.abs v < 2 ^ (E + 1))
    (hE : -1022 ≤ E) : exp64 v ≤ E := by
  unfold exp64
  have hpos := abs_pos_of_ne hv
  obtain ⟨h1, _⟩ := floorLog2_spec hpos
  have hn : ¬ E + 1 ≤ floorLog2 (Rat.abs v) := fun hc => by
    have := two_pow_le hc
    grind
  omega

theorem exp64_le_1023 {v : ℚ} (hv : Binary64Value v) (h0 : v ≠ 0) : exp64 v ≤ 1023 :=
  exp64_le_of_abs_lt h0 (binary64Value_abs_lt hv) (by decide)

theorem binary64_pow2Of {v : ℚ} (hv : Binary64Value v) : Binary64Value (pow2Of v) := by
  unfold pow2Of
  split
  · exact binary64Value_zero
  · rename_i h0
    exact binary64Value_two_pow (exp64_ge v) (exp64_le_1023 hv h0)

theorem binary64_lossyOf {e D : ℤ} (he1 : -1022 ≤ e) (he2 : e ≤ 1023) (hD : 1 ≤ D) :
    Binary64Value (lossyOf e D) := by
  unfold lossyOf
  split
  · rename_i hD2
    obtain ⟨n, hn⟩ : ∃ n : ℕ, (n : ℤ) = D - 1 := ⟨(D - 1).toNat, by omega⟩
    refine ⟨((2 ^ 52 + 2 ^ n : ℕ) : ℤ), e, he1, he2, ?_, ?_⟩
    · have : 2 ^ n ≤ 2 ^ 51 := Nat.pow_le_pow_right (by decide) (by omega)
      have h53 : (2 : ℕ) ^ 53 = 2 ^ 52 + 2 ^ 52 := by decide
      simp only [Int.natAbs_natCast]
      omega
    · rw [Rat.intCast_natCast, Rat.natCast_add, ← two_pow_natCast, ← two_pow_natCast, Rat.add_mul,
        ← two_pow_add, ← two_pow_add]
      congr 2 <;> omega
  · exact binary64Value_two_pow he1 he2

theorem binary64_lossyMap {e D : ℤ} (hD : 1 ≤ D) {v : ℚ} (hv : Binary64Value v) :
    Binary64Value (lossyMap e D v) := by
  unfold lossyMap
  split
  · exact binary64Value_zero
  · rename_i h0
    split
    · rename_i h
      exact binary64_lossyOf (by rw [← h]; exact exp64_ge v) (by rw [← h]; exact exp64_le_1023 hv h0)
        hD
    · exact binary64Value_two_pow (exp64_ge v) (exp64_le_1023 hv h0)

theorem pow2Of_bounds (v : ℚ) : 0 ≤ pow2Of v ∧ pow2Of v ≤ 2 * pow2Of v := by
  unfold pow2Of; split
  · constructor <;> grind
  · have := two_pow_pos (exp64 v); constructor <;> grind

theorem lossyMap_bounds {e D : ℤ} (hD : 1 ≤ D) (v : ℚ) :
    0 ≤ lossyMap e D v ∧ lossyMap e D v ≤ 2 * pow2Of v := by
  unfold lossyMap pow2Of
  split
  · constructor <;> grind
  · split
    · rename_i h0 h
      obtain ⟨h1, h2⟩ := lossyOf_bounds e hD
      rw [h]
      have h2' : (2 : ℚ) ^ (e + 1) = 2 * 2 ^ e := by rw [two_pow_add, two_pow_one]; grind
      have := two_pow_pos e
      constructor <;> grind
    · have := two_pow_pos (exp64 v); constructor <;> grind

/-! ## Every product loses to fixed point -/

theorem fixedValue_bounds {a : ℚ} (ha : 0 ≤ a) (s : ℤ) :
    0 ≤ fixedValue s a ∧ fixedValue s a ≤ a := by
  unfold fixedValue
  have hs := two_pow_pos s
  have hs' := two_pow_pos (-s)
  have hnn : 0 ≤ a * 2 ^ s := Rat.mul_nonneg ha (Rat.le_of_lt hs)
  have hf0 : (0 : ℚ) ≤ ((a * 2 ^ s).floor : ℚ) := by
    have : (0 : ℤ) ≤ (a * 2 ^ s).floor := Rat.le_floor_iff.mpr (by rw [Rat.intCast_zero]; exact hnn)
    exact_mod_cast this
  have hfl := Rat.floor_le (a * 2 ^ s)
  have hinv : (2 : ℚ) ^ s * 2 ^ (-s) = 1 := by
    rw [← two_pow_add, show s + -s = 0 by omega]; rfl
  constructor
  · exact Rat.mul_nonneg hf0 (Rat.le_of_lt hs')
  · have := Rat.mul_le_mul_of_nonneg_right hfl (Rat.le_of_lt hs')
    calc ((a * 2 ^ s).floor : ℚ) * 2 ^ (-s) ≤ a * 2 ^ s * 2 ^ (-s) := this
      _ = a := by rw [Rat.mul_assoc, hinv, Rat.mul_one]

/-- **Fixed point never gains, with nonnegative entries**: the exact product exceeds the converted
one by at least `(a − ã) b` and `a (b − b̃)` for every pair `(a, b)`. -/
theorem dot_sub_fixed_ge (sx sy : ℤ) : ∀ (x y : List ℚ), (∀ a ∈ x, 0 ≤ a) → (∀ b ∈ y, 0 ≤ b) →
    0 ≤ dot x y - dot (x.map (fixedValue sx)) (y.map (fixedValue sy)) ∧
    ∀ ab ∈ List.zip x y,
      (ab.1 - fixedValue sx ab.1) * ab.2 ≤
          dot x y - dot (x.map (fixedValue sx)) (y.map (fixedValue sy)) ∧
        ab.1 * (ab.2 - fixedValue sy ab.2) ≤
          dot x y - dot (x.map (fixedValue sx)) (y.map (fixedValue sy))
  | [], _, _, _ => ⟨by simp only [List.map_nil, dot_nil_left]; grind, fun ab hab => by simp at hab⟩
  | _ :: _, [], _, _ =>
    ⟨by simp only [List.map_nil, dot_nil_right]; grind, fun ab hab => by simp at hab⟩
  | a :: x, b :: y, hx, hy => by
    have ha : 0 ≤ a := hx a List.mem_cons_self
    have hb : 0 ≤ b := hy b List.mem_cons_self
    obtain ⟨ih0, ih⟩ := dot_sub_fixed_ge sx sy x y (fun c hc => hx c (List.mem_cons_of_mem _ hc))
      (fun c hc => hy c (List.mem_cons_of_mem _ hc))
    obtain ⟨fa0, fa1⟩ := fixedValue_bounds ha sx
    obtain ⟨fb0, fb1⟩ := fixedValue_bounds hb sy
    simp only [List.map_cons, dot_cons, List.zip_cons_cons, List.mem_cons]
    have t1 : (a - fixedValue sx a) * b ≤ a * b - fixedValue sx a * fixedValue sy b := by
      have := Rat.mul_le_mul_of_nonneg_left fb1 fa0
      have e : (a - fixedValue sx a) * b = a * b - fixedValue sx a * b := by
        grind
      rw [e]; grind
    have t2 : a * (b - fixedValue sy b) ≤ a * b - fixedValue sx a * fixedValue sy b := by
      have := Rat.mul_le_mul_of_nonneg_right fa1 fb0
      have e : a * (b - fixedValue sy b) = a * b - a * fixedValue sy b := by
        grind
      rw [e]; grind
    have t0 : 0 ≤ a * b - fixedValue sx a * fixedValue sy b := by
      have := Rat.mul_nonneg (show 0 ≤ a - fixedValue sx a by grind) hb
      grind
    refine ⟨by grind, fun ab hab => ?_⟩
    rcases hab with rfl | hab
    · exact ⟨by simp only; grind, by simp only; grind⟩
    · obtain ⟨h1, h2⟩ := ih ab hab
      exact ⟨by grind, by grind⟩

/-! ## The lossy value's loss -/

/-- **The lossy value loses `2^(e − 53 + min(D, 53))`** in a conversion with shift `s`,
`e + s = 52 − D`: half a fixed-point unit when `D ≤ 52`, the whole value `2^e` otherwise. -/
theorem lossyOf_loss {e D s : ℤ} (hD : 1 ≤ D) (hs : e + s = 52 - D) :
    (2 : ℚ) ^ (e - 53 + min D 53) ≤ lossyOf e D - fixedValue s (lossyOf e D) := by
  unfold lossyOf fixedValue
  split
  · rename_i hD2
    obtain ⟨n, hn⟩ : ∃ n : ℕ, (n : ℤ) = 52 - D := ⟨(52 - D).toNat, by omega⟩
    have ht : (2 ^ e + 2 ^ (e + D - 53)) * (2 : ℚ) ^ s =
        (((2 ^ n : ℕ) : ℤ) : ℚ) + 2 ^ (-1 : ℤ) := by
      rw [Rat.add_mul, ← two_pow_add, ← two_pow_add, Rat.intCast_natCast, ← two_pow_natCast, hn,
        show e + s = 52 - D by omega, show e + D - 53 + s = -1 by omega]
    have hhalf : (2 : ℚ) ^ (-1 : ℤ) < 1 := by
      have := two_pow_lt (show (-1 : ℤ) < 0 by decide)
      rwa [show (2 : ℚ) ^ (0 : ℤ) = 1 from rfl] at this
    have hfl : ((2 ^ e + 2 ^ (e + D - 53)) * (2 : ℚ) ^ s).floor = ((2 ^ n : ℕ) : ℤ) := by
      apply floor_eq_of
      · rw [ht]; have := two_pow_pos (-1 : ℤ); grind
      · rw [ht]; grind
    rw [hfl, Rat.intCast_natCast, ← two_pow_natCast, hn, ← two_pow_add,
      show 52 - D + -s = e by omega, show e - 53 + min D 53 = e + D - 53 by omega]
    grind
  · rename_i hD2
    have hlt : (2 : ℚ) ^ e * 2 ^ s < 1 := by
      rw [← two_pow_add, hs]
      have := two_pow_lt (show 52 - D < 0 by omega)
      rwa [show (2 : ℚ) ^ (0 : ℤ) = 1 from rfl] at this
    have hnn : (0 : ℚ) ≤ 2 ^ e * 2 ^ s :=
      Rat.mul_nonneg (Rat.le_of_lt (two_pow_pos e)) (Rat.le_of_lt (two_pow_pos s))
    have hfl : ((2 : ℚ) ^ e * 2 ^ s).floor = 0 :=
      floor_eq_of (by rw [Rat.intCast_zero]; exact hnn) (by rw [Rat.intCast_zero]; grind)
    rw [hfl, show e - 53 + min D 53 = e by omega, Rat.intCast_zero, Rat.zero_mul]
    grind

/-! ## The exponent pattern's product sum -/

/-- `2^E` for an exponent, `0` for `−∞`. -/
def expTerm : Exp → ℚ
  | some E => 2 ^ E
  | none => 0

/-- **The pattern's product sum** `P = Σ 2^(exp xᵢ + exp yᵢ)` over the nonzero products: a function
of the exponent pattern only. -/
def patSum (ex ey : List Exp) : ℚ := ((List.zipWith eAdd ex ey).map expTerm).sum

theorem pow2Of_mul (v w : ℚ) : pow2Of v * pow2Of w = expTerm (eAdd (expOf v) (expOf w)) := by
  unfold pow2Of
  by_cases hv : v = 0
  · simp [hv, expOf, eAdd, expTerm]
  · by_cases hw : w = 0
    · simp [hw, expOf, eAdd, expTerm]
    · rw [if_neg hv, if_neg hw, expOf_ne hv, expOf_ne hw]
      simp only [eAdd, expTerm]
      rw [two_pow_add]

/-- With `0 ≤ f v ≤ c_f 2^exp(v)` and `0 ≤ g w ≤ c_g 2^exp(w)`, the product is at most
`c_f c_g P`. -/
theorem dot_le_patSum {f g : ℚ → ℚ} {cf cg : ℚ} (hcf : 0 ≤ cf)
    (hf : ∀ v, 0 ≤ f v ∧ f v ≤ cf * pow2Of v) (hg : ∀ w, 0 ≤ g w ∧ g w ≤ cg * pow2Of w) :
    ∀ x y : List ℚ, dot (x.map f) (y.map g) ≤ cf * cg * patSum (expsOf x) (expsOf y)
  | [], _ => by simp [patSum, expsOf]
  | _ :: _, [] => by simp [patSum, expsOf]
  | a :: x, b :: y => by
    have ih := dot_le_patSum hcf hf hg x y
    simp only [List.map_cons, dot_cons, patSum, expsOf, List.zipWith_cons_cons, List.sum_cons]
    simp only [patSum, expsOf] at ih
    obtain ⟨fa0, fa1⟩ := hf a
    obtain ⟨gb0, gb1⟩ := hg b
    have hpa : 0 ≤ pow2Of a := (pow2Of_bounds a).1
    have hpb : 0 ≤ pow2Of b := (pow2Of_bounds b).1
    have m1 : f a * g b ≤ cf * pow2Of a * g b := Rat.mul_le_mul_of_nonneg_right fa1 gb0
    have m2 : cf * pow2Of a * g b ≤ cf * pow2Of a * (cg * pow2Of b) :=
      Rat.mul_le_mul_of_nonneg_left gb1 (Rat.mul_nonneg hcf hpa)
    have e : cf * pow2Of a * (cg * pow2Of b) = cf * cg * (pow2Of a * pow2Of b) := by grind
    rw [pow2Of_mul] at e
    grind

/-! ## One entry that breaks Grade A -/

theorem dot_nonneg : ∀ (x y : List ℚ), (∀ a ∈ x, 0 ≤ a) → (∀ b ∈ y, 0 ≤ b) → 0 ≤ dot x y
  | [], _, _, _ => by simp only [dot_nil_left]; grind
  | _ :: _, [], _, _ => by simp only [dot_nil_right]; grind
  | a :: x, b :: y, hx, hy => by
    rw [dot_cons]
    have := Rat.mul_nonneg (hx a List.mem_cons_self) (hy b List.mem_cons_self)
    have := dot_nonneg x y (fun c hc => hx c (List.mem_cons_of_mem _ hc))
      (fun c hc => hy c (List.mem_cons_of_mem _ hc))
    grind

theorem sum_abs_of_nonneg : ∀ (l : List ℚ), (∀ a ∈ l, 0 ≤ a) → (l.map Rat.abs).sum = l.sum
  | [], _ => rfl
  | a :: l, h => by
    simp only [List.map_cons, List.sum_cons]
    rw [abs_of_nonneg (h a List.mem_cons_self),
      sum_abs_of_nonneg l (fun b hb => h b (List.mem_cons_of_mem _ hb))]

theorem zipWith_mul_nonneg : ∀ (x y : List ℚ), (∀ a ∈ x, 0 ≤ a) → (∀ b ∈ y, 0 ≤ b) →
    ∀ c ∈ List.zipWith (· * ·) x y, 0 ≤ c
  | [], _, _, _ => by simp
  | _ :: _, [], _, _ => by simp
  | a :: x, b :: y, hx, hy => by
    intro c hc
    simp only [List.zipWith_cons_cons, List.mem_cons] at hc
    rcases hc with rfl | hc
    · exact Rat.mul_nonneg (hx a List.mem_cons_self) (hy b List.mem_cons_self)
    · exact zipWith_mul_nonneg x y (fun d hd => hx d (List.mem_cons_of_mem _ hd))
        (fun d hd => hy d (List.mem_cons_of_mem _ hd)) c hc

/-- **The failure, abstractly.** Nonnegative entries; the conversion loses at least `L`; the
product is at most `2P`; and `(8k + 4) 2^-53 P + 2^-1074 < L`. Then one binary64 rounding of the
converted product breaks Grade A. -/
theorem gradeA_fails_core {x y : List ℚ} {sx sy : ℤ} {P L c : ℚ}
    (hx : ∀ a ∈ x, 0 ≤ a) (hy : ∀ b ∈ y, 0 ≤ b)
    (hgap : L ≤ dot x y - dot (x.map (fixedValue sx)) (y.map (fixedValue sy)))
    (hS : dot x y ≤ 2 * P)
    (hcond : (8 * (x.length : ℚ) + 4) * 2 ^ (-53 : ℤ) * P + 2 ^ (-1074 : ℤ) < L)
    (hc : rne64 (dot (x.map (fixedValue sx)) (y.map (fixedValue sy))) = some c) :
    gradeAEntry x y c = false := by
  have hx' : ∀ a ∈ x.map (fixedValue sx), 0 ≤ a := fun a ha => by
    obtain ⟨b, hb, rfl⟩ := List.mem_map.mp ha; exact (fixedValue_bounds (hx b hb) sx).1
  have hy' : ∀ a ∈ y.map (fixedValue sy), 0 ≤ a := fun a ha => by
    obtain ⟨b, hb, rfl⟩ := List.mem_map.mp ha; exact (fixedValue_bounds (hy b hb) sy).1
  have hF0 := dot_nonneg _ _ hx' hy'
  have hFS := (dot_sub_fixed_ge sx sy x y hx hy).1
  have hsum : ((List.zipWith (· * ·) x y).map Rat.abs).sum = dot x y :=
    sum_abs_of_nonneg _ (zipWith_mul_nonneg x y hx hy)
  unfold gradeAEntry
  rw [hsum]
  apply decide_eq_false
  intro hle
  generalize dot x y = S at *
  generalize dot (x.map (fixedValue sx)) (y.map (fixedValue sy)) = F at *
  have hFS' : F ≤ S := by grind
  have hr := rne64_within F c hc
  rw [abs_of_nonneg hF0] at hr
  have hu := two_pow_pos (-53 : ℤ)
  generalize hU : (2 : ℚ) ^ (-53 : ℤ) = u at *
  have hη : (2 : ℚ) ^ (-1074 : ℤ) = 2 ^ (-1075 : ℤ) + 2 ^ (-1075 : ℤ) := by
    rw [show (-1074 : ℤ) = -1075 + 1 by omega, two_pow_add, two_pow_one]; grind
  rw [hη] at hcond
  generalize (2 : ℚ) ^ (-1075 : ℤ) = η at *
  have hk : (0 : ℚ) ≤ x.length := Rat.natCast_nonneg
  rw [abs_le_iff] at hle hr
  obtain ⟨hle1, _⟩ := hle
  obtain ⟨_, hr2⟩ := hr
  have m1 : u * F ≤ u * S := Rat.mul_le_mul_of_nonneg_left hFS' (Rat.le_of_lt hu)
  have hc4 : 0 ≤ (4 * (x.length : ℚ) + 2) * u := Rat.mul_nonneg (by grind) (Rat.le_of_lt hu)
  have m2 : (4 * (x.length : ℚ) + 2) * u * S ≤ (4 * (x.length : ℚ) + 2) * u * (2 * P) :=
    Rat.mul_le_mul_of_nonneg_left hS hc4
  grind

/-- **Left factor.** If `xₜ` loses `D ≥ 1` bits in fixed point and the pattern condition holds, then
replacing the entries by `lossyMap` (left) and their powers of two (right) breaks Grade A. -/
theorem lossy_left_fails {x y : List ℚ} {W ep e D : ℤ} (hep : maxE (expsOf x) = some ep) {t : ℕ}
    {a b : ℚ} (ha : x[t]? = some a) (hb : y[t]? = some b) (ha0 : a ≠ 0) (hb0 : b ≠ 0)
    (he : exp64 a = e) (hDdef : D = ep - e + 53 - W) (hD : 1 ≤ D)
    (hcond : (8 * (x.length : ℚ) + 4) * 2 ^ (-53 : ℤ) * patSum (expsOf x) (expsOf y) +
      2 ^ (-1074 : ℤ) < 2 ^ (e + exp64 b - 53 + min D 53))
    {c : ℚ} (hc : rne64 (fixedProduct W (x.map (lossyMap e D)) (y.map pow2Of)) = some c) :
    gradeAEntry (x.map (lossyMap e D)) (y.map pow2Of) c = false := by
  have hx' : expsOf (x.map (lossyMap e D)) = expsOf x := expsOf_map (expOf_lossyMap hD) x
  have hsx : shiftOf W (x.map (lossyMap e D)) = W - 1 - ep := by
    unfold shiftOf; rw [hx', hep]
  unfold fixedProduct at hc
  rw [← dot_fixedValue] at hc
  have hnx : ∀ v ∈ x.map (lossyMap e D), 0 ≤ v := fun v hv => by
    obtain ⟨w, _, rfl⟩ := List.mem_map.mp hv; exact (lossyMap_bounds hD w).1
  have hny : ∀ v ∈ y.map pow2Of, 0 ≤ v := fun v hv => by
    obtain ⟨w, _, rfl⟩ := List.mem_map.mp hv; exact (pow2Of_bounds w).1
  refine gradeA_fails_core (sx := shiftOf W (x.map (lossyMap e D))) (sy := shiftOf W (y.map pow2Of))
    hnx hny ?_ ?_ (by rw [List.length_map]; exact hcond) hc
  · -- the pair `(xₜ, yₜ)` loses at least `2^(e + exp(yₜ) − 53 + min(D, 53))`
    obtain ⟨hti, hxa⟩ := List.getElem?_eq_some_iff.mp ha
    obtain ⟨htj, hyb⟩ := List.getElem?_eq_some_iff.mp hb
    have hmem : (lossyMap e D a, pow2Of b) ∈ List.zip (x.map (lossyMap e D)) (y.map pow2Of) := by
      rw [← hxa, ← hyb]
      have h1 : t < (List.zip (x.map (lossyMap e D)) (y.map pow2Of)).length := by simp; omega
      have := List.getElem_mem h1
      simpa [List.getElem_zip] using this
    obtain ⟨h1, _⟩ := (dot_sub_fixed_ge (shiftOf W (x.map (lossyMap e D))) (shiftOf W (y.map pow2Of))
      _ _ hnx hny).2 _ hmem
    simp only at h1
    have hla : lossyMap e D a = lossyOf e D := by unfold lossyMap; rw [if_neg ha0, if_pos he]
    have hpb : pow2Of b = 2 ^ exp64 b := by unfold pow2Of; rw [if_neg hb0]
    rw [hla, hpb] at h1
    have hloss := lossyOf_loss (e := e) (D := D) (s := shiftOf W (x.map (lossyMap e D))) hD
      (by rw [hsx]; omega)
    have hm := Rat.mul_le_mul_of_nonneg_right hloss (Rat.le_of_lt (two_pow_pos (exp64 b)))
    rw [← two_pow_add, show e - 53 + min D 53 + exp64 b = e + exp64 b - 53 + min D 53 by omega]
      at hm
    exact Rat.le_trans hm h1
  · have := dot_le_patSum (f := lossyMap e D) (g := pow2Of) (cf := 2) (cg := 1) (by decide)
      (fun v => lossyMap_bounds hD v) (fun w => ⟨(pow2Of_bounds w).1, by grind⟩) x y
    grind

/-- **Right factor.** The same with the loss in `yₜ`, `D = exp(y_max) − exp(yₜ) + 53 − W`. -/
theorem lossy_right_fails {x y : List ℚ} {W eq e D : ℤ} (heq : maxE (expsOf y) = some eq) {t : ℕ}
    {a b : ℚ} (ha : x[t]? = some a) (hb : y[t]? = some b) (ha0 : a ≠ 0) (hb0 : b ≠ 0)
    (he : exp64 b = e) (hDdef : D = eq - e + 53 - W) (hD : 1 ≤ D)
    (hcond : (8 * (x.length : ℚ) + 4) * 2 ^ (-53 : ℤ) * patSum (expsOf x) (expsOf y) +
      2 ^ (-1074 : ℤ) < 2 ^ (exp64 a + e - 53 + min D 53))
    {c : ℚ} (hc : rne64 (fixedProduct W (x.map pow2Of) (y.map (lossyMap e D))) = some c) :
    gradeAEntry (x.map pow2Of) (y.map (lossyMap e D)) c = false := by
  have hy' : expsOf (y.map (lossyMap e D)) = expsOf y := expsOf_map (expOf_lossyMap hD) y
  have hsy : shiftOf W (y.map (lossyMap e D)) = W - 1 - eq := by
    unfold shiftOf; rw [hy', heq]
  unfold fixedProduct at hc
  rw [← dot_fixedValue] at hc
  have hnx : ∀ v ∈ x.map pow2Of, 0 ≤ v := fun v hv => by
    obtain ⟨w, _, rfl⟩ := List.mem_map.mp hv; exact (pow2Of_bounds w).1
  have hny : ∀ v ∈ y.map (lossyMap e D), 0 ≤ v := fun v hv => by
    obtain ⟨w, _, rfl⟩ := List.mem_map.mp hv; exact (lossyMap_bounds hD w).1
  refine gradeA_fails_core (sx := shiftOf W (x.map pow2Of)) (sy := shiftOf W (y.map (lossyMap e D)))
    hnx hny ?_ ?_ (by rw [List.length_map]; exact hcond) hc
  · obtain ⟨hti, hxa⟩ := List.getElem?_eq_some_iff.mp ha
    obtain ⟨htj, hyb⟩ := List.getElem?_eq_some_iff.mp hb
    have hmem : (pow2Of a, lossyMap e D b) ∈ List.zip (x.map pow2Of) (y.map (lossyMap e D)) := by
      rw [← hxa, ← hyb]
      have h1 : t < (List.zip (x.map pow2Of) (y.map (lossyMap e D))).length := by simp; omega
      have := List.getElem_mem h1
      simpa [List.getElem_zip] using this
    obtain ⟨_, h2⟩ := (dot_sub_fixed_ge (shiftOf W (x.map pow2Of)) (shiftOf W (y.map (lossyMap e D)))
      _ _ hnx hny).2 _ hmem
    simp only at h2
    have hlb : lossyMap e D b = lossyOf e D := by unfold lossyMap; rw [if_neg hb0, if_pos he]
    have hpa : pow2Of a = 2 ^ exp64 a := by unfold pow2Of; rw [if_neg ha0]
    rw [hlb, hpa] at h2
    have hloss := lossyOf_loss (e := e) (D := D) (s := shiftOf W (y.map (lossyMap e D))) hD
      (by rw [hsy]; omega)
    have hm := Rat.mul_le_mul_of_nonneg_left hloss (Rat.le_of_lt (two_pow_pos (exp64 a)))
    rw [← two_pow_add, show exp64 a + (e - 53 + min D 53) = exp64 a + e - 53 + min D 53 by omega]
      at hm
    exact Rat.le_trans hm h2
  · have := dot_le_patSum (f := pow2Of) (g := lossyMap e D) (cf := 1) (cg := 2) (by decide)
      (fun v => ⟨(pow2Of_bounds v).1, by grind⟩) (fun w => lossyMap_bounds hD w) x y
    grind

/-! ## The routine on the constructed inputs -/

theorem exists_matrix64 : ∀ (Q : List (List ℚ)), (∀ r ∈ Q, ∀ v ∈ r, Binary64Value v) →
    ∃ M : List (List (BitVec 64)), decodeMatrix64 M = some Q
  | [], _ => ⟨[], rfl⟩
  | r :: Q, h => by
    obtain ⟨ws, hws⟩ := exists_words64 r (h r List.mem_cons_self)
    obtain ⟨M, hM⟩ := exists_matrix64 Q (fun r' hr' => h r' (List.mem_cons_of_mem _ hr'))
    refine ⟨ws :: M, ?_⟩
    unfold decodeMatrix64 at hM ⊢
    rw [List.mapM_cons, hws, hM]; rfl

theorem transpose_map_entries (g : ℚ → ℚ) (B : List (List ℚ)) :
    transpose (B.map (·.map g)) = (transpose B).map (·.map g) := by
  rw [transpose_eq_transposeG, transpose_eq_transposeG, transposeG_map]

theorem escCoarsePolicy_congr (pol : ZeroPolicy) (n : ℕ) {x x' y y' : List ℚ}
    (hx : expsOf x' = expsOf x) (hy : expsOf y' = expsOf y) :
    escCoarsePolicy pol n x' y' = escCoarsePolicy pol n x y := by
  unfold escCoarsePolicy; rw [hx, hy]

/-- **The matrix ESC depends only on the exponent pattern.** -/
theorem matrixEscPolicy_map {f g : ℚ → ℚ} (hf : ∀ v, expOf (f v) = expOf v)
    (hg : ∀ v, expOf (g v) = expOf v) (pol : ZeroPolicy) (n : ℕ) (A cols : List (List ℚ)) :
    matrixEscPolicy pol n (A.map (·.map f)) (cols.map (·.map g)) = matrixEscPolicy pol n A cols := by
  unfold matrixEscPolicy
  congr 1
  induction A with
  | nil => rfl
  | cons x A ih =>
    simp only [List.map_cons, List.flatMap_cons]
    rw [ih, List.map_map]
    congr 1
    apply List.map_congr_left
    intro y _
    exact escCoarsePolicy_congr pol n (expsOf_map hf x) (expsOf_map hg y)

/-- The constructed inputs have the original exponent pattern, row by row. -/
theorem rows_expsOf_map {f : ℚ → ℚ} (hf : ∀ v, expOf (f v) = expOf v) (A : List (List ℚ)) :
    (A.map (·.map f)).map expsOf = A.map expsOf := by
  rw [List.map_map]; exact List.map_congr_left (fun x _ => expsOf_map hf x)

theorem pow2Of_le {v : ℚ} (h : Rat.abs v < 2 ^ (500 : ℤ)) : pow2Of v ≤ 2 ^ (499 : ℤ) := by
  unfold pow2Of; split
  · exact Rat.le_of_lt (two_pow_pos _)
  · rename_i h0; exact two_pow_le (exp64_le_of_abs_lt h0 h (by decide))

theorem mapped_le {f : ℚ → ℚ} (hf : ∀ v, 0 ≤ f v ∧ f v ≤ 2 * pow2Of v) {v : ℚ}
    (h : Rat.abs v < 2 ^ (500 : ℤ)) : 0 ≤ f v ∧ f v ≤ 2 ^ (500 : ℤ) := by
  obtain ⟨h0, h1⟩ := hf v
  have := pow2Of_le h
  have e : (2 : ℚ) ^ (500 : ℤ) = 2 * 2 ^ (499 : ℤ) := by
    rw [show (500 : ℤ) = 1 + 499 from rfl, two_pow_add, two_pow_one]
  exact ⟨h0, by grind⟩

theorem dot_le_len_mul {α β : ℚ} (hα : 0 ≤ α) (hβ : 0 ≤ β) : ∀ (x y : List ℚ),
    (∀ a ∈ x, 0 ≤ a ∧ a ≤ α) → (∀ b ∈ y, 0 ≤ b ∧ b ≤ β) → dot x y ≤ x.length * (α * β)
  | [], _, _, _ => by simp only [dot_nil_left, List.length_nil]; grind
  | _ :: _, [], _, _ => by
    simp only [dot_nil_right]
    exact Rat.mul_nonneg Rat.natCast_nonneg (Rat.mul_nonneg hα hβ)
  | a :: x, b :: y, hx, hy => by
    obtain ⟨ha0, ha1⟩ := hx a List.mem_cons_self
    obtain ⟨hb0, hb1⟩ := hy b List.mem_cons_self
    have ih := dot_le_len_mul hα hβ x y (fun c hc => hx c (List.mem_cons_of_mem _ hc))
      (fun c hc => hy c (List.mem_cons_of_mem _ hc))
    have m1 : a * b ≤ α * b := Rat.mul_le_mul_of_nonneg_right ha1 hb0
    have m2 : α * b ≤ α * β := Rat.mul_le_mul_of_nonneg_left hb1 hα
    rw [dot_cons, List.length_cons, Rat.natCast_add]
    grind

theorem maxFormat_ge_1017 : (2 : ℚ) ^ (1017 : ℤ) ≤ maxFormat 53 1023 := by decide +kernel

/-- The emulated entries of the constructed inputs round without overflow. -/
theorem rne64_fixedProduct_isSome {x y : List ℚ} (W : ℤ)
    (hx : ∀ a ∈ x, 0 ≤ a ∧ a ≤ 2 ^ (500 : ℤ)) (hy : ∀ b ∈ y, 0 ≤ b ∧ b ≤ 2 ^ (500 : ℤ))
    (hk : x.length * (128 * 128) < 2 ^ 31) : ∃ c, rne64 (fixedProduct W x y) = some c := by
  unfold fixedProduct
  rw [← dot_fixedValue]
  have hx0 : ∀ a ∈ x, 0 ≤ a := fun a ha => (hx a ha).1
  have hy0 : ∀ b ∈ y, 0 ≤ b := fun b hb => (hy b hb).1
  have hx' : ∀ a ∈ x.map (fixedValue (shiftOf W x)), 0 ≤ a := fun a ha => by
    obtain ⟨b, hb, rfl⟩ := List.mem_map.mp ha; exact (fixedValue_bounds (hx0 b hb) _).1
  have hy' : ∀ a ∈ y.map (fixedValue (shiftOf W y)), 0 ≤ a := fun a ha => by
    obtain ⟨b, hb, rfl⟩ := List.mem_map.mp ha; exact (fixedValue_bounds (hy0 b hb) _).1
  have hF0 := dot_nonneg _ _ hx' hy'
  have hFS := (dot_sub_fixed_ge (shiftOf W x) (shiftOf W y) x y hx0 hy0).1
  have hS := dot_le_len_mul (Rat.le_of_lt (two_pow_pos 500)) (Rat.le_of_lt (two_pow_pos 500)) x y
    hx hy
  have hkq : (x.length : ℚ) ≤ 2 ^ (17 : ℤ) := by
    have : x.length ≤ 2 ^ 17 := by omega
    show (x.length : ℚ) ≤ 2 ^ ((17 : ℕ) : ℤ)
    rw [two_pow_natCast 17]; exact_mod_cast this
  have hpp : (2 : ℚ) ^ (500 : ℤ) * 2 ^ (500 : ℤ) = 2 ^ (1000 : ℤ) := by
    rw [← two_pow_add, show (500 : ℤ) + 500 = 1000 from rfl]
  have h1017 : (2 : ℚ) ^ (17 : ℤ) * 2 ^ (1000 : ℤ) = 2 ^ (1017 : ℤ) := by
    rw [← two_pow_add, show (17 : ℤ) + 1000 = 1017 from rfl]
  have hm := Rat.mul_le_mul_of_nonneg_right hkq (Rat.le_of_lt (two_pow_pos 1000))
  have hmax := maxFormat_ge_1017
  have hq : Rat.abs (dot (x.map (fixedValue (shiftOf W x))) (y.map (fixedValue (shiftOf W y)))) ≤
      maxFormat 53 1023 := by
    rw [abs_of_nonneg hF0]; rw [hpp] at hS; grind
  exact Option.isSome_iff_exists.mp (rne64_isSome hq)

/-- **The routine on inputs with the same exponent pattern.** Replace every entry `v` of `A` by `f v`
and of `B` by `g v`, where `f` and `g` keep the exponent pattern and binary64 values and satisfy
`0 ≤ f v ≤ 2 · 2^exp(v)`. Then the constructed words decode to the mapped matrices, the matrix ESC
(hence the width and the slice count) is the same, the run emulates, and every entry is the binary64
rounding of its fixed-point product. Entries below `2^500` keep every result finite. -/
theorem adpPolicy_mapped {cfg : ADPConfig} {pol : ZeroPolicy} {f g : ℚ → ℚ}
    (hfe : ∀ v, expOf (f v) = expOf v) (hge : ∀ v, expOf (g v) = expOf v)
    (hfb : ∀ v, Binary64Value v → Binary64Value (f v))
    (hgb : ∀ v, Binary64Value v → Binary64Value (g v))
    (hf : ∀ v, 0 ≤ f v ∧ f v ≤ 2 * pow2Of v) (hg : ∀ v, 0 ≤ g v ∧ g v ≤ 2 * pow2Of v)
    {A B : List (List (BitVec 64))} {Aq Bq : List (List ℚ)}
    (hA : decodeMatrix64 A = some Aq) (hB : decodeMatrix64 B = some Bq) {e0 : ℤ}
    (he : matrixEscPolicy pol cfg.block Aq (transpose Bq) = some e0)
    (hsq : slicesNeeded (adpWidth e0) * slicesNeeded (adpWidth e0) ≤ cfg.speedRatio)
    (hk : ∀ x ∈ Aq, x.length * (128 * 128) < 2 ^ 31)
    (hrA : ∀ x ∈ Aq, ∀ a ∈ x, Rat.abs a < 2 ^ (500 : ℤ))
    (hrB : ∀ r ∈ Bq, ∀ b ∈ r, Rat.abs b < 2 ^ (500 : ℤ)) :
    ∃ (A' B' : List (List (BitVec 64))) (C' : List (List ℚ)),
      decodeMatrix64 A' = some (Aq.map (·.map f)) ∧ decodeMatrix64 B' = some (Bq.map (·.map g)) ∧
      matrixEscPolicy pol cfg.block (Aq.map (·.map f)) (transpose (Bq.map (·.map g))) = some e0 ∧
      adpPolicy cfg pol A' B' = (.emulated, some C') ∧
      ∀ (i j : ℕ) (x y : List ℚ), Aq[i]? = some x → (transpose Bq)[j]? = some y →
        ∃ row c, C'[i]? = some row ∧ row[j]? = some c ∧
          rne64 (fixedProduct (adpWidth e0) (x.map f) (y.map g)) = some c := by
  have bA := decode_binary64 hA
  have bB := decode_binary64 hB
  obtain ⟨A', hA'⟩ := exists_matrix64 (Aq.map (·.map f)) (by
    intro r hr v hv
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hr
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hv
    exact hfb a (bA x hx a ha))
  obtain ⟨B', hB'⟩ := exists_matrix64 (Bq.map (·.map g)) (by
    intro r hr v hv
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hr
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hv
    exact hgb a (bB x hx a ha))
  have htr := transpose_map_entries g Bq
  have hesc : matrixEscPolicy pol cfg.block (Aq.map (·.map f)) (transpose (Bq.map (·.map g))) =
      some e0 := by
    rw [htr, matrixEscPolicy_map hfe hge]; exact he
  obtain ⟨hs1, hfit, _⟩ := slicesNeeded_spec (adpWidth e0)
  have hent : ∀ x' ∈ Aq.map (·.map f), ∀ y' ∈ (transpose Bq).map (·.map g),
      ∃ c, emulEntry (adpWidth e0) (slicesNeeded (adpWidth e0)) x' y' = some c := by
    intro x' hx' y' hy'
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hx'
    obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hy'
    have hkx : (x.map f).length * (128 * 128) < 2 ^ 31 := by rw [List.length_map]; exact hk x hx
    rw [emulEntry_eq hs1 hfit hkx]
    exact rne64_fixedProduct_isSome _
      (fun a ha => by
        obtain ⟨v, hv, rfl⟩ := List.mem_map.mp ha
        exact mapped_le hf (hrA x hx v hv))
      (fun b hb => by
        obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hb
        obtain ⟨r, hr, hvr⟩ := mem_transpose Bq y hy v hv
        exact mapped_le hg (hrB r hr v hvr)) hkx
  obtain ⟨C', hC'⟩ := mapM_isSome (l := Aq.map (·.map f))
    (f := fun x' => ((transpose Bq).map (·.map g)).mapM fun y' =>
      emulEntry (adpWidth e0) (slicesNeeded (adpWidth e0)) x' y')
    (fun x' hx' => mapM_isSome (fun y' hy' => hent x' hx' y' hy'))
  refine ⟨A', B', C', hA', hB', hesc, ?_, ?_⟩
  · unfold adpPolicy
    rw [hA', hB']
    simp only
    rw [hesc]
    simp only
    rw [if_pos hsq, htr, hC']
  · intro i j x y hx hy
    obtain ⟨hi, hxi⟩ := List.getElem?_eq_some_iff.mp hx
    obtain ⟨hj, hyj⟩ := List.getElem?_eq_some_iff.mp hy
    obtain ⟨hl, hrows⟩ := mapM_some_index _ C' hC'
    have hi' : i < (Aq.map (·.map f)).length := by rw [List.length_map]; exact hi
    have hiC : i < C'.length := by omega
    have hrow := hrows i hi' hiC
    obtain ⟨hl2, hents⟩ := mapM_some_index _ _ hrow
    have hj' : j < ((transpose Bq).map (·.map g)).length := by rw [List.length_map]; exact hj
    have hjC : j < C'[i].length := by omega
    have hc := hents j hj' hjC
    simp only [List.getElem_map] at hc
    rw [hxi, hyj] at hc
    have hkx : (x.map f).length * (128 * 128) < 2 ^ 31 := by
      rw [List.length_map]; rw [← hxi]; exact hk _ (List.getElem_mem hi)
    rw [emulEntry_eq hs1 hfit hkx] at hc
    exact ⟨C'[i], C'[i][j], List.getElem?_eq_getElem hiC, List.getElem?_eq_getElem hjC, hc⟩

/-! ## Necessary: the converse -/

/-- **Necessary, left factor.** Suppose ADP with zero policy `pol` emulates with matrix ESC `e0`
(width `W = adpWidth e0`), and for the entry with row `x = Aq[i]` and column `y = (Bᵀ)[j]` some
product `xₜyₜ ≠ 0` has `xₜ` losing `D ≥ 1` of its 53 bits in fixed point,
`D = exp(x_max) − exp(xₜ) + 53 − W`, with
`(8k + 4) 2^-53 P + 2^-1074 < 2^(exp(xₜ) + exp(yₜ) − 53 + min(D, 53))`, `P` the pattern's product
sum. Then there are binary64 inputs with the same exponent pattern (the entries replaced by
`lossyMap` in `A` and by their powers of two in `B`) on which the run has the same matrix ESC,
emulates, and returns for that entry a value that breaks Grade A. Entries below `2^500` keep the
results finite. -/
theorem adpPolicy_unmasked_fails_left {cfg : ADPConfig} {pol : ZeroPolicy}
    {A B : List (List (BitVec 64))} {Aq Bq : List (List ℚ)}
    (hA : decodeMatrix64 A = some Aq) (hB : decodeMatrix64 B = some Bq) {e0 : ℤ}
    (he : matrixEscPolicy pol cfg.block Aq (transpose Bq) = some e0)
    (hsq : slicesNeeded (adpWidth e0) * slicesNeeded (adpWidth e0) ≤ cfg.speedRatio)
    (hk : ∀ x ∈ Aq, x.length * (128 * 128) < 2 ^ 31)
    (hrA : ∀ x ∈ Aq, ∀ a ∈ x, Rat.abs a < 2 ^ (500 : ℤ))
    (hrB : ∀ r ∈ Bq, ∀ b ∈ r, Rat.abs b < 2 ^ (500 : ℤ))
    {i j t : ℕ} {x y : List ℚ} (hx : Aq[i]? = some x) (hy : (transpose Bq)[j]? = some y)
    {a b : ℚ} (ha : x[t]? = some a) (hb : y[t]? = some b) (ha0 : a ≠ 0) (hb0 : b ≠ 0)
    {ep e D : ℤ} (hep : maxE (expsOf x) = some ep) (he' : exp64 a = e)
    (hDdef : D = ep - e + 53 - (adpWidth e0 : ℤ)) (hD : 1 ≤ D)
    (hcond : (8 * (x.length : ℚ) + 4) * 2 ^ (-53 : ℤ) * patSum (expsOf x) (expsOf y) +
      2 ^ (-1074 : ℤ) < 2 ^ (e + exp64 b - 53 + min D 53)) :
    ∃ (A' B' : List (List (BitVec 64))) (C' : List (List ℚ)) (row : List ℚ) (c : ℚ),
      decodeMatrix64 A' = some (Aq.map (·.map (lossyMap e D))) ∧
      decodeMatrix64 B' = some (Bq.map (·.map pow2Of)) ∧
      matrixEscPolicy pol cfg.block (Aq.map (·.map (lossyMap e D)))
        (transpose (Bq.map (·.map pow2Of))) = some e0 ∧
      adpPolicy cfg pol A' B' = (.emulated, some C') ∧ C'[i]? = some row ∧ row[j]? = some c ∧
      gradeAEntry (x.map (lossyMap e D)) (y.map pow2Of) c = false := by
  obtain ⟨A', B', C', hA', hB', hesc, hrun, hents⟩ := adpPolicy_mapped (f := lossyMap e D)
    (g := pow2Of) (expOf_lossyMap hD) expOf_pow2Of (fun _ hv => binary64_lossyMap hD hv)
    (fun _ hv => binary64_pow2Of hv) (lossyMap_bounds hD) pow2Of_bounds hA hB he hsq hk hrA hrB
  obtain ⟨row, c, hrow, hc, hround⟩ := hents i j x y hx hy
  exact ⟨A', B', C', row, c, hA', hB', hesc, hrun, hrow, hc,
    lossy_left_fails hep ha hb ha0 hb0 he' hDdef hD hcond hround⟩

/-- **Necessary, right factor.** The same with the loss in `yₜ`, `D = exp(y_max) − exp(yₜ) + 53 − W`:
`A`'s entries become their powers of two and `B`'s are replaced by `lossyMap`. -/
theorem adpPolicy_unmasked_fails_right {cfg : ADPConfig} {pol : ZeroPolicy}
    {A B : List (List (BitVec 64))} {Aq Bq : List (List ℚ)}
    (hA : decodeMatrix64 A = some Aq) (hB : decodeMatrix64 B = some Bq) {e0 : ℤ}
    (he : matrixEscPolicy pol cfg.block Aq (transpose Bq) = some e0)
    (hsq : slicesNeeded (adpWidth e0) * slicesNeeded (adpWidth e0) ≤ cfg.speedRatio)
    (hk : ∀ x ∈ Aq, x.length * (128 * 128) < 2 ^ 31)
    (hrA : ∀ x ∈ Aq, ∀ a ∈ x, Rat.abs a < 2 ^ (500 : ℤ))
    (hrB : ∀ r ∈ Bq, ∀ b ∈ r, Rat.abs b < 2 ^ (500 : ℤ))
    {i j t : ℕ} {x y : List ℚ} (hx : Aq[i]? = some x) (hy : (transpose Bq)[j]? = some y)
    {a b : ℚ} (ha : x[t]? = some a) (hb : y[t]? = some b) (ha0 : a ≠ 0) (hb0 : b ≠ 0)
    {eq e D : ℤ} (heq : maxE (expsOf y) = some eq) (he' : exp64 b = e)
    (hDdef : D = eq - e + 53 - (adpWidth e0 : ℤ)) (hD : 1 ≤ D)
    (hcond : (8 * (x.length : ℚ) + 4) * 2 ^ (-53 : ℤ) * patSum (expsOf x) (expsOf y) +
      2 ^ (-1074 : ℤ) < 2 ^ (exp64 a + e - 53 + min D 53)) :
    ∃ (A' B' : List (List (BitVec 64))) (C' : List (List ℚ)) (row : List ℚ) (c : ℚ),
      decodeMatrix64 A' = some (Aq.map (·.map pow2Of)) ∧
      decodeMatrix64 B' = some (Bq.map (·.map (lossyMap e D))) ∧
      matrixEscPolicy pol cfg.block (Aq.map (·.map pow2Of))
        (transpose (Bq.map (·.map (lossyMap e D)))) = some e0 ∧
      adpPolicy cfg pol A' B' = (.emulated, some C') ∧ C'[i]? = some row ∧ row[j]? = some c ∧
      gradeAEntry (x.map pow2Of) (y.map (lossyMap e D)) c = false := by
  obtain ⟨A', B', C', hA', hB', hesc, hrun, hents⟩ := adpPolicy_mapped (f := pow2Of)
    (g := lossyMap e D) expOf_pow2Of (expOf_lossyMap hD) (fun _ hv => binary64_pow2Of hv)
    (fun _ hv => binary64_lossyMap hD hv) pow2Of_bounds (lossyMap_bounds hD) hA hB he hsq hk hrA hrB
  obtain ⟨row, c, hrow, hc, hround⟩ := hents i j x y hx hy
  exact ⟨A', B', C', row, c, hA', hB', hesc, hrun, hrow, hc,
    lossy_right_fails heq ha hb ha0 hb0 he' hDdef hD hcond hround⟩

end Ozaki.TC
