import OzakiTC.ADPZeroPolicyIff

/-! # The gap between the two conditions: why it exists, and how narrow it is

`OzakiTC/ADPZeroPolicyIff.lean` gives, for ADP run with an unsafe zero policy, a sufficient
condition for an entry to meet Grade A (`adpPolicy_entry_gradeA`: the run's ESC covers the entry's
exact ESC, so no factor loses a bit) and a necessary one (`adpPolicy_unmasked_fails_left`: some
factor loses enough bits that inputs with the same exponent pattern break Grade A). This file
explains the gap between them and narrows it.

* **The pattern does not decide the outcome of one input** (`adpPolicy_pow2_gradeA`): whenever
  every factor keeps its leading bit (each nonzero entry lies within `W − 1` binades of its row's
  or column's largest, `KeepsLead`), the input made of the powers of two of the pattern converts
  exactly and meets Grade A. So wherever the necessary condition applies, the same exponent pattern
  admits an input that meets Grade A and one that breaks it (`adpPolicy_pattern_undecided_left`,
  `adpPolicy_pattern_undecided_right`). The right question for a pattern is therefore whether
  *every* input with it meets Grade A.
* **A sharper sufficient condition, from the loss in bits** (`adpPolicy_entry_gradeA_loss`): if
  every nonzero factor of the row loses at most `Dx` bits in fixed point and of the column at most
  `Dy`, its conversion error is at most `2^(Dx − 52)` (resp. `2^(Dy − 52)`) times its magnitude
  (`fixedValue_loss_le`), so the converted product is within `Λ = λx + λy + λx λy` of the exact
  one relative to `Σ|xᵢyᵢ|` (`dot_sub_map_le`), and Grade A holds for every input with the pattern
  (normal or zero entries) whenever `Λ + u (1 + Λ) ≤ (4k + 1) u`. Unlike `adpPolicy_entry_gradeA`
  it allows bits to be lost: roughly `2^(Dx+1) + 2^(Dy+1) ≤ 4k`.
* **A sharper necessary condition, from the worst-case input** (`adpPolicy_unmasked_fails_full_left`,
  `adpPolicy_unmasked_fails_full_right`): the constructed factor now has every dropped bit set
  (`fullLossOf`), losing `2^(e + D − 52) − 2^(e − 52)`, almost a whole fixed-point unit rather than
  half of one, and the product is bounded by `(1 + 2^(D − 52)) P` rather than `2P`: Grade A fails
  for some input with the pattern whenever
  `(4k + 2) (1 + 2^(min(D, 52) − 52)) u P + 2^-1074 < (2^(e + D − 52) − 2^(e − 52)) 2^(exp yₜ)`.

**What remains between them.** For one dominant product (`P = 2^(exp xₜ + exp yₜ)`) losing `D` bits
in one factor, with the other factor exact, the sufficient condition holds for `2^(D+1) + 2 ≲ 4k`
and the necessary one for `2^(D+1) ≳ 4k + 4`: the two now leave about one value of `D` undecided
(for `k = 4`, `D = 3`: `tests/OzakiTCTests/ZeroPolicyGap.lean` checks that both theorems are silent
there, and that the worst-case input still meets Grade A). The slack is the analysis, not the
routine: the sufficient side bounds the loss by a whole unit and adds a full rounding error, the
necessary side drops the other products' contributions; an exact characterization would have to
compute, for each pattern, the largest error over all significands, which depends on how the
losses of different products add up. Losses spread over both factors of a product, and the
subnormal range (the sufficient side needs normal or zero entries), are covered only by these
bounds. -/

open TensorCore

namespace Ozaki.TC

open ADP

/-! ## Powers of two always meet Grade A -/

theorem fixedValue_zero (s : ℤ) : fixedValue s 0 = 0 := by
  unfold fixedValue; simp [floor_zero]

/-- A power of two on the fixed-point grid converts exactly. -/
theorem fixedValue_two_pow {e s : ℤ} (h : 0 ≤ e + s) : fixedValue s ((2 : ℚ) ^ e) = 2 ^ e := by
  obtain ⟨n, hn⟩ : ∃ n : ℕ, (n : ℤ) = e + s := ⟨(e + s).toNat, by omega⟩
  unfold fixedValue
  have ht : (2 : ℚ) ^ e * 2 ^ s = (((2 ^ n : ℕ) : ℤ) : ℚ) := by
    rw [← two_pow_add, Rat.intCast_natCast, ← two_pow_natCast, hn]
  have hfl : ((2 : ℚ) ^ e * 2 ^ s).floor = ((2 ^ n : ℕ) : ℤ) :=
    floor_eq_of (by rw [ht]; exact Rat.le_refl) (by rw [ht]; grind)
  rw [hfl, Rat.intCast_natCast, ← two_pow_natCast, hn, ← two_pow_add,
    show e + s + -s = e by omega]

theorem fixedValue_pow2Of {s : ℤ} {v : ℚ} (h : v ≠ 0 → 0 ≤ exp64 v + s) :
    fixedValue s (pow2Of v) = pow2Of v := by
  unfold pow2Of
  split
  · exact fixedValue_zero s
  · rename_i h0; exact fixedValue_two_pow (h h0)

/-- **Every factor keeps its leading bit**: each nonzero entry lies within `W − 1` binades of the
largest, `exp(x_max) − exp(v) ≤ W − 1`, i.e. it loses at most `52` of its `53` bits. -/
def KeepsLead (W : ℤ) (x : List ℚ) : Prop :=
  ∀ ep, maxE (expsOf x) = some ep → ∀ v ∈ x, v ≠ 0 → ep - exp64 v ≤ W - 1

theorem map_fixedValue_pow2Of {W : ℤ} {x : List ℚ} (h : KeepsLead W x) :
    (x.map pow2Of).map (fixedValue (shiftOf W (x.map pow2Of))) = x.map pow2Of := by
  have hs : shiftOf W (x.map pow2Of) = shiftOf W x := by
    unfold shiftOf; rw [expsOf_map expOf_pow2Of]
  rw [List.map_map, hs]
  apply List.map_congr_left
  intro v hv
  show fixedValue (shiftOf W x) (pow2Of v) = pow2Of v
  apply fixedValue_pow2Of
  intro h0
  unfold shiftOf
  cases hm : maxE (expsOf x) with
  | none => exact absurd (eq_zero_of_maxE_none hm v hv) h0
  | some ep =>
    simp only
    have := h ep hm v hv h0
    omega

/-- The powers of two of the pattern convert exactly, so the fixed-point product is the exact
one. -/
theorem fixedProduct_pow2Of {W : ℤ} {x y : List ℚ} (hx : KeepsLead W x) (hy : KeepsLead W y) :
    fixedProduct W (x.map pow2Of) (y.map pow2Of) = dot (x.map pow2Of) (y.map pow2Of) := by
  unfold fixedProduct
  rw [← dot_fixedValue, map_fixedValue_pow2Of hx, map_fixedValue_pow2Of hy]

theorem pow2Of_gradeA {W : ℤ} {x y : List ℚ} (hx : KeepsLead W x) (hy : KeepsLead W y) {c : ℚ}
    (hc : rne64 (fixedProduct W (x.map pow2Of) (y.map pow2Of)) = some c) :
    gradeAEntry (x.map pow2Of) (y.map pow2Of) c = true := by
  rw [fixedProduct_pow2Of hx hy] at hc
  have hr := rne64_within _ _ hc
  have hnx : ∀ v ∈ x.map pow2Of, 0 ≤ v := fun v hv => by
    obtain ⟨w, _, rfl⟩ := List.mem_map.mp hv; exact (pow2Of_bounds w).1
  have hny : ∀ v ∈ y.map pow2Of, 0 ≤ v := fun v hv => by
    obtain ⟨w, _, rfl⟩ := List.mem_map.mp hv; exact (pow2Of_bounds w).1
  have hsum : ((List.zipWith (· * ·) (x.map pow2Of) (y.map pow2Of)).map Rat.abs).sum =
      dot (x.map pow2Of) (y.map pow2Of) :=
    sum_abs_of_nonneg _ (zipWith_mul_nonneg _ _ hnx hny)
  have hd0 := dot_nonneg _ _ hnx hny
  unfold gradeAEntry
  rw [hsum]
  apply decide_eq_true
  rw [abs_of_nonneg hd0] at hr
  generalize dot (x.map pow2Of) (y.map pow2Of) = S at *
  have hu := two_pow_pos (-53 : ℤ)
  generalize (2 : ℚ) ^ (-53 : ℤ) = u at *
  have hk : (0 : ℚ) ≤ ((x.map pow2Of).length : ℚ) := Rat.natCast_nonneg
  have huS := Rat.mul_nonneg (Rat.le_of_lt hu) hd0
  have h4 : (0 : ℚ) ≤ 4 * ((x.map pow2Of).length : ℚ) * (u * S) := Rat.mul_nonneg (by grind) huS
  grind

/-- **The powers of two of any pattern meet Grade A.** If ADP with zero policy `pol` emulates with
matrix ESC `e0` and the row `x` and column `y` keep their leading bits at width `W = adpWidth e0`,
then on the inputs made of the powers of two of the pattern (same exponent pattern, same ESC, same
path) the entry meets Grade A. Entries below `2^500` keep every result finite. -/
theorem adpPolicy_pow2_gradeA {cfg : ADPConfig} {pol : ZeroPolicy}
    {A B : List (List (BitVec 64))} {Aq Bq : List (List ℚ)}
    (hA : decodeMatrix64 A = some Aq) (hB : decodeMatrix64 B = some Bq) {e0 : ℤ}
    (he : matrixEscPolicy pol cfg.block Aq (transpose Bq) = some e0)
    (hsq : slicesNeeded (adpWidth e0) * slicesNeeded (adpWidth e0) ≤ cfg.speedRatio)
    (hk : ∀ x ∈ Aq, x.length * (128 * 128) < 2 ^ 31)
    (hrA : ∀ x ∈ Aq, ∀ a ∈ x, Rat.abs a < 2 ^ (500 : ℤ))
    (hrB : ∀ r ∈ Bq, ∀ b ∈ r, Rat.abs b < 2 ^ (500 : ℤ))
    {i j : ℕ} {x y : List ℚ} (hx : Aq[i]? = some x) (hy : (transpose Bq)[j]? = some y)
    (hxL : KeepsLead (adpWidth e0 : ℤ) x) (hyL : KeepsLead (adpWidth e0 : ℤ) y) :
    ∃ (A' B' : List (List (BitVec 64))) (C' : List (List ℚ)) (row : List ℚ) (c : ℚ),
      decodeMatrix64 A' = some (Aq.map (·.map pow2Of)) ∧
      decodeMatrix64 B' = some (Bq.map (·.map pow2Of)) ∧
      matrixEscPolicy pol cfg.block (Aq.map (·.map pow2Of))
        (transpose (Bq.map (·.map pow2Of))) = some e0 ∧
      adpPolicy cfg pol A' B' = (.emulated, some C') ∧ C'[i]? = some row ∧ row[j]? = some c ∧
      gradeAEntry (x.map pow2Of) (y.map pow2Of) c = true := by
  obtain ⟨A', B', C', hA', hB', hesc, hrun, hents⟩ := adpPolicy_mapped (f := pow2Of)
    (g := pow2Of) expOf_pow2Of expOf_pow2Of (fun _ hv => binary64_pow2Of hv)
    (fun _ hv => binary64_pow2Of hv) pow2Of_bounds pow2Of_bounds hA hB he hsq hk hrA hrB
  obtain ⟨row, c, hrow, hc, hround⟩ := hents i j x y hx hy
  exact ⟨A', B', C', row, c, hA', hB', hesc, hrun, hrow, hc, pow2Of_gradeA hxL hyL hround⟩

/-! ## Sufficient, from the loss in bits -/

/-- A normal or zero value whose fixed-point conversion drops at most `Dx` bits loses at most
`2^(Dx − 52)` times its magnitude: the loss is below one fixed-point unit
`2^-s ≤ 2^(exp a + Dx − 52)`. -/
theorem fixedValue_loss_le {a : ℚ} {s Dx : ℤ} (hn : Normal64 a)
    (hD : a ≠ 0 → -s ≤ exp64 a + Dx - 52) :
    Rat.abs (a - fixedValue s a) ≤ 2 ^ (Dx - 52) * Rat.abs a := by
  by_cases h0 : a = 0
  · subst h0
    rw [fixedValue_zero, show (0 : ℚ) - 0 = 0 by grind, abs_zero]
    exact Rat.mul_nonneg (Rat.le_of_lt (two_pow_pos _)) (abs_nonneg 0)
  · obtain ⟨f1, f2⟩ := fixed_floor a s
    have hs' := two_pow_pos (-s)
    have hinv : (2 : ℚ) ^ s * 2 ^ (-s) = 1 := by
      rw [← two_pow_add, show s + -s = 0 by omega]; rfl
    have e : a - fixedValue s a = (a * 2 ^ s - ((a * 2 ^ s).floor : ℚ)) * 2 ^ (-s) := by
      unfold fixedValue
      have : a * 2 ^ s * 2 ^ (-s) = a := by rw [Rat.mul_assoc, hinv, Rat.mul_one]
      grind
    generalize a * 2 ^ s - ((a * 2 ^ s).floor : ℚ) = r at e f1 f2
    have hloss : Rat.abs (a - fixedValue s a) ≤ 2 ^ (-s) := by
      rw [e, abs_mul, abs_of_nonneg f1, abs_of_nonneg (Rat.le_of_lt hs')]
      have := Rat.mul_le_mul_of_nonneg_right (Rat.le_of_lt f2) (Rat.le_of_lt hs')
      grind
    have h2 : (2 : ℚ) ^ (-s) ≤ 2 ^ (Dx - 52) * 2 ^ exp64 a := by
      rw [← two_pow_add]; exact two_pow_le (by have := hD h0; omega)
    have h3 := exp64_le_abs h0 hn
    have h4 := Rat.mul_le_mul_of_nonneg_left h3 (Rat.le_of_lt (two_pow_pos (Dx - 52)))
    exact Rat.le_trans hloss (Rat.le_trans h2 h4)

/-- **The converted product's error, from per-factor relative losses**: if every `a ∈ x` changes
by at most `λx |a|` and every `b ∈ y` by at most `λy |b|`, the dot product changes by at most
`(λx + λy + λx λy) Σ|aᵢbᵢ|`. -/
theorem dot_sub_map_le {f g : ℚ → ℚ} {lx ly : ℚ} (hlx : 0 ≤ lx) (hly : 0 ≤ ly) :
    ∀ x y : List ℚ, (∀ a ∈ x, Rat.abs (a - f a) ≤ lx * Rat.abs a) →
      (∀ b ∈ y, Rat.abs (b - g b) ≤ ly * Rat.abs b) →
      Rat.abs (dot x y - dot (x.map f) (y.map g)) ≤
        (lx + ly + lx * ly) * ((List.zipWith (· * ·) x y).map Rat.abs).sum
  | [], _, _, _ => by
    simp only [List.map_nil, dot_nil_left, List.zipWith_nil_left, List.sum_nil]
    rw [show (0 : ℚ) - 0 = 0 by grind, abs_zero]; grind
  | _ :: _, [], _, _ => by
    simp only [List.map_nil, dot_nil_right, List.zipWith_nil_right, List.sum_nil]
    rw [show (0 : ℚ) - 0 = 0 by grind, abs_zero]; grind
  | a :: x, b :: y, hx, hy => by
    have ih := dot_sub_map_le hlx hly x y (fun c hc => hx c (List.mem_cons_of_mem _ hc))
      (fun c hc => hy c (List.mem_cons_of_mem _ hc))
    have ha := hx a List.mem_cons_self
    have hb := hy b List.mem_cons_self
    simp only [List.map_cons, dot_cons, List.zipWith_cons_cons, List.sum_cons]
    have ht := term_error a (f a) b (g b) (lx * Rat.abs a) (ly * Rat.abs b) ha hb
    have hfa : Rat.abs (f a) ≤ Rat.abs a + lx * Rat.abs a := by
      have h1 := abs_sub_le a (a - f a)
      rw [show a - (a - f a) = f a by grind] at h1
      grind
    have hnb : 0 ≤ ly * Rat.abs b := Rat.mul_nonneg hly (abs_nonneg b)
    have m1 := Rat.mul_le_mul_of_nonneg_right hfa hnb
    have e : a * b + dot x y - (f a * g b + dot (x.map f) (y.map g)) =
        (a * b - f a * g b) + (dot x y - dot (x.map f) (y.map g)) := by grind
    rw [e, abs_mul a b]
    refine Rat.le_trans (abs_add_le _ _) ?_
    generalize ((List.zipWith (· * ·) x y).map Rat.abs).sum = T at ih
    grind

/-- The relative loss `Λ = λx + λy + λx λy` of a product whose factors drop at most `Dx` and `Dy`
bits, `λ = 2^(D − 52)`. -/
def lossFactor (Dx Dy : ℤ) : ℚ :=
  2 ^ (Dx - 52) + 2 ^ (Dy - 52) + 2 ^ (Dx - 52) * 2 ^ (Dy - 52)

theorem lossFactor_nonneg (Dx Dy : ℤ) : 0 ≤ lossFactor Dx Dy := by
  unfold lossFactor
  have := two_pow_pos (Dx - 52); have := two_pow_pos (Dy - 52)
  have := Rat.mul_nonneg (Rat.le_of_lt (two_pow_pos (Dx - 52))) (Rat.le_of_lt (two_pow_pos (Dy - 52)))
  grind

/-- **Grade A from the loss in bits.** If every nonzero factor of `x` loses at most `Dx` bits and
of `y` at most `Dy` at width `W`, on normal or zero entries, one binary64 rounding of the
fixed-point product meets Grade A whenever `Λ + u (1 + Λ) ≤ (4k + 1) u`. -/
theorem loss_gradeA {x y : List ℚ} {W Dx Dy : ℤ}
    (hnx : ∀ a ∈ x, Normal64 a) (hny : ∀ b ∈ y, Normal64 b)
    (hDx : ∀ ep, maxE (expsOf x) = some ep → ∀ a ∈ x, a ≠ 0 → ep - exp64 a + 53 - W ≤ Dx)
    (hDy : ∀ eq, maxE (expsOf y) = some eq → ∀ b ∈ y, b ≠ 0 → eq - exp64 b + 53 - W ≤ Dy)
    (hcond : lossFactor Dx Dy + 2 ^ (-53 : ℤ) * (1 + lossFactor Dx Dy) ≤
      (4 * (x.length : ℚ) + 1) * 2 ^ (-53 : ℤ))
    {c : ℚ} (hc : fp64Round (fixedProduct W x y) = some c) :
    gradeAEntry x y c = true := by
  unfold fixedProduct at hc
  rw [← dot_fixedValue] at hc
  have hlx : ∀ a ∈ x, Rat.abs (a - fixedValue (shiftOf W x) a) ≤ 2 ^ (Dx - 52) * Rat.abs a := by
    intro a ha
    apply fixedValue_loss_le (hnx a ha)
    intro h0
    unfold shiftOf
    cases hm : maxE (expsOf x) with
    | none => exact absurd (eq_zero_of_maxE_none hm a ha) h0
    | some ep => simp only; have := hDx ep hm a ha h0; omega
  have hly : ∀ b ∈ y, Rat.abs (b - fixedValue (shiftOf W y) b) ≤ 2 ^ (Dy - 52) * Rat.abs b := by
    intro b hb
    apply fixedValue_loss_le (hny b hb)
    intro h0
    unfold shiftOf
    cases hm : maxE (expsOf y) with
    | none => exact absurd (eq_zero_of_maxE_none hm b hb) h0
    | some eq => simp only; have := hDy eq hm b hb h0; omega
  have hF := dot_sub_map_le (Rat.le_of_lt (two_pow_pos _)) (Rat.le_of_lt (two_pow_pos _)) x y
    hlx hly
  have hr := fp64Round_within _ _ hc
  have hS := abs_dot_le_sum x y
  have hL0 := lossFactor_nonneg Dx Dy
  unfold gradeAEntry
  apply decide_eq_true
  have hFL : (2 ^ (Dx - 52) + 2 ^ (Dy - 52) + 2 ^ (Dx - 52) * 2 ^ (Dy - 52) : ℚ) =
      lossFactor Dx Dy := rfl
  rw [hFL] at hF
  generalize lossFactor Dx Dy = L at *
  generalize dot x y = S at *
  generalize dot (x.map (fixedValue (shiftOf W x))) (y.map (fixedValue (shiftOf W y))) = F at *
  generalize ((List.zipWith (· * ·) x y).map Rat.abs).sum = T at *
  have hu := two_pow_pos (-53 : ℤ)
  generalize (2 : ℚ) ^ (-53 : ℤ) = u at *
  have hT0 : 0 ≤ T := Rat.le_trans (abs_nonneg S) hS
  -- |F| ≤ |S| + |S − F| ≤ T + L T
  have hFabs : Rat.abs F ≤ T + L * T := by
    have h1 := abs_sub_le S (S - F)
    rw [show S - (S - F) = F by grind] at h1
    grind
  have h3 := Rat.mul_le_mul_of_nonneg_left hFabs (Rat.le_of_lt hu)
  have h4 := Rat.mul_le_mul_of_nonneg_right hcond hT0
  have h5 : Rat.abs (c - S) ≤ Rat.abs (c - F) + Rat.abs (F - S) := by
    have := abs_add_le (c - F) (F - S)
    rw [show c - F + (F - S) = c - S by grind] at this
    exact this
  rw [abs_sub_comm F S] at h5
  grind

/-- **Sufficient, from the loss in bits, for the routine.** If ADP with any zero policy emulates
with matrix ESC `e`, and in the entry's row every nonzero factor loses at most `Dx` bits and in its
column at most `Dy` at the width `W = adpWidth e`, the entry meets Grade A whenever
`Λ + u (1 + Λ) ≤ (4k + 1) u`, `Λ = lossFactor Dx Dy`, for every input with that exponent pattern
(normal or zero entries, `k · 2^14 < 2^31`). With no bit lost (`Dx, Dy ≤ 0`) this holds for every
`k ≥ 1`. -/
theorem adpPolicy_entry_gradeA_loss {cfg : ADPConfig} {pol : ZeroPolicy}
    {A B : List (List (BitVec 64))} {C : List (List ℚ)}
    (h : adpPolicy cfg pol A B = (.emulated, some C)) {Aq Bq : List (List ℚ)}
    (hA : decodeMatrix64 A = some Aq) (hB : decodeMatrix64 B = some Bq) {e : ℤ}
    (he : matrixEscPolicy pol cfg.block Aq (transpose Bq) = some e)
    {i j : ℕ} (hi : i < Aq.length) (hj : j < (transpose Bq).length)
    (hnx : ∀ a ∈ Aq[i], Normal64 a) (hny : ∀ b ∈ (transpose Bq)[j], Normal64 b)
    (hk : Aq[i].length * (128 * 128) < 2 ^ 31) {Dx Dy : ℤ}
    (hDx : ∀ ep, maxE (expsOf Aq[i]) = some ep → ∀ a ∈ Aq[i], a ≠ 0 →
      ep - exp64 a + 53 - (adpWidth e : ℤ) ≤ Dx)
    (hDy : ∀ eq, maxE (expsOf (transpose Bq)[j]) = some eq → ∀ b ∈ (transpose Bq)[j], b ≠ 0 →
      eq - exp64 b + 53 - (adpWidth e : ℤ) ≤ Dy)
    (hcond : lossFactor Dx Dy + 2 ^ (-53 : ℤ) * (1 + lossFactor Dx Dy) ≤
      (4 * (Aq[i].length : ℚ) + 1) * 2 ^ (-53 : ℤ)) :
    ∃ (hiC : i < C.length) (hjC : j < C[i].length),
      gradeAEntry Aq[i] (transpose Bq)[j] C[i][j] = true := by
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
    have hent := hents j hj hjC
    rw [emulEntry_eq hs1 hfit hk] at hent
    exact loss_gradeA hnx hny hDx hDy hcond hent
  · simp at h

/-! ## Necessary, from the worst-case input -/

/-- A value with exponent `e` whose conversion, dropping `D` of its 53 bits (`1 ≤ D ≤ 52`), loses
as much as any value with that exponent: every dropped bit set,
`2^e + 2^(e + D − 52) − 2^(e − 52)`. For `D ≥ 53` the power `2^e`, lost entirely. -/
def fullLossOf (e D : ℤ) : ℚ := if D ≤ 52 then 2 ^ e + 2 ^ (e + D - 52) - 2 ^ (e - 52) else 2 ^ e

/-- What `fullLossOf e D` loses: `2^(e + D − 52) − 2^(e − 52)`, or `2^e` when `D ≥ 53`. -/
def fullLossAmt (e D : ℤ) : ℚ := if D ≤ 52 then 2 ^ (e + D - 52) - 2 ^ (e - 52) else 2 ^ e

/-- The bound `fullLossOf e D ≤ β · 2^e`, `β = 1 + 2^(min(D, 52) − 52)`. -/
def fullBeta (D : ℤ) : ℚ := 1 + 2 ^ (min D 52 - 52)

/-- Every nonzero entry with exponent `e` becomes `fullLossOf e D`, every other nonzero entry its
power of two. -/
def fullLossMap (e D : ℤ) (v : ℚ) : ℚ :=
  if v = 0 then 0 else if exp64 v = e then fullLossOf e D else 2 ^ exp64 v

theorem fullLossOf_bounds (e : ℤ) {D : ℤ} (hD : 1 ≤ D) :
    (2 : ℚ) ^ e ≤ fullLossOf e D ∧ fullLossOf e D < 2 ^ (e + 1) ∧
      fullLossOf e D ≤ fullBeta D * 2 ^ e := by
  have he := two_pow_pos e
  have h2 : (2 : ℚ) ^ (e + 1) = 2 ^ e + 2 ^ e := by rw [two_pow_add, two_pow_one]; grind
  unfold fullLossOf fullBeta
  split
  · rename_i hD2
    have hb : (2 : ℚ) ^ (e - 52) < 2 ^ (e + D - 52) := two_pow_lt (by omega)
    have hc : (2 : ℚ) ^ (e + D - 52) ≤ 2 ^ e := two_pow_le (by omega)
    have hl := two_pow_pos (e - 52)
    have hm : (2 : ℚ) ^ (min D 52 - 52) * 2 ^ e = 2 ^ (e + D - 52) := by
      rw [← two_pow_add]; congr 1; omega
    refine ⟨by grind, by grind, ?_⟩
    rw [Rat.add_mul, Rat.one_mul, hm]; grind
  · have hm : (2 : ℚ) ^ (min D 52 - 52) = 1 := by
      rw [show min D 52 - 52 = 0 by omega]; rfl
    refine ⟨Rat.le_refl, by grind, ?_⟩
    rw [hm]; grind

theorem fullBeta_bounds (D : ℤ) : 0 ≤ fullBeta D ∧ fullBeta D ≤ 2 := by
  unfold fullBeta
  have := two_pow_pos (min D 52 - 52)
  have h1 : (2 : ℚ) ^ (min D 52 - 52) ≤ 2 ^ (0 : ℤ) := two_pow_le (by omega)
  have : (2 : ℚ) ^ (0 : ℤ) = 1 := rfl
  constructor <;> grind

theorem exp64_fullLossOf {e D : ℤ} (he : -1022 ≤ e) (hD : 1 ≤ D) : exp64 (fullLossOf e D) = e := by
  obtain ⟨h1, h2, _⟩ := fullLossOf_bounds e hD
  have hpos : 0 ≤ fullLossOf e D := Rat.le_trans (Rat.le_of_lt (two_pow_pos e)) h1
  apply exp64_of_bounds he <;> rw [abs_of_nonneg hpos]
  · exact h1
  · exact h2

theorem fullLossOf_ne_zero (e : ℤ) {D : ℤ} (hD : 1 ≤ D) : fullLossOf e D ≠ 0 := by
  have := (fullLossOf_bounds e hD).1; have := two_pow_pos e; grind

theorem expOf_fullLossMap {e D : ℤ} (hD : 1 ≤ D) (v : ℚ) :
    expOf (fullLossMap e D v) = expOf v := by
  unfold fullLossMap
  by_cases hv : v = 0
  · simp [hv]
  · rw [if_neg hv, expOf_ne hv]
    split
    · rename_i h
      rw [expOf_ne (fullLossOf_ne_zero e hD),
        exp64_fullLossOf (by rw [← h]; exact exp64_ge v) hD, h]
    · rw [expOf_ne (Rat.ne_of_gt (two_pow_pos _)), exp64_two_pow (exp64_ge v)]

theorem binary64_fullLossOf {e D : ℤ} (he1 : -1022 ≤ e) (he2 : e ≤ 1023) (hD : 1 ≤ D) :
    Binary64Value (fullLossOf e D) := by
  unfold fullLossOf
  split
  · rename_i hD2
    obtain ⟨n, hn⟩ : ∃ n : ℕ, (n : ℤ) = D := ⟨D.toNat, by omega⟩
    have h1 : 1 ≤ 2 ^ n := Nat.one_le_two_pow
    have h2 : 2 ^ n ≤ 2 ^ 52 := Nat.pow_le_pow_right (by decide) (by omega)
    refine ⟨((2 ^ 52 + 2 ^ n : ℕ) : ℤ) - 1, e, he1, he2, ?_, ?_⟩
    · have h53 : (2 : ℕ) ^ 53 = 2 ^ 52 + 2 ^ 52 := by decide
      omega
    · have a1 : (2 : ℚ) ^ e = 2 ^ ((52 : ℕ) : ℤ) * 2 ^ (e - ((53 : ℕ) - 1)) := by
        rw [← two_pow_add]; congr 1; omega
      have a2 : (2 : ℚ) ^ (e + D - 52) = 2 ^ (n : ℤ) * 2 ^ (e - ((53 : ℕ) - 1)) := by
        rw [← two_pow_add]; congr 1; omega
      have a3 : (2 : ℚ) ^ (e - 52) = 2 ^ (e - ((53 : ℕ) - 1)) := by congr 1
      rw [a1, a2, a3, Rat.intCast_sub, Rat.intCast_natCast, Rat.natCast_add, two_pow_natCast,
        two_pow_natCast]
      simp only [Rat.intCast_one]
      grind
  · exact binary64Value_two_pow he1 he2

theorem binary64_fullLossMap {e D : ℤ} (hD : 1 ≤ D) {v : ℚ} (hv : Binary64Value v) :
    Binary64Value (fullLossMap e D v) := by
  unfold fullLossMap
  split
  · exact binary64Value_zero
  · rename_i h0
    split
    · rename_i h
      exact binary64_fullLossOf (by rw [← h]; exact exp64_ge v)
        (by rw [← h]; exact exp64_le_1023 hv h0) hD
    · exact binary64Value_two_pow (exp64_ge v) (exp64_le_1023 hv h0)

theorem fullLossMap_bounds {e D : ℤ} (hD : 1 ≤ D) (v : ℚ) :
    0 ≤ fullLossMap e D v ∧ fullLossMap e D v ≤ fullBeta D * pow2Of v := by
  have hb := fullBeta_bounds D
  unfold fullLossMap pow2Of
  split
  · constructor <;> grind
  · split
    · rename_i h0 h
      obtain ⟨h1, _, h3⟩ := fullLossOf_bounds e hD
      rw [h]
      have := two_pow_pos e
      constructor <;> grind
    · have := two_pow_pos (exp64 v)
      have : (1 : ℚ) ≤ fullBeta D := by
        unfold fullBeta; have := two_pow_pos (min D 52 - 52); grind
      have := Rat.mul_le_mul_of_nonneg_right this (Rat.le_of_lt (two_pow_pos (exp64 v)))
      constructor <;> grind

theorem fullLossMap_le_two {e D : ℤ} (hD : 1 ≤ D) (v : ℚ) :
    0 ≤ fullLossMap e D v ∧ fullLossMap e D v ≤ 2 * pow2Of v := by
  obtain ⟨h0, h1⟩ := fullLossMap_bounds (e := e) hD v
  have hb := fullBeta_bounds D
  have hp := (pow2Of_bounds v).1
  have := Rat.mul_le_mul_of_nonneg_right hb.2 hp
  exact ⟨h0, Rat.le_trans h1 this⟩

/-- **The worst-case value loses `fullLossAmt e D`** in a conversion with shift `s`,
`e + s = 52 − D`. -/
theorem fullLossOf_loss {e D s : ℤ} (hD : 1 ≤ D) (hs : e + s = 52 - D) :
    fullLossAmt e D ≤ fullLossOf e D - fixedValue s (fullLossOf e D) := by
  unfold fullLossOf fullLossAmt fixedValue
  split
  · rename_i hD2
    obtain ⟨n, hn⟩ : ∃ n : ℕ, (n : ℤ) = 52 - D := ⟨(52 - D).toNat, by omega⟩
    have a1 : (2 : ℚ) ^ e * 2 ^ s = (((2 ^ n : ℕ) : ℤ) : ℚ) := by
      rw [← two_pow_add, Rat.intCast_natCast, ← two_pow_natCast, hn, hs]
    have a2 : (2 : ℚ) ^ (e + D - 52) * 2 ^ s = 1 := by
      rw [← two_pow_add, show e + D - 52 + s = 0 by omega]; rfl
    have a3 : (2 : ℚ) ^ (e - 52) * 2 ^ s = 2 ^ (-D) := by
      rw [← two_pow_add]; congr 1; omega
    have ht : (2 ^ e + 2 ^ (e + D - 52) - 2 ^ (e - 52)) * (2 : ℚ) ^ s =
        (((2 ^ n : ℕ) : ℤ) : ℚ) + (1 - 2 ^ (-D)) := by
      rw [← a1, ← a3, show (1 : ℚ) = 2 ^ (e + D - 52) * 2 ^ s from a2.symm]; grind
    have hD' := two_pow_pos (-D)
    have hD1 : (2 : ℚ) ^ (-D) ≤ 2 ^ (-1 : ℤ) := two_pow_le (by omega)
    have hhalf : (2 : ℚ) ^ (-1 : ℤ) < 1 := by
      have := two_pow_lt (show (-1 : ℤ) < 0 by decide)
      rwa [show (2 : ℚ) ^ (0 : ℤ) = 1 from rfl] at this
    have hfl : ((2 ^ e + 2 ^ (e + D - 52) - 2 ^ (e - 52)) * (2 : ℚ) ^ s).floor =
        ((2 ^ n : ℕ) : ℤ) := by
      apply floor_eq_of
      · rw [ht]; grind
      · rw [ht]; grind
    rw [hfl, Rat.intCast_natCast, ← two_pow_natCast, hn, ← two_pow_add,
      show 52 - D + -s = e by omega]
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
    rw [hfl, Rat.intCast_zero, Rat.zero_mul]
    grind

/-- **The failure, abstractly, with the product bounded by `β P`**: nonnegative entries; the
conversion loses at least `L`; `dot ≤ β P`; and `(4k + 2) β u P + 2^-1074 < L`. -/
theorem gradeA_fails_core_beta {x y : List ℚ} {sx sy : ℤ} {P L β c : ℚ}
    (hx : ∀ a ∈ x, 0 ≤ a) (hy : ∀ b ∈ y, 0 ≤ b)
    (hgap : L ≤ dot x y - dot (x.map (fixedValue sx)) (y.map (fixedValue sy)))
    (hS : dot x y ≤ β * P)
    (hcond : (4 * (x.length : ℚ) + 2) * β * 2 ^ (-53 : ℤ) * P + 2 ^ (-1074 : ℤ) < L)
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
  have m2 : (4 * (x.length : ℚ) + 2) * u * S ≤ (4 * (x.length : ℚ) + 2) * u * (β * P) :=
    Rat.mul_le_mul_of_nonneg_left hS hc4
  grind

/-- **Left factor, worst case.** If `xₜ` loses `D ≥ 1` bits and
`(4k + 2) β u P + 2^-1074 < fullLossAmt(exp xₜ, D) 2^(exp yₜ)`, then replacing the entries by
`fullLossMap` (left) and their powers of two (right) breaks Grade A. -/
theorem full_left_fails {x y : List ℚ} {W ep e D : ℤ} (hep : maxE (expsOf x) = some ep) {t : ℕ}
    {a b : ℚ} (ha : x[t]? = some a) (hb : y[t]? = some b) (ha0 : a ≠ 0) (hb0 : b ≠ 0)
    (he : exp64 a = e) (hDdef : D = ep - e + 53 - W) (hD : 1 ≤ D)
    (hcond : (4 * (x.length : ℚ) + 2) * fullBeta D * 2 ^ (-53 : ℤ) *
      patSum (expsOf x) (expsOf y) + 2 ^ (-1074 : ℤ) < fullLossAmt e D * 2 ^ exp64 b)
    {c : ℚ} (hc : rne64 (fixedProduct W (x.map (fullLossMap e D)) (y.map pow2Of)) = some c) :
    gradeAEntry (x.map (fullLossMap e D)) (y.map pow2Of) c = false := by
  have hx' : expsOf (x.map (fullLossMap e D)) = expsOf x := expsOf_map (expOf_fullLossMap hD) x
  have hsx : shiftOf W (x.map (fullLossMap e D)) = W - 1 - ep := by
    unfold shiftOf; rw [hx', hep]
  unfold fixedProduct at hc
  rw [← dot_fixedValue] at hc
  have hnx : ∀ v ∈ x.map (fullLossMap e D), 0 ≤ v := fun v hv => by
    obtain ⟨w, _, rfl⟩ := List.mem_map.mp hv; exact (fullLossMap_bounds hD w).1
  have hny : ∀ v ∈ y.map pow2Of, 0 ≤ v := fun v hv => by
    obtain ⟨w, _, rfl⟩ := List.mem_map.mp hv; exact (pow2Of_bounds w).1
  refine gradeA_fails_core_beta (sx := shiftOf W (x.map (fullLossMap e D)))
    (sy := shiftOf W (y.map pow2Of)) hnx hny ?_ ?_
    (by rw [List.length_map]; exact hcond) hc
  · obtain ⟨hti, hxa⟩ := List.getElem?_eq_some_iff.mp ha
    obtain ⟨htj, hyb⟩ := List.getElem?_eq_some_iff.mp hb
    have hmem : (fullLossMap e D a, pow2Of b) ∈
        List.zip (x.map (fullLossMap e D)) (y.map pow2Of) := by
      rw [← hxa, ← hyb]
      have h1 : t < (List.zip (x.map (fullLossMap e D)) (y.map pow2Of)).length := by
        simp; omega
      have := List.getElem_mem h1
      simpa [List.getElem_zip] using this
    obtain ⟨h1, _⟩ := (dot_sub_fixed_ge (shiftOf W (x.map (fullLossMap e D)))
      (shiftOf W (y.map pow2Of)) _ _ hnx hny).2 _ hmem
    simp only at h1
    have hla : fullLossMap e D a = fullLossOf e D := by
      unfold fullLossMap; rw [if_neg ha0, if_pos he]
    have hpb : pow2Of b = 2 ^ exp64 b := by unfold pow2Of; rw [if_neg hb0]
    rw [hla, hpb] at h1
    have hloss := fullLossOf_loss (e := e) (D := D) (s := shiftOf W (x.map (fullLossMap e D))) hD
      (by rw [hsx]; omega)
    have hm := Rat.mul_le_mul_of_nonneg_right hloss (Rat.le_of_lt (two_pow_pos (exp64 b)))
    exact Rat.le_trans hm h1
  · have := dot_le_patSum (f := fullLossMap e D) (g := pow2Of) (cf := fullBeta D) (cg := 1)
      (fullBeta_bounds D).1 (fun v => fullLossMap_bounds hD v)
      (fun w => ⟨(pow2Of_bounds w).1, by grind⟩) x y
    grind

/-- **Right factor, worst case.** -/
theorem full_right_fails {x y : List ℚ} {W eq e D : ℤ} (heq : maxE (expsOf y) = some eq) {t : ℕ}
    {a b : ℚ} (ha : x[t]? = some a) (hb : y[t]? = some b) (ha0 : a ≠ 0) (hb0 : b ≠ 0)
    (he : exp64 b = e) (hDdef : D = eq - e + 53 - W) (hD : 1 ≤ D)
    (hcond : (4 * (x.length : ℚ) + 2) * fullBeta D * 2 ^ (-53 : ℤ) *
      patSum (expsOf x) (expsOf y) + 2 ^ (-1074 : ℤ) < 2 ^ exp64 a * fullLossAmt e D)
    {c : ℚ} (hc : rne64 (fixedProduct W (x.map pow2Of) (y.map (fullLossMap e D))) = some c) :
    gradeAEntry (x.map pow2Of) (y.map (fullLossMap e D)) c = false := by
  have hy' : expsOf (y.map (fullLossMap e D)) = expsOf y := expsOf_map (expOf_fullLossMap hD) y
  have hsy : shiftOf W (y.map (fullLossMap e D)) = W - 1 - eq := by
    unfold shiftOf; rw [hy', heq]
  unfold fixedProduct at hc
  rw [← dot_fixedValue] at hc
  have hnx : ∀ v ∈ x.map pow2Of, 0 ≤ v := fun v hv => by
    obtain ⟨w, _, rfl⟩ := List.mem_map.mp hv; exact (pow2Of_bounds w).1
  have hny : ∀ v ∈ y.map (fullLossMap e D), 0 ≤ v := fun v hv => by
    obtain ⟨w, _, rfl⟩ := List.mem_map.mp hv; exact (fullLossMap_bounds hD w).1
  refine gradeA_fails_core_beta (sx := shiftOf W (x.map pow2Of))
    (sy := shiftOf W (y.map (fullLossMap e D))) hnx hny ?_ ?_
    (by rw [List.length_map]; exact hcond) hc
  · obtain ⟨hti, hxa⟩ := List.getElem?_eq_some_iff.mp ha
    obtain ⟨htj, hyb⟩ := List.getElem?_eq_some_iff.mp hb
    have hmem : (pow2Of a, fullLossMap e D b) ∈
        List.zip (x.map pow2Of) (y.map (fullLossMap e D)) := by
      rw [← hxa, ← hyb]
      have h1 : t < (List.zip (x.map pow2Of) (y.map (fullLossMap e D))).length := by
        simp; omega
      have := List.getElem_mem h1
      simpa [List.getElem_zip] using this
    obtain ⟨_, h2⟩ := (dot_sub_fixed_ge (shiftOf W (x.map pow2Of))
      (shiftOf W (y.map (fullLossMap e D))) _ _ hnx hny).2 _ hmem
    simp only at h2
    have hlb : fullLossMap e D b = fullLossOf e D := by
      unfold fullLossMap; rw [if_neg hb0, if_pos he]
    have hpa : pow2Of a = 2 ^ exp64 a := by unfold pow2Of; rw [if_neg ha0]
    rw [hlb, hpa] at h2
    have hloss := fullLossOf_loss (e := e) (D := D) (s := shiftOf W (y.map (fullLossMap e D))) hD
      (by rw [hsy]; omega)
    have hm := Rat.mul_le_mul_of_nonneg_left hloss (Rat.le_of_lt (two_pow_pos (exp64 a)))
    exact Rat.le_trans hm h2
  · have := dot_le_patSum (f := pow2Of) (g := fullLossMap e D) (cf := 1) (cg := fullBeta D)
      (by decide) (fun v => ⟨(pow2Of_bounds v).1, by grind⟩)
      (fun w => fullLossMap_bounds hD w) x y
    grind

/-- **Necessary, left factor, worst case.** `adpPolicy_unmasked_fails_left` with the worst-case
input: the condition becomes
`(4k + 2) β u P + 2^-1074 < (2^(e + D − 52) − 2^(e − 52)) 2^(exp yₜ)`, `β = fullBeta D`. -/
theorem adpPolicy_unmasked_fails_full_left {cfg : ADPConfig} {pol : ZeroPolicy}
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
    (hcond : (4 * (x.length : ℚ) + 2) * fullBeta D * 2 ^ (-53 : ℤ) *
      patSum (expsOf x) (expsOf y) + 2 ^ (-1074 : ℤ) < fullLossAmt e D * 2 ^ exp64 b) :
    ∃ (A' B' : List (List (BitVec 64))) (C' : List (List ℚ)) (row : List ℚ) (c : ℚ),
      decodeMatrix64 A' = some (Aq.map (·.map (fullLossMap e D))) ∧
      decodeMatrix64 B' = some (Bq.map (·.map pow2Of)) ∧
      matrixEscPolicy pol cfg.block (Aq.map (·.map (fullLossMap e D)))
        (transpose (Bq.map (·.map pow2Of))) = some e0 ∧
      adpPolicy cfg pol A' B' = (.emulated, some C') ∧ C'[i]? = some row ∧ row[j]? = some c ∧
      gradeAEntry (x.map (fullLossMap e D)) (y.map pow2Of) c = false := by
  obtain ⟨A', B', C', hA', hB', hesc, hrun, hents⟩ := adpPolicy_mapped (f := fullLossMap e D)
    (g := pow2Of) (expOf_fullLossMap hD) expOf_pow2Of (fun _ hv => binary64_fullLossMap hD hv)
    (fun _ hv => binary64_pow2Of hv) (fullLossMap_le_two hD) pow2Of_bounds hA hB he hsq hk
    hrA hrB
  obtain ⟨row, c, hrow, hc, hround⟩ := hents i j x y hx hy
  exact ⟨A', B', C', row, c, hA', hB', hesc, hrun, hrow, hc,
    full_left_fails hep ha hb ha0 hb0 he' hDdef hD hcond hround⟩

/-- **Necessary, right factor, worst case.** -/
theorem adpPolicy_unmasked_fails_full_right {cfg : ADPConfig} {pol : ZeroPolicy}
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
    (hcond : (4 * (x.length : ℚ) + 2) * fullBeta D * 2 ^ (-53 : ℤ) *
      patSum (expsOf x) (expsOf y) + 2 ^ (-1074 : ℤ) < 2 ^ exp64 a * fullLossAmt e D) :
    ∃ (A' B' : List (List (BitVec 64))) (C' : List (List ℚ)) (row : List ℚ) (c : ℚ),
      decodeMatrix64 A' = some (Aq.map (·.map pow2Of)) ∧
      decodeMatrix64 B' = some (Bq.map (·.map (fullLossMap e D))) ∧
      matrixEscPolicy pol cfg.block (Aq.map (·.map pow2Of))
        (transpose (Bq.map (·.map (fullLossMap e D)))) = some e0 ∧
      adpPolicy cfg pol A' B' = (.emulated, some C') ∧ C'[i]? = some row ∧ row[j]? = some c ∧
      gradeAEntry (x.map pow2Of) (y.map (fullLossMap e D)) c = false := by
  obtain ⟨A', B', C', hA', hB', hesc, hrun, hents⟩ := adpPolicy_mapped (f := pow2Of)
    (g := fullLossMap e D) expOf_pow2Of (expOf_fullLossMap hD) (fun _ hv => binary64_pow2Of hv)
    (fun _ hv => binary64_fullLossMap hD hv) pow2Of_bounds (fullLossMap_le_two hD) hA hB he hsq
    hk hrA hrB
  obtain ⟨row, c, hrow, hc, hround⟩ := hents i j x y hx hy
  exact ⟨A', B', C', row, c, hA', hB', hesc, hrun, hrow, hc,
    full_right_fails heq ha hb ha0 hb0 he' hDdef hD hcond hround⟩

/-! ## The pattern alone does not decide -/

/-- **Both outcomes, left factor.** Under the hypotheses of `adpPolicy_unmasked_fails_full_left`,
with every factor of the row and column keeping its leading bit, the same exponent pattern (same
matrix ESC, width and slice count, the run emulating) admits an input on which the entry meets
Grade A (its powers of two) and one on which it breaks Grade A. -/
theorem adpPolicy_pattern_undecided_left {cfg : ADPConfig} {pol : ZeroPolicy}
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
    (hcond : (4 * (x.length : ℚ) + 2) * fullBeta D * 2 ^ (-53 : ℤ) *
      patSum (expsOf x) (expsOf y) + 2 ^ (-1074 : ℤ) < fullLossAmt e D * 2 ^ exp64 b)
    (hxL : KeepsLead (adpWidth e0 : ℤ) x) (hyL : KeepsLead (adpWidth e0 : ℤ) y) :
    (∃ (A' B' : List (List (BitVec 64))) (C' : List (List ℚ)) (row : List ℚ) (c : ℚ),
      decodeMatrix64 A' = some (Aq.map (·.map pow2Of)) ∧
      decodeMatrix64 B' = some (Bq.map (·.map pow2Of)) ∧
      matrixEscPolicy pol cfg.block (Aq.map (·.map pow2Of))
        (transpose (Bq.map (·.map pow2Of))) = some e0 ∧
      adpPolicy cfg pol A' B' = (.emulated, some C') ∧ C'[i]? = some row ∧ row[j]? = some c ∧
      gradeAEntry (x.map pow2Of) (y.map pow2Of) c = true) ∧
    (∃ (A' B' : List (List (BitVec 64))) (C' : List (List ℚ)) (row : List ℚ) (c : ℚ),
      decodeMatrix64 A' = some (Aq.map (·.map (fullLossMap e D))) ∧
      decodeMatrix64 B' = some (Bq.map (·.map pow2Of)) ∧
      matrixEscPolicy pol cfg.block (Aq.map (·.map (fullLossMap e D)))
        (transpose (Bq.map (·.map pow2Of))) = some e0 ∧
      adpPolicy cfg pol A' B' = (.emulated, some C') ∧ C'[i]? = some row ∧ row[j]? = some c ∧
      gradeAEntry (x.map (fullLossMap e D)) (y.map pow2Of) c = false) :=
  ⟨adpPolicy_pow2_gradeA hA hB he hsq hk hrA hrB hx hy hxL hyL,
    adpPolicy_unmasked_fails_full_left hA hB he hsq hk hrA hrB hx hy ha hb ha0 hb0 hep he' hDdef
      hD hcond⟩

/-- **Both outcomes, right factor.** -/
theorem adpPolicy_pattern_undecided_right {cfg : ADPConfig} {pol : ZeroPolicy}
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
    (hcond : (4 * (x.length : ℚ) + 2) * fullBeta D * 2 ^ (-53 : ℤ) *
      patSum (expsOf x) (expsOf y) + 2 ^ (-1074 : ℤ) < 2 ^ exp64 a * fullLossAmt e D)
    (hxL : KeepsLead (adpWidth e0 : ℤ) x) (hyL : KeepsLead (adpWidth e0 : ℤ) y) :
    (∃ (A' B' : List (List (BitVec 64))) (C' : List (List ℚ)) (row : List ℚ) (c : ℚ),
      decodeMatrix64 A' = some (Aq.map (·.map pow2Of)) ∧
      decodeMatrix64 B' = some (Bq.map (·.map pow2Of)) ∧
      matrixEscPolicy pol cfg.block (Aq.map (·.map pow2Of))
        (transpose (Bq.map (·.map pow2Of))) = some e0 ∧
      adpPolicy cfg pol A' B' = (.emulated, some C') ∧ C'[i]? = some row ∧ row[j]? = some c ∧
      gradeAEntry (x.map pow2Of) (y.map pow2Of) c = true) ∧
    (∃ (A' B' : List (List (BitVec 64))) (C' : List (List ℚ)) (row : List ℚ) (c : ℚ),
      decodeMatrix64 A' = some (Aq.map (·.map pow2Of)) ∧
      decodeMatrix64 B' = some (Bq.map (·.map (fullLossMap e D))) ∧
      matrixEscPolicy pol cfg.block (Aq.map (·.map pow2Of))
        (transpose (Bq.map (·.map (fullLossMap e D)))) = some e0 ∧
      adpPolicy cfg pol A' B' = (.emulated, some C') ∧ C'[i]? = some row ∧ row[j]? = some c ∧
      gradeAEntry (x.map pow2Of) (y.map (fullLossMap e D)) c = false) :=
  ⟨adpPolicy_pow2_gradeA hA hB he hsq hk hrA hrB hx hy hxL hyL,
    adpPolicy_unmasked_fails_full_right hA hB he hsq hk hrA hrB hx hy ha hb ha0 hb0 heq he' hDdef
      hD hcond⟩

end Ozaki.TC
