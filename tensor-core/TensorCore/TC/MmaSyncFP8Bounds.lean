import TensorCore.TC.MmaSyncFP8
import TensorCore.TC.ErrorBounds
import TensorCore.TC.StageResiduals
import TensorCore.Numerics.Rounding

/-! # The error of an FP8 `mma.sync`

Against the exact `c + Σ a_k b_k`: the errors of the two FP16 block FMAs and of the final FP32
addition add up. -/

namespace TensorCore

/-- The value of an FP16 word; `0` for an infinity or NaN. -/
def value16 (w : F16) : ℚ := ((decode16 w).map Decoded.value).getD 0

/-- The exact `c + Σ a_k b_k` of an FP8 `mma.sync`, on the operands' FP16 conversions. -/
def mmaSyncFP8Exact (conv : BitVec 8 → F16) (c : F32) (ps : List (BitVec 8 × BitVec 8)) : ℚ :=
  (value32 c).getD 0 + sumQ (ps.map fun (a, b) => value16 (conv a) * value16 (conv b))

/-! ## The two groups partition the products -/

theorem sumQ_filter_split (l : List α) (g : α → ℚ) (p : α → Bool) :
    sumQ (l.map g) = sumQ ((l.filter p).map g) + sumQ ((l.filter fun x => !p x).map g) := by
  induction l with
  | nil => simp only [List.filter_nil, List.map_nil, sumQ]; exact (Rat.add_zero 0).symm
  | cons x xs ih =>
    cases hp : p x <;> simp [hp, sumQ, ih] <;> grind

theorem sumQ_groups (xs : List α) (g : α → ℚ) :
    sumQ (xs.map g) = sumQ ((groupA xs).map g) + sumQ ((groupB xs).map g) := by
  have h := sumQ_filter_split xs.zipIdx (fun x => g x.1) (fun x => decide (x.2 % 4 < 2))
  have hB : (xs.zipIdx.filter fun x => !decide (x.2 % 4 < 2)) =
      xs.zipIdx.filter fun x => decide (2 ≤ x.2 % 4) := by
    apply List.filter_congr; intro x _
    by_cases hx : x.2 % 4 < 2 <;> simp [hx] <;> omega
  rw [hB] at h
  unfold groupA groupB
  rw [List.map_map, List.map_map]
  have hx : xs.map g = xs.zipIdx.map fun x => g x.1 := by
    conv => lhs; rw [← List.zipIdx_map_fst 0 xs]
    rw [List.map_map]; rfl
  rw [hx]
  exact h

/-! ## A block's exact sum -/

theorem value16_zero : value16 0 = 0 := by decide +kernel

theorem mapM_some_cons {f : α → Option β} {x : α} {xs : List α} {ys : List β}
    (h : (x :: xs).mapM f = some ys) :
    ∃ y ys', f x = some y ∧ xs.mapM f = some ys' ∧ ys = y :: ys' := by
  rw [List.mapM_cons] at h
  cases hx : f x <;> simp [hx] at h
  cases hxs : xs.mapM f <;> simp [hxs] at h
  exact ⟨_, _, rfl, rfl, h.symm⟩

theorem prepareProducts_value : ∀ {ps : List (F16 × F16)} {ds : List (Decoded × Decoded)},
    prepareProducts hopperF16F32 ps = some ds →
      sumQ (ds.map fun (a, b) => a.value * b.value) =
        sumQ (ps.map fun (a, b) => value16 a * value16 b)
  | [], ds, h => by simp [prepareProducts] at h; subst h; rfl
  | (a, b) :: rest, ds, h => by
    obtain ⟨⟨x, y⟩, ds', hf, hr, rfl⟩ := mapM_some_cons h
    have ih := prepareProducts_value (ps := rest) hr
    have hxy : decode16 a = some x ∧ decode16 b = some y := by
      change (do return (← hopperF16F32.decode a, ← hopperF16F32.decode b)) = some (x, y) at hf
      cases ha : hopperF16F32.decode a <;> cases hb : hopperF16F32.decode b <;> simp [ha, hb] at hf
      exact ⟨by rw [← hf.1]; exact ha, by rw [← hf.2]; exact hb⟩
    simp only [List.map_cons, sumQ]
    rw [ih]
    congr 1
    simp [value16, hxy.1, hxy.2]

theorem sumQ_append_eq (xs ys : List ℚ) : sumQ (xs ++ ys) = sumQ xs + sumQ ys := by
  induction xs with
  | nil => simp only [List.nil_append, sumQ]; exact (Rat.zero_add _).symm
  | cons x xs ih => simp only [List.cons_append, sumQ, ih]; grind

theorem sumQ_padTo (n : ℕ) (ps : List (F16 × F16)) :
    sumQ ((padTo n ps).map fun (a, b) => value16 a * value16 b) =
      sumQ (ps.map fun (a, b) => value16 a * value16 b) := by
  unfold padTo
  rw [List.map_append, sumQ_append_eq]
  have : sumQ ((List.replicate (n - ps.length) ((0 : F16), (0 : F16))).map
      fun (a, b) => value16 a * value16 b) = 0 := by
    generalize n - ps.length = k
    induction k with
    | zero => rfl
    | succ k ih =>
      simp only [List.replicate_succ, List.map_cons, sumQ, ih, value16_zero]
      grind
  rw [this]; grind

theorem hopper_block_exact {g : List (F16 × F16)} {c0 : F32} {t : BlockTrace}
    (h : evalBlock (p := hopperF16F32) ⟨padTo 16 g, c0⟩ = .ok t) :
    t.block.exactDot = (value32 c0).getD 0 + sumQ (g.map fun (a, b) => value16 a * value16 b) := by
  have hp := evalBlock_prepared h
  unfold prepare at hp
  cases hc : decode32 c0 <;> cases hs : prepareProducts hopperF16F32 (padTo 16 g) <;>
    simp [hc, hs] at hp
  rename_i cd ds
  rw [← hp]
  unfold PreparedBlock.exactDot PreparedBlock.exactProducts
  rw [prepareProducts_value hs, sumQ_padTo]
  simp [value32, hc]

/-! ## The error bound -/

theorem value32_outputBits (t : BlockTrace) : value32 t.output.bits = some t.output.value := by
  simp [value32, t.output.valid, Finite32.value]

/-- FP32 rounding to nearest is within half a unit in the last place of its result. -/
theorem round32_nearestEven_error {x : ℚ} {b : F32} (h : round32 .nearestEven x = some b) :
    ∃ v, value32 b = some v ∧ absQ (x - v) ≤ pow2 (outputUlpExponent b - 1) := by
  by_cases hx : x = 0
  · subst hx
    have : b = 0 := by
      have h0 : round32 .nearestEven 0 = some 0 := by decide +kernel
      rw [h0] at h; exact (Option.some.inj h).symm
    subst this
    exact ⟨0, by decide +kernel, by
      rw [show (0 : ℚ) - 0 = 0 by grind]
      simp [absQ, Rat.le_of_lt (pow2_pos _)]⟩
  · obtain ⟨b', hb', hv, _, hulp⟩ := round32_nonzero_spec .nearestEven x hx (round32_range h)
    rw [h] at hb'
    cases Option.some.inj hb'
    refine ⟨_, hv, ?_⟩
    have hq := pow2_pos (normExp (absQ x) - 23)
    have hd := rneInt_dist_le_half (absQ x / pow2 (normExp (absQ x) - 23))
    have hm : absQ x - magnitudeRounded .nearestEven (absQ x) =
        (absQ x / pow2 (normExp (absQ x) - 23) -
          rneInt (absQ x / pow2 (normExp (absQ x) - 23))) * pow2 (normExp (absQ x) - 23) := by
      unfold magnitudeRounded roundedSignificand roundSignificand
      have : absQ x = absQ x / pow2 (normExp (absQ x) - 23) * pow2 (normExp (absQ x) - 23) :=
        (Rat.div_mul_cancel (Rat.ne_of_gt (pow2_pos _))).symm
      grind
    have he : absQ (x - signedRounded .nearestEven x) =
        absQ (absQ x - magnitudeRounded .nearestEven (absQ x)) := by
      unfold signedRounded
      generalize magnitudeRounded .nearestEven (absQ x) = M
      by_cases hn : x < 0
      · rw [if_pos hn, absQ_of_neg hn, show x - -M = -(-x - M) by grind, absQ_neg]
      · rw [if_neg hn, absQ_of_nonneg (x := x) (by grind)]
    rw [he, hm, absQ_mul_pos _ _ hq]
    have hq2 : pow2 (normExp (absQ x) - 23) = pow2 (normExp (absQ x) - 24) * 2 := by
      rw [← pow2_succ]; congr 1; omega
    have : absQ (absQ x / pow2 (normExp (absQ x) - 23) -
        rneInt (absQ x / pow2 (normExp (absQ x) - 23))) * pow2 (normExp (absQ x) - 23) ≤
        pow2 (normExp (absQ x) - 24) := by
      have := Rat.mul_le_mul_of_nonneg_right hd (Rat.le_of_lt hq)
      rw [hq2] at this ⊢
      grind
    exact Rat.le_trans this (pow2_le_of_le (by omega))

/-- The output of an FP8 `mma.sync` is within the two blocks' error bounds and half a unit in its
last place of the exact `c + Σ a_k b_k`. -/
theorem mmaSyncFP8_error {conv : BitVec 8 → F16} {c o : F32} {ps : List (BitVec 8 × BitVec 8)}
    (h : mmaSyncFP8 conv c ps = some o) :
    ∃ t₁ t₂ v,
      evalBlock (p := hopperF16F32) ⟨padTo 16 (groupA (ps.map fun (a, b) => (conv a, conv b))), 0⟩ =
        .ok t₁ ∧
      evalBlock (p := hopperF16F32)
        ⟨padTo 16 (groupB (ps.map fun (a, b) => (conv a, conv b))), t₁.output.bits⟩ = .ok t₂ ∧
      value32 o = some v ∧
      absQ (mmaSyncFP8Exact conv c ps - v) <
        ((t₁.block.terms.length : ℚ) * pow2 t₁.block.alignGridExponent +
          pow2 (outputUlpExponent t₁.output.bits)) +
        ((t₂.block.terms.length : ℚ) * pow2 t₂.block.alignGridExponent +
          pow2 (outputUlpExponent t₂.output.bits)) +
        pow2 (outputUlpExponent o - 1) := by
  generalize hq : ps.map (fun (a, b) => (conv a, conv b)) = qs
  unfold mmaSyncFP8 hmma at h
  dsimp only at h
  rw [hq] at h
  cases h₁ : evalBlock (p := hopperF16F32) ⟨padTo 16 (groupA qs), 0⟩ with
  | error e => rw [h₁] at h; simp [Except.toOption] at h
  | ok t₁ =>
    rw [h₁] at h
    simp only [Except.toOption, Option.map_some, Option.bind_eq_bind, Option.bind_some] at h
    cases h₂ : evalBlock (p := hopperF16F32) ⟨padTo 16 (groupB qs), t₁.output.bits⟩ with
    | error e => rw [h₂] at h; simp at h
    | ok t₂ =>
      rw [h₂] at h
      simp only [Option.map_some, Option.bind_some] at h
      simp only [addFp32, value32_outputBits, Option.bind_eq_bind, Option.bind_some] at h
      cases hc : value32 c with
      | none => simp [hc] at h
      | some vc =>
        simp only [hc, Option.bind_some] at h
        obtain ⟨v, hv, hfin⟩ := round32_nearestEven_error h
        refine ⟨t₁, t₂, v, by first | rfl | exact h₁, by first | rfl | exact h₂, hv, ?_⟩
        have e₁ := evalBlock_error_bound h₁ (by decide)
        have e₂ := evalBlock_error_bound h₂ (by decide)
        have x₁ := hopper_block_exact h₁
        have x₂ := hopper_block_exact h₂
        rw [show value32 (0 : F32) = some 0 by decide +kernel, Option.getD_some] at x₁
        rw [value32_outputBits, Option.getD_some] at x₂
        have hs : mmaSyncFP8Exact conv c ps = vc + sumQ ((groupA qs).map fun (a, b) => value16 a * value16 b) +
            sumQ ((groupB qs).map fun (a, b) => value16 a * value16 b) := by
          unfold mmaSyncFP8Exact
          rw [hc, Option.getD_some, ← hq]
          have := sumQ_groups (ps.map fun (a, b) => (conv a, conv b)) (fun (a, b) => value16 a * value16 b)
          rw [List.map_map] at this
          rw [show (fun (x : BitVec 8 × BitVec 8) => value16 (conv x.1) * value16 (conv x.2)) =
            (fun (x : F16 × F16) => value16 x.1 * value16 x.2) ∘ (fun (a, b) => (conv a, conv b)) from rfl,
            this]
          grind
        rw [hs]
        have t1 := absQ_add_le (t₁.block.exactDot - t₁.output.value)
          ((t₂.block.exactDot - t₂.output.value) + (t₂.output.value + vc - v))
        have t2 := absQ_add_le (t₂.block.exactDot - t₂.output.value) (t₂.output.value + vc - v)
        have heq : vc + sumQ ((groupA qs).map fun (a, b) => value16 a * value16 b) +
            sumQ ((groupB qs).map fun (a, b) => value16 a * value16 b) - v =
            (t₁.block.exactDot - t₁.output.value) +
              ((t₂.block.exactDot - t₂.output.value) + (t₂.output.value + vc - v)) := by
          rw [x₁, x₂]; grind
        rw [heq]
        grind

end TensorCore
