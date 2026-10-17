import MatrixCore.MC.LossCondition

/-! # Correct rounding when nothing is lost before the final rounding

CDNA 1 rounds the exact `Σ p_ℓ + c` once (`correctRounding_nearestEven`). CDNA 3 and CDNA 2
discard bits before the final RNE, but on inputs where these steps happen to be exact they too
round the exact sum once.

* CDNA 3 (Algorithms 1 and 2). Every product lies on the alignment grid
  `2^(e_max − 23 − padding)` of the `23 + padding` mantissa bits kept after alignment, so its
  truncation keeps it, and the late accumulation of `c` loses nothing (`LosslessAlignment`).
  Then `S_acc = Σ p_ℓ + c`, and the output is the binary32 value nearest to the exact sum, ties
  to even (`aligned_nearestEven_of_lossless`), with the nearest-even predicate of
  `correctRounding_nearestEven`.
* CDNA 2. No operand is flushed, the conversion of every product to binary32 keeps it, and the
  pairwise sum of the products is exact. Then `S_acc = Σ p_ℓ + c` and the output is
  `fl{Σ p_ℓ + c}` (`pairwise_fl_exact_of_lossless`). -/

namespace MatrixCore

/-! ## CDNA 3 -/

/-- Algorithm 1 or 2 loses nothing on this block. With `e_max` the exponent of `S_{p_i,sum}` and
`e_c` that of `c` (`e_{c=0}` for `c = 0`):

* every product lies on the alignment grid `2^(e_max − 23 − padding)`;
* when `e_c ≤ e_max`, `c` lies on the grid `2^(e_max − 24)` of `s'_c`;
* when `e_c > e_max`, or every product is zero, `Σ p_ℓ` lies on the grid `2^(e_c − 32)` of
  `S'_{p_i,sum}`, and the exact `Σ p_ℓ + c` on the grid of its normalization and RD to `31`
  mantissa bits. -/
structure LosslessAlignment (P : Model) (x : Prepared) : Prop where
  products : ∀ e, (productSum P x.p).1 = some e →
    ∀ p ∈ x.p, OnGrid p.value (e - (23 + P.padding : ℕ))
  early : ∀ e eC, (productSum P x.p).1 = some e → cExp P x.c = some eC → eC ≤ e →
    OnGrid x.c.value (e - P.late.cMantissaBits)
  late : ∀ eC, cExp P x.c = some eC → (∀ e, (productSum P x.p).1 = some e → e < eC) →
    OnGrid (sumQ (x.p.map Unpacked.value)) (eC - P.late.sumMantissaBits) ∧
      (x.exact ≠ 0 → OnGrid x.exact (normExp (absQ x.exact) - P.late.accMantissaBits))

/-- A value lies on every grid at or below its own grid `2^(e − t)`, and zero on every grid: a
product is kept by the alignment when `e_max − 23 − padding ≤ e_p − t_p`. -/
theorem Unpacked.onGrid_of_le {p : Unpacked} {g : ℤ} (h : p.m = 0 ∨ g ≤ p.e - p.t) :
    OnGrid p.value g := by
  rcases h with h | h
  · rw [(Unpacked.value_eq_zero_iff p).mpr h]; exact OnGrid.zero g
  · exact (Unpacked.value_onGrid p).mono h

/-- `c` added before `e_max` without loss: every product lies on the alignment grid, `e_c ≤ e_max`,
and `c` lies on the grid `2^(e_max − 24)` of `s'_c`. -/
theorem LosslessAlignment.of_early {P : Model} {x : Prepared} {e eC : ℤ}
    (he : (productSum P x.p).1 = some e) (hce : cExp P x.c = some eC) (hle : eC ≤ e)
    (hp : ∀ p ∈ x.p, OnGrid p.value (e - (23 + P.padding : ℕ)))
    (hcg : OnGrid x.c.value (e - P.late.cMantissaBits)) : LosslessAlignment P x where
  products e' he' := by rw [he] at he'; cases he'; exact hp
  early e' eC' he' hce' _ := by rw [he] at he'; cases he'; rw [hce] at hce'; cases hce'; exact hcg
  late eC' hce' hlt := by
    rw [hce] at hce'; cases hce'
    exact absurd (hlt e he) (by omega)

/-- `c = 0` with `e_{c=0} ≤ e_max` (or no exponent for zero): only the products need to lie on the
alignment grid. -/
theorem LosslessAlignment.of_c_zero {P : Model} {x : Prepared} {e : ℤ}
    (he : (productSum P x.p).1 = some e) (hc : x.c.m = 0)
    (hz : ∀ eZ, P.cZeroExp = some eZ → eZ ≤ e)
    (hp : ∀ p ∈ x.p, OnGrid p.value (e - (23 + P.padding : ℕ))) : LosslessAlignment P x := by
  have hcv : x.c.value = 0 := (Unpacked.value_eq_zero_iff x.c).mpr hc
  have hce : cExp P x.c = P.cZeroExp := by unfold cExp; simp [hc]
  cases hZ : P.cZeroExp with
  | none =>
    refine ⟨fun e' he' => ?_, fun _ _ _ hc' _ => ?_, fun _ hc' _ => ?_⟩
    · rw [he] at he'; cases he'; exact hp
    · rw [hce, hZ] at hc'; cases hc'
    · rw [hce, hZ] at hc'; cases hc'
  | some eZ =>
    rw [hZ] at hce
    exact LosslessAlignment.of_early he hce (hz eZ hZ) hp (by rw [hcv]; exact OnGrid.zero _)

/-- A grid point smaller in magnitude than the grid step is zero. -/
theorem onGrid_eq_zero {x : ℚ} {g : ℤ} (h : OnGrid x g) (hs : absQ x < pow2 g) : x = 0 := by
  obtain ⟨k, rfl⟩ := h
  have hq := pow2_pos g
  rw [absQ_mul_pos _ _ hq, absQ_intCast] at hs
  have hk : ((k.natAbs : ℕ) : ℚ) < 1 := by
    apply Rat.not_le.mp
    intro h1
    have := Rat.mul_le_mul_of_nonneg_right h1 (Rat.le_of_lt hq)
    grind
  have : k.natAbs = 0 := by
    have : k.natAbs < 1 := by exact_mod_cast hk
    omega
  have hk0 : k = 0 := Int.natAbs_eq_zero.mp this
  subst hk0
  simp

/-- With every product on its grid, a group aligned to an exponent not above the grid's keeps
every product. -/
theorem alignedSum_exact_of_grid {padding : ℕ} {ps : List Unpacked} {g : ℤ}
    (hg : ∀ p ∈ ps, OnGrid p.value g)
    (hle : ∀ e, (alignedSum padding ps).1 = some e → e - (23 + padding : ℕ) ≤ g) :
    (alignedSum padding ps).2 = sumQ (ps.map Unpacked.value) := by
  unfold alignedSum at hle ⊢
  split
  · rename_i hm
    exact (sum_of_zero (maxExp_none hm)).symm
  · rename_i e he
    rw [he] at hle
    have hle' := hle e rfl
    simp only
    congr 1
    apply List.map_congr_left
    intro p hp
    exact truncGrid_of_onGrid ((hg p hp).mono hle')

/-- With every product on the alignment grid, `S_{p_i,sum}` is the exact `Σ p_ℓ`, for global
alignment and for odd/even grouping. -/
theorem productSum_exact_of_grid (P : Model) {ps : List Unpacked}
    (h : ∀ e, (productSum P ps).1 = some e → ∀ p ∈ ps, OnGrid p.value (e - (23 + P.padding : ℕ))) :
    (productSum P ps).2 = sumQ (ps.map Unpacked.value) := by
  cases hs : (productSum P ps).1 with
  | none =>
    obtain ⟨h1, h2⟩ := productSum_none_exact P hs
    rw [h1, h2]
  | some e =>
    have hg := h e hs
    unfold productSum at hs ⊢
    cases hacc : P.accumulation <;> simp only [hacc] at hs ⊢
    case oddEvenGrouping =>
      obtain ⟨hsum, _⟩ := sumQ_odd_even Unpacked.value ps
      have hgo : ∀ p ∈ oddIndexed ps, OnGrid p.value (e - (23 + P.padding : ℕ)) :=
        fun p hp => hg p (oddIndexed_subset ps p hp)
      have hge : ∀ p ∈ evenIndexed ps, OnGrid p.value (e - (23 + P.padding : ℕ)) :=
        fun p hp => hg p (evenIndexed_subset ps p hp)
      generalize hO : alignedSum P.padding (oddIndexed ps) = O at hs ⊢
      generalize hE : alignedSum P.padding (evenIndexed ps) = E at hs ⊢
      obtain ⟨eo, So⟩ := O
      obtain ⟨ee, Se⟩ := E
      simp only at hs ⊢
      cases hj : joinExp eo ee with
      | none => rw [hj] at hs; simp at hs
      | some e' =>
        rw [hj] at hs
        simp only [Option.some.injEq] at hs
        subst hs
        simp only
        have hjo : ∀ v, eo = some v → v ≤ e' := by
          intro v hv; subst hv; cases ee <;> simp [joinExp] at hj <;> omega
        have hje : ∀ v, ee = some v → v ≤ e' := by
          intro v hv; subst hv; cases eo <;> simp [joinExp] at hj <;> omega
        have ho : So = sumQ ((oddIndexed ps).map Unpacked.value) := by
          have := alignedSum_exact_of_grid hgo (padding := P.padding) (fun v hv => by
            rw [hO] at hv; have := hjo v hv; omega)
          rw [hO] at this; exact this
        have he' : Se = sumQ ((evenIndexed ps).map Unpacked.value) := by
          have := alignedSum_exact_of_grid hge (padding := P.padding) (fun v hv => by
            rw [hE] at hv; have := hje v hv; omega)
          rw [hE] at this; exact this
        have hgO : OnGrid So (e' - (23 + P.padding : ℕ)) := by
          rw [ho]; apply onGrid_sumQ; intro v hv
          simp only [List.mem_map] at hv
          obtain ⟨p, hp, rfl⟩ := hv
          exact hgo p hp
        have hgE : OnGrid Se (e' - (23 + P.padding : ℕ)) := by
          rw [he']; apply onGrid_sumQ; intro v hv
          simp only [List.mem_map] at hv
          obtain ⟨p, hp, rfl⟩ := hv
          exact hge p hp
        show rdGrid So _ + rdGrid Se _ = _
        rw [rdGrid_of_onGrid hgO, rdGrid_of_onGrid hgE, ho, he', hsum]
    all_goals
      exact alignedSum_exact_of_grid hg (fun v hv => by rw [hs] at hv; cases hv; omega)

/-- With `c` on the grid `2^(e_max − 24)`, `s'_c = c`; the binary8 cutoff then only removes
`c = 0`. -/
theorem shiftedC_of_onGrid (P : Model) {e eC : ℤ} {c : Unpacked}
    (hcut : ∀ n, P.late.cCutoff = some n → P.late.cMantissaBits ≤ n)
    (hc : absQ c.value < pow2 (eC + 1)) (hg : OnGrid c.value (e - P.late.cMantissaBits)) :
    shiftedC P e eC c = c.value := by
  have hrd : rdMantissa c.value e P.late.cMantissaBits = c.value := rdGrid_of_onGrid hg
  unfold shiftedC
  split
  · rename_i n hn
    split
    · rename_i hgt
      have hle := hcut n hn
      have := pow2_le_of_le (show eC + 1 ≤ e - P.late.cMantissaBits by omega)
      exact (onGrid_eq_zero hg (by grind)).symm
    · exact hrd
  · exact hrd

/-- **`S_acc` is exact when nothing is lost.** On a block where Algorithm 1 or 2 loses nothing,
`S_acc` is the exact `Σ p_ℓ + c`. -/
theorem alignedAccumulation_of_lossless (P : Model) (x : Prepared)
    (hcut : ∀ n, P.late.cCutoff = some n → P.late.cMantissaBits ≤ n)
    (hc : ∀ eC, cExp P x.c = some eC → absQ x.c.value < pow2 (eC + 1))
    (hl : LosslessAlignment P x) : alignedAccumulation P x = x.exact := by
  have hS := productSum_exact_of_grid P hl.products
  have hex : x.exact = sumQ (x.p.map Unpacked.value) + x.c.value := rfl
  unfold alignedAccumulation
  simp only
  rcases lateSum_cases P (productSum P x.p).1 (productSum P x.p).2 x.c with
    ⟨hn, h1⟩ | ⟨e, eC, he, hce, hle, h2⟩ | ⟨eC, hce, hlt, h3⟩
  · rw [h1, hS, hex, cExp_none hn]; grind
  · rw [h2, hS, hex, shiftedC_of_onGrid P hcut (hc eC hce) (hl.early e eC he hce hle)]
  · rw [h3]
    obtain ⟨hgs, hgx⟩ := hl.late eC hce hlt
    have hrd : rdMantissa (sumQ (x.p.map Unpacked.value)) eC P.late.sumMantissaBits =
        sumQ (x.p.map Unpacked.value) := rdGrid_of_onGrid hgs
    unfold shiftedSum
    rw [hS, hrd, ← hex]
    by_cases h0 : x.exact = 0
    · rw [h0]; unfold normalizeRD; simp
    · unfold normalizeRD
      simp only [h0, ↓reduceIte]
      exact rdGrid_of_onGrid (hgx h0)

/-- **CDNA 3 is correctly rounded when the alignment loses nothing.** On Algorithm 1 or 2 with
subnormals, if every product lies on the alignment grid and the late accumulation of `c` loses
nothing (`LosslessAlignment`), then `S_acc` is the exact `Σ a_ℓ b_ℓ + c` and the output is the
binary32 value nearest to it, ties to even. -/
theorem aligned_nearestEven_of_lossless {P : Model}
    (hacc : P.accumulation = .globalAlignment ∨ P.accumulation = .oddEvenGrouping)
    (hcut : ∀ n, P.late.cCutoff = some n → P.late.cMantissaBits ≤ n) (hs : P.subnormals = true)
    {x : BlockInput P} {t : BlockTrace P} (h : evalBlock x = .ok t)
    (hl : LosslessAlignment P t.prepared) :
    t.sAcc = t.prepared.exact ∧ NearestEven32 t.prepared.exact t.d := by
  have hp := (evalBlock_ok h).2.2.1
  have he : t.sAcc = t.prepared.exact := by
    rw [accumulate_aligned hacc (evalBlock_ok h).2.2.2.1]
    exact alignedAccumulation_of_lossless P t.prepared hcut (prepare_cExp_bound hp) hl
  refine ⟨he, ?_⟩
  rw [← he]
  exact evalBlock_nearestEven h hs

/-- CDNA 3 fp16 is correctly rounded on blocks where the alignment loses nothing. -/
theorem cdna3F16_nearestEven_of_lossless {x : BlockInput cdna3F16} {t : BlockTrace cdna3F16}
    (h : evalBlock x = .ok t) (hl : LosslessAlignment cdna3F16 t.prepared) :
    NearestEven32 t.prepared.exact t.d :=
  (aligned_nearestEven_of_lossless (Or.inl rfl) (fun _ h => by simp [cdna3F16] at h) rfl h hl).2

/-- CDNA 3 bf16 is correctly rounded on blocks where the alignment loses nothing. -/
theorem cdna3BF16_nearestEven_of_lossless {x : BlockInput cdna3BF16} {t : BlockTrace cdna3BF16}
    (h : evalBlock x = .ok t) (hl : LosslessAlignment cdna3BF16 t.prepared) :
    NearestEven32 t.prepared.exact t.d :=
  (aligned_nearestEven_of_lossless (Or.inl rfl) (fun _ h => by simp [cdna3BF16] at h) rfl h hl).2

/-- CDNA 3 XF32 is correctly rounded on blocks where the alignment loses nothing. -/
theorem cdna3XF32_nearestEven_of_lossless {x : BlockInput cdna3XF32} {t : BlockTrace cdna3XF32}
    (h : evalBlock x = .ok t) (hl : LosslessAlignment cdna3XF32 t.prepared) :
    NearestEven32 t.prepared.exact t.d :=
  (aligned_nearestEven_of_lossless (Or.inl rfl) (fun _ h => by simp [cdna3XF32] at h) rfl h hl).2

/-- CDNA 3 binary8 (Algorithm 2) is correctly rounded on blocks where the alignment loses
nothing. -/
theorem cdna3FP8_nearestEven_of_lossless (fa fb : Format) {x : BlockInput (cdna3FP8 fa fb)}
    {t : BlockTrace (cdna3FP8 fa fb)} (h : evalBlock x = .ok t)
    (hl : LosslessAlignment (cdna3FP8 fa fb) t.prepared) : NearestEven32 t.prepared.exact t.d :=
  (aligned_nearestEven_of_lossless (Or.inr rfl)
    (fun n h => by simp [cdna3FP8] at h ⊢; omega) rfl h hl).2

/-! ## CDNA 2 -/

/-- **CDNA 2 when every `fl{·}` before the last is exact.** On the pairwise-sum configuration, if
flushing changes no operand, the conversion of every product to binary32 keeps it, and the
pairwise sum of the products is exact, then `S_acc` is the exact `Σ a_ℓ b_ℓ + c` and the output
is `fl{Σ a_ℓ b_ℓ + c}`: its RNE, with a subnormal result flushed to zero. -/
theorem pairwise_fl_exact_of_lossless {P : Model} (hacc : P.accumulation = .pairWiseSum)
    {x : BlockInput P} {t : BlockTrace P} (h : evalBlock x = .ok t)
    (hf : P.subnormals = true ∨ t.prepared.flushed = t.prepared)
    (hconv : t.prepared.p.mapM (fun p => flValue (!P.subnormals) p.value) =
      some (t.prepared.p.map Unpacked.value))
    (hsum : pairwiseGroupSum (!P.subnormals) t.prepared.p.length
      (t.prepared.p.map Unpacked.value) = some (sumQ (t.prepared.p.map Unpacked.value))) :
    t.sAcc = t.prepared.exact ∧ fl32 (!P.subnormals) t.prepared.exact = some t.d := by
  obtain ⟨ps, u, hm, hu, hs⟩ := pairwiseSum_stages (accumulate_pairwise hacc (evalBlock_ok h).2.2.2.1)
  have hy : (if P.subnormals then t.prepared else t.prepared.flushed) = t.prepared := by
    split
    · rfl
    · rename_i hn
      rcases hf with hf | hf
      · exact absurd hf hn
      · exact hf
  rw [hy] at hm hs
  rw [hconv] at hm
  have hps := (Option.some.inj hm).symm
  subst hps
  rw [List.length_map] at hu
  rw [hsum] at hu
  have hu' := (Option.some.inj hu).symm
  subst hu'
  have he : t.sAcc = t.prepared.exact := by
    rw [hs]; unfold Prepared.exact; grind
  refine ⟨he, ?_⟩
  rw [← he]
  exact (evalBlock_ok h).2.2.2.2

end MatrixCore
