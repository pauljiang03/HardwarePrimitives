import OzakiMC.Cancellation
import OzakiMC.IEEE

/-! # Two passes through `c` on the matrix-core model

On the Tensor Core, running a group a second time from `c = −D1` recovers exactly what the first
pass truncated (`Ozaki.TC.twoPass_exact`). Here is what happens on each AMD architecture.

* **SFMA and CDNA 1** (`correct_rounding`): `S_acc` is the exact sum `c + Σ aᵢbᵢ`, rounded once
  to nearest. Pass 1 gives `D1 = rne(S)`; pass 2 adds `c = −D1` exactly and returns
  `rne(S − D1) = S − D1`, an integer of at most `2^24`. So two passes recover `S` for integer
  products whose sum is at most `2^48` (`mcTwoPass_exact`). On the SFMA, whose block is one
  product, this is the classical TwoProdFMA: it makes products of `24`-bit integers exact, where
  one pass allows only `12`-bit slices.
* **CDNA 3** (`global_alignment`): products of exponent at most `24` align without loss, and the late
  addition of `c` is exact for an integer `c` up to `2^31` when the exact sum is within `2^31`
  (`alignedAccumulation_wide`). Pass 1 rounds `S` to `D1` and pass 2 returns `S − D1` exactly, so
  two passes recover `S` for full groups of `11`-bit fp16 products, which one pass does not
  (`cdna3F16_full_group`, `cdna3F16_twoPass_full_group`).
* **CDNA 2** (`pair_wise_sum`): every node of the pairwise tree is rounded to binary32 before `c`
  is added. A second pass from `c = −D1` sees the same rounded tree, so it recovers what the final
  rounding lost but not what the tree lost; with operands whose tree rounds, two passes return the
  tree's value, not the exact sum (`cdna2_twoPass_fails`). For Ozaki's integer slices the tree
  never rounds: a full group of four `11`-bit products is at most `2^24` (`pairwiseSumsBounded_of_bound`).

**Is a second pass ever needed?** On CDNA 1 and 2 (`4` fp16 products per block, `2` or `4` bf16) and
CDNA 3 XF32 (`4`), a full group of the widest slices fits the `2^24` budget, so one pass is exact.
On CDNA 3 fp16 a group holds `8` products and `8 · 2^22 = 2^25`, so `11`-bit slices in full groups
need two passes; `10`-bit slices fit in one. On the SFMA two passes allow `24`-bit slices.

`mcMultiplier2` runs every block twice and adds the results exactly; it is exact on vectors of every
length on the SFMA with `24`-bit slices and on CDNA 1 and CDNA 3 whenever a full group of products
is at most `2^30` (`mcMultiplier2_exactOn`). -/

open MatrixCore

namespace Ozaki.MC

/-! ## Integer blocks with a wide `c` -/

/-- A prepared block of integer operands and an integer `c`: every product within `2^24`, and `c`
and the exact sum within `2^31`. -/
structure IntPreparedW (x : Prepared) : Prop where
  a : ∀ u ∈ x.a, IntOperand u
  b : ∀ u ∈ x.b, IntOperand u
  c : IntOperand x.c
  p_le : ∀ q ∈ x.p, absQ q.value ≤ pow2 24
  c_le : absQ x.c.value ≤ pow2 31
  sum_le : absQ x.exact ≤ pow2 31

namespace IntPreparedW

variable {x : Prepared} (h : IntPreparedW x)
include h

theorem p : ∀ q ∈ x.p, IntOperand q := by
  intro q hq
  obtain ⟨a, ha, b, hb, rfl⟩ := mem_zipWith' hq
  exact (h.a a ha).mul (h.b b hb)

theorem productOverflows : x.productOverflows = false := by
  unfold Prepared.productOverflows
  apply List.any_eq_false.mpr
  intro q hq hle
  have h1 := h.p_le q hq
  have h2 : pow2 24 < pow2 128 := pow2_lt_of_lt (by decide)
  have := of_decide_eq_true hle
  grind

theorem ints : ∃ zs : List ℤ, x.p.map Unpacked.value = zs.map (fun z : ℤ => (z : ℚ)) :=
  intList (x.p.map Unpacked.value) (by
    intro q hq
    obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hq
    obtain ⟨⟨z, hz⟩, _⟩ := h.p r hr
    exact ⟨z, hz⟩)

theorem c_int : ∃ z : ℤ, x.c.value = z := h.c.1

end IntPreparedW

/-- **CDNA 3 with a wide `c`**: global alignment of integer products within `2^24` and an integer
`c` within `2^31` is exact whenever the exact sum is within `2^31`. -/
theorem alignedAccumulation_wide {P : Model} (hacc : P.accumulation = .globalAlignment)
    (hneab : 1 ≤ P.neab) (hlate : P.late = {}) (hcz : P.cZeroExp = some (-126)) {x : Prepared}
    (h : IntPreparedW x) : alignedAccumulation P x = x.exact := by
  have hprod := h.p
  have he24 : ∀ q ∈ x.p, q.m ≠ 0 → q.e ≤ 24 := fun q hq hm => (hprod q hq).exp_le hm (h.p_le q hq)
  obtain ⟨zs, hzs⟩ := h.ints
  have hS : sumQ (x.p.map Unpacked.value) = ((zs.sum : ℤ) : ℚ) := by rw [hzs, sumQ_cast]
  have hal : productSum P x.p = alignedSum P.neab x.p := by unfold productSum; rw [hacc]
  have hps : productSum P x.p = (maxExp x.p, sumQ (x.p.map Unpacked.value)) := by
    rw [hal]
    unfold alignedSum
    split
    · rename_i hm; rw [hm, sum_of_zero (maxExp_none hm)]
    · rename_i e hm
      rw [hm]
      congr 1
      congr 1
      apply List.map_congr_left
      intro q hq
      have he := maxExp_upper he24 e hm
      exact truncGrid_of_onGrid ((hprod q hq).onGrid (by omega))
  have heMax : ∀ e, (productSum P x.p).1 = some e → e ≤ 24 := by
    rw [hps]; exact maxExp_upper he24
  have hcE : ∀ eC, cExp P x.c = some eC → eC ≤ 31 := by
    intro eC he
    unfold cExp at he
    split at he
    · rw [hcz] at he; cases he; omega
    · rename_i hm; cases he; exact h.c.exp_le hm h.c_le
  obtain ⟨zc, hzc⟩ := h.c_int
  have hT : ∀ T : ℤ, absQ (T : ℚ) ≤ pow2 31 → normaliseRD P.late.accFracBits (T : ℚ) = T := by
    intro T hT
    unfold normaliseRD
    split
    · rename_i h0; rw [h0]
    · rename_i h0
      have hpos := absQ_pos h0
      have hlog : log2Floor (absQ (T : ℚ)) ≤ 31 :=
        pow2_le_iff.mp (Rat.le_trans (log2Floor_spec hpos).1 hT)
      have hn : normExp (absQ (T : ℚ)) ≤ 31 := by unfold normExp; omega
      have hacc31 : P.late.accFracBits = 31 := by rw [hlate]
      exact rdGrid_of_onGrid (OnGrid.mono ⟨T, by rw [pow2_zero, Rat.mul_one]⟩ (by omega))
  have hsumbound : absQ ((zs.sum + zc : ℤ) : ℚ) ≤ pow2 31 := by
    have := h.sum_le
    unfold Prepared.exact at this
    rw [hS, hzc, ← Rat.intCast_add] at this
    exact this
  unfold alignedAccumulation
  simp only
  rcases lateSum_cases P (productSum P x.p).1 (productSum P x.p).2 x.c with
    ⟨hc0, hl⟩ | ⟨e, eC, he, hce, _, hl⟩ | ⟨eC, hce, _, hl⟩
  · rw [hl, hps]; unfold Prepared.exact; rw [cExp_none hc0]; grind
  · rw [hl, hps]
    have hsc : shiftedC P e eC x.c = x.c.value := by
      unfold shiftedC
      rw [hlate]
      simp only
      have := heMax e he
      exact rdGrid_of_onGrid (h.c.onGrid (by omega))
    rw [hsc]; rfl
  · rw [hl, hps]
    have hle := hcE eC hce
    unfold shiftedSum
    rw [hS, hlate]
    simp only [rdFrac]
    rw [rdGrid_of_onGrid (OnGrid.mono ⟨zs.sum, by rw [pow2_zero, Rat.mul_one]⟩ (by omega)), hzc,
      ← Rat.intCast_add]
    have := hT (zs.sum + zc) hsumbound
    rw [hlate] at this
    rw [this]
    unfold Prepared.exact
    rw [hS, hzc, Rat.intCast_add]

/-! ## Rounding an integer sum -/

/-- `2^n` is a value of the unbounded binary32 format. -/
theorem two_pow_uValue (n : ℕ) : UValue 24 (-126) ((2 : ℚ) ^ (n : ℤ)) := by
  refine ⟨2 ^ 23, n, by omega, by decide, ?_⟩
  have h : ((2 ^ 23 : ℤ) : ℚ) = (2 : ℚ) ^ ((23 : ℕ) : ℤ) := by
    rw [two_pow_natCast]; rfl
  rw [h, ← two_pow_add]
  congr 1
  omega

/-- **Binary32 round to nearest of an integer sum.** For an integer `S` with `|S| ≤ 2^n`,
`n ≤ 48`, the rounded value is an integer `D` with `|S − D| ≤ 2^24` and `|D| ≤ 2^n`. -/
theorem rneValue_intSum (S : ℤ) {n : ℕ} (hn : n ≤ 48) (hS : Rat.abs (S : ℚ) ≤ 2 ^ (n : ℤ)) :
    ∃ D : ℤ, rneValue (S : ℚ) = D ∧ (S - D).natAbs ≤ 2 ^ 24 ∧ Rat.abs (D : ℚ) ≤ 2 ^ (n : ℤ) := by
  rw [rneValue_eq_rneU]
  have hmono : ∀ {a b : ℚ}, a ≤ b → rneU 24 (-126) a ≤ rneU 24 (-126) b :=
    fun hab => rneU_monotone (p := 24) (emin := -126) (by decide) hab
  have hfix : ∀ m : ℕ, rneU 24 (-126) ((2 : ℚ) ^ (m : ℤ)) = 2 ^ (m : ℤ) :=
    fun m => rneU_of_uValue (by decide) (two_pow_uValue m)
  have hfixn : ∀ m : ℕ, rneU 24 (-126) (-(2 : ℚ) ^ (m : ℤ)) = -2 ^ (m : ℤ) :=
    fun m => rneU_of_uValue (by decide) (two_pow_uValue m).neg
  obtain ⟨h1, h2⟩ := (abs_le_iff _ _).mp hS
  have hR1 := hmono h1
  have hR2 := hmono h2
  rw [hfixn] at hR1
  rw [hfix] at hR2
  have hbound : ∀ D : ℤ, rneU 24 (-126) (S : ℚ) = D → Rat.abs (D : ℚ) ≤ 2 ^ (n : ℤ) := by
    intro D hD
    rw [hD] at hR1 hR2
    exact (abs_le_iff _ _).mpr ⟨hR1, hR2⟩
  by_cases hsmall : S.natAbs ≤ 2 ^ 24
  · have hf := int_finiteValue32 S hsmall
    have hv : rneValue (S : ℚ) = S := rneValue_of_finite hf
    rw [rneValue_eq_rneU] at hv
    exact ⟨S, hv, by simp, hbound S hv⟩
  · -- the rounded value is at least `2^24` in magnitude, so it is an integer
    have hbig : (2 : ℚ) ^ ((24 : ℕ) : ℤ) ≤ Rat.abs (rneU 24 (-126) (S : ℚ)) := by
      rcases (show 2 ^ 24 < S ∨ S < -2 ^ 24 by omega) with hp | hneg
      · have hq : (2 : ℚ) ^ ((24 : ℕ) : ℤ) ≤ (S : ℚ) := by
          rw [two_pow_natCast]
          have : ((2 ^ 24 : ℕ) : ℤ) ≤ S := by omega
          have h' : ((((2 ^ 24 : ℕ) : ℤ)) : ℚ) ≤ ((S : ℤ) : ℚ) := Rat.intCast_le_intCast.mpr this
          rwa [Rat.intCast_natCast] at h'
        have := hmono hq
        rw [hfix] at this
        rw [abs_of_nonneg (Rat.le_trans (Rat.le_of_lt (two_pow_pos _)) this)]
        exact this
      · have hq : (S : ℚ) ≤ -(2 : ℚ) ^ ((24 : ℕ) : ℤ) := by
          rw [two_pow_natCast]
          have : S ≤ -((2 ^ 24 : ℕ) : ℤ) := by omega
          have h' : ((S : ℤ) : ℚ) ≤ ((-((2 ^ 24 : ℕ) : ℤ) : ℤ) : ℚ) := Rat.intCast_le_intCast.mpr this
          rw [Rat.intCast_neg, Rat.intCast_natCast] at h'
          exact h'
        have := hmono hq
        rw [hfixn] at this
        have hneg' : rneU 24 (-126) (S : ℚ) < 0 := by
          have := two_pow_pos ((24 : ℕ) : ℤ); grind
        rw [abs_of_neg hneg']
        grind
    obtain ⟨k, e, _, hk, hR, _⟩ := rneU_repr (p := 24) (emin := -126) (by decide) (S : ℚ)
    have he : 24 ≤ e := by
      have habs : Rat.abs (rneU 24 (-126) (S : ℚ)) < 2 ^ (e + 1) := by
        rw [hR, abs_mul, abs_intCast, abs_two_pow]
        have hk' : ((k.natAbs : ℕ) : ℚ) < (2 : ℚ) ^ ((24 : ℕ) : ℤ) := by
          rw [two_pow_natCast]; exact Rat.natCast_lt_natCast.mpr hk
        have := Rat.mul_lt_mul_of_pos_right hk' (two_pow_pos (e - ((24 : ℕ) - 1 : ℤ)))
        rw [← two_pow_add] at this
        have e1 : ((24 : ℕ) : ℤ) + (e - (((24 : ℕ) : ℤ) - 1)) = e + 1 := by omega
        rw [e1] at this
        exact this
      have hlt : (2 : ℚ) ^ ((24 : ℕ) : ℤ) < 2 ^ (e + 1) := lt_of_le_of_lt' hbig habs
      have hlt' : pow2 ((24 : ℕ) : ℤ) < pow2 (e + 1) := by rw [pow2_eq, pow2_eq]; exact hlt
      have := pow2_lt_iff.mp hlt'
      omega
    refine ⟨k * 2 ^ (e - 23).toNat, ?_, ?_, ?_⟩
    · rw [hR]
      have e1 : e - (((24 : ℕ) : ℤ) - 1) = (((e - 23).toNat : ℕ) : ℤ) := by omega
      rw [e1, two_pow_natCast, Rat.intCast_mul]
      congr 1
    · -- `|S − D| ≤ 2^-24 |S| + 2^-150 < 2^24 + 1`
      have herr := rneU_error (p := 24) (emin := -126) (S : ℚ)
      have hD : rneU 24 (-126) (S : ℚ) = ((k * 2 ^ (e - 23).toNat : ℤ) : ℚ) := by
        rw [hR]
        have e1 : e - (((24 : ℕ) : ℤ) - 1) = (((e - 23).toNat : ℕ) : ℤ) := by omega
        rw [e1, two_pow_natCast, Rat.intCast_mul]
        congr 1
      rw [hD] at herr
      have hscale : (2 : ℚ) ^ (-((24 : ℕ) : ℤ)) * Rat.abs (S : ℚ) ≤ 2 ^ ((24 : ℕ) : ℤ) := by
        have := Rat.mul_le_mul_of_nonneg_left hS (Rat.le_of_lt (two_pow_pos (-((24 : ℕ) : ℤ))))
        rw [← two_pow_add] at this
        refine Rat.le_trans this ?_
        have hle : -((24 : ℕ) : ℤ) + (n : ℤ) ≤ ((24 : ℕ) : ℤ) := by omega
        have := pow2_le_iff.mpr hle
        rwa [pow2_eq, pow2_eq] at this
      have htiny : (2 : ℚ) ^ ((-126 : ℤ) - ((24 : ℕ) : ℤ)) < 1 := by decide +kernel
      have hlt : Rat.abs ((((k * 2 ^ (e - 23).toNat : ℤ) : ℚ)) - (S : ℚ)) < 2 ^ ((24 : ℕ) : ℤ) + 1 := by
        grind
      rw [← Rat.intCast_sub, abs_intCast, two_pow_natCast] at hlt
      have hc : ((2 ^ 24 : ℕ) : ℚ) + 1 = (((2 ^ 24 + 1 : ℕ)) : ℚ) := by decide +kernel
      have hlt' : (((k * 2 ^ (e - 23).toNat - S).natAbs : ℕ) : ℚ) < (((2 ^ 24 + 1 : ℕ)) : ℚ) := by
        rw [← hc]; exact hlt
      have := Rat.natCast_lt_natCast.mp hlt'
      have hsw : (S - k * 2 ^ (e - 23).toNat).natAbs = (k * 2 ^ (e - 23).toNat - S).natAbs := by
        omega
      omega
    · apply hbound
      rw [hR]
      have e1 : e - (((24 : ℕ) : ℤ) - 1) = (((e - 23).toNat : ℕ) : ℤ) := by omega
      rw [e1, two_pow_natCast, Rat.intCast_mul]
      congr 1

/-! ## Blocks of integer words -/

/-- Integer operand words and an integer `c` prepare into integer operands whose exact sum is
`c + Σ aᵢbᵢ`. -/
theorem prepare_intW {P : Model} (hfa : smallSubnormals P.a) (hfb : smallSubnormals P.b)
    {x : BlockInput P} (ha : ∀ w ∈ x.a, IntWord P.a w) (hb : ∀ w ∈ x.b, IntWord P.b w)
    {zc : ℤ} (hc : value32 x.c = some (zc : ℚ)) :
    ∃ px, prepare x = some px ∧ (∀ u ∈ px.a, IntOperand u) ∧ (∀ u ∈ px.b, IntOperand u) ∧
      IntOperand px.c ∧ px.c.value = zc ∧ px.exact = (zc : ℚ) + exactProducts P x.a x.b ∧
      px.p.map Unpacked.value =
        List.zipWith (fun w w' => P.a.wordValue w * P.b.wordValue w') x.a x.b := by
  obtain ⟨A, hA⟩ := mapM_exists x.a fun w hw => by
    obtain ⟨u, hu, _⟩ := ha w hw; exact ⟨u, hu⟩
  obtain ⟨B, hB⟩ := mapM_exists x.b fun w hw => by
    obtain ⟨u, hu, _⟩ := hb w hw; exact ⟨u, hu⟩
  obtain ⟨uc, hC, hcv⟩ : ∃ uc, (binary32.decode x.c).toFinite = some uc ∧ uc.value = zc := by
    unfold value32 at hc
    cases hd : (binary32.decode x.c).toFinite with
    | none => rw [hd] at hc; simp at hc
    | some uc => rw [hd] at hc; simp at hc; exact ⟨uc, rfl, hc⟩
  have hprep : prepare x = some ⟨A, B, uc⟩ := by
    unfold prepare; simp only [hA, hB, hC]; rfl
  have hops : ∀ (i : InputFormat) (ws : List i.Word) (U : List Unpacked), smallSubnormals i →
      (∀ w ∈ ws, IntWord i w) → ws.mapM (fun w => (i.read w).toFinite) = some U →
      ∀ u ∈ U, IntOperand u := by
    intro i ws U hi hw hU u hu
    obtain ⟨w, hw', hr⟩ := mapM_mem_option hU u hu
    obtain ⟨u', hu', z, hz⟩ := hw w hw'
    rw [hr] at hu'; cases hu'
    exact ⟨⟨z, hz⟩, int_normal (fun hm => read_sub hi hr hm) hz⟩
  have hpv : (Prepared.p ⟨A, B, uc⟩).map Unpacked.value =
      List.zipWith (fun w w' => P.a.wordValue w * P.b.wordValue w') x.a x.b := by
    unfold Prepared.p
    simp only [List.map_zipWith, Unpacked.value_mul]
    exact mapM_zipWith (fun a b => a * b) x.a x.b A B hA hB
  have hexact : (Prepared.exact ⟨A, B, uc⟩) = (zc : ℚ) + exactProducts P x.a x.b := by
    rw [Prepared.exact_eq]
    simp only
    rw [mapM_products x.a x.b A B hA hB, hcv]
    grind
  exact ⟨⟨A, B, uc⟩, hprep, hops _ _ _ hfa ha hA, hops _ _ _ hfb hb hB,
    ⟨⟨zc, hcv⟩, int_normal (binary32_sub hC) hcv⟩, hcv, hexact, hpv⟩

/-- A block whose accumulation is exact returns the binary32 round to nearest of its exact sum
(with subnormals, so the final `fl{·}` is round to nearest even). -/
theorem evalBlock_rne {P : Model} (hsub : P.subnormals = true) {x : BlockInput P}
    (hla : x.a.length = P.nfma) (hlb : x.b.length = P.nfma) {px : Prepared}
    (hprep : prepare x = some px) (hacc : accumulate P px = .ok px.exact)
    (hov : absQ px.exact < overflowThreshold32) :
    ∃ t, evalBlock x = .ok t ∧ value32 t.d = some (rneValue px.exact) := by
  obtain ⟨w, hw⟩ := Option.isSome_iff_exists.mp ((rne32_isSome_iff _).mpr hov)
  refine ⟨⟨px, px.exact, w⟩, ?_, rne32_value hw⟩
  unfold evalBlock
  rw [if_neg (by omega), hprep]
  simp only [hacc, hsub, Bool.not_true, fl32_false, hw]

/-! ## Two passes -/

/-- **Two passes of one block**: from `c = +0`, giving `D1`, then from `c = −D1`, giving `D2`; the
result is `D1 + D2`. -/
def mcTwoPass (P : Model) (a : List P.a.Word) (b : List P.b.Word) : Option ℚ :=
  match evalBlock (P := P) ⟨a, b, 0⟩ with
  | .ok t1 =>
    match value32 t1.d with
    | some d1 =>
      match evalBlock (P := P) ⟨a, b, (rne32 (-d1)).getD 0⟩ with
      | .ok t2 => (value32 t2.d).map (d1 + ·)
      | .error _ => none
    | none => none
  | .error _ => none

theorem pow2_48_lt : (2 : ℚ) ^ ((48 : ℕ) : ℤ) < overflowThreshold32 := by decide +kernel

/-- **Two passes recover an integer block**, on any configuration that adds integer operands and an
integer `c` of at most `2^n` exactly when the exact sum is at most `2^n` (`24 ≤ n ≤ 48`): pass 1
rounds `S` to an integer `D1` with `|S − D1| ≤ 2^24`, and pass 2 returns `S − D1` exactly. -/
theorem twoPass_of_acc {P : Model} (hsub : P.subnormals = true) (hfa : smallSubnormals P.a)
    (hfb : smallSubnormals P.b) {a : List P.a.Word} {b : List P.b.Word} (hla : a.length = P.nfma)
    (hlb : b.length = P.nfma) (ha : ∀ w ∈ a, IntWord P.a w) (hb : ∀ w ∈ b, IntWord P.b w)
    {n : ℕ} (h24 : 24 ≤ n) (hn : n ≤ 48) {S : ℤ} (hS : exactProducts P a b = S)
    (hSn : Rat.abs (S : ℚ) ≤ 2 ^ (n : ℤ))
    (hacc : ∀ px : Prepared, (∀ u ∈ px.a, IntOperand u) → (∀ u ∈ px.b, IntOperand u) →
      IntOperand px.c → Rat.abs px.c.value ≤ 2 ^ (n : ℤ) → Rat.abs px.exact ≤ 2 ^ (n : ℤ) →
      px.p.map Unpacked.value = List.zipWith (fun w w' => P.a.wordValue w * P.b.wordValue w') a b →
      accumulate P px = .ok px.exact) :
    mcTwoPass P a b = some (S : ℚ) := by
  have hpos : (0 : ℚ) ≤ 2 ^ (n : ℤ) := Rat.le_of_lt (two_pow_pos _)
  have hnle : (2 : ℚ) ^ (n : ℤ) ≤ 2 ^ ((48 : ℕ) : ℤ) := by
    have := pow2_le_iff.mpr (show ((n : ℕ) : ℤ) ≤ ((48 : ℕ) : ℤ) by omega)
    rwa [pow2_eq, pow2_eq] at this
  have hov : ∀ q : ℚ, Rat.abs q ≤ 2 ^ (n : ℤ) → absQ q < overflowThreshold32 := by
    intro q hq
    rw [absQ_eq]
    exact lt_of_le_of_lt' (Rat.le_trans hq hnle) pow2_48_lt
  -- pass 1, from `c = 0`
  obtain ⟨px1, hp1, hpa1, hpb1, hpc1, hcv1, hex1, hpv1⟩ :=
    prepare_intW (x := ⟨a, b, 0⟩) hfa hfb ha hb (zc := 0) (by rw [Rat.intCast_zero]; exact value32_zero)
  have hex1' : px1.exact = (S : ℚ) := by
    rw [hex1]; simp only; rw [hS, Rat.intCast_zero]; grind
  have hacc1 := hacc px1 hpa1 hpb1 hpc1 (by rw [hcv1, Rat.intCast_zero, abs_zero]; exact hpos)
    (by rw [hex1']; exact hSn) hpv1
  obtain ⟨t1, ht1, hv1⟩ := evalBlock_rne (x := ⟨a, b, 0⟩) hsub hla hlb hp1 hacc1
    (hov _ (by rw [hex1']; exact hSn))
  obtain ⟨D, hD, hSD, hDn⟩ := rneValue_intSum S hn hSn
  rw [hex1', hD] at hv1
  -- the word of `−D1`
  have hfinD : FiniteValue32 (D : ℚ) := value32_finiteValue hv1
  obtain ⟨w, hw⟩ := Option.isSome_iff_exists.mp
    ((rne32_isSome_iff (-(D : ℚ))).mpr (hov _ (by rw [abs_neg]; exact hDn)))
  have hwv : value32 w = some ((-D : ℤ) : ℚ) := by
    rw [rne32_value hw, rneValue_of_finite hfinD.neg, Rat.intCast_neg]
  -- pass 2, from `c = −D1`
  obtain ⟨px2, hp2, hpa2, hpb2, hpc2, hcv2, hex2, hpv2⟩ :=
    prepare_intW (x := ⟨a, b, w⟩) hfa hfb ha hb hwv
  have hex2' : px2.exact = ((S - D : ℤ) : ℚ) := by
    rw [hex2]; simp only; rw [hS, Rat.intCast_sub, Rat.intCast_neg]; grind
  have hSDle : Rat.abs (((S - D : ℤ) : ℚ)) ≤ 2 ^ (n : ℤ) := by
    rw [abs_intCast]
    have h1 : (((S - D).natAbs : ℕ) : ℚ) ≤ ((2 ^ 24 : ℕ) : ℚ) := Rat.natCast_le_natCast.mpr hSD
    have h2 : (2 : ℚ) ^ ((24 : ℕ) : ℤ) ≤ 2 ^ (n : ℤ) := by
      have := pow2_le_iff.mpr (show ((24 : ℕ) : ℤ) ≤ ((n : ℕ) : ℤ) by omega)
      rwa [pow2_eq, pow2_eq] at this
    rw [two_pow_natCast] at h2
    exact Rat.le_trans h1 h2
  have hacc2 := hacc px2 hpa2 hpb2 hpc2 (by rw [hcv2, Rat.intCast_neg, abs_neg]; exact hDn)
    (by rw [hex2']; exact hSDle) hpv2
  obtain ⟨t2, ht2, hv2⟩ := evalBlock_rne (x := ⟨a, b, w⟩) hsub hla hlb hp2 hacc2
    (hov _ (by rw [hex2']; exact hSDle))
  rw [hex2', rneValue_of_finite (int_finiteValue32 _ hSD)] at hv2
  unfold mcTwoPass
  simp only [ht1, hv1, hw, Option.getD_some, ht2, hv2, Option.map_some]
  congr 1
  rw [Rat.intCast_sub]; grind

/-! ## Where two passes are exact -/

/-- `correct_rounding` without product-overflow detection (SFMA, CDNA 1) adds exactly. -/
theorem accumulate_cr {P : Model} (hacc : P.accumulation = .correctRounding)
    (hpo : P.productOverflow = false) (x : Prepared) : accumulate P x = .ok x.exact := by
  unfold accumulate; rw [hpo, hacc]; simp

/-- CDNA 3's global alignment adds an integer block with a wide `c` exactly. -/
theorem accumulate_wide {P : Model} (hacc : P.accumulation = .globalAlignment) (hn : 1 ≤ P.neab)
    (hl : P.late = {}) (hc : P.cZeroExp = some (-126)) {x : Prepared} (h : IntPreparedW x) :
    accumulate P x = .ok x.exact := by
  unfold accumulate
  rw [h.productOverflows, Bool.and_false]
  simp only [Bool.false_eq_true, ↓reduceIte]
  rw [hacc]; simp only [alignedAccumulation_wide hacc hn hl hc h]

theorem exactProducts_intZ {P : Model} {a : List P.a.Word} {b : List P.b.Word}
    (ha : ∀ w ∈ a, IntWord P.a w) (hb : ∀ w ∈ b, IntWord P.b w) :
    ∃ S : ℤ, exactProducts P a b = S := by
  obtain ⟨Z, hZ, _⟩ := exactProducts_int a b ha hb; exact ⟨Z, hZ⟩

/-- **SFMA and CDNA 1: two passes recover a block** of integer products whose sum is at most
`2^48`; on the SFMA (one product per block) this is TwoProdFMA. -/
theorem mcTwoPass_exact_cr {P : Model} (hacc : P.accumulation = .correctRounding)
    (hpo : P.productOverflow = false) (hsub : P.subnormals = true) (hfa : smallSubnormals P.a)
    (hfb : smallSubnormals P.b) {a : List P.a.Word} {b : List P.b.Word} (hla : a.length = P.nfma)
    (hlb : b.length = P.nfma) (ha : ∀ w ∈ a, IntWord P.a w) (hb : ∀ w ∈ b, IntWord P.b w)
    (hS : Rat.abs (exactProducts P a b) ≤ 2 ^ ((48 : ℕ) : ℤ)) :
    mcTwoPass P a b = some (exactProducts P a b) := by
  obtain ⟨S, hSv⟩ := exactProducts_intZ ha hb
  rw [hSv] at hS ⊢
  exact twoPass_of_acc hsub hfa hfb hla hlb ha hb (n := 48) (by omega) (by omega) hSv hS
    fun px _ _ _ _ _ _ => accumulate_cr hacc hpo px

/-- **CDNA 3: two passes recover a block** of integer products each at most `2^24` whose sum is at
most `2^30`. -/
theorem mcTwoPass_exact_ga {P : Model} (hacc : P.accumulation = .globalAlignment)
    (hn : 1 ≤ P.neab) (hl : P.late = {}) (hc : P.cZeroExp = some (-126))
    (hsub : P.subnormals = true) (hfa : smallSubnormals P.a)
    (hfb : smallSubnormals P.b) {a : List P.a.Word} {b : List P.b.Word} (hla : a.length = P.nfma)
    (hlb : b.length = P.nfma) (ha : ∀ w ∈ a, IntWord P.a w) (hb : ∀ w ∈ b, IntWord P.b w)
    (hprod : ∀ v ∈ List.zipWith (fun w w' => P.a.wordValue w * P.b.wordValue w') a b,
      Rat.abs v ≤ 2 ^ ((24 : ℕ) : ℤ))
    (hS : Rat.abs (exactProducts P a b) ≤ 2 ^ ((30 : ℕ) : ℤ)) :
    mcTwoPass P a b = some (exactProducts P a b) := by
  obtain ⟨S, hSv⟩ := exactProducts_intZ ha hb
  rw [hSv] at hS ⊢
  have h3031 : (2 : ℚ) ^ ((30 : ℕ) : ℤ) ≤ pow2 31 := by decide +kernel
  refine twoPass_of_acc hsub hfa hfb hla hlb ha hb (n := 30) (by omega) (by omega) hSv hS ?_
  intro px hpa hpb hpc hcle hsle hpv
  refine accumulate_wide hacc hn hl hc ⟨hpa, hpb, hpc, ?_, ?_, ?_⟩
  · intro q hq
    have hmem : q.value ∈ px.p.map Unpacked.value := List.mem_map_of_mem hq
    rw [hpv] at hmem
    rw [absQ_eq]
    have := hprod _ hmem
    rw [pow2_eq]; exact this
  · rw [absQ_eq]; exact Rat.le_trans hcle h3031
  · rw [absQ_eq]; exact Rat.le_trans hsle h3031

/-! ## The two-pass engine -/

/-- Split-K with chunks of at most `m`, for an engine exact on vectors of at most `m` entries: exact
on vectors of every length. -/
theorem chunked_exactOn_short {mult : MatrixMultiplier} {b m : ℕ} (hm : 0 < m)
    (hmult : ∀ x y : List ℤ, x.length = y.length → x.length ≤ m → (∀ a ∈ x, a.natAbs ≤ 2 ^ b) →
      (∀ a ∈ y, a.natAbs ≤ 2 ^ b) → mult x y = some (dotZ x y)) (B : ℕ) :
    (chunked m mult).ExactOn b B := by
  intro x y hlen hx hy _
  unfold chunked chunksOf
  rw [hlen]
  obtain ⟨hpairs, hsum⟩ := chunksAux_pairs hm y.length x y hlen (by omega)
  rw [mapM_eq_some_map (g := fun p : List ℤ × List ℤ => ((dotZ p.1 p.2 : ℤ) : ℚ))]
  · rw [Option.map_some, ← intCast_sum_map, hsum]
    rfl
  · intro p hp
    obtain ⟨h1, h2, h3, h4⟩ := hpairs p hp
    exact hmult _ _ h1 h2 (fun a ha => hx a (h3 a ha)) (fun a ha => hy a (h4 a ha))

/-- One block run twice: the integers padded with zeros to `N_FMA`, encoded, and run by
`mcTwoPass`. -/
def mcGroup2 (P : Model) : MatrixMultiplier := fun x y => do
  let a ← (x ++ List.replicate (P.nfma - x.length) 0).mapM fun z : ℤ => P.a.encodeExact (z : ℚ)
  let b ← (y ++ List.replicate (P.nfma - y.length) 0).mapM fun z : ℤ => P.b.encodeExact (z : ℚ)
  mcTwoPass P a b

/-- **The two-pass matrix-core engine**: split-K with chunks of one block, every block run twice,
the block results added exactly. -/
def mcMultiplier2 (P : Model) : MatrixMultiplier := chunked P.nfma (mcGroup2 P)

/-- The configurations and slice widths for which a block of `b`-bit integers run twice is exact:
`correct_rounding` (no product-overflow detection) with `N_FMA · 2^(2b) ≤ 2^48`, or CDNA 3's global
alignment with `2b ≤ 24` and `N_FMA · 2^(2b) ≤ 2^30`; subnormals supported. -/
def TwoPassOK (P : Model) (b : ℕ) : Prop :=
  P.subnormals = true ∧
    ((P.accumulation = .correctRounding ∧ P.productOverflow = false ∧
        P.nfma * 2 ^ (2 * b) ≤ 2 ^ 48) ∨
      (P.accumulation = .globalAlignment ∧ 1 ≤ P.neab ∧ P.late = {} ∧
        P.cZeroExp = some (-126) ∧ 2 * b ≤ 24 ∧ P.nfma * 2 ^ (2 * b) ≤ 2 ^ 30))

instance (P : Model) (b : ℕ) : Decidable (TwoPassOK P b) := by unfold TwoPassOK; infer_instance

theorem dotZ_replicate_zero : ∀ k : ℕ, dotZ (List.replicate k 0) (List.replicate k 0) = 0
  | 0 => rfl
  | k + 1 => by simp [List.replicate_succ, dotZ_cons, dotZ_replicate_zero k]

/-- **The two-pass engine is exact on vectors of every length** with `b`-bit slices, whenever
`TwoPassOK P b`. -/
theorem mcMultiplier2_exactOn {P : Model} {b : ℕ} (hok : TwoPassOK P b) (hfa : smallSubnormals P.a)
    (hfb : smallSubnormals P.b) (hn : 0 < P.nfma) (hea : EncodesInts P.a b)
    (heb : EncodesInts P.b b) (B : ℕ) : (mcMultiplier2 P).ExactOn b B := by
  apply chunked_exactOn_short hn
  intro x y hlen hlx hx hy
  let x' := x ++ List.replicate (P.nfma - x.length) 0
  let y' := y ++ List.replicate (P.nfma - y.length) 0
  have hz : ∀ k : ℕ, ∀ z ∈ List.replicate k (0 : ℤ), z.natAbs ≤ 2 ^ b := by
    intro k z hz; rw [(List.mem_replicate.mp hz).2]; simp
  have hx' : ∀ z ∈ x', z.natAbs ≤ 2 ^ b := by
    intro z hz'; rcases List.mem_append.mp hz' with h | h
    · exact hx z h
    · exact hz _ z h
  have hy' : ∀ z ∈ y', z.natAbs ≤ 2 ^ b := by
    intro z hz'; rcases List.mem_append.mp hz' with h | h
    · exact hy z h
    · exact hz _ z h
  have hlx' : x'.length = P.nfma := by simp [x']; omega
  have hly' : y'.length = P.nfma := by simp [y']; omega
  let Ea : ℤ → P.a.Word := fun z => (P.a.encodeExact (z : ℚ)).getD 0
  let Eb : ℤ → P.b.Word := fun z => (P.b.encodeExact (z : ℚ)).getD 0
  have hEa : ∀ z ∈ x', P.a.encodeExact (z : ℚ) = some (Ea z) ∧ IntWord P.a (Ea z) ∧
      P.a.wordValue (Ea z) = z := by
    intro z hz
    obtain ⟨w, hw, hi, hv⟩ := hea z (hx' z hz)
    have : Ea z = w := by simp [Ea, hw]
    rw [this]; exact ⟨hw, hi, hv⟩
  have hEb : ∀ z ∈ y', P.b.encodeExact (z : ℚ) = some (Eb z) ∧ IntWord P.b (Eb z) ∧
      P.b.wordValue (Eb z) = z := by
    intro z hz
    obtain ⟨w, hw, hi, hv⟩ := heb z (hy' z hz)
    have : Eb z = w := by simp [Eb, hw]
    rw [this]; exact ⟨hw, hi, hv⟩
  have hmx : x'.mapM (fun z : ℤ => P.a.encodeExact (z : ℚ)) = some (x'.map Ea) :=
    mapM_eq_some_map fun z hz => (hEa z hz).1
  have hmy : y'.mapM (fun z : ℤ => P.b.encodeExact (z : ℚ)) = some (y'.map Eb) :=
    mapM_eq_some_map fun z hz => (hEb z hz).1
  obtain ⟨hprod, _⟩ := encoded_products Ea Eb x' y' (fun z hz => (hEa z hz).2.2)
    (fun z hz => (hEb z hz).2.2)
  have hdot : dotZ x' y' = dotZ x y := by
    simp only [x', y']
    rw [dotZ_append _ _ hlen, hlen, dotZ_replicate_zero, Int.add_zero]
  have hia : ∀ w ∈ x'.map Ea, IntWord P.a w := by
    intro w hw; obtain ⟨z, hz, rfl⟩ := List.mem_map.mp hw; exact (hEa z hz).2.1
  have hib : ∀ w ∈ y'.map Eb, IntWord P.b w := by
    intro w hw; obtain ⟨z, hz, rfl⟩ := List.mem_map.mp hw; exact (hEb z hz).2.1
  have hla : (x'.map Ea).length = P.nfma := by simp [hlx']
  have hlb : (y'.map Eb).length = P.nfma := by simp [hly']
  -- the block sum is at most `N_FMA · 2^(2b)`
  have hbud : Rat.abs ((dotZ x' y' : ℤ) : ℚ) ≤ ((P.nfma * 2 ^ (2 * b) : ℕ) : ℚ) := by
    rw [abs_intCast]
    apply Rat.natCast_le_natCast.mpr
    refine Nat.le_trans (natAbs_dotZ_le _ _) (Nat.le_trans (dotAbs_le _ _ _ _ hx' hy') ?_)
    rw [hlx', ← Nat.pow_add, show b + b = 2 * b by omega]
    exact Nat.le_refl _
  have hrun : mcTwoPass P (x'.map Ea) (y'.map Eb) = some (dotZ x' y' : ℚ) := by
    rw [← hprod]
    obtain ⟨hsub, hcfg⟩ := hok
    rcases hcfg with ⟨hacc, hpo, hK⟩ | ⟨hacc, hneab, hlate, hcz, h2b, hK⟩
    · refine mcTwoPass_exact_cr hacc hpo hsub hfa hfb hla hlb hia hib ?_
      rw [hprod]
      refine Rat.le_trans hbud ?_
      rw [two_pow_natCast]; exact Rat.natCast_le_natCast.mpr hK
    · refine mcTwoPass_exact_ga hacc hneab hlate hcz hsub hfa hfb hla hlb hia hib ?_ ?_
      · intro v hv
        obtain ⟨w, hw, w', hw', rfl⟩ := mem_zipWith' hv
        obtain ⟨z, hz, rfl⟩ := List.mem_map.mp hw
        obtain ⟨z', hz', rfl⟩ := List.mem_map.mp hw'
        rw [(hEa z hz).2.2, (hEb z' hz').2.2, ← Rat.intCast_mul, abs_intCast, two_pow_natCast]
        apply Rat.natCast_le_natCast.mpr
        rw [Int.natAbs_mul]
        calc z.natAbs * z'.natAbs ≤ 2 ^ b * 2 ^ b := Nat.mul_le_mul (hx' z hz) (hy' z' hz')
          _ = 2 ^ (2 * b) := by rw [← Nat.pow_add]; congr 1; omega
          _ ≤ 2 ^ 24 := Nat.pow_le_pow_right (by decide) h2b
      · rw [hprod]
        refine Rat.le_trans hbud ?_
        rw [two_pow_natCast]; exact Rat.natCast_le_natCast.mpr hK
  have hmx' : (x ++ List.replicate (P.nfma - x.length) 0).mapM
      (fun z : ℤ => P.a.encodeExact (z : ℚ)) = some (x'.map Ea) := hmx
  have hmy' : (y ++ List.replicate (P.nfma - y.length) 0).mapM
      (fun z : ℤ => P.b.encodeExact (z : ℚ)) = some (y'.map Eb) := hmy
  unfold mcGroup2
  simp only [hmx', hmy', Option.bind_eq_bind, Option.bind_some]
  rw [hrun, hdot]; rfl

/-! ## Instances -/

/-- **CDNA 3 fp16 with full groups**: eight products of `11`-bit slices (`8 · 2^22 = 2^25`), two
passes each, exact for every length. -/
theorem cdna3F16_exactOn2 (B : ℕ) : (mcMultiplier2 cdna3F16).ExactOn 11 B :=
  mcMultiplier2_exactOn (by decide) binary16_small binary16_small (by decide)
    (binary16_encodesInts (Nat.le_refl _)) (binary16_encodesInts (Nat.le_refl _)) B

/-- **The SFMA with `24`-bit slices**: one product per block, two passes (TwoProdFMA), exact for
every length; one pass allows only `12`-bit slices. -/
theorem sfma_exactOn2 (B : ℕ) : (mcMultiplier2 sfmaF32).ExactOn 24 B :=
  mcMultiplier2_exactOn (by decide) binary32_small binary32_small (by decide)
    (binary32_encodesInts (Nat.le_refl _)) (binary32_encodesInts (Nat.le_refl _)) B

theorem cdna1F16_exactOn2 (B : ℕ) : (mcMultiplier2 cdna1F16).ExactOn 11 B :=
  mcMultiplier2_exactOn (by decide) binary16_small binary16_small (by decide)
    (binary16_encodesInts (Nat.le_refl _)) (binary16_encodesInts (Nat.le_refl _)) B

theorem cdna3XF32_exactOn2 (B : ℕ) : (mcMultiplier2 cdna3XF32).ExactOn 11 B :=
  mcMultiplier2_exactOn (P := cdna3XF32) (by decide) trivial trivial (by decide)
    (xf32_encodesInts_le (Nat.le_refl _)) (xf32_encodesInts_le (Nat.le_refl _)) B

/-! ## When a second pass is needed, and when it fails -/

/-- **Where one pass is not enough.** A full group of the widest slices each path encodes fits the
`2^24` budget on CDNA 1 and 2 (fp16 and bf16) and CDNA 3 bf16 and XF32; it does not on CDNA 3 fp16
(`8 · 2^22 = 2^25`), and on the SFMA a single product of slices wider than `12` bits exceeds it. -/
theorem full_groups_fit :
    cdna1F16.nfma * 2 ^ 22 ≤ 2 ^ 24 ∧ cdna1BF16.nfma * 2 ^ 16 ≤ 2 ^ 24 ∧
    cdna2F16.nfma * 2 ^ 22 ≤ 2 ^ 24 ∧ cdna2BF16.nfma * 2 ^ 16 ≤ 2 ^ 24 ∧
    cdna2BF16_1k.nfma * 2 ^ 16 ≤ 2 ^ 24 ∧ cdna3BF16.nfma * 2 ^ 16 ≤ 2 ^ 24 ∧
    cdna3XF32.nfma * 2 ^ 22 ≤ 2 ^ 24 ∧
    ¬ cdna3F16.nfma * 2 ^ 22 ≤ 2 ^ 24 ∧ ¬ sfmaF32.nfma * 2 ^ 26 ≤ 2 ^ 24 := by
  decide

/-- **CDNA 3 fp16, a full group recovered.** `7 × 2047² = 29331463`, which one pass returns as
`29331464` (`cdna3F16_full_group`); two passes return it exactly. -/
theorem cdna3F16_twoPass_full_group :
    mcTwoPass cdna3F16 (List.replicate 7 (0x67FF : BitVec 16) ++ [0]) (List.replicate 8 0x67FF) =
      some 29331463 := by
  decide +kernel

/-- **The SFMA's two passes are TwoProdFMA.** `(2^24 − 1)² = 2^48 − 2^25 + 1`: one pass rounds it to
`2^48 − 2^25`, two passes return it exactly (`0x4B7FFFFF` is `2^24 − 1`). -/
theorem sfma_twoProd :
    (blockBits (P := sfmaF32) ⟨[(0x4B7FFFFF : BitVec 32)], [0x4B7FFFFF], 0⟩).map value32 =
      .ok (some 281474943156224) ∧
    mcTwoPass sfmaF32 [(0x4B7FFFFF : BitVec 32)] [0x4B7FFFFF] = some 281474943156225 ∧
    (16777215 * 16777215 : ℤ) = 281474943156225 := by
  decide +kernel

/-- **CDNA 2: two passes can fail.** Products `2^22` and `2^-14` (fp16 `0x6800 · 0x6800` and
`0x0400 · 0x3C00`): the pairwise tree rounds `2^22 + 2^-14` to `2^22` before `c` is added, so pass 2
from `c = −2^22` sees the same rounded node and returns `0`; two passes return `2^22`, not the exact
`2^22 + 2^-14`. On CDNA 1, which adds exactly, the same block is recovered. -/
theorem cdna2_twoPass_fails :
    mcTwoPass cdna2F16 [(0x6800 : BitVec 16), 0x0400, 0, 0] [0x6800, 0x3C00, 0, 0] =
      some (2 ^ (22 : ℕ)) ∧
    mcTwoPass cdna1F16 [(0x6800 : BitVec 16), 0x0400, 0, 0] [0x6800, 0x3C00, 0, 0] =
      some (2 ^ (22 : ℕ) + pow2 (-14)) := by
  decide +kernel

end Ozaki.MC
