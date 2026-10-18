import MatrixCore
import Ozaki

/-! # Exact integer blocks on the AMD Matrix Core model

The Ozaki schemes need the Matrix Core to multiply small integers exactly. On the model of
`MatrixCore`, a block computes `S_acc` by one of the paper's configurations and rounds it once to
binary32 with RNE. This file shows that for integer operands nothing is lost on three of them:

* `correct_rounding` (SFMA, CDNA 1): `S_acc` is the exact sum;
* `pair_wise_sum` (CDNA 2): every `fl{·}` of the pairwise sum rounds an integer partial sum, and
  flushing subnormals leaves integer operands unchanged;
* `global_alignment` (CDNA 3 fp16, bf16, XF32): products of exponent at most `24` are aligned to
  `24` mantissa bits, and both RD steps of the late addition of `c` act on integers.

`evalBlock_int`: integer operands and an integer `c` with `|c| + Σ|aᵢbᵢ| ≤ 2^24` give
`c + Σ aᵢbᵢ` exactly; `runBlocks_int` chains blocks through their binary32 outputs. As on the
Tensor Core, the bound is set by the binary32 output, not by an accumulator: a block of at most
`2^24` in total magnitude is exact whatever the alignment width. -/

open MatrixCore

namespace Ozaki.MC

/-! ## Bridges to the scheme library's arithmetic -/

theorem absQ_eq (x : ℚ) : absQ x = Rat.abs x := by
  unfold absQ; rw [abs_def]; split <;> split <;> grind

theorem pow2_eq (e : ℤ) : pow2 e = (2 : ℚ) ^ e := rfl

theorem sumQ_eq (xs : List ℚ) : sumQ xs = xs.sum := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [sumQ, ih]

/-! ## Binary32 rounding of integers -/

/-- RNE returns every binary32 value unchanged. -/
theorem rneValue_of_finite {x : ℚ} (h : FiniteValue32 x) : rneValue x = x := by
  by_cases hx : x = 0
  · subst hx; exact rneValue_zero
  have ha := absQ_pos hx
  have habs : FiniteValue32 (absQ x) := by unfold absQ; split; exact h.neg; exact h
  have hn := (rneMagnitude_nearest ha habs).1
  rw [show absQ x - absQ x = 0 by grind, show absQ (0 : ℚ) = 0 from rfl] at hn
  have hz : absQ (absQ x - rneMagnitude (absQ x)) = 0 :=
    Rat.le_antisymm hn (absQ_nonneg _)
  have hm : rneMagnitude (absQ x) = absQ x := by
    have := absQ_eq_zero.mp hz; grind
  unfold rneValue
  split
  · rename_i hneg; rw [hm, absQ_of_neg hneg]; grind
  · rename_i hnn; rw [hm, absQ_of_nonneg (by grind)]

/-- Every integer of magnitude at most `2^24` is a binary32 value. -/
theorem int_finiteValue32 (z : ℤ) (h : z.natAbs ≤ 2 ^ 24) : FiniteValue32 (z : ℚ) := by
  by_cases hz : z.natAbs < 16777216
  · exact ⟨z, 23, by omega, by omega, hz, by rw [show (23 : ℤ) - 23 = 0 by rfl, pow2_zero,
      Rat.mul_one]⟩
  · refine ⟨z / 2, 24, by omega, by omega, by omega, ?_⟩
    have hz2 : z = z / 2 * 2 := by omega
    rw [show (24 : ℤ) - 23 = 1 by rfl, pow2_one]
    conv => lhs; rw [hz2]
    rw [Rat.intCast_mul, Rat.intCast_ofNat]

theorem natAbs_le_cast {z : ℤ} {n : ℕ} (h : z.natAbs ≤ n) : absQ (z : ℚ) ≤ (n : ℚ) := by
  rw [absQ_intCast]; exact Rat.natCast_le_natCast.mpr h

theorem one_le_absQ_int {z : ℤ} (h : z ≠ 0) : 1 ≤ absQ (z : ℚ) := by
  rw [absQ_intCast]
  have : 1 ≤ z.natAbs := by omega
  exact_mod_cast this

/-- Binary32 RNE of an integer within `2^24` is that integer. -/
theorem rne32_int (z : ℤ) (h : z.natAbs ≤ 2 ^ 24) :
    ∃ w, rne32 (z : ℚ) = some w ∧ value32 w = some (z : ℚ) := by
  have hlt : absQ (z : ℚ) < overflowThreshold32 := by
    have h1 := natAbs_le_cast h
    have h2 : (((2 ^ 24 : ℕ)) : ℚ) < overflowThreshold32 := by decide +kernel
    exact lt_of_le_of_lt' h1 h2
  obtain ⟨w, hw⟩ := Option.isSome_iff_exists.mp ((rne32_isSome_iff _).mpr hlt)
  exact ⟨w, hw, by rw [rne32_value hw, rneValue_of_finite (int_finiteValue32 z h)]⟩

/-- `fl{·}`, with or without flushing subnormal results, returns an integer within `2^24`. -/
theorem fl32_int (ftz : Bool) (z : ℤ) (h : z.natAbs ≤ 2 ^ 24) :
    ∃ w, fl32 ftz (z : ℚ) = some w ∧ value32 w = some (z : ℚ) := by
  obtain ⟨w, hw, hv⟩ := rne32_int z h
  refine ⟨w, ?_, hv⟩
  have hs : isSubnormal32 w = false := by
    cases hsub : isSubnormal32 w
    · rfl
    · exfalso
      obtain ⟨hne, hlt⟩ := (value32_subnormal hv).1 hsub
      have hz : z ≠ 0 := fun h0 => hne (by rw [h0]; rfl)
      have h1 := one_le_absQ_int hz
      have h2 : pow2 (-126) < 1 := by decide +kernel
      grind
  unfold fl32; rw [hw]; simp [hs]

theorem flValue_int (ftz : Bool) (z : ℤ) (h : z.natAbs ≤ 2 ^ 24) :
    flValue ftz (z : ℚ) = some (z : ℚ) := by
  obtain ⟨w, hw, hv⟩ := fl32_int ftz z h
  unfold flValue; rw [hw]; exact hv

/-! ## Integer operands -/

/-- Formats whose subnormal values lie below `1` (exponent at most `0`): integer operands are
then zero or normal. Every format in use qualifies. -/
def smallSubnormals : InputFormat → Prop
  | .packed f => f.emin ≤ 0
  | .xf32 => True

theorem unpackFields_sub (f : Format) (neg : Bool) (E M : ℕ)
    (h : (f.unpackFields neg E M).m < 2 ^ (f.unpackFields neg E M).t) :
    (f.unpackFields neg E M).e = f.emin := by
  by_cases hE : E = 0 <;> simp [Format.unpackFields, hE] at h ⊢
  omega

theorem decodeNat_sub {f : Format} {n : ℕ} {u : Unpacked} (h : f.decodeNat n = .finite u)
    (hm : u.m < 2 ^ u.t) : u.e = f.emin := by
  unfold Format.decodeNat at h
  dsimp only at h
  split at h
  · split at h
    · split at h <;> simp at h
    · simp only [Datum.finite.injEq] at h; subst h; exact unpackFields_sub _ _ _ _ hm
  · split at h
    · simp at h
    · simp only [Datum.finite.injEq] at h; subst h; exact unpackFields_sub _ _ _ _ hm

/-- A subnormal operand has exponent at most `0`. -/
theorem read_sub {i : InputFormat} (hi : smallSubnormals i) {w : i.Word} {u : Unpacked}
    (h : (i.read w).toFinite = some u) (hm : u.m < 2 ^ u.t) : u.e ≤ 0 := by
  cases i with
  | packed f =>
    simp only [InputFormat.read, Format.decode] at h
    cases hd : f.decodeNat w.toNat with
    | finite v =>
      rw [hd] at h; simp only [Datum.toFinite, Option.some.injEq] at h; subst h
      rw [decodeNat_sub hd hm]; exact hi
    | infinity _ => rw [hd] at h; simp [Datum.toFinite] at h
    | nan => rw [hd] at h; simp [Datum.toFinite] at h
  | xf32 =>
    simp only [InputFormat.read] at h
    cases hd : fp32.decode w with
    | finite v =>
      rw [hd] at h; simp only [Datum.toFinite, Option.some.injEq] at h; subst h
      obtain ⟨_, _, _, _, hn⟩ := decode32_finite_fields hd
      simp only [InputFormat.truncateXF32] at hm ⊢
      have : v.m < 8388608 := by
        have := (Nat.div_lt_iff_lt_mul (Nat.two_pow_pos 13)).mp hm; omega
      omega
    | infinity _ => rw [hd] at h; simp [Datum.toFinite] at h
    | nan => rw [hd] at h; simp [Datum.toFinite] at h

/-- `2^e ≤ |value|` for a normal significand. -/
theorem pow2_le_absQ {u : Unpacked} (h : 2 ^ u.t ≤ u.m) : pow2 u.e ≤ absQ u.value := by
  rw [Unpacked.absQ_value]
  have h1 : ((2 ^ u.t : ℕ) : ℚ) ≤ (u.m : ℚ) := Rat.natCast_le_natCast.mpr h
  have h2 := Rat.mul_le_mul_of_nonneg_right h1 (Rat.le_of_lt (pow2_pos (u.e - u.t)))
  rwa [← pow2_natCast, ← pow2_add, show (u.t : ℤ) + (u.e - u.t) = u.e by omega] at h2

/-- An integer value whose subnormal significands have exponent at most `0` is zero or normal. -/
theorem int_normal {u : Unpacked} (hsub : u.m < 2 ^ u.t → u.e ≤ 0) {z : ℤ} (hz : u.value = z) :
    u.m = 0 ∨ 2 ^ u.t ≤ u.m := by
  by_cases hm : u.m < 2 ^ u.t
  · left
    have he := hsub hm
    have hlt : absQ u.value < 1 := by
      rw [Unpacked.absQ_value]
      have h1 : (u.m : ℚ) < ((2 ^ u.t : ℕ) : ℚ) := Rat.natCast_lt_natCast.mpr hm
      have h2 := Rat.mul_lt_mul_of_pos_right h1 (pow2_pos (u.e - u.t))
      rw [← pow2_natCast, ← pow2_add, show (u.t : ℤ) + (u.e - u.t) = u.e by omega] at h2
      have h3 : pow2 u.e ≤ 1 := by have := pow2_le_of_le he; rwa [pow2_zero] at this
      grind
    have hz0 : z = 0 := by
      apply Classical.byContradiction
      intro h0
      have := one_le_absQ_int h0
      rw [← hz] at this; grind
    have hv : u.value = 0 := by rw [hz, hz0]; rfl
    exact (Unpacked.value_eq_zero_iff u).mp hv
  · right; omega

/-- An operand whose value is an integer, with a significand that is zero or normal. -/
def IntOperand (u : Unpacked) : Prop := (∃ z : ℤ, u.value = z) ∧ (u.m = 0 ∨ 2 ^ u.t ≤ u.m)

theorem IntOperand.mul {a b : Unpacked} (ha : IntOperand a) (hb : IntOperand b) :
    IntOperand (a.mul b) := by
  obtain ⟨⟨za, hza⟩, hna⟩ := ha
  obtain ⟨⟨zb, hzb⟩, hnb⟩ := hb
  refine ⟨⟨za * zb, by rw [Unpacked.value_mul, hza, hzb, Rat.intCast_mul]⟩, ?_⟩
  simp only [Unpacked.mul]
  rcases hna with h | h
  · left; rw [h, Nat.zero_mul]
  · rcases hnb with h' | h'
    · left; rw [h', Nat.mul_zero]
    · right; rw [Nat.pow_add]; exact Nat.mul_le_mul h h'

theorem IntOperand.flush {u : Unpacked} (h : IntOperand u) : u.flush = u := by
  unfold Unpacked.flush
  split
  · rename_i hm
    rcases h.2 with h0 | h0
    · cases u; simp_all
    · omega
  · rfl

/-- A nonzero integer operand of magnitude at most `2^U` has exponent at most `U`. -/
theorem IntOperand.exp_le {u : Unpacked} (h : IntOperand u) (hm : u.m ≠ 0) {U : ℤ}
    (hv : absQ u.value ≤ pow2 U) : u.e ≤ U := by
  rcases h.2 with h0 | h0
  · exact absurd h0 hm
  · exact pow2_le_iff.mp (Rat.le_trans (pow2_le_absQ h0) hv)

theorem IntOperand.onGrid {u : Unpacked} (h : IntOperand u) {g : ℤ} (hg : g ≤ 0) :
    OnGrid u.value g := by
  obtain ⟨⟨z, hz⟩, _⟩ := h
  rw [hz]
  exact OnGrid.mono ⟨z, by rw [pow2_zero, Rat.mul_one]⟩ hg

/-! ## Integer lists -/

theorem intList (l : List ℚ) (h : ∀ q ∈ l, ∃ z : ℤ, q = z) :
    ∃ zs : List ℤ, l = zs.map fun z : ℤ => (z : ℚ) := by
  induction l with
  | nil => exact ⟨[], rfl⟩
  | cons q l ih =>
    obtain ⟨z, hz⟩ := h q (by simp)
    obtain ⟨zs, hzs⟩ := ih (fun q' hq => h q' (by simp [hq]))
    exact ⟨z :: zs, by simp [hz, hzs]⟩

theorem natAbs_sum_le (zs : List ℤ) : zs.sum.natAbs ≤ (zs.map Int.natAbs).sum := by
  induction zs with
  | nil => simp
  | cons z zs ih =>
    simp only [List.sum_cons, List.map_cons]
    have := Int.natAbs_add_le z zs.sum
    omega

theorem sumQ_cast (zs : List ℤ) : sumQ (zs.map fun z : ℤ => (z : ℚ)) = ((zs.sum : ℤ) : ℚ) := by
  induction zs with
  | nil => rfl
  | cons z zs ih => simp only [List.map_cons, sumQ, ih, List.sum_cons, Rat.intCast_add]

theorem sumQ_absQ_cast (zs : List ℤ) :
    sumQ ((zs.map fun z : ℤ => (z : ℚ)).map absQ) = (((zs.map Int.natAbs).sum : ℕ) : ℚ) := by
  induction zs with
  | nil => rfl
  | cons z zs ih =>
    simp only [List.map_cons, sumQ, ih, List.sum_cons, Rat.natCast_add, absQ_intCast]

/-! ## The pairwise sum -/

/-- The pairwise sum of integers whose magnitudes total at most `2^24` is their exact sum. -/
theorem pairwiseGroupSum_int (ftz : Bool) : ∀ (depth : ℕ) (zs : List ℤ), zs.length ≤ depth + 1 →
    (zs.map Int.natAbs).sum ≤ 2 ^ 24 →
    pairwiseGroupSum ftz depth (zs.map fun z : ℤ => (z : ℚ)) = some ((zs.sum : ℤ) : ℚ)
  | _, [], _, _ => by simp [pairwiseGroupSum]
  | _, [z], _, _ => by simp [pairwiseGroupSum]
  | 0, _ :: _ :: _, hl, _ => by simp at hl
  | depth + 1, z1 :: z2 :: rest, hl, hb => by
    generalize hzs : z1 :: z2 :: rest = zs at hl hb
    have h2 : 2 ≤ zs.length := by rw [← hzs]; simp
    have hunfold : pairwiseGroupSum ftz (depth + 1) (zs.map fun z : ℤ => (z : ℚ)) =
        (pairwiseGroupSum ftz depth ((zs.take (zs.length / 2)).map fun z : ℤ => (z : ℚ))).bind fun u =>
          (pairwiseGroupSum ftz depth ((zs.drop (zs.length / 2)).map fun z : ℤ => (z : ℚ))).bind fun v =>
            flValue ftz (u + v) := by
      rw [← hzs, List.map_cons, List.map_cons, pairwiseGroupSum]
      simp only [List.length_cons, List.map_take, List.map_drop, List.map_cons, List.length_map,
        Option.bind_eq_bind]
      all_goals simp
    have htd := List.take_append_drop (zs.length / 2) zs
    have hsplit : (zs.map Int.natAbs).sum = ((zs.take (zs.length / 2)).map Int.natAbs).sum +
        ((zs.drop (zs.length / 2)).map Int.natAbs).sum := by
      conv => lhs; rw [← htd]
      rw [List.map_append, List.sum_append]
    have hsum : zs.sum = (zs.take (zs.length / 2)).sum + (zs.drop (zs.length / 2)).sum := by
      conv => lhs; rw [← htd]
      rw [List.sum_append]
    rw [hunfold, pairwiseGroupSum_int ftz depth _ (by simp; omega) (by omega),
      pairwiseGroupSum_int ftz depth _ (by simp; omega) (by omega)]
    simp only [Option.bind_some]
    rw [← Rat.intCast_add, ← hsum]
    exact flValue_int ftz _ (Nat.le_trans (natAbs_sum_le zs) hb)

/-! ## Prepared blocks of integers -/

/-- A prepared block of integer operands and an integer `c`, with `|c| + Σ|p_ℓ| ≤ 2^24`. -/
structure IntPrepared (x : Prepared) : Prop where
  a : ∀ u ∈ x.a, IntOperand u
  b : ∀ u ∈ x.b, IntOperand u
  c : IntOperand x.c
  bound : absQ x.c.value + sumQ (x.p.map fun p => absQ p.value) ≤ pow2 24

theorem natAbs_le_of_absQ {z : ℤ} (h : absQ (z : ℚ) ≤ pow2 24) : z.natAbs ≤ 2 ^ 24 := by
  rw [absQ_intCast, show (24 : ℤ) = ((24 : ℕ) : ℤ) from rfl, pow2_natCast] at h
  exact Rat.natCast_le_natCast.mp h

theorem sum_absQ_nonneg (x : Prepared) : 0 ≤ sumQ (x.p.map fun p => absQ p.value) := by
  rw [sumQ_eq]; exact Ozaki.sum_nonneg fun _ _ => absQ_nonneg _

namespace IntPrepared

variable {x : Prepared} (h : IntPrepared x)
include h

theorem p : ∀ q ∈ x.p, IntOperand q := by
  intro q hq
  obtain ⟨a, ha, b, hb, rfl⟩ := mem_zipWith' hq
  exact (h.a a ha).mul (h.b b hb)

theorem p_le : ∀ q ∈ x.p, absQ q.value ≤ pow2 24 := by
  intro q hq
  have h1 : absQ q.value ≤ sumQ (x.p.map fun p => absQ p.value) := by
    rw [sumQ_eq]
    exact le_sum_of_mem (l := x.p) (f := fun p => absQ p.value) (fun _ _ => absQ_nonneg _) hq
  have := h.bound; have := absQ_nonneg x.c.value
  grind

theorem c_le : absQ x.c.value ≤ pow2 24 := by
  have := h.bound; have := sum_absQ_nonneg x; grind

theorem flushed : x.flushed = x := by
  obtain ⟨a, b, c⟩ := x
  simp only [Prepared.flushed, Prepared.mk.injEq]
  refine ⟨?_, ?_, h.c.flush⟩
  · conv => rhs; rw [← List.map_id a]
    exact List.map_congr_left fun u hu => (h.a u hu).flush
  · conv => rhs; rw [← List.map_id b]
    exact List.map_congr_left fun u hu => (h.b u hu).flush

theorem productOverflows : x.productOverflows = false := by
  unfold Prepared.productOverflows
  apply List.any_eq_false.mpr
  intro q hq hle
  have h1 := h.p_le q hq
  have h2 : pow2 24 < pow2 128 := pow2_lt_of_lt (by decide)
  have := of_decide_eq_true hle
  grind

/-- The products as a list of integers within the exactness bound. -/
theorem ints : ∃ zs : List ℤ, x.p.map Unpacked.value = zs.map (fun z : ℤ => (z : ℚ)) ∧
    (zs.map Int.natAbs).sum ≤ 2 ^ 24 := by
  obtain ⟨zs, hzs⟩ := intList (x.p.map Unpacked.value) (by
    intro q hq
    obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hq
    obtain ⟨⟨z, hz⟩, _⟩ := h.p r hr
    exact ⟨z, hz⟩)
  refine ⟨zs, hzs, ?_⟩
  have hs := sumQ_absQ_cast zs
  rw [← hzs, List.map_map] at hs
  have hb : sumQ (x.p.map fun p => absQ p.value) ≤ pow2 24 := by
    have := h.bound; have := absQ_nonneg x.c.value; grind
  have : sumQ (List.map (absQ ∘ Unpacked.value) x.p) = sumQ (x.p.map fun p => absQ p.value) := rfl
  rw [this] at hs
  rw [hs, show (24 : ℤ) = ((24 : ℕ) : ℤ) from rfl, pow2_natCast] at hb
  exact Rat.natCast_le_natCast.mp hb

theorem c_int : ∃ z : ℤ, x.c.value = z := h.c.1

end IntPrepared

/-- CDNA 2: the pairwise sum of integer products is their exact sum. -/
theorem pairwiseSum_int (P : Model) {x : Prepared} (h : IntPrepared x) :
    pairwiseSum P x = some x.exact := by
  have hx' : (if P.subnormals then x else x.flushed) = x := by
    split
    · rfl
    · exact h.flushed
  obtain ⟨zs, hzs, hb⟩ := h.ints
  have hps : x.p.mapM (fun p => flValue (!P.subnormals) p.value) =
      some (zs.map fun z : ℤ => (z : ℚ)) := by
    rw [← hzs]
    refine Ozaki.mapM_eq_some_map fun q hq => ?_
    obtain ⟨⟨z, hz⟩, _⟩ := h.p q hq
    rw [hz]
    exact flValue_int _ z (natAbs_le_of_absQ (by rw [← hz]; exact h.p_le q hq))
  have htree := pairwiseGroupSum_int (!P.subnormals) zs.length zs (by omega) hb
  unfold pairwiseSum
  simp only [hx', hps, Option.bind_eq_bind, Option.bind_some, List.length_map, htree]
  unfold Prepared.exact
  rw [hzs, sumQ_cast]
  congr 1
  grind

theorem foldl_maxExpStep_upper (U : ℤ) :
    ∀ (ps : List Unpacked) (acc : Option ℤ), (∀ v, acc = some v → v ≤ U) →
      (∀ p ∈ ps, p.m ≠ 0 → p.e ≤ U) → ∀ e, ps.foldl maxExpStep acc = some e → e ≤ U
  | [], acc, hacc, _, e, he => hacc e he
  | q :: qs, acc, hacc, hps, e, he => by
    simp only [List.foldl_cons] at he
    refine foldl_maxExpStep_upper U qs _ ?_ (fun p hp => hps p (by simp [hp])) e he
    intro v hv
    unfold maxExpStep at hv
    split at hv
    · exact hacc v hv
    · rename_i hq
      have hqe := hps q (by simp) hq
      cases acc with
      | none => simp at hv; omega
      | some w => have := hacc w rfl; simp at hv; omega

theorem maxExp_upper {ps : List Unpacked} {U : ℤ} (hps : ∀ p ∈ ps, p.m ≠ 0 → p.e ≤ U) :
    ∀ e, maxExp ps = some e → e ≤ U :=
  foldl_maxExpStep_upper U ps none (by simp) hps

/-- CDNA 3 (`global_alignment` with the paper's late-`c` parameters): integer blocks are exact. -/
theorem alignedAccumulation_int {P : Model} (hacc : P.accumulation = .globalAlignment)
    (hpadding : 1 ≤ P.padding) (hlate : P.late = {}) (hcz : P.cZeroExp = some (-126)) {x : Prepared}
    (h : IntPrepared x) : alignedAccumulation P x = x.exact := by
  have hprod := h.p
  have he24 : ∀ q ∈ x.p, q.m ≠ 0 → q.e ≤ 24 := fun q hq hm => (hprod q hq).exp_le hm (h.p_le q hq)
  obtain ⟨zs, hzs, hzb⟩ := h.ints
  have hS : sumQ (x.p.map Unpacked.value) = ((zs.sum : ℤ) : ℚ) := by rw [hzs, sumQ_cast]
  -- the product sum: truncation to `23 + padding ≥ 24` mantissa bits is exact
  have hal : productSum P x.p = alignedSum P.padding x.p := by unfold productSum; rw [hacc]
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
  have hcE : ∀ eC, cExp P x.c = some eC → eC ≤ 24 := by
    intro eC he
    unfold cExp at he
    split at he
    · rw [hcz] at he; cases he; omega
    · rename_i hm; cases he; exact h.c.exp_le hm h.c_le
  obtain ⟨zc, hzc⟩ := h.c_int
  have hT : ∀ T : ℤ, absQ (T : ℚ) ≤ pow2 24 → normalizeRD P.late.accMantissaBits (T : ℚ) = T := by
    intro T hT
    unfold normalizeRD
    split
    · rename_i h0; rw [h0]
    · rename_i h0
      have hpos := absQ_pos h0
      have hlog : log2Floor (absQ (T : ℚ)) ≤ 24 :=
        pow2_le_iff.mp (Rat.le_trans (log2Floor_spec hpos).1 hT)
      have hn : normExp (absQ (T : ℚ)) ≤ 24 := by unfold normExp; omega
      have hacc31 : P.late.accMantissaBits = 31 := by rw [hlate]
      exact rdGrid_of_onGrid (OnGrid.mono ⟨T, by rw [pow2_zero, Rat.mul_one]⟩ (by omega))
  have hsumbound : absQ ((zs.sum + zc : ℤ) : ℚ) ≤ pow2 24 := by
    have h1 := natAbs_sum_le zs
    have h2 := h.bound
    rw [Rat.intCast_add]
    have h3 := absQ_add_le ((zs.sum : ℤ) : ℚ) (zc : ℚ)
    rw [← hzc] at h3 ⊢
    have h4 : absQ ((zs.sum : ℤ) : ℚ) ≤ sumQ (x.p.map fun p => absQ p.value) := by
      rw [absQ_intCast]
      have hs := sumQ_absQ_cast zs
      rw [← hzs, List.map_map] at hs
      have : sumQ (List.map (absQ ∘ Unpacked.value) x.p) =
          sumQ (x.p.map fun p => absQ p.value) := rfl
      rw [this] at hs
      rw [hs]; exact Rat.natCast_le_natCast.mpr h1
    grind
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
    simp only [rdMantissa]
    rw [rdGrid_of_onGrid (OnGrid.mono ⟨zs.sum, by rw [pow2_zero, Rat.mul_one]⟩ (by omega)), hzc,
      ← Rat.intCast_add]
    have := hT (zs.sum + zc) hsumbound
    rw [hlate] at this
    rw [this]
    unfold Prepared.exact
    rw [hS, hzc, Rat.intCast_add]

/-- The configurations on which integer blocks are exact: correct rounding (SFMA, CDNA 1), the
pairwise sum (CDNA 2), and global alignment with the paper's CDNA 3 parameters. -/
def ExactConfig (P : Model) : Prop :=
  P.accumulation = .correctRounding ∨ P.accumulation = .pairWiseSum ∨
    (P.accumulation = .globalAlignment ∧ 1 ≤ P.padding ∧ P.late = {} ∧ P.cZeroExp = some (-126))

/-- **Exact accumulation.** On an exact configuration, `S_acc` of an integer block is its exact
sum `Σ p_ℓ + c`. -/
theorem accumulate_int {P : Model} (hP : ExactConfig P) {x : Prepared} (h : IntPrepared x) :
    accumulate P x = .ok x.exact := by
  unfold accumulate
  rw [h.productOverflows, Bool.and_false]
  simp only [Bool.false_eq_true, ↓reduceIte]
  rcases hP with hP | hP | ⟨hP, hn, hl, hc⟩
  · rw [hP]
  · rw [hP]; simp only [pairwiseSum_int P h]
  · rw [hP]; simp only [alignedAccumulation_int hP hn hl hc h]

/-! ## Encoded blocks -/

/-- A finite operand word whose value is an integer. -/
def IntWord (i : InputFormat) (w : i.Word) : Prop :=
  ∃ u, (i.read w).toFinite = some u ∧ ∃ z : ℤ, u.value = z

/-- `Σ |aᵢ bᵢ|` of operand words. -/
def wordDotAbs (P : Model) (a : List P.a.Word) (b : List P.b.Word) : ℚ :=
  sumQ (List.zipWith (fun x y => absQ (P.a.wordValue x * P.b.wordValue y)) a b)

theorem mapM_exists {f : α → Option β} :
    ∀ l : List α, (∀ a ∈ l, ∃ b, f a = some b) → ∃ l', l.mapM f = some l'
  | [], _ => ⟨[], rfl⟩
  | a :: l, h => by
    obtain ⟨b, hb⟩ := h a (by simp)
    obtain ⟨l', hl'⟩ := mapM_exists l (fun a' ha => h a' (by simp [ha]))
    exact ⟨b :: l', by simp [List.mapM_cons, hb, hl']⟩

/-- Pairing decoded operands is pairing the values of their words. -/
theorem mapM_zipWith {P : Model} (g : ℚ → ℚ → ℚ) :
    ∀ (xa : List P.a.Word) (xb : List P.b.Word) (A B : List Unpacked),
      xa.mapM (fun w => (P.a.read w).toFinite) = some A →
      xb.mapM (fun w => (P.b.read w).toFinite) = some B →
      List.zipWith (fun u v => g u.value v.value) A B =
        List.zipWith (fun w w' => g (P.a.wordValue w) (P.b.wordValue w')) xa xb
  | [], xb, A, B, ha, _ => by simp at ha; subst ha; simp
  | _ :: _, [], A, B, _, hb => by simp at hb; subst hb; simp
  | x :: xs, y :: ys, A, B, ha, hb => by
    simp only [List.mapM_cons] at ha hb
    cases hx : (P.a.read x).toFinite with
    | none => rw [hx] at ha; simp at ha
    | some u =>
      cases hxs : xs.mapM (fun w => (P.a.read w).toFinite) with
      | none => rw [hx, hxs] at ha; simp at ha
      | some us =>
        cases hy : (P.b.read y).toFinite with
        | none => rw [hy] at hb; simp at hb
        | some v =>
          cases hys : ys.mapM (fun w => (P.b.read w).toFinite) with
          | none => rw [hy, hys] at hb; simp at hb
          | some vs =>
            rw [hx, hxs] at ha; rw [hy, hys] at hb
            simp at ha hb; subst ha; subst hb
            simp only [List.zipWith_cons_cons, mapM_zipWith g xs ys us vs hxs hys,
              InputFormat.wordValue, hx, hy, Option.map_some, Option.getD_some]

theorem wordValue_of_read {i : InputFormat} {w : i.Word} {u : Unpacked}
    (h : (i.read w).toFinite = some u) : i.wordValue w = u.value := by
  unfold InputFormat.wordValue; rw [h]; rfl

/-- The products of integer words add up to an integer within the sum of their magnitudes. -/
theorem exactProducts_int {P : Model} :
    ∀ (a : List P.a.Word) (b : List P.b.Word), (∀ w ∈ a, IntWord P.a w) → (∀ w ∈ b, IntWord P.b w) →
      ∃ Z : ℤ, exactProducts P a b = Z ∧ absQ (Z : ℚ) ≤ wordDotAbs P a b
  | [], _, _, _ => ⟨0, rfl, by simp [wordDotAbs, sumQ]; decide⟩
  | _ :: _, [], _, _ => ⟨0, rfl, by simp [wordDotAbs, sumQ]; decide⟩
  | x :: xs, y :: ys, ha, hb => by
    obtain ⟨u, hu, zu, hzu⟩ := ha x (by simp)
    obtain ⟨v, hv, zv, hzv⟩ := hb y (by simp)
    obtain ⟨Z, hZ, hZb⟩ := exactProducts_int xs ys (fun w hw => ha w (by simp [hw]))
      (fun w hw => hb w (by simp [hw]))
    refine ⟨zu * zv + Z, ?_, ?_⟩
    · unfold exactProducts at hZ ⊢
      simp only [List.zipWith_cons_cons, sumQ, hZ, wordValue_of_read hu, wordValue_of_read hv,
        hzu, hzv, Rat.intCast_add, Rat.intCast_mul]
    · unfold wordDotAbs at hZb ⊢
      simp only [List.zipWith_cons_cons, sumQ, wordValue_of_read hu, wordValue_of_read hv, hzu, hzv]
      rw [Rat.intCast_add, Rat.intCast_mul]
      have := absQ_add_le ((zu : ℚ) * zv) (Z : ℚ)
      grind

theorem wordDotAbs_nonneg (P : Model) :
    ∀ (a : List P.a.Word) (b : List P.b.Word), 0 ≤ wordDotAbs P a b
  | [], _ => by simp [wordDotAbs, sumQ]
  | _ :: _, [] => by simp [wordDotAbs, sumQ]
  | x :: xs, y :: ys => by
    have := wordDotAbs_nonneg P xs ys
    unfold wordDotAbs at this ⊢
    simp only [List.zipWith_cons_cons, sumQ]
    have := absQ_nonneg (P.a.wordValue x * P.b.wordValue y)
    grind

theorem binary32_sub {w : F32} {u : Unpacked} (h : (fp32.decode w).toFinite = some u) :
    u.m < 2 ^ u.t → u.e ≤ 0 := by
  intro hm
  cases hd : fp32.decode w with
  | finite v =>
    rw [hd] at h; simp only [Datum.toFinite, Option.some.injEq] at h; subst h
    obtain ⟨ht, _, _, _, hn⟩ := decode32_finite_fields hd
    rw [ht] at hm
    have : v.m < 8388608 := hm
    omega
  | infinity _ => rw [hd] at h; simp [Datum.toFinite] at h
  | nan => rw [hd] at h; simp [Datum.toFinite] at h

/-- **Exact integer block.** On an exact configuration, integer operands and an integer `c` with
`|c| + Σ|aᵢbᵢ| ≤ 2^24` give the binary32 word of `c + Σ aᵢbᵢ`. -/
theorem evalBlock_int {P : Model} (hP : ExactConfig P) (hfa : smallSubnormals P.a)
    (hfb : smallSubnormals P.b) {x : BlockInput P} (hla : x.a.length = P.nfma)
    (hlb : x.b.length = P.nfma) (ha : ∀ w ∈ x.a, IntWord P.a w) (hb : ∀ w ∈ x.b, IntWord P.b w)
    {zc : ℤ} (hc : value32 x.c = some (zc : ℚ))
    (hbound : absQ (zc : ℚ) + wordDotAbs P x.a x.b ≤ pow2 24) :
    ∃ t, evalBlock x = .ok t ∧ value32 t.d = some ((zc : ℚ) + exactProducts P x.a x.b) := by
  obtain ⟨A, hA⟩ := mapM_exists x.a fun w hw => by
    obtain ⟨u, hu, _⟩ := ha w hw; exact ⟨u, hu⟩
  obtain ⟨B, hB⟩ := mapM_exists x.b fun w hw => by
    obtain ⟨u, hu, _⟩ := hb w hw; exact ⟨u, hu⟩
  obtain ⟨uc, hC, hcv⟩ : ∃ uc, (fp32.decode x.c).toFinite = some uc ∧ uc.value = zc := by
    unfold value32 at hc
    cases hd : (fp32.decode x.c).toFinite with
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
  have hint : IntPrepared ⟨A, B, uc⟩ := by
    refine ⟨hops _ _ _ hfa ha hA, hops _ _ _ hfb hb hB,
      ⟨⟨zc, hcv⟩, int_normal (binary32_sub hC) hcv⟩, ?_⟩
    have hbud : sumQ ((Prepared.p ⟨A, B, uc⟩).map fun p => absQ p.value) =
        wordDotAbs P x.a x.b := by
      unfold Prepared.p wordDotAbs
      simp only [List.map_zipWith, Unpacked.value_mul]
      rw [← mapM_zipWith (fun a b => absQ (a * b)) x.a x.b A B hA hB]
    simp only [hcv, hbud]
    exact hbound
  have hexact : (Prepared.exact ⟨A, B, uc⟩) = (zc : ℚ) + exactProducts P x.a x.b := by
    rw [Prepared.exact_eq]
    simp only
    rw [mapM_products x.a x.b A B hA hB, hcv]
    grind
  obtain ⟨Z, hZ, hZb⟩ := exactProducts_int x.a x.b ha hb
  have hbnd : (zc + Z).natAbs ≤ 2 ^ 24 := by
    apply natAbs_le_of_absQ
    rw [Rat.intCast_add]
    have := absQ_add_le (zc : ℚ) (Z : ℚ)
    grind
  obtain ⟨w, hw, hv⟩ := fl32_int (!P.subnormals) (zc + Z) hbnd
  refine ⟨⟨⟨A, B, uc⟩, Prepared.exact ⟨A, B, uc⟩, w⟩, ?_, ?_⟩
  · unfold evalBlock
    rw [if_neg (by omega), hprep]
    simp only [accumulate_int hP hint]
    rw [hexact, hZ, ← Rat.intCast_add, hw]
  · simp only
    rw [hv, hZ, Rat.intCast_add]

/-! ## Chained blocks -/

/-- **Exact chain.** Blocks of integer operands, chained through their binary32 outputs from an
integer `c`, return `c + Σ aᵢbᵢ` exactly when `|c| + Σ|aᵢbᵢ| ≤ 2^24`. -/
theorem runBlocks_int {P : Model} (hP : ExactConfig P) (hfa : smallSubnormals P.a)
    (hfb : smallSubnormals P.b) :
    ∀ (blocks : List (List P.a.Word × List P.b.Word)) (c : F32) (zc : ℤ),
      value32 c = some (zc : ℚ) →
      (∀ g ∈ blocks, g.1.length = P.nfma ∧ g.2.length = P.nfma ∧
        (∀ w ∈ g.1, IntWord P.a w) ∧ ∀ w ∈ g.2, IntWord P.b w) →
      absQ (zc : ℚ) + sumQ (blocks.map fun g => wordDotAbs P g.1 g.2) ≤ pow2 24 →
      ∃ ts, runBlocks P c blocks = .ok ts ∧
        value32 (lastOutput c ts) = some ((zc : ℚ) + sumQ (blocks.map fun g =>
          exactProducts P g.1 g.2))
  | [], c, zc, hc, _, _ => ⟨[], rfl, by simp [lastOutput, hc, sumQ]; grind⟩
  | g :: rest, c, zc, hc, hg, hbound => by
    obtain ⟨hl1, hl2, ha, hb⟩ := hg g (by simp)
    simp only [List.map_cons, sumQ] at hbound ⊢
    have hrest0 : 0 ≤ sumQ (rest.map fun g => wordDotAbs P g.1 g.2) := by
      rw [sumQ_eq]; exact Ozaki.sum_nonneg fun g' _ => wordDotAbs_nonneg P g'.1 g'.2
    have hg0 := wordDotAbs_nonneg P g.1 g.2
    obtain ⟨t, ht, hv⟩ := evalBlock_int (x := ⟨g.1, g.2, c⟩) hP hfa hfb hl1 hl2 ha hb hc
      (by grind)
    obtain ⟨Z, hZ, hZb⟩ := exactProducts_int g.1 g.2 ha hb
    have hc' : value32 t.d = some ((zc + Z : ℤ) : ℚ) := by rw [hv, hZ, Rat.intCast_add]
    have hbound' : absQ ((zc + Z : ℤ) : ℚ) + sumQ (rest.map fun g => wordDotAbs P g.1 g.2) ≤
        pow2 24 := by
      have := absQ_add_le (zc : ℚ) (Z : ℚ); rw [Rat.intCast_add]; grind
    obtain ⟨ts, hts, hval⟩ := runBlocks_int hP hfa hfb rest t.d (zc + Z) hc'
      (fun g' hg' => hg g' (by simp [hg'])) hbound'
    refine ⟨t :: ts, ?_, ?_⟩
    · simp only [runBlocks]; rw [ht]; simp only; rw [hts]
    · simp only [lastOutput]; rw [hval, hZ, Rat.intCast_add]; grind

/-! ## Inner products of any length -/

theorem chunks_length_mem {n : ℕ} (hn : 0 < n) :
    ∀ (fuel : ℕ) (xs : List α), n ∣ xs.length → ∀ g ∈ chunks n fuel xs, g.length = n
  | fuel, [], _ => by intro g hg; cases fuel <;> simp [chunks] at hg
  | 0, _ :: _, _ => by simp [chunks]
  | fuel + 1, x :: xs, hd => by
    intro g hg
    simp only [chunks, List.mem_cons] at hg
    rcases hg with rfl | hg
    · rw [List.length_take]
      have : n ≤ (x :: xs).length := Nat.le_of_dvd (by simp) hd
      omega
    · refine chunks_length_mem hn fuel _ ?_ g hg
      rw [List.length_drop]
      exact Nat.dvd_sub hd (Nat.dvd_refl n)

theorem chunks_mem_mem {n : ℕ} :
    ∀ (fuel : ℕ) (xs : List α), ∀ g ∈ chunks n fuel xs, ∀ w ∈ g, w ∈ xs
  | fuel, [] => by intro g hg; cases fuel <;> simp [chunks] at hg
  | 0, _ :: _ => by simp [chunks]
  | fuel + 1, x :: xs => by
    intro g hg w hw
    simp only [chunks, List.mem_cons] at hg
    rcases hg with rfl | hg
    · exact List.mem_of_mem_take hw
    · exact List.mem_of_mem_drop (chunks_mem_mem fuel _ g hg w hw)

theorem padToBlocks_dvd {n : ℕ} (hn : 0 < n) (xs : List (BitVec w)) :
    n ∣ (padToBlocks n xs).length := by
  rw [padToBlocks_length]
  have hL := Nat.div_add_mod xs.length n
  have hr := Nat.mod_lt xs.length hn
  by_cases h0 : xs.length % n = 0
  · rw [h0, Nat.sub_zero, Nat.mod_self, Nat.add_zero]
    exact Nat.dvd_of_mod_eq_zero h0
  · rw [Nat.mod_eq_of_lt (by omega : n - xs.length % n < n)]
    refine ⟨xs.length / n + 1, ?_⟩
    rw [Nat.mul_succ]
    omega

theorem mem_padToBlocks {n : ℕ} {xs : List (BitVec w)} {v : BitVec w}
    (h : v ∈ padToBlocks n xs) : v ∈ xs ∨ v = 0 := by
  unfold padToBlocks at h
  rcases List.mem_append.mp h with h | h
  · exact Or.inl h
  · exact Or.inr (List.mem_replicate.mp h).2

/-- The blocks' sums of product magnitudes add up to that of the whole vectors. -/
theorem blocks_dotAbs (P : Model) (hn : 0 < P.nfma) {a : List P.a.Word} {b : List P.b.Word}
    (hlen : a.length = b.length) :
    sumQ ((blocks P a b).map fun ab => wordDotAbs P ab.1 ab.2) = wordDotAbs P a b := by
  unfold blocks
  dsimp only
  have hpl : (padToBlocks P.nfma a).length = (padToBlocks P.nfma b).length := by
    rw [padToBlocks_length, padToBlocks_length, hlen]
  rw [← hpl]
  have := sum_chunks (fun x y => absQ (P.a.wordValue x * P.b.wordValue y)) P.nfma hn
    (padToBlocks P.nfma a).length (padToBlocks P.nfma a) (padToBlocks P.nfma b) hpl (Nat.le_refl _)
  unfold wordDotAbs
  rw [this]
  unfold padToBlocks
  rw [List.zipWith_append hlen, sumQ_append, hlen, List.zipWith_replicate,
    InputFormat.wordValue_zero, InputFormat.wordValue_zero]
  have hz : ∀ m : ℕ, sumQ (List.replicate m (absQ ((0 : ℚ) * 0))) = 0 := by
    intro m
    induction m with
    | zero => rfl
    | succ m ih => simp only [List.replicate_succ, sumQ, ih]; decide +kernel
  rw [hz]; grind

/-- **Exact inner product.** On an exact configuration, integer vectors and an integer `c` with
`|c| + Σ|aᵢbᵢ| ≤ 2^24` give the binary32 word of `c + Σ aᵢbᵢ`, block by block. -/
theorem dotBits_int {P : Model} (hP : ExactConfig P) (hfa : smallSubnormals P.a)
    (hfb : smallSubnormals P.b) (hn : 0 < P.nfma) (h0a : IntWord P.a 0) (h0b : IntWord P.b 0)
    {a : List P.a.Word} {b : List P.b.Word} (hlen : a.length = b.length)
    (ha : ∀ w ∈ a, IntWord P.a w) (hb : ∀ w ∈ b, IntWord P.b w) {c : F32} {zc : ℤ}
    (hc : value32 c = some (zc : ℚ)) (hbound : absQ (zc : ℚ) + wordDotAbs P a b ≤ pow2 24) :
    ∃ d, dotBits P a b c = .ok d ∧ value32 d = some ((zc : ℚ) + exactProducts P a b) := by
  have hblocks : ∀ g ∈ blocks P a b, g.1.length = P.nfma ∧ g.2.length = P.nfma ∧
      (∀ w ∈ g.1, IntWord P.a w) ∧ ∀ w ∈ g.2, IntWord P.b w := by
    intro g hg
    unfold blocks at hg
    obtain ⟨g1, g2⟩ := g
    have hm := List.of_mem_zip hg
    refine ⟨chunks_length_mem hn _ _ (padToBlocks_dvd hn a) g1 hm.1,
      chunks_length_mem hn _ _ (padToBlocks_dvd hn b) g2 hm.2, ?_, ?_⟩
    · intro w hw
      rcases mem_padToBlocks (chunks_mem_mem _ _ g1 hm.1 w hw) with h | h
      · exact ha w h
      · rw [h]; exact h0a
    · intro w hw
      rcases mem_padToBlocks (chunks_mem_mem _ _ g2 hm.2 w hw) with h | h
      · exact hb w h
      · rw [h]; exact h0b
  obtain ⟨ts, hts, hv⟩ := runBlocks_int hP hfa hfb (blocks P a b) c zc hc hblocks
    (by rw [blocks_dotAbs P hn hlen]; exact hbound)
  refine ⟨lastOutput c ts, ?_, ?_⟩
  · rw [dotBits_eq_runBlocks P c hlen, hts]; rfl
  · rw [hv, blocks_products P hn hlen]

end Ozaki.MC
