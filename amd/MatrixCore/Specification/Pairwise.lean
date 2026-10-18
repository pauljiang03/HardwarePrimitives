import MatrixCore.Specification.Equivalence

/-! # CDNA 2 meets the independent specification

For the CDNA 2 models and every input, the model returns `w` exactly when `w` satisfies the
specification's transcription of Fig. 2 (`Spec.PairwiseResult`). -/

namespace MatrixCore.Spec

open MatrixCore

/-! ## `fl{·}` with flush to zero -/

theorem isSubnormal32_iff {w : F32} {d : ℚ} (h : MatrixCore.value32 w = some d) :
    isSubnormal32 w = true ↔ (d ≠ 0 ∧ absQ d < pow2 (-126)) := by
  obtain ⟨h1, h2⟩ := value32_subnormal h
  constructor
  · exact h1
  · intro hd
    cases hs : isSubnormal32 w
    · rcases h2 hs with h | h
      · exact absurd h hd.1
      · exact absurd hd.2 (Rat.not_lt.mpr h)
    · rfl

/-- The flushed result of an RNE word. -/
def flushed32 (w₀ : F32) (d : ℚ) : F32 :=
  if d ≠ 0 ∧ absQ d < pow2 (-126) then signedZero32 w₀ else w₀

theorem fl32_true_iff (x : ℚ) (w : F32) :
    fl32 true x = some w ↔
      ∃ w₀ d, rne32 x = some w₀ ∧ MatrixCore.value32 w₀ = some d ∧ w = flushed32 w₀ d := by
  unfold fl32 flushed32
  cases hr : rne32 x with
  | none => simp
  | some w₀ =>
    have hv := rne32_value hr
    have hsub := isSubnormal32_iff hv
    simp only [Bool.true_and, Option.some.injEq]
    constructor
    · intro h
      refine ⟨w₀, rneValue x, rfl, hv, ?_⟩
      rw [← h]
      by_cases hs : isSubnormal32 w₀ = true
      · rw [if_pos hs, if_pos (hsub.mp hs)]
      · rw [if_neg hs, if_neg (fun h' => hs (hsub.mpr h'))]
    · rintro ⟨w₁, d, hw, hd, rfl⟩
      cases hw
      rw [hv] at hd; cases hd
      by_cases hs : isSubnormal32 w₀ = true
      · rw [if_pos hs, if_pos (hsub.mp hs)]
      · rw [if_neg hs, if_neg (fun h' => hs (hsub.mpr h'))]

theorem flValue_true_iff (x y : ℚ) :
    flValue true x = some y ↔
      ∃ w₀ d, rne32 x = some w₀ ∧ MatrixCore.value32 w₀ = some d ∧
        y = (if d ≠ 0 ∧ absQ d < pow2 (-126) then 0 else d) := by
  unfold flValue
  cases h : fl32 true x with
  | none =>
    simp only [Option.bind_none, reduceCtorEq, false_iff]
    rintro ⟨w₀, d, hr, hd, _⟩
    have := (fl32_true_iff x (flushed32 w₀ d)).mpr ⟨w₀, d, hr, hd, rfl⟩
    rw [h] at this; simp at this
  | some w =>
    obtain ⟨w₀, d, hr, hd, rfl⟩ := (fl32_true_iff x w).mp h
    simp only [Option.bind_some]
    constructor
    · intro hy
      refine ⟨w₀, d, hr, hd, ?_⟩
      unfold flushed32 at hy
      split at hy
      · rename_i hc; rw [value32_signedZero32] at hy; rw [if_pos hc]; exact (Option.some.inj hy).symm
      · rename_i hc; rw [hd] at hy; rw [if_neg hc]; exact (Option.some.inj hy).symm
    · rintro ⟨w₁, d₁, hr₁, hd₁, rfl⟩
      rw [hr] at hr₁; cases hr₁
      rw [hd] at hd₁; cases hd₁
      unfold flushed32
      split
      · exact value32_signedZero32 _
      · exact hd

/-- The specification's `fl{·}` is the model's. -/
theorem fl_iff (x y : ℚ) : Fl x y ↔ flValue true x = some y := by
  rw [flValue_true_iff]
  unfold Fl
  simp only [rounds_iff, value32_eq, overflows_iff, Classical.not_not]
  have hm : ∀ q, magnitude q = absQ q := fun _ => rfl
  have hn : minNormal = pow2 (-126) := rfl
  simp only [hm, hn]
  constructor
  · rintro ⟨hx, w, d, hw, hd, rfl⟩
    exact ⟨w, d, (rne32_iff hx).mpr hw, hd, rfl⟩
  · rintro ⟨w, d, hw, hd, rfl⟩
    exact ⟨(rne32_isSome_iff x).mp (by rw [hw]; rfl), w, d, rne32_rounds hw, hd, rfl⟩

/-- The specification's output word of `fl{·}` is the model's. -/
theorem flWord_iff (x : ℚ) (w : F32) : FlWord x w ↔ fl32 true x = some w := by
  rw [fl32_true_iff]
  unfold FlWord
  simp only [rounds_iff, value32_eq, overflows_iff, Classical.not_not]
  have hm : ∀ q, magnitude q = absQ q := fun _ => rfl
  have hn : minNormal = pow2 (-126) := rfl
  have hz : ∀ w₀ : F32, BitVec.ofNat 32 (w₀.toNat / 2147483648 % 2 * 2147483648) = signedZero32 w₀ :=
    fun _ => rfl
  simp only [hm, hn, hz]
  constructor
  · rintro ⟨hx, w₀, d, hw, hd, rfl⟩
    exact ⟨w₀, d, (rne32_iff hx).mpr hw, hd, rfl⟩
  · rintro ⟨w₀, d, hw, hd, rfl⟩
    exact ⟨(rne32_isSome_iff x).mp (by rw [hw]; rfl), w₀, d, rne32_rounds hw, hd, rfl⟩

/-! ## Inputs -/

theorem flushNum_numOf (u : Unpacked) : flushNum (numOf u) = numOf u.flush := by
  unfold flushNum numOf Unpacked.flush
  by_cases h : u.m < 2 ^ u.t <;> simp [h]

theorem pairwise_products (as bs : List Unpacked) :
    (List.zipWith mul ((as.map numOf).map flushNum) ((bs.map numOf).map flushNum)).map Num.val =
      (List.zipWith Unpacked.mul (as.map Unpacked.flush) (bs.map Unpacked.flush)).map
        Unpacked.value := by
  have ha : (as.map numOf).map flushNum = (as.map Unpacked.flush).map numOf := by
    simp [List.map_map, Function.comp_def, flushNum_numOf]
  have hb : (bs.map numOf).map flushNum = (bs.map Unpacked.flush).map numOf := by
    simp [List.map_map, Function.comp_def, flushNum_numOf]
  rw [ha, hb, zipWith_mul_map, List.map_map]
  congr 1; funext p; exact val_numOf p

/-- A model and its CDNA 2 transcription. -/
structure SupportedPairwise (P : Model) (S : PairwiseParams) : Prop where
  a : S.a = operandOf P.a
  b : S.b = operandOf P.b
  group : S.group = P.nfma
  accumulation : P.accumulation = .pairWiseSum
  subnormals : P.subnormals = false
  limit : P.productOverflow = false
  size : S.group = 2 ∨ S.group = 4

theorem blockBits_ok_iff {P : Model} (x : BlockInput P) (w : F32) :
    blockBits x = .ok w ↔ x.a.length = P.nfma ∧ x.b.length = P.nfma ∧
      ∃ px s, prepare x = some px ∧ accumulate P px = .ok s ∧ fl32 (!P.subnormals) s = some w := by
  constructor
  · intro h
    unfold blockBits at h
    cases ht : evalBlock x with
    | error e => rw [ht] at h; simp [Except.map] at h
    | ok t =>
      rw [ht] at h
      simp only [Except.map, Except.ok.injEq] at h
      subst h
      obtain ⟨ha, hb, hp, hs, hd⟩ := evalBlock_ok ht
      exact ⟨ha, hb, t.prepared, t.sAcc, hp, hs, hd⟩
  · rintro ⟨ha, hb, px, s, hp, hs, hd⟩
    unfold blockBits evalBlock
    rw [if_neg (by omega), hp]
    simp only [hs, hd]; rfl

/-- **Equivalence for CDNA 2.** On the CDNA 2 models and for every input, the model returns `w`
exactly when `w` is the specification's result. -/
theorem pairwise_eq_spec {P : Model} {S : PairwiseParams} (hS : SupportedPairwise P S)
    (x : BlockInput P) (w : F32) :
    blockBits x = .ok w ↔
      PairwiseResult S (x.a.map BitVec.toNat) (x.b.map BitVec.toNat) x.c w := by
  rw [blockBits_ok_iff]
  unfold PairwiseResult
  simp only [List.length_map, hS.group]
  have hdec : (((x.a.map BitVec.toNat).mapM S.a.decode).bind fun as =>
      ((x.b.map BitVec.toNat).mapM S.b.decode).bind fun bs =>
        (decode fp32 x.c.toNat).bind fun cn => some (as, bs, cn)) =
      (prepare x).map fun px => (px.a.map numOf, px.b.map numOf, numOf px.c) := by
    rw [hS.a, hS.b, mapM_decode_eq, mapM_decode_eq, decode_c_eq]
    unfold prepare
    cases x.a.mapM fun w => (P.a.read w).toFinite <;> simp
    cases x.b.mapM fun w => (P.b.read w).toFinite <;> simp
    cases (MatrixCore.fp32.decode x.c).toFinite <;> simp
  -- the model's side, for decoded inputs
  have hacc : ∀ (px : Prepared) (s : ℚ), accumulate P px = .ok s ↔ pairwiseSum P px = some s := by
    intro px s
    unfold accumulate
    simp only [hS.limit, Bool.false_and, Bool.false_eq_true, ↓reduceIte, hS.accumulation]
    cases pairwiseSum P px <;> simp
  have key : ∀ px : Prepared, px.a.length = P.nfma → px.b.length = P.nfma →
      ((∃ s, accumulate P px = .ok s ∧ fl32 (!P.subnormals) s = some w) ↔
        pairwiseOutput ((List.zipWith mul ((px.a.map numOf).map flushNum)
          ((px.b.map numOf).map flushNum)).map Num.val) (flushNum (numOf px.c)).val w) := by
    intro px ha hb
    rw [pairwise_products, flushNum_numOf, val_numOf, hS.subnormals]
    have hsub : (if P.subnormals then px else px.flushed) = px.flushed := by simp [hS.subnormals]
    have hlen : px.flushed.p.length = P.nfma := by
      simp [Prepared.flushed, Prepared.p, ha, hb]
    have hp : px.flushed.p = List.zipWith Unpacked.mul (px.a.map Unpacked.flush) (px.b.map Unpacked.flush) := rfl
    rw [← hp]
    have hacc' : (∃ s, accumulate P px = .ok s ∧ fl32 true s = some w) ↔
        ∃ s, pairwiseSum P px = some s ∧ fl32 true s = some w := by
      simp only [hacc]
    simp only [Bool.not_false]
    rw [hacc']
    rcases hS.size with h2 | h4
    · rw [hS.group] at h2
      rw [h2] at hlen
      match hq : px.flushed.p, hlen with
      | [p₁, p₂], _ =>
        rw [pairwiseSum_two P px p₁ p₂ (by rw [hsub, hq]), hsub]
        simp only [List.map_cons, List.map_nil, pairwiseOutput, fl_iff, flWord_iff, hS.subnormals,
          Bool.not_false]
        constructor
        · rintro ⟨s, hs, hw⟩
          cases h₁ : flValue true p₁.value <;> rw [h₁] at hs <;> simp at hs
          rename_i q₁
          cases h₂ : flValue true p₂.value <;> rw [h₂] at hs <;> simp at hs
          rename_i q₂
          cases ht : flValue true (q₁ + q₂) <;> rw [ht] at hs <;> simp at hs
          rename_i t
          subst hs
          exact ⟨q₁, q₂, t, rfl, rfl, ht, hw⟩
        · rintro ⟨q₁, q₂, t, h₁, h₂, ht, hw⟩
          exact ⟨px.c.flush.value + t, by simp [h₁, h₂, ht, Prepared.flushed], hw⟩
    · rw [hS.group] at h4
      rw [h4] at hlen
      match hq : px.flushed.p, hlen with
      | [p₁, p₂, p₃, p₄], _ =>
        rw [pairwiseSum_four P px p₁ p₂ p₃ p₄ (by rw [hsub, hq]), hsub]
        simp only [List.map_cons, List.map_nil, pairwiseOutput, fl_iff, flWord_iff, hS.subnormals,
          Bool.not_false]
        constructor
        · rintro ⟨s, hs, hw⟩
          cases h₁ : flValue true p₁.value <;> rw [h₁] at hs <;> simp at hs
          rename_i q₁
          cases h₂ : flValue true p₂.value <;> rw [h₂] at hs <;> simp at hs
          rename_i q₂
          cases h₃ : flValue true p₃.value <;> rw [h₃] at hs <;> simp at hs
          rename_i q₃
          cases h₄ : flValue true p₄.value <;> rw [h₄] at hs <;> simp at hs
          rename_i q₄
          cases hu : flValue true (q₁ + q₂) <;> rw [hu] at hs <;> simp at hs
          rename_i u
          cases hv : flValue true (q₃ + q₄) <;> rw [hv] at hs <;> simp at hs
          rename_i v
          cases ht : flValue true (u + v) <;> rw [ht] at hs <;> simp at hs
          rename_i t
          subst hs
          exact ⟨q₁, q₂, q₃, q₄, u, v, t, rfl, rfl, rfl, rfl, hu, hv, ht, hw⟩
        · rintro ⟨q₁, q₂, q₃, q₄, u, v, t, h₁, h₂, h₃, h₄, hu, hv, ht, hw⟩
          exact ⟨px.c.flush.value + t,
            by simp [h₁, h₂, h₃, h₄, hu, hv, ht, Prepared.flushed], hw⟩
  constructor
  · rintro ⟨ha, hb, px, s, hp, hs, hw⟩
    rw [hp, Option.map_some] at hdec
    obtain ⟨hA, hB, hC⟩ := triple_some.mp hdec
    obtain ⟨la, lb⟩ := prepare_lengths hp
    refine ⟨ha, hb, _, _, _, hA, hB, hC, ?_⟩
    exact (key px (by omega) (by omega)).mp ⟨s, hs, hw⟩
  · rintro ⟨ha, hb, as, bs, cn, hA, hB, hC, hout⟩
    rw [hA, hB, hC] at hdec
    simp only [Option.bind_some] at hdec
    cases hp : prepare x with
    | none => rw [hp] at hdec; simp at hdec
    | some px =>
      rw [hp, Option.map_some, Option.some.injEq, Prod.mk.injEq, Prod.mk.injEq] at hdec
      obtain ⟨rfl, rfl, rfl⟩ := hdec
      obtain ⟨la, lb⟩ := prepare_lengths hp
      obtain ⟨s, hs, hw⟩ := (key px (by omega) (by omega)).mpr hout
      exact ⟨ha, hb, px, s, rfl, hs, hw⟩

theorem supported_cdna2F16 : SupportedPairwise MatrixCore.cdna2F16 Spec.cdna2F16 :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, Or.inr rfl⟩
theorem supported_cdna2BF16 : SupportedPairwise MatrixCore.cdna2BF16 Spec.cdna2BF16 :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, Or.inl rfl⟩
theorem supported_cdna2BF16_1k : SupportedPairwise MatrixCore.cdna2BF16_1k Spec.cdna2BF16_1k :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, Or.inr rfl⟩

end MatrixCore.Spec
