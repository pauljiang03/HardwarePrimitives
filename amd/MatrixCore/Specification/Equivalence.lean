import MatrixCore.Specification.Stages

/-! # The implementation meets the independent specification

For every model the specification transcribes (CDNA 1 and the SFMA with correct rounding,
CDNA 3 with Algorithms 1 and 2), and for every input, the implementation returns the word `w`
exactly when the specification's `Result` holds for `w`. -/

namespace MatrixCore.Spec

open MatrixCore

/-- A model and its transcription in the specification. -/
structure Supported (P : Model) (S : Params) : Prop where
  a : S.a = operandOf P.a
  b : S.b = operandOf P.b
  nfma : S.nfma = P.nfma
  limit : S.productLimit = P.productOverflow
  subnormals : P.subnormals = true
  cFrac : 23 ≤ P.late.sumFracBits
  kind : (P.accumulation = .correctRounding ∧ S.kind = .exact) ∨
    (P.accumulation = .globalAlignment ∧ S.kind = .algorithm1 (lateOf P)) ∨
    (P.accumulation = .oddEvenGrouping ∧ S.kind = .algorithm2 (lateOf P))

theorem zipWith_mul_map (as bs : List Unpacked) :
    List.zipWith mul (as.map numOf) (bs.map numOf) = (List.zipWith Unpacked.mul as bs).map numOf := by
  induction as generalizing bs with
  | nil => simp
  | cons a as ih => cases bs with
    | nil => simp
    | cons b bs => simp [ih, mul_numOf]

theorem sum_val (ps : List Unpacked) : ((ps.map numOf).map Num.val).sum = sumQ (ps.map Unpacked.value) := by
  induction ps with
  | nil => rfl
  | cons p ps ih =>
    rw [List.map_cons, List.map_cons, List.sum_cons, val_numOf, ih]; rfl

/-- The specification's accumulated value is the implementation's `S_acc`. -/
theorem accumulated_eq {P : Model} {S : Params} (hS : Supported P S) (x : Prepared)
    (hc : x.c.t = 23) :
    accumulated S (x.a.map numOf) (x.b.map numOf) (numOf x.c) =
      match P.accumulation with
      | .correctRounding => x.exact
      | _ => alignedAccumulation P x := by
  have hct : x.c.t ≤ P.late.sumFracBits := by rw [hc]; exact hS.cFrac
  unfold accumulated
  rw [zipWith_mul_map]
  rcases hS.kind with ⟨hP, hK⟩ | ⟨hP, hK⟩ | ⟨hP, hK⟩ <;> rw [hP, hK] <;> simp only
  · rw [sum_val, val_numOf]; rfl
  · exact algorithm1_eq P hP x.p x.c hct
  · exact algorithm2_eq P hP x.p x.c hct

/-! ## Rounding -/

theorem rounds_iff (x : ℚ) (w : F32) : RoundsNearestEven x w ↔ RoundsNearestEven32 x w := by
  unfold RoundsNearestEven RoundsNearestEven32 NearestEven32
  have hv : ∀ v, value32 v = MatrixCore.value32 v := value32_eq
  have hm : ∀ q, magnitude q = absQ q := fun _ => rfl
  simp only [hv, hm]
  have hsign : (w.toNat / 2147483648 % 2 = 1 ↔ x < 0) ↔ sign32 w = decide (x < 0) := by
    unfold sign32
    by_cases h : w.toNat / 2147483648 % 2 = 1 <;> by_cases hx : x < 0 <;> simp [h, hx]
  rw [hsign]
  constructor
  · rintro ⟨hs, hn⟩; exact ⟨hn, hs⟩
  · rintro ⟨hn, hs⟩; exact ⟨hs, hn⟩

theorem overflows_iff (x : ℚ) : overflows x ↔ ¬ absQ x < overflowThreshold32 := by
  unfold overflows overflowThreshold32
  have : (2 : ℚ) ^ (128 : ℤ) - (2 : ℚ) ^ (103 : ℤ) = pow2 128 - pow2 103 := rfl
  rw [this]
  exact ⟨fun h h' => by unfold magnitude at h; unfold absQ at h'; grind,
    fun h => by unfold magnitude; unfold absQ at h; grind⟩

/-! ## Blocks -/

theorem decode_c_eq (c : F32) :
    decode binary32 c.toNat = (MatrixCore.binary32.decode c).toFinite.map numOf :=
  decode_eq MatrixCore.binary32 c.toNat

theorem triple_some {oa : Option α} {ob : Option β} {oc : Option γ} {a : α} {b : β} {c : γ} :
    (oa.bind fun x => ob.bind fun y => oc.bind fun z => some (x, y, z)) = some (a, b, c) ↔
      oa = some a ∧ ob = some b ∧ oc = some c := by
  cases oa <;> cases ob <;> cases oc <;> simp

/-- Decoding the words through the specification gives the implementation's decoded inputs. -/
theorem prepare_spec {P : Model} {S : Params} (hS : Supported P S) (x : BlockInput P) :
    (((x.a.map BitVec.toNat).mapM S.a.decode).bind fun as =>
      ((x.b.map BitVec.toNat).mapM S.b.decode).bind fun bs =>
        (decode binary32 x.c.toNat).bind fun cn => some (as, bs, cn)) =
      (prepare x).map fun px => (px.a.map numOf, px.b.map numOf, numOf px.c) := by
  rw [hS.a, hS.b, mapM_decode_eq, mapM_decode_eq, decode_c_eq]
  unfold prepare
  cases x.a.mapM fun w => (P.a.read w).toFinite <;> simp
  cases x.b.mapM fun w => (P.b.read w).toFinite <;> simp
  cases (MatrixCore.binary32.decode x.c).toFinite <;> simp

theorem productOverflows_false {x : Prepared} (h : x.productOverflows = false) :
    ∀ p ∈ x.p, absQ p.value < pow2 128 := by
  intro p hp
  unfold Prepared.productOverflows at h
  have := List.any_eq_false.mp h p hp
  simp at this
  grind

theorem productOverflows_of {x : Prepared} (h : ∀ p ∈ x.p, absQ p.value < pow2 128) :
    x.productOverflows = false := by
  unfold Prepared.productOverflows
  apply List.any_eq_false.mpr
  intro p hp
  have := h p hp
  simp; grind

/-- The value accumulated by the implementation when no product overflows. -/
theorem accumulate_supported {P : Model} {S : Params} (hS : Supported P S) (x : Prepared)
    (hov : P.productOverflow = false ∨ x.productOverflows = false) :
    accumulate P x = .ok (match P.accumulation with
      | .correctRounding => x.exact
      | _ => alignedAccumulation P x) := by
  have hno : (P.productOverflow && x.productOverflows) = false := by
    rcases hov with h | h <;> simp [h]
  unfold accumulate
  rw [hno]
  rcases hS.kind with ⟨hP, _⟩ | ⟨hP, _⟩ | ⟨hP, _⟩ <;> simp [hP]

/-- **Equivalence.** On every supported model and for every input, the implementation returns
`w` exactly when `w` is the specification's result. -/
theorem blockBits_eq_spec {P : Model} {S : Params} (hS : Supported P S) (x : BlockInput P)
    (w : F32) :
    blockBits x = .ok w ↔ Result S (x.a.map BitVec.toNat) (x.b.map BitVec.toNat) x.c w := by
  have hdec := prepare_spec hS x
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
      rw [hS.subnormals, Bool.not_true, fl32_false] at hd
      have hct := prepare_c_t hp
      have hand : (P.productOverflow && t.prepared.productOverflows) = false := by
        cases h : (P.productOverflow && t.prepared.productOverflows)
        · rfl
        · unfold accumulate at hs; rw [h] at hs; simp at hs
      have hov : P.productOverflow = false ∨ t.prepared.productOverflows = false := by
        cases hpo : P.productOverflow <;> cases hxo : t.prepared.productOverflows <;> simp_all
      have hacc := accumulate_supported hS t.prepared hov
      rw [hs] at hacc
      injection hacc with hacc
      rw [hp, Option.map_some] at hdec
      obtain ⟨hA, hB, hC⟩ := triple_some.mp hdec
      refine ⟨by simp [ha, hS.nfma], by simp [hb, hS.nfma], t.prepared.a.map numOf,
        t.prepared.b.map numOf, numOf t.prepared.c, hA, hB, hC, ?_, ?_, ?_⟩
      · intro hl
        rw [hS.limit] at hl
        have hno : t.prepared.productOverflows = false := by
          rcases hov with h | h
          · rw [hl] at h; simp at h
          · exact h
        rw [zipWith_mul_map]
        intro p hp'
        obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp'
        rw [val_numOf]
        exact productOverflows_false hno q hq
      · rw [accumulated_eq hS _ hct, ← hacc, overflows_iff, Classical.not_not]
        exact (rne32_isSome_iff _).mp (by rw [hd]; rfl)
      · rw [accumulated_eq hS _ hct, ← hacc, rounds_iff]
        exact rne32_rounds hd
  · rintro ⟨ha, hb, as, bs, cn, hA, hB, hC, hlim, hnov, hr⟩
    rw [hA, hB, hC] at hdec
    simp only [Option.bind_some] at hdec
    cases hp : prepare x with
    | none => rw [hp] at hdec; simp at hdec
    | some px =>
      rw [hp, Option.map_some, Option.some.injEq, Prod.mk.injEq, Prod.mk.injEq] at hdec
      obtain ⟨rfl, rfl, rfl⟩ := hdec
      have hct := prepare_c_t hp
      have hov : P.productOverflow = false ∨ px.productOverflows = false := by
        cases hpo : P.productOverflow
        · left; rfl
        · right
          apply productOverflows_of
          intro q hq
          have := hlim (by rw [hS.limit, hpo]) (numOf q) (by
            rw [zipWith_mul_map]; exact List.mem_map.mpr ⟨q, hq, rfl⟩)
          rwa [val_numOf] at this
      have hacc := accumulate_supported hS px hov
      rw [accumulated_eq hS px hct] at hnov hr
      rw [overflows_iff, Classical.not_not] at hnov
      rw [rounds_iff] at hr
      have hw := (rne32_iff hnov).mpr hr
      unfold blockBits evalBlock
      rw [if_neg (by rw [← hS.nfma]; simp only [List.length_map] at ha hb; omega), hp]
      simp only [hacc, hS.subnormals, Bool.not_true, fl32_false, hw]
      rfl

/-! ## The paper's variants -/

theorem supported_sfma : Supported sfmaF32 sfma := ⟨rfl, rfl, rfl, rfl, rfl, by decide, Or.inl ⟨rfl, rfl⟩⟩
theorem supported_cdna1F16 : Supported MatrixCore.cdna1F16 Spec.cdna1F16 :=
  ⟨rfl, rfl, rfl, rfl, rfl, by decide, Or.inl ⟨rfl, rfl⟩⟩
theorem supported_cdna1BF16 : Supported MatrixCore.cdna1BF16 Spec.cdna1BF16 :=
  ⟨rfl, rfl, rfl, rfl, rfl, by decide, Or.inl ⟨rfl, rfl⟩⟩
theorem supported_cdna3F16 : Supported MatrixCore.cdna3F16 Spec.cdna3F16 :=
  ⟨rfl, rfl, rfl, rfl, rfl, by decide, Or.inr (Or.inl ⟨rfl, rfl⟩)⟩
theorem supported_cdna3BF16 : Supported MatrixCore.cdna3BF16 Spec.cdna3BF16 :=
  ⟨rfl, rfl, rfl, rfl, rfl, by decide, Or.inr (Or.inl ⟨rfl, rfl⟩)⟩
theorem supported_cdna3XF32 : Supported MatrixCore.cdna3XF32 Spec.cdna3XF32 :=
  ⟨rfl, rfl, rfl, rfl, rfl, by decide, Or.inr (Or.inl ⟨rfl, rfl⟩)⟩
theorem supported_cdna3FP8 (a b : Format) :
    Supported (MatrixCore.cdna3FP8 a b) (Spec.cdna3FP8 (layoutOf a) (layoutOf b)) :=
  ⟨rfl, rfl, rfl, rfl, rfl, show 23 ≤ 32 by decide, Or.inr (Or.inr ⟨rfl, rfl⟩)⟩

theorem layoutOf_e4m3 : layoutOf e4m3fnuz = e4m3 := rfl
theorem layoutOf_e5m2 : layoutOf e5m2fnuz = e5m2 := rfl

/-- The paper's variants, each with the implementation model and its transcription. -/
theorem supported_eq_spec_cdna3F16 (x : BlockInput MatrixCore.cdna3F16) (w : F32) :
    blockBits x = .ok w ↔ Result Spec.cdna3F16 (x.a.map BitVec.toNat) (x.b.map BitVec.toNat) x.c w :=
  blockBits_eq_spec supported_cdna3F16 x w

theorem supported_eq_spec_cdna3FP8 (x : BlockInput (MatrixCore.cdna3FP8 e4m3fnuz e5m2fnuz)) (w : F32) :
    blockBits x = .ok w ↔
      Result (Spec.cdna3FP8 e4m3 e5m2) (x.a.map BitVec.toNat) (x.b.map BitVec.toNat) x.c w :=
  blockBits_eq_spec (supported_cdna3FP8 e4m3fnuz e5m2fnuz) x w

end MatrixCore.Spec
