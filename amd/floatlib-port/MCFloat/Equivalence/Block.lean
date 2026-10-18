import MCFloat.Equivalence.Special

/-! # One block

For every pair of models that correspond (`Corresponds`), and for all input words, the FloatLib
block observes as Matrix-Core's `blockOutcome`: the same finite word, the same infinity, or
NaN. -/

set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false

namespace MCFloat.Equivalence
open FloatLib.Floats.Formats.BinaryInterchange

theorem map_agree {R : α → β → Prop} {f : α → γ} {g : β → γ} {xs : List α} {ys : List β}
    (h : List.Forall₂ R xs ys) (hfg : ∀ x y, R x y → f x = g y) : xs.map f = ys.map g := by
  induction h with
  | nil => rfl
  | cons hr _ ih => simp [ih, hfg _ _ hr]

theorem any_agree {R : α → β → Prop} {f : α → Bool} {g : β → Bool} {xs : List α} {ys : List β}
    (h : List.Forall₂ R xs ys) (hfg : ∀ x y, R x y → f x = g y) : xs.any f = ys.any g := by
  induction h with
  | nil => rfl
  | cons hr _ ih => simp [ih, hfg _ _ hr]

/-! ## CDNA 2 -/

theorem wordX_add32 {u v : MCFloat.F32} {X Y : MatrixCore.XVal} (hu : WordX u X) (hv : WordX v Y) :
    WordX (MCFloat.add32 u v) (MatrixCore.XVal.fl true (MatrixCore.XVal.add X Y)) := by
  cases X <;> cases Y <;> simp only [WordX] at hu hv
  · obtain ⟨t, ht, rfl⟩ := hu
    obtain ⟨t', ht', rfl⟩ := hv
    simp only [MCFloat.add32, ht, ht', MatrixCore.XVal.add]
    exact wordX_fl true _
  all_goals first
    | (obtain ⟨t, ht, rfl⟩ := hu
       simp [MCFloat.add32, ht, hv, MatrixCore.XVal.add, MatrixCore.XVal.fl, WordX, classify_nan32])
    | (obtain ⟨t, ht, rfl⟩ := hv
       simp [MCFloat.add32, ht, hu, MatrixCore.XVal.add, MatrixCore.XVal.fl, WordX, classify_nan32])
    | (rename_i s t
       by_cases hst : s = t <;>
         simp [MCFloat.add32, hu, hv, hst, MatrixCore.XVal.add, MatrixCore.XVal.fl, WordX,
           classify_nan32])
    | simp [MCFloat.add32, hu, hv, MatrixCore.XVal.add, MatrixCore.XVal.fl, WordX, classify_nan32]

theorem wordX_pairwiseGroupSum : ∀ (d : ℕ) {ws : List MCFloat.F32} {xs : List MatrixCore.XVal},
    List.Forall₂ WordX ws xs → WordX (MCFloat.pairwiseGroupSum d ws) (MatrixCore.pairwiseGroupSumX true d xs)
  | _, [], [], .nil => by
    simp only [MCFloat.pairwiseGroupSum, MatrixCore.pairwiseGroupSumX, WordX, classify_posZero]
    exact ⟨_, rfl, by simp [MCFloat.Term.value, FloatLib.Numerics.Dyadic.toRat,
      FloatLib.Numerics.Dyadic.signedSignificand]⟩
  | _, [_], [_], .cons h .nil => by simpa [MCFloat.pairwiseGroupSum, MatrixCore.pairwiseGroupSumX] using h
  | 0, _ :: _ :: _, _ :: _ :: _, _ => by
    simp [MCFloat.pairwiseGroupSum, MatrixCore.pairwiseGroupSumX, WordX, classify_nan32]
  | d + 1, w1 :: w2 :: ws, x1 :: x2 :: xs, h => by
    have hl := h.length_eq
    simp only [MCFloat.pairwiseGroupSum, MatrixCore.pairwiseGroupSumX]
    rw [hl]
    exact wordX_add32 (wordX_pairwiseGroupSum d (List.forall₂_take _ h)) (wordX_pairwiseGroupSum d (List.forall₂_drop _ h))

theorem flushed_agree {t : MCFloat.Term} {u : MatrixCore.Unpacked} (h : TermAgree t u) :
    t.flushed = (MatrixCore.Unpacked.flush u).value := by
  unfold MCFloat.Term.flushed MatrixCore.Unpacked.flush
  rw [h.small]
  by_cases hm : u.m < 2 ^ u.t
  · simp [hm, MatrixCore.Unpacked.value]
  · simp [hm, h.value]

theorem leaves_agree {as bs : List MCFloat.Term} {us vs : List MatrixCore.Unpacked}
    (ha : List.Forall₂ TermAgree as us) (hb : List.Forall₂ TermAgree bs vs) :
    List.Forall₂ WordX (List.zipWith (fun a b => MCFloat.fl true (a.flushed * b.flushed)) as bs)
      ((List.zipWith MatrixCore.Unpacked.mul (us.map MatrixCore.Unpacked.flush)
        (vs.map MatrixCore.Unpacked.flush)).map fun p =>
          MatrixCore.XVal.fl true (.fin p.value)) := by
  induction ha generalizing bs vs with
  | nil => simp
  | cons h _ ih =>
    cases hb with
    | nil => simp
    | cons h' hs =>
      simp only [List.zipWith_cons_cons, List.map_cons]
      refine .cons ?_ (ih hs)
      rw [MatrixCore.Unpacked.value_mul, ← flushed_agree h, ← flushed_agree h']
      exact wordX_fl true _

theorem observe_finish (c : ℚ) {t : MCFloat.F32} {T : MatrixCore.XVal} (h : WordX t T) :
    observe (match MCFloat.classifyModel t with
      | .finite q => MCFloat.fl true (c + q.value)
      | _ => t) = MatrixCore.finishOutcome true (MatrixCore.XVal.add (.fin c) T) := by
  cases T <;> simp only [WordX] at h
  · obtain ⟨q, hq, rfl⟩ := h
    simp only [hq, MatrixCore.XVal.add, MatrixCore.finishOutcome]
    exact observe_fl true _
  · simp [h, observe, MatrixCore.XVal.add, MatrixCore.finishOutcome]
  · simp [h, observe, MatrixCore.XVal.add, MatrixCore.finishOutcome]

theorem pairwise_agree (Q : MatrixCore.Model) (hs : Q.subnormals = false)
    {as bs : List MCFloat.Term} {us vs : List MatrixCore.Unpacked} {c : MCFloat.Term}
    {uc : MatrixCore.Unpacked} (ha : List.Forall₂ TermAgree as us)
    (hb : List.Forall₂ TermAgree bs vs) (hc : TermAgree c uc) :
    observe (MCFloat.pairwiseBlock as bs c) = MatrixCore.pairwiseOutcome Q ⟨us, vs, uc⟩ := by
  have hl := leaves_agree ha hb
  unfold MCFloat.pairwiseBlock MatrixCore.pairwiseOutcome
  simp only [hs, Bool.not_false, Bool.false_eq_true, ite_false, MatrixCore.Prepared.flushed,
    MatrixCore.Prepared.p]
  rw [hl.length_eq, flushed_agree hc]
  exact observe_finish _ (wordX_pairwiseGroupSum _ hl)

/-! ## Finite inputs -/

/-- An MCFloat model and a Matrix-Core model describe the same block. -/
structure Corresponds (P : MCFloat.MCModel) (Q : MatrixCore.Model) : Prop where
  a : OperandAgree P.a Q.a
  b : OperandAgree P.b Q.b
  nfma : P.nfma = Q.nfma
  rules : ProductRules P Q
  padding : Q.padding = 1
  cZero : Q.cZeroExp = some (-126)
  kind : match P.kind with
    | .exact => Q.accumulation = .correctRounding ∧ Q.subnormals = true
    | .pairwise => Q.accumulation = .pairWiseSum ∧ Q.subnormals = false
    | .late i cut => Q.accumulation = (if i then .oddEvenGrouping else .globalAlignment) ∧
        Q.subnormals = true ∧ Q.late = { cCutoff := cut }

theorem finiteBlock_agree {P : MCFloat.MCModel} {Q : MatrixCore.Model} (h : Corresponds P Q)
    {as bs : List MCFloat.Term} {us vs : List MatrixCore.Unpacked} {c : MCFloat.Term}
    {uc : MatrixCore.Unpacked} (ha : List.Forall₂ TermAgree as us)
    (hb : List.Forall₂ TermAgree bs vs) (hc : TermAgree c uc) :
    observe (MCFloat.finiteBlock P as bs c) = MatrixCore.finiteOutcome Q ⟨us, vs, uc⟩ := by
  have hp := zip_agree ha hb
  have hover : (P.productLimit && (List.zipWith MCFloat.Term.mul as bs).any
      (fun p => decide (MCFloat.pow2 128 ≤ |p.value|))) =
      (Q.productOverflow && (MatrixCore.Prepared.productOverflows ⟨us, vs, uc⟩)) := by
    rw [h.rules.limit]
    congr 1
    exact any_agree hp (fun p u hpu => by simp [hpu.value])
  unfold MCFloat.finiteBlock MatrixCore.finiteOutcome
  simp only
  rw [hover]
  split
  · rw [observe_special, List.map_map]
    congr 2
    apply map_agree hp
    intro p u hpu
    simp only [Function.comp_apply, hpu.value, abs_eq, pow2_eq]
    split <;> rfl
  · have hk := h.kind
    cases hkind : P.kind with
    | exact =>
      rw [hkind] at hk
      simp only [hk.1, hk.2, Bool.not_true]
      rw [observe_fl]
      congr 1
      simp only [MatrixCore.Prepared.exact, MatrixCore.Prepared.p]
      rw [sum_agree hp (fun p u hpu => hpu.value), hc.value]
    | pairwise =>
      rw [hkind] at hk
      simp only [hk.1]
      exact pairwise_agree Q hk.2 ha hb hc
    | late i cut =>
      rw [hkind] at hk
      obtain ⟨hacc, hsub, hlate⟩ := hk
      simp only [hsub, Bool.not_true]
      rw [observe_fl, lateC_agree Q cut h.cZero hlate hc,
        productSum_agree Q h.padding i hacc hp]
      cases i <;> simp only [hacc, ite_true, Bool.false_eq_true, ite_false] <;> rfl

/-! ## Any input words -/

/-- Finite-or-not agreement of decoded operands. -/
def Decoded (R : α → β → Prop) (o : Option α) (r : Option β) : Prop :=
  (∃ t u, o = some t ∧ r = some u ∧ R t u) ∨ (o = none ∧ r = none)

theorem mapM_agree {vs : List MCFloat.Value} {ds : List MatrixCore.Datum}
    (h : List.Forall₂ Agree vs ds) :
    Decoded (List.Forall₂ TermAgree) (vs.mapM MCFloat.Value.finite?)
      (ds.mapM MatrixCore.Datum.toFinite) := by
  induction h with
  | nil => exact .inl ⟨[], [], rfl, rfl, .nil⟩
  | @cons v d vs ds hvd _ ih =>
    cases v <;> cases d <;> simp only [Agree] at hvd
    · rcases ih with ⟨ts, us, h1, h2, h3⟩ | ⟨h1, h2⟩
      · left
        exact ⟨_ :: ts, _ :: us, by simp [List.mapM_cons, MCFloat.Value.finite?, h1],
          by simp [List.mapM_cons, MatrixCore.Datum.toFinite, h2], .cons hvd h3⟩
      · right
        simp [List.mapM_cons, MCFloat.Value.finite?, MatrixCore.Datum.toFinite, h1, h2]
    all_goals first
      | exact hvd.elim
      | (right; simp [List.mapM_cons, MCFloat.Value.finite?, MatrixCore.Datum.toFinite])

theorem single_agree {v : MCFloat.Value} {d : MatrixCore.Datum} (h : Agree v d) :
    Decoded TermAgree v.finite? d.toFinite := by
  cases v <;> cases d <;> simp only [Agree] at h
  · exact .inl ⟨_, _, rfl, rfl, h⟩
  all_goals first | exact h.elim | exact .inr ⟨rfl, rfl⟩

theorem match_agree {oa ob : Option (List MCFloat.Term)} {oc : Option MCFloat.Term}
    {ra rb : Option (List MatrixCore.Unpacked)} {rc : Option MatrixCore.Unpacked}
    (X : List MCFloat.Term → List MCFloat.Term → MCFloat.Term → MCFloat.F32) (S : MCFloat.F32)
    (F : MatrixCore.Prepared → MatrixCore.Outcome) (S' : MatrixCore.Outcome)
    (ha : Decoded (List.Forall₂ TermAgree) oa ra) (hb : Decoded (List.Forall₂ TermAgree) ob rb)
    (hc : Decoded TermAgree oc rc)
    (hfin : ∀ ts us ts' us' t u, List.Forall₂ TermAgree ts us → List.Forall₂ TermAgree ts' us' →
      TermAgree t u → observe (X ts ts' t) = F ⟨us, us', u⟩)
    (hsp : observe S = S') :
    Option.map observe (match (generalizing := false) oa, ob, oc with
      | some as, some bs, some ct => some (X as bs ct)
      | _, _, _ => some S) =
    (match (generalizing := false)
        (do let a ← ra; let b ← rb; let c ← rc; return (⟨a, b, c⟩ : MatrixCore.Prepared)) with
      | some px => some (F px)
      | none => some S') := by
  rcases ha with ⟨_, _, rfl, rfl, h1⟩ | ⟨rfl, rfl⟩
  · rcases hb with ⟨_, _, rfl, rfl, h2⟩ | ⟨rfl, rfl⟩
    · rcases hc with ⟨_, _, rfl, rfl, h3⟩ | ⟨rfl, rfl⟩
      · simp [hfin _ _ _ _ _ _ h1 h2 h3]
      · simp [hsp]
    · rcases hc with ⟨_, _, rfl, rfl, _⟩ | ⟨rfl, rfl⟩ <;> simp [hsp]
  · rcases hb with ⟨_, _, rfl, rfl, _⟩ | ⟨rfl, rfl⟩ <;>
      rcases hc with ⟨_, _, rfl, rfl, _⟩ | ⟨rfl, rfl⟩ <;> simp [hsp]

theorem read_agree {o : MCFloat.Operand} {i : MatrixCore.InputFormat} (h : OperandAgree o i)
    (ws : List i.Word) :
    List.Forall₂ Agree ((ws.map BitVec.toNat).map o.read) (ws.map i.read) := by
  induction ws with
  | nil => exact .nil
  | cons w ws ih => exact .cons (h w) ih

theorem products_agree {P : MCFloat.MCModel} {Q : MatrixCore.Model} (hP : ProductRules P Q)
    {A B : List MCFloat.Value} {DA DB : List MatrixCore.Datum}
    (ha : List.Forall₂ Agree A DA) (hb : List.Forall₂ Agree B DB) :
    (List.zipWith (MCFloat.product P) A B).map extX = List.zipWith (MatrixCore.productX Q) DA DB := by
  induction ha generalizing B DB with
  | nil => simp
  | cons h _ ih =>
    cases hb with
    | nil => simp
    | cons h' hs =>
      simp only [List.zipWith_cons_cons, List.map_cons]
      rw [product_agree hP h h', ih hs]

theorem mapM_map {f : β → Option γ} {g : α → β} (l : List α) :
    l.mapM (fun x => f (g x)) = (l.map g).mapM f := by
  induction l with
  | nil => rfl
  | cons x l ih => simp [List.mapM_cons, ih]

/-- **One block.** For corresponding models and any input words, the FloatLib block's result
word observes as Matrix-Core's `blockOutcome`. -/
theorem block_agree {P : MCFloat.MCModel} {Q : MatrixCore.Model} (h : Corresponds P Q)
    (x : MatrixCore.BlockInput Q) :
    (MCFloat.block P (x.a.map BitVec.toNat) (x.b.map BitVec.toNat) x.c.toNat).map observe =
      MatrixCore.blockOutcome x := by
  have hA := read_agree h.a x.a
  have hB := read_agree h.b x.b
  have hC : Agree (MCFloat.classify .binary32 x.c.toNat) (MatrixCore.fp32.decode x.c) :=
    fp32_agree x.c.toNat x.c.isLt
  have hspecial : observe (MCFloat.special ((MCFloat.classify .binary32 x.c.toNat).ext ::
      List.zipWith (MCFloat.product P) ((x.a.map BitVec.toNat).map P.a.read)
        ((x.b.map BitVec.toNat).map P.b.read))) =
      (MatrixCore.combineSpecial (MatrixCore.XVal.ofDatum (MatrixCore.fp32.decode x.c) ::
        MatrixCore.blockProducts x)).getD .nan := by
    rw [observe_special, List.map_cons, ext_agree hC, products_agree h.rules hA hB]
    unfold MatrixCore.blockProducts
    rw [List.zipWith_map]
  unfold MCFloat.block MatrixCore.blockOutcome MatrixCore.prepare
  simp only [List.length_map, h.nfma]
  split
  · rfl
  · rw [mapM_map (f := MatrixCore.Datum.toFinite) (g := Q.a.read),
      mapM_map (f := MatrixCore.Datum.toFinite) (g := Q.b.read)]
    exact match_agree _ _ _ _ (mapM_agree hA) (mapM_agree hB) (single_agree hC)
      (fun _ _ _ _ _ _ h1 h2 h3 => finiteBlock_agree h h1 h2 h3) hspecial

end MCFloat.Equivalence
