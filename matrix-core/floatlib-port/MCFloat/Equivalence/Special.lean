import MCFloat.Equivalence.Stages

/-! # Special values

FloatLib's special-value results and products with special values observe as `combineSpecial`
and `productX`. -/

set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false

namespace MCFloat.Equivalence
open FloatLib.Floats.Formats.BinaryInterchange

def extX : MCFloat.Ext → MatrixCore.XVal
  | .fin q => .fin q
  | .inf s => .inf s
  | .nan => .nan

theorem observe_nan32 : observe MCFloat.nan32 = .nan := by decide +kernel
theorem observe_posInf : observe (Model.posInf .binary32) = .infinity false := by decide +kernel
theorem observe_negInf : observe (Model.negInf .binary32) = .infinity true := by decide +kernel
theorem classify_nan32 : MCFloat.classifyModel MCFloat.nan32 = .nan := by rfl
theorem classify_posZero :
    MCFloat.classifyModel (Model.posZero .binary32) = .finite ⟨⟨false, 0, 0⟩, -126, true⟩ := by
  rfl

theorem observe_special (xs : List MCFloat.Ext) :
    observe (MCFloat.special xs) = (MatrixCore.combineSpecial (xs.map extX)).getD .nan := by
  have h1 : ∀ e : MCFloat.Ext, (extX e == .nan) = e.isNaN := by
    intro e; cases e <;> rfl
  have h2 : ∀ (s : Bool) (e : MCFloat.Ext), (extX e == .inf s) = e.isInf s := by
    intro s e; cases e <;> simp [extX, MCFloat.Ext.isInf]
  unfold MCFloat.special MatrixCore.combineSpecial
  simp only [List.any_map, Function.comp_def, h1, h2]
  split_ifs <;> simp [observe_nan32, observe_posInf, observe_negInf]

theorem isInf_classify (w : MCFloat.F32) :
    Model.isInf w = (match MCFloat.classifyModel w with | .inf _ => true | _ => false) := by
  unfold MCFloat.classifyModel
  split_ifs with h1 h2
  · simp only [Model.isNaN, Model.isInf, Model.IEEE.isNaN, Model.IEEE.isInf,
      show FloatFormat.binary32.encoding = .ieee from rfl] at h1 ⊢
    simp only [Bool.and_eq_true, bne_iff_ne, ne_eq] at h1
    simp [h1.1, h1.2]
  · simp [h2]
  · simp only [Bool.not_eq_true] at h2
    rw [h2]; cases Model.toDyadic? w <;> rfl

theorem isInf_fl (ftz : Bool) (x : ℚ) :
    Model.isInf (MCFloat.fl ftz x) = (MatrixCore.flValue ftz x).isNone := by
  have h := wordX_fl ftz x
  rw [isInf_classify]
  unfold MatrixCore.XVal.fl at h
  cases hv : MatrixCore.flValue ftz x with
  | some v =>
    simp only [hv, WordX] at h
    obtain ⟨t, ht, _⟩ := h
    simp [ht]
  | none =>
    simp only [hv, WordX] at h
    simp [h]

/-! ## Products with special values -/

theorem ext_agree {v : MCFloat.Value} {d : MatrixCore.Datum} (h : Agree v d) :
    extX v.ext = MatrixCore.XVal.ofDatum d := by
  cases v <;> cases d <;> simp only [Agree] at h <;>
    simp only [extX, MCFloat.Value.ext, MatrixCore.XVal.ofDatum] <;>
    first | rw [h.value] | rw [h]

theorem sign_agree {t : MCFloat.Term} {u : MatrixCore.Unpacked} (h : TermAgree t u)
    (hz : t.isZero = false) : decide (u.value < 0) = t.dyadic.negative := by
  have hm : u.m ≠ 0 := by have := h.zero; simp_all
  rw [h.negative]
  cases hn : u.negative <;> simp [MatrixCore.Unpacked.value_neg_iff, hn, hm]

theorem zero_agree {t : MCFloat.Term} {u : MatrixCore.Unpacked} (h : TermAgree t u) :
    (u.value = 0) ↔ t.isZero = true := by
  rw [MatrixCore.Unpacked.value_eq_zero_iff, h.zero]; simp

/-- The models' product rules correspond. -/
structure ProductRules (P : MCFloat.MCModel) (Q : MatrixCore.Model) : Prop where
  limit : P.productLimit = Q.productOverflow
  pairwise : P.kind = .pairwise ↔ Q.accumulation = .pairWiseSum
  subnormals : Q.accumulation = .pairWiseSum → Q.subnormals = false

theorem product_agree {P : MCFloat.MCModel} {Q : MatrixCore.Model} (hP : ProductRules P Q)
    {va vb : MCFloat.Value} {da db : MatrixCore.Datum} (ha : Agree va da) (hb : Agree vb db) :
    extX (MCFloat.product P va vb) = MatrixCore.productX Q da db := by
  cases va <;> cases da <;> simp [Agree] at ha <;> cases vb <;> cases db <;> simp [Agree] at hb <;>
    simp only [MCFloat.product, MatrixCore.productX, MatrixCore.XVal.ofDatum, MatrixCore.XVal.mul,
      extX]
  · rename_i a u b v
    have hv := (mul_agree ha hb).value
    rw [hv, hP.limit]
    simp only [abs_eq, pow2_eq]
    by_cases ho : Q.productOverflow && decide (MCFloat.pow2 128 ≤ |(u.mul v).value|)
    · simp only [ho, ite_true, extX]
    · simp only [ho, Bool.false_eq_true, ite_false]
      by_cases hq : Q.accumulation = .pairWiseSum
      · have hk : P.kind = .pairwise := hP.pairwise.mpr hq
        rw [hk, isInf_fl, hP.subnormals hq]
        cases hf : MatrixCore.flValue true (u.mul v).value <;> simp [hf, hq, extX]
      · have hk : P.kind ≠ .pairwise := fun h => hq (hP.pairwise.mp h)
        revert hk
        cases P.kind <;> simp [hq, extX]
  all_goals first
    | (subst_vars; simp [extX])
    | (rename_i t u s s'
       subst_vars
       by_cases hz : t.isZero
       · simp [hz, (zero_agree ha).mpr hz, extX]
       · have hz' : t.isZero = false := by simpa using hz
         simp [hz', (zero_agree ha).not.mpr (by simp [hz']), sign_agree ha hz', extX])
    | (rename_i s s' t u
       subst_vars
       by_cases hz : t.isZero
       · simp [hz, (zero_agree hb).mpr hz, extX]
       · have hz' : t.isZero = false := by simpa using hz
         simp [hz', (zero_agree hb).not.mpr (by simp [hz']), sign_agree hb hz', extX])

end MCFloat.Equivalence
