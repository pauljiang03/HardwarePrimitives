import TensorCore.TC.Specification.Defs
import TensorCore.TC.AcceptedDomain
import TensorCore.TC.CanonicalFormats

/-! Bridges for decoding and the four pre-rounding stages. -/

namespace TensorCore.IndependentSpec

@[implicit_reducible] def layoutOf (f : Format) : Layout := ⟨f.mantissaBits, f.exponentBits, f.bias⟩
def parametersOf (p : Model) : Parameters :=
  ⟨layoutOf p.input, p.nfma, p.alignFracBits, p.eAlignMin⟩
def inputOf {p : Model} (x : BlockInput p) : Input (parametersOf p) := ⟨x.products, x.c⟩
def termOf (d : Decoded) : Term := ⟨d.value, d.unnormalizedExp⟩
def unnormalizedTermOf (t : UnnormalizedProduct) : Term := ⟨t.value, t.unnormalizedExp⟩

theorem decode_eq (f : Format) (n : ℕ) :
    decode (layoutOf f) n = ((classifyNat f n).finite).map termOf := by
  unfold decode layoutOf classifyNat
  dsimp only
  by_cases ht : n / 2 ^ f.mantissaBits % 2 ^ f.exponentBits = 2 ^ f.exponentBits - 1
  · simp only [ht, ↓reduceIte]
    split <;> rfl
  · simp only [ht, ↓reduceIte]
    by_cases he : n / 2 ^ f.mantissaBits % 2 ^ f.exponentBits = 0
    · by_cases hm : n % 2 ^ f.mantissaBits = 0
      · simp [he, hm, Classification.finite, termOf, Decoded.value]
      · by_cases hs : n / 2 ^ (f.mantissaBits + f.exponentBits) = 0
        all_goals simp only [he, hm, hs, bne_iff_ne, ne_eq, ↓reduceIte, not_false_eq_true, not_true_eq_false,
          and_false,
          Classification.finite, Option.map_some, termOf, Decoded.value,
          Rat.intCast_neg, Rat.intCast_natCast, Rat.intCast_one, Rat.one_mul, Rat.neg_mul, pow2]
    · by_cases hs : n / 2 ^ (f.mantissaBits + f.exponentBits) = 0
      all_goals simp only [he, hs, bne_iff_ne, ne_eq, ↓reduceIte, not_false_eq_true, not_true_eq_false,
        false_and,
        Classification.finite, Option.map_some, termOf, Decoded.value,
        Rat.intCast_neg, Rat.intCast_natCast, Rat.intCast_one, Rat.one_mul, Rat.neg_mul, pow2]

theorem product_eq (a b : Decoded) :
    product (termOf a) (termOf b) = unnormalizedTermOf (unnormalizedMul a b) := by
  change Term.mk (a.value * b.value) (a.unnormalizedExp + b.unnormalizedExp) =
    Term.mk (unnormalizedMul a b).value (unnormalizedMul a b).unnormalizedExp
  rw [unnormalizedProduct_value]
  rfl

theorem decode_products_eq (p : Model) (ps : List (p.Word × p.Word)) :
    (ps.mapM fun (a, b) => do
      return product (← decode (layoutOf p.input) a.toNat)
        (← decode (layoutOf p.input) b.toNat)) =
      (prepareProducts p ps).map (fun ds => ds.map fun (a, b) => unnormalizedTermOf (unnormalizedMul a b)) := by
  induction ps with
  | nil => rfl
  | cons ab rest ih =>
    rcases ab with ⟨a, b⟩
    simp only [prepareProducts, List.mapM_cons, decode_eq] at *
    cases ha : p.decode a <;> cases hb : p.decode b <;>
      cases hr : prepareProducts p rest <;>
      simp_all [Model.decode, classify, prepareProducts, product_eq]

theorem terms_eq {p : Model} (x : BlockInput p) :
    terms (parametersOf p) (inputOf x) =
      (prepare x).map (fun b => b.terms.map unnormalizedTermOf) := by
  unfold terms inputOf parametersOf
  change (do
    let c ← decode (layoutOf fp32) x.c.toNat
    let ps ← x.products.mapM fun (pair : p.Word × p.Word) => do
      return product (← decode (layoutOf p.input) pair.1.toNat)
        (← decode (layoutOf p.input) pair.2.toNat)
    return c :: ps) = _
  rw [decode_eq, decode_products_eq]
  change (do
    let c ← (decode32 x.c).map termOf
    let ps ← (prepareProducts p x.products).map
      (fun (ds : List (Decoded × Decoded)) => ds.map fun (a, b) => unnormalizedTermOf (unnormalizedMul a b))
    return c :: ps) = _
  unfold prepare
  cases decode32 x.c <;> cases prepareProducts p x.products <;>
    simp [PreparedBlock.terms, List.map_map, termOf, unnormalizedTermOf, UnnormalizedProduct.value, Decoded.value]

theorem unnormalizedProduct_value_zero (t : UnnormalizedProduct) : t.value = 0 ↔ t.significand = 0 := by
  unfold UnnormalizedProduct.value
  have hp := pow2_pos (t.unnormalizedExp - t.mantissaBits)
  constructor
  · intro h
    have hcast : (t.significand : ℚ) = 0 := by grind
    exact Rat.intCast_inj.mp (by simpa using hcast)
  · intro h; simp [h]

private theorem join_assoc (a b c : Option ℤ) :
    joinExponent (joinExponent a b) c = joinExponent a (joinExponent b c) := by
  cases a <;> cases b <;> cases c <;> simp [joinExponent] <;> omega

private theorem join_none (a : Option ℤ) : joinExponent a none = a := by
  cases a <;> rfl

private theorem fold_max (es : List ℤ) (acc : Option ℤ) :
    es.foldl (fun a e => some (match a with | none => e | some v => max v e)) acc =
      joinExponent acc (es.foldr (fun e a => joinExponent (some e) a) none) := by
  induction es generalizing acc with
  | nil => exact (join_none acc).symm
  | cons e es ih =>
    simp only [List.foldl_cons, List.foldr_cons]
    rw [ih]
    have he : some (match acc with | none => e | some v => max v e) =
        joinExponent acc (some e) := by cases acc <;> rfl
    rw [he, join_assoc]

theorem largestExponent_eq (ts : List UnnormalizedProduct) :
    largestExponent (ts.map unnormalizedTermOf) = maxTermExp ts := by
  unfold maxTermExp
  have hf := fold_max (ts.filterMap fun t => if t.significand = 0 then none else some t.unnormalizedExp) none
  refine Eq.trans ?_ hf.symm
  clear hf
  change largestExponent (ts.map unnormalizedTermOf) =
    (ts.filterMap fun t => if t.significand = 0 then none else some t.unnormalizedExp).foldr
      (fun e a => joinExponent (some e) a) none
  induction ts with
  | nil => rfl
  | cons t ts ih =>
    by_cases hz : t.significand = 0
    · have hv := (unnormalizedProduct_value_zero t).mpr hz
      simpa [largestExponent, unnormalizedTermOf, hz, hv] using ih
    · have hv : t.value ≠ 0 := fun h => hz ((unnormalizedProduct_value_zero t).mp h)
      simpa [largestExponent, unnormalizedTermOf, hz, hv] using congrArg (joinExponent (some t.unnormalizedExp)) ih

theorem exponent_eq (b : PreparedBlock) :
    exponent (parametersOf b.model) (b.terms.map unnormalizedTermOf) = b.alignExp := by
  unfold exponent PreparedBlock.alignExp
  rw [largestExponent_eq]
  cases maxTermExp b.terms <;> rfl

theorem coefficient_eq (v : ℚ) (e : ℤ) :
    keptBits v ((2 : ℚ) ^ e) = truncBits v e := by
  unfold keptBits magnitude truncBits pow2
  split <;> simp

theorem accumulated_eq (b : PreparedBlock) :
    accumulated (parametersOf b.model) (b.terms.map unnormalizedTermOf) = b.accumulator := by
  unfold accumulated
  rw [exponent_eq]
  change ((b.terms.map unnormalizedTermOf).foldr (fun t z =>
      keptBits t.value ((2 : ℚ) ^ b.alignGridExponent) + z) 0 : ℤ) *
      (2 : ℚ) ^ b.alignGridExponent = _
  unfold PreparedBlock.accumulator PreparedBlock.alignedBits
  apply congrArg (fun z : ℤ => (z : ℚ) * pow2 b.alignGridExponent)
  induction b.terms with
  | nil => rfl
  | cons t ts ih => simpa [unnormalizedTermOf, coefficient_eq, sumZ] using congrArg (truncBits t.value b.alignGridExponent + ·) ih

theorem valid_iff {p : Model} (x : BlockInput p) :
    Valid (parametersOf p) (inputOf x) ↔ ∃ t, evalBlock x = .ok t := by
  rw [evalBlock_success_iff]
  unfold Valid
  change (x.products.length = p.nfma ∧ _) ↔ _
  rw [terms_eq]
  cases hp : prepare x with
  | none => simp
  | some b =>
    have hprof := prepare_model hp
    simp only [Option.map_some, Option.some.injEq, exists_eq_left']
    have ha := accumulated_eq b
    rw [hprof] at ha
    rw [ha]
    rfl

end TensorCore.IndependentSpec
