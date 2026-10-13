import TensorCore.Kernels.Datapath.Decode
import TensorCore.Kernels.Datapath.Normalize
import TensorCore.Kernels.EFT.Preparation
import TensorCore.TC.AcceptedDomain

/-! The bitvector datapath computes the Tensor Core model's output word on every input. -/

namespace TensorCore.Datapath

open EFMachine

set_option exponentiation.threshold 1024

/-- Valid terms whose nonzero exponents are positive. -/
def Term.Accepted (t : Term) : Prop := t.Valid ∧ (t.significand ≠ 0 → 1 ≤ t.biasedExp.toNat)

theorem product_spec {kind : InputKind} {x y : F32} {a b : Input}
    (ha : decodeInput kind x = some a) (hb : decodeInput kind y = some b) :
    (product a b).unnormalized = unnormalizedMul a.decoded b.decoded ∧ (product a b).Accepted := by
  obtain ⟨ha1, ha2, ha3, ha4⟩ := decodeInput_bounds ha
  obtain ⟨hb1, hb2, hb3, hb4⟩ := decodeInput_bounds hb
  have hmul : (multiplySignificands a.significand b.significand).toNat =
      a.significand.toNat * b.significand.toNat := by
    have hlt : a.significand.toNat * b.significand.toNat < 2 ^ 24 := by
      have := Nat.mul_lt_mul'' a.significand.isLt b.significand.isLt
      omega
    unfold multiplySignificands
    rw [BitVec.toNat_mul, BitVec.toNat_setWidth, BitVec.toNat_setWidth,
      Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le a.significand.isLt (by decide)),
      Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le b.significand.isLt (by decide)), Nat.mod_eq_of_lt hlt]
  have hexp : (a.biasedExp + b.biasedExp).toNat = a.biasedExp.toNat + b.biasedExp.toNat := by
    rw [BitVec.toNat_add, Nat.mod_eq_of_lt (by change _ < 512; omega)]
  have hmb : (a.mantissaBits + b.mantissaBits).toNat = a.mantissaBits.toNat + b.mantissaBits.toNat := by
    rw [BitVec.toNat_add, Nat.mod_eq_of_lt (by change _ < 32; omega)]
  refine ⟨?_, ⟨?_, ?_⟩, ?_⟩
  · simp only [Term.unnormalized, product, unnormalizedMul, Input.decoded, hmul, hexp, hmb,
      UnnormalizedProduct.mk.injEq]
    refine ⟨?_, by omega, by omega⟩
    cases a.negative <;> cases b.negative <;> simp [Int.neg_mul, Int.mul_neg]
  · simp only [product, hmul, hmb]
    have := Nat.mul_lt_mul'' ha1 hb1
    rw [← Nat.pow_add] at this
    rw [show a.mantissaBits.toNat + b.mantissaBits.toNat + 2 =
      a.mantissaBits.toNat + 1 + (b.mantissaBits.toNat + 1) by omega]
    exact this
  · simp only [product, hmb]; omega
  · intro _; simp only [product, hexp]; omega

theorem decodeC_accepted {bits : F32} {c : Term} (h : decodeC bits = some c) : c.Accepted := by
  have h1 := fp32_exponent9_toNat bits
  unfold decodeC at h
  dsimp only at h
  split at h
  · contradiction
  · rename_i he
    have h3 : (((bits >>> 23).setWidth 8).zeroExtend 9 : Exp).toNat ≠ 255 := by
      intro h'; exact he (by simpa using BitVec.eq_of_toNat_eq h')
    split at h
    · split at h <;> simp only [Option.some.injEq] at h <;> subst h <;>
        refine ⟨⟨?_, ?_⟩, ?_⟩ <;> dsimp only
      · decide
      · decide
      · intro h; exact absurd rfl h
      · exact Nat.lt_of_lt_of_le (BitVec.isLt _) (by decide)
      · decide
      · intro _; decide
    · simp only [Option.some.injEq] at h
      subst h
      refine ⟨⟨?_, ?_⟩, ?_⟩ <;> dsimp only
      · exact Nat.lt_of_lt_of_le (BitVec.isLt _) (by decide)
      · decide
      · intro _
        rw [BitVec.toNat_add, h1]
        change 1 ≤ (bits.toNat / 8388608 % 256 + 129) % 512
        omega

theorem decodeTerm_spec (variant : Variant) (pair : variant.model.Word × variant.model.Word) :
    (decodeTerm variant pair).map Term.unnormalized =
      ((do return (← variant.model.decode pair.1, ← variant.model.decode pair.2) :
        Option (Decoded × Decoded))).map (fun (a, b) => unnormalizedMul a b) := by
  rw [← decodeInput_model, ← decodeInput_model]
  cases ha : decodeInput variant.kind (pair.1.zeroExtend 32) with
  | none => simp [decodeTerm, ha]
  | some a =>
    cases hb : decodeInput variant.kind (pair.2.zeroExtend 32) with
    | none => simp [decodeTerm, ha, hb]
    | some b =>
      simp only [decodeTerm, ha, hb, Option.map_some, pure, bind, Option.bind]
      exact congrArg some (product_spec ha hb).1

theorem decodeTerm_accepted {variant : Variant} {pair : variant.model.Word × variant.model.Word} {t : Term}
    (h : decodeTerm variant pair = some t) : t.Accepted := by
  cases ha : decodeInput variant.kind (pair.1.zeroExtend 32) with
  | none => simp [decodeTerm, ha] at h
  | some a =>
    cases hb : decodeInput variant.kind (pair.2.zeroExtend 32) with
    | none => simp [decodeTerm, ha, hb] at h
    | some b =>
      simp [decodeTerm, ha, hb] at h
      rw [← h]
      exact (product_spec ha hb).2

theorem sumZ_map_zero (ts : List α) (f : α → ℤ) (h : ∀ t ∈ ts, f t = 0) : sumZ (ts.map f) = 0 := by
  induction ts with
  | nil => rfl
  | cons t ts ih =>
    simp only [List.map_cons, sumZ, h t (by simp), ih (fun u hu => h u (by simp [hu]))]
    rfl

theorem variant_eAlignMin (variant : Variant) :
    (variant.model.eAlignMin = none ∧ (eAlignMin variant).toNat = 0) ∨
      ∃ f, variant.model.eAlignMin = some f ∧ ((eAlignMin variant).toNat : ℤ) = f + 256 := by
  cases variant <;> decide

theorem variant_alignment (variant : Variant) :
    variant.model.alignFracBits = (alignBits variant).toNat ∧ 23 ≤ (alignBits variant).toNat ∧
      (alignBits variant).toNat ≤ 25 := by
  cases variant <;> decide

/-- The bitvector accumulator, read on its grid, is the model's aligned accumulator. -/
theorem accumulator_eq (variant : Variant) (ts : List Term) (b : PreparedBlock)
    (hprof : b.model = variant.model) (hterms : b.terms = ts.map Term.unnormalized)
    (hacc : ∀ t ∈ ts, t.Accepted) (hlen : ts.length = variant.model.nfma + 1) :
    ((accumulate variant (alignExp variant ts) ts).toInt : ℚ) *
      pow2 (((alignExp variant ts).toNat : ℤ) - 256 - (alignBits variant).toNat) = b.accumulator := by
  obtain ⟨hal, hF, _⟩ := variant_alignment variant
  obtain ⟨hA1, hA2, hA3⟩ := alignFold_spec ts (eAlignMin variant)
  change (eAlignMin variant).toNat ≤ (alignExp variant ts).toNat at hA1
  change ∀ t ∈ ts, t.significand ≠ 0 → t.biasedExp.toNat ≤ (alignExp variant ts).toNat at hA2
  change alignExp variant ts = eAlignMin variant ∨ ∃ t ∈ ts, t.significand ≠ 0 ∧ alignExp variant ts = t.biasedExp at hA3
  generalize hA : alignExp variant ts = A at hA1 hA2 hA3
  have htr : ∀ t ∈ ts, truncBits t.unnormalized.value ((A.toNat : ℤ) - 256 - (alignBits variant).toNat) =
      if t.negative then -((t.aligned variant A).toNat : ℤ) else ((t.aligned variant A).toNat : ℤ) :=
    fun t ht => t.truncBits_eq variant A (hacc t ht).1 hF (hA2 t ht)
  rw [accumulate_toInt variant A ts hlen, ← List.map_congr_left htr]
  have hsig : ∀ t : Term, t.unnormalized.significand = 0 ↔ t.significand = 0 := by
    intro t
    have : t.significand = 0 ↔ t.significand.toNat = 0 :=
      ⟨fun h => by rw [h]; rfl, fun h => BitVec.eq_of_toNat_eq (by rw [h]; rfl)⟩
    rw [this]
    unfold Term.unnormalized
    cases t.negative <;> simp
  unfold PreparedBlock.accumulator PreparedBlock.alignedBits
  rw [hterms, List.map_map]
  by_cases hall : ∀ t ∈ ts, t.significand = 0
  · have hv : ∀ t ∈ ts, t.unnormalized.value = 0 := by
      intro t ht
      simp [UnnormalizedProduct.value, (hsig t).mpr (hall t ht)]
    rw [sumZ_map_zero _ _ (fun t ht => by rw [hv t ht, truncBits_zero]),
      sumZ_map_zero _ _ (fun t ht => by simp only [Function.comp, hv t ht, truncBits_zero])]
    simp
  · have hex : ∃ t ∈ ts, t.significand ≠ 0 := by
      apply Classical.byContradiction
      intro h
      exact hall (fun t ht => Classical.byContradiction fun hz => h ⟨t, ht, hz⟩)
    obtain ⟨t0, ht0, hz0⟩ := hex
    have hmem : t0.unnormalized ∈ b.terms := by rw [hterms]; exact List.mem_map_of_mem ht0
    obtain ⟨m, hm, hm0⟩ := maxTermExp_term b.terms t0.unnormalized hmem (mt (hsig t0).mp hz0)
    have hup : m ≤ (A.toNat : ℤ) - 256 := by
      apply maxTermExp_upper b.terms _ _ m (by rw [hm]; rfl)
      intro u hu hnz
      rw [hterms] at hu
      obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hu
      have := hA2 t ht (mt (hsig t).mpr hnz)
      simp only [Term.unnormalized]
      omega
    have ht0E : (t0.biasedExp.toNat : ℤ) - 256 ≤ m := hm0
    have hlow : ∀ t ∈ ts, t.significand ≠ 0 → (t.biasedExp.toNat : ℤ) - 256 ≤ m := by
      intro t ht hnz
      obtain ⟨m', hm', hle⟩ := maxTermExp_term b.terms t.unnormalized
        (by rw [hterms]; exact List.mem_map_of_mem ht) (mt (hsig t).mp hnz)
      rw [hm] at hm'
      cases Option.some.inj hm'
      exact hle
    have hexp : b.alignExp = some ((A.toNat : ℤ) - 256) := by
      unfold PreparedBlock.alignExp Model.applyEAlignMin
      rw [hm, hprof]
      rcases variant_eAlignMin variant with ⟨hf, hf0⟩ | ⟨f, hf, hf0⟩
      · rw [hf]
        dsimp only
        congr 1
        rcases hA3 with h | ⟨t, ht, hnz, h⟩
        · exfalso
          have h1 := hA2 t0 ht0 hz0
          have h2 := (hacc t0 ht0).2 hz0
          rw [h, hf0] at h1
          omega
        · have := hlow t ht hnz
          have : A.toNat = t.biasedExp.toNat := by rw [h]
          omega
      · rw [hf]
        dsimp only
        congr 1
        rcases hA3 with h | ⟨t, ht, hnz, h⟩
        · have : A.toNat = (eAlignMin variant).toNat := by rw [h]
          omega
        · have := hlow t ht hnz
          have : A.toNat = t.biasedExp.toNat := by rw [h]
          omega
    have hgrid : b.alignGridExponent = (A.toNat : ℤ) - 256 - (alignBits variant).toNat := by
      unfold PreparedBlock.alignGridExponent
      rw [hexp, hprof, hal]
      rfl
    rw [hgrid]
    rfl

/-- The bitvector datapath returns the integer model's output word, or the same error, on every input. -/
theorem evalBlock_eq (variant : Variant) (x : BlockInput variant.model) :
    Datapath.evalBlock variant x = (TensorCore.evalBlock x).map (·.output.bits) := by
  unfold Datapath.evalBlock TensorCore.evalBlock
  by_cases hlen : x.products.length = variant.model.nfma
  · simp only [hlen, bne_self_eq_false, Bool.false_eq_true, if_false]
    have hmap := mapM_project_eq (f := decodeTerm variant) (v := Term.unnormalized)
      (g := fun (a, b) => do return (← variant.model.decode a, ← variant.model.decode b))
      (w := fun (a, b) => unnormalizedMul a b)
      (fun pair => by rcases pair with ⟨a, b⟩; exact decodeTerm_spec variant (a, b)) x.products
    have hcmap := decodeC_spec x.c
    cases hc : decodeC x.c with
    | none =>
      have hdc : decode32 x.c = none := by
        rw [hc] at hcmap
        cases hd : decode32 x.c with
        | none => rfl
        | some _ => rw [hd] at hcmap; simp at hcmap
      simp only [prepare, hdc]
      rfl
    | some c =>
      rw [hc] at hcmap
      obtain ⟨dc, hdc, hcs⟩ : ∃ dc, decode32 x.c = some dc ∧
          c.unnormalized = ⟨dc.significand, dc.unnormalizedExp, dc.mantissaBits⟩ := by
        cases hd : decode32 x.c with
        | none => rw [hd] at hcmap; simp at hcmap
        | some dc =>
          rw [hd] at hcmap
          exact ⟨dc, rfl, Option.some.inj hcmap⟩
      cases hps : x.products.mapM (decodeTerm variant) with
      | none =>
        have hpp : prepareProducts variant.model x.products = none := by
          unfold prepareProducts
          rw [hps] at hmap
          cases hq : x.products.mapM (fun (a, b) => do return (← variant.model.decode a, ← variant.model.decode b) :
              variant.model.Word × variant.model.Word → Option (Decoded × Decoded)) with
          | none => rfl
          | some _ => rw [hq] at hmap; simp at hmap
        simp only [prepare, hdc, hpp]
        rfl
      | some ps =>
        rw [hps] at hmap
        cases hpp : prepareProducts variant.model x.products with
        | none =>
          unfold prepareProducts at hpp
          rw [hpp] at hmap
          simp at hmap
        | some ds =>
          unfold prepareProducts at hpp
          rw [hpp] at hmap
          simp only [Option.map_some, Option.some.injEq] at hmap
          have hprep : prepare x = some ⟨variant.model, ds, dc⟩ := by
            simp only [prepare, hdc, prepareProducts, hpp]
          rw [hprep]
          dsimp only
          have hterms : (PreparedBlock.mk variant.model ds dc).terms =
              (c :: ps).map Term.unnormalized := by
            simp only [PreparedBlock.terms, List.map_cons, hcs]
            rw [hmap]
          obtain ⟨hpl, hpa⟩ := mapM_bounds (fun _ _ h => decodeTerm_accepted h) hps
          have hacc : ∀ t ∈ c :: ps, t.Accepted := by
            intro t ht
            rcases List.mem_cons.mp ht with rfl | ht
            · exact decodeC_accepted hc
            · exact hpa t ht
          have hlen' : (c :: ps).length = variant.model.nfma + 1 := by
            simp [hpl, hlen]
          have hw : 24 ≤ accWidth variant ∧ accWidth variant ≤ 64 := by
            cases variant <;> decide
          rw [normalize_eq _ _ _ hw.1 hw.2,
            accumulator_eq variant _ _ rfl hterms hacc hlen']
          unfold evalPrepared
          cases hr : round32 .truncate (PreparedBlock.mk variant.model ds dc).accumulator with
          | none => rfl
          | some bits =>
            obtain ⟨bits', d, hb', hd⟩ := round32_finite_exists .truncate _ (round32_range hr)
            rw [hr] at hb'
            cases Option.some.inj hb'
            have hf : finite32 bits = some ⟨bits, d, hd⟩ := by
              unfold finite32
              split
              · rename_i he; rw [hd] at he; contradiction
              · rename_i d' he; rw [hd] at he; cases Option.some.inj he; rfl
            simp only [hf]
            rfl
  · have hb : (x.products.length != variant.model.nfma) = true := by simpa using hlen
    rw [if_pos hb, if_pos hb]
    rfl

end TensorCore.Datapath
