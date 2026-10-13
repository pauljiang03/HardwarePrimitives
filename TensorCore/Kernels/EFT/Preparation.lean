import TensorCore.Kernels.EFT.Defs
import TensorCore.Kernels.EFT.Decode

/-! Correctness of bounded block preparation. -/

namespace TensorCore.EFMachine

set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
set_option exponentiation.threshold 1024

theorem decodeFactor_model (variant : Variant) (word : variant.model.Word) :
    (decodeFactor variant.kind (word.zeroExtend 32)).map Factor.decoded = variant.model.decode word := by
  rw [decodeFactor_asDecoded]
  cases variant <;> rw [BitVec.toNat_setWidth_of_le (by decide)] <;> rfl

theorem decodeProduct_value (variant : Variant) (pair : variant.model.Word × variant.model.Word) :
    (decodeProduct variant pair).map (fun t => t.word.value) =
      (do let a ← variant.model.decode pair.1
          let b ← variant.model.decode pair.2
          pure (a.value * b.value) : Option ℚ) := by
  rw [← decodeFactor_model, ← decodeFactor_model]
  cases ha : decodeFactor variant.kind (pair.1.zeroExtend 32) with
  | none => simp [decodeProduct, ha]
  | some a =>
    cases hb : decodeFactor variant.kind (pair.2.zeroExtend 32) with
    | none => simp [decodeProduct, ha, hb]
    | some b =>
      simp only [decodeProduct, ha, hb, Option.map_some, pure]
      exact congrArg some ((product_value (decodeFactor_bounds ha)
        (decodeFactor_bounds hb)).trans (unnormalizedProduct_value _ _))

theorem decodeProduct_magnitude {variant : Variant} {pair : variant.model.Word × variant.model.Word}
    {t : Term} (h : decodeProduct variant pair = some t) : t.word.magnitude.toNat < 2 ^ 550 := by
  cases ha : decodeFactor variant.kind (pair.1.zeroExtend 32) with
  | none => simp [decodeProduct, ha] at h
  | some a =>
    cases hb : decodeFactor variant.kind (pair.2.zeroExtend 32) with
    | none => simp [decodeProduct, ha, hb] at h
    | some b =>
      simp [decodeProduct, ha, hb] at h
      rw [← h]
      exact product_magnitude (decodeFactor_bounds ha) (decodeFactor_bounds hb)

theorem mapM_project_eq {f : α → Option β} {g : α → Option γ} {v : β → δ} {w : γ → δ}
    (h : ∀ x, (f x).map v = (g x).map w) (xs : List α) :
    (xs.mapM f).map (List.map v) = (xs.mapM g).map (List.map w) := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    have hh := h x
    cases hf : f x <;> cases hg : g x <;>
      cases hfs : xs.mapM f <;> cases hgs : xs.mapM g <;>
      simp_all [List.mapM_cons]

theorem mapM_bounds {f : α → Option β} {P : β → Prop}
    (hf : ∀ x y, f x = some y → P y) {xs : List α} {ys : List β}
    (h : xs.mapM f = some ys) : ys.length = xs.length ∧ ∀ y ∈ ys, P y := by
  induction xs generalizing ys with
  | nil => simp at h; subst ys; simp
  | cons x xs ih =>
    cases hh : f x with
    | none => simp [List.mapM_cons, hh] at h
    | some y =>
      cases ht : xs.mapM f with
      | none => simp [List.mapM_cons, hh, ht] at h
      | some zs =>
        simp [List.mapM_cons, hh, ht] at h
        subst ys
        obtain ⟨hlen, hP⟩ := ih ht
        refine ⟨by simp [hlen], ?_⟩
        intro z hz
        rcases List.mem_cons.mp hz with rfl | hz
        · exact hf x z hh
        · exact hP z hz

theorem decodeProducts_values (variant : Variant) (ps : List (variant.model.Word × variant.model.Word)) :
    (ps.mapM (decodeProduct variant)).map (fun ts => ts.map fun t => t.word.value) =
      (TensorCore.prepareProducts variant.model ps).map
        (fun ds => ds.map fun (a, b) => a.value * b.value) := by
  apply mapM_project_eq
  intro pair
  rw [decodeProduct_value]
  rcases pair with ⟨a, b⟩
  dsimp only
  cases variant.model.decode a <;> cases variant.model.decode b <;> rfl

def Prepared.ideal (p : Prepared) : ℚ := sumQ (p.terms.map fun t => t.word.value)

theorem prepare_spec {variant : Variant} {x : BlockInput variant.model} {D : F32} {p : Prepared}
    (h : prepare variant x D = .ok p) :
    x.products.length = variant.model.nfma ∧
      TensorCore.exactDot x = some p.ideal ∧
      TensorCore.value32 D = some p.output.value ∧
      p.terms.length = variant.model.nfma + 1 ∧
      (∀ t ∈ p.terms, t.word.magnitude.toNat < 2 ^ 550) ∧
      p.output.magnitude.toNat < 2 ^ 424 := by
  unfold prepare at h
  dsimp only at h
  split at h
  · contradiction
  · rename_i hlen
    have hlen' : x.products.length = variant.model.nfma := by simpa using hlen
    cases hc : decode32Term x.c with
    | none => simp [hc] at h
    | some c =>
      cases hps : x.products.mapM (decodeProduct variant) with
      | none => simp [hc, hps] at h
      | some ps =>
        cases hd : decode32Word D with
        | none => simp [hc, hps, hd] at h
        | some d =>
          simp [hc, hps, hd, pure, Except.pure] at h
          subst p
          have hdc : decode32Word x.c = some c.word := by simp [decode32Word, hc]
          have hvc : TensorCore.value32 x.c = some c.word.value := by
            rw [← decode32Word_value, hdc]; rfl
          have hvd : TensorCore.value32 D = some d.value := by
            rw [← decode32Word_value, hd]; rfl
          have hvs := decodeProducts_values variant x.products
          rw [hps] at hvs
          cases hp : TensorCore.prepareProducts variant.model x.products with
          | none => simp [hp] at hvs
          | some ds =>
            simp only [hp, Option.map_some, Option.some.injEq] at hvs
            have hb := mapM_bounds (fun a b h => decodeProduct_magnitude h) hps
            have hmb := decode32Word_magnitude hdc
            refine ⟨hlen', ?_, hvd, by simp [← hlen', hb.1], ?_, decode32Word_magnitude hd⟩
            · cases hcc : decode32 x.c with
              | none => simp [TensorCore.value32, hcc] at hvc
              | some dc =>
                simp only [TensorCore.value32, hcc, Option.map_some, Option.some.injEq] at hvc
                simp only [TensorCore.exactDot, TensorCore.prepare, hcc, hp, Option.map_some,
                  PreparedBlock.exactDot, PreparedBlock.exactProducts, Prepared.ideal,
                  List.map_cons, sumQ]
                rw [hvc, ← hvs]
            · intro t ht
              rcases List.mem_cons.mp ht with rfl | ht
              · omega
              · exact hb.2 t ht

theorem variant_count (variant : Variant) : variant.model.nfma ≤ 16 := by cases variant <;> decide

theorem prepare_capacity {variant : Variant} {x : BlockInput variant.model} {D : F32} {p : Prepared}
    (h : prepare variant x D = .ok p) :
    wordMagnitudeSum (p.terms.map Term.word) < 2 ^ 555 ∧ p.output.magnitude.toNat < 2 ^ 424 := by
  obtain ⟨_, _, _, hlen, ht, hd⟩ := prepare_spec h
  have hc := variant_count variant
  have hb : wordMagnitudeSum (p.terms.map Term.word) ≤ p.terms.length * (2 ^ 550 - 1) := by
    suffices ∀ ts : List Term, (∀ t ∈ ts, t.word.magnitude.toNat < 2 ^ 550) →
        wordMagnitudeSum (ts.map Term.word) ≤ ts.length * (2 ^ 550 - 1) from this p.terms ht
    intro ts ht
    induction ts with
    | nil => simp [wordMagnitudeSum]
    | cons t ts ih =>
      have hm := ht t (by simp)
      have hh := ih (by intro u hu; exact ht u (by simp [hu]))
      simp only [List.map_cons, wordMagnitudeSum, List.sum_cons, List.length_cons]
      simp only [wordMagnitudeSum, List.map_map] at hh
      simp only [List.map_map]
      omega
  exact ⟨by omega, hd⟩

end TensorCore.EFMachine
