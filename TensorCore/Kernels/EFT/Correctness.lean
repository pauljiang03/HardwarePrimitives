import TensorCore.Kernels.EFT.ScalarGuard

/-! Correctness and success of the 576-bit TC-EFT. -/

namespace TensorCore.EFMachine

set_option exponentiation.threshold 1024

/-- A shape-correct block with finite inputs and finite supplied D always prepares. -/
theorem prepare_exists {variant : Variant} {x : BlockInput variant.model} {D : F32} {s d : ℚ}
    (hlen : x.products.length = variant.model.nfma)
    (hx : TensorCore.exactDot x = some s) (hD : TensorCore.value32 D = some d) :
    ∃ p, prepare variant x D = .ok p := by
  cases hc : decode32Term x.c with
  | none =>
    have hz : TensorCore.value32 x.c = none := by rw [← decode32Word_value]; simp [decode32Word, hc]
    cases hd : decode32 x.c with
    | none => simp [TensorCore.exactDot, TensorCore.prepare, hd] at hx
    | some a => simp [TensorCore.value32, hd] at hz
  | some c =>
    cases hps : x.products.mapM (decodeProduct variant) with
    | none =>
      have hp := decodeProducts_values variant x.products
      rw [hps] at hp
      cases hr : TensorCore.prepareProducts variant.model x.products with
      | none => simp [TensorCore.exactDot, TensorCore.prepare, hr] at hx
      | some ps => simp [hr] at hp
    | some ps =>
      cases hd : decode32Word D with
      | none => rw [← decode32Word_value, hd] at hD; contradiction
      | some d =>
        unfold prepare
        simp only [hlen, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte, hc, hps, hd]
        exact ⟨_, rfl⟩

theorem Prepared.ideal_allZero {p : Prepared}
    (h : p.terms.all (fun t => t.word.magnitude == 0) = true) : p.ideal = 0 := by
  have ht : ∀ t ∈ p.terms, t.word.value = 0 := by
    intro t ht
    have hz := List.all_eq_true.mp h t ht
    simp only [beq_iff_eq] at hz
    simp [Word.value, Word.coefficient, hz, Rat.zero_mul]
  unfold Prepared.ideal
  suffices ∀ ts : List Term, (∀ t ∈ ts, t.word.value = 0) →
      sumQ (ts.map fun t => t.word.value) = 0 from this _ ht
  intro ts ht
  induction ts with
  | nil => rfl
  | cons t ts ih =>
    have hv := ht t (by simp)
    have hs := ih (by intro u hu; exact ht u (by simp [hu]))
    simp [sumQ, hv, hs, Rat.zero_add]

/-- Full bounded execution terminates without workspace overflow. -/
theorem tcEft_prepared {variant : Variant} {x : BlockInput variant.model} {D : F32} {p : Prepared}
    (hp : prepare variant x D = .ok p) :
    ∃ r, tcEft variant x D = .ok r ∧
      r.bits = TensorCore.round32 .nearestEven p.ideal := by
  have hcap := prepare_capacity hp
  obtain ⟨c, hc⟩ := extract_exists hcap.1 hcap.2
  have hs := extract_spec hc
  unfold tcEft
  simp only [hp, Bind.bind, Except.bind]
  by_cases hz : p.terms.all (fun t => t.word.magnitude == 0) = true
  · refine ⟨.allZero, ?_, ?_⟩
    · rw [if_pos hz]; rfl
    · rw [Prepared.ideal_allZero hz]; decide +kernel
  · cases hb : c.scalar with
    | some b =>
      refine ⟨.scalar b, by rw [if_neg hz, hc]; dsimp +instances only; rw [hb]; rfl, ?_⟩
      exact (Components.scalar_correct hp hc hb).symm
    | none =>
      have hr := c.recovered.round32_eq
      rw [hs.2.2.2.2.2.2.2] at hr
      cases hf : c.recovered.round32 with
      | none => exact ⟨.outOfRange, by rw [if_neg hz, hc]; dsimp +instances only; rw [hb, hf]; rfl, hf.symm.trans hr⟩
      | some b => exact ⟨.boundedExact b, by rw [if_neg hz, hc]; dsimp +instances only; rw [hb, hf]; rfl, hf.symm.trans hr⟩

/-- Universal finite-input theorem for all eight variants and any finite supplied D. -/
theorem tcEft_correct {variant : Variant} {x : BlockInput variant.model} {D : F32} {s d : ℚ}
    (hlen : x.products.length = variant.model.nfma)
    (hx : TensorCore.exactDot x = some s) (hD : TensorCore.value32 D = some d) :
    ∃ r, tcEft variant x D = .ok r ∧ r.bits = TensorCore.round32 .nearestEven s := by
  obtain ⟨p, hp⟩ := prepare_exists hlen hx hD
  have hi := (prepare_spec hp).2.1
  have hv : p.ideal = s := Option.some.inj (hi.symm.trans hx)
  obtain ⟨r, hr, hb⟩ := tcEft_prepared hp
  exact ⟨r, hr, by simpa [hv] using hb⟩

/-- Useful success family: every shape-correct finite block whose *independent* ideal is within the finite FP32 interval. -/
theorem tcEft_success {variant : Variant} {x : BlockInput variant.model} {D : F32} {s d : ℚ}
    (hlen : x.products.length = variant.model.nfma)
    (hx : TensorCore.exactDot x = some s) (hD : TensorCore.value32 D = some d)
    (hrange : absQ s ≤ maxFinite32) :
    ∃ r b, tcEft variant x D = .ok r ∧ r.bits = some b ∧ NearestEven32 s b := by
  obtain ⟨r, hr, hb⟩ := tcEft_correct hlen hx hD
  obtain ⟨b, hround, hn⟩ := round32_nearestEven_correct s hrange
  exact ⟨r, b, hr, hb.trans hround, hn⟩

/-- After valid decoding, range acceptance is both necessary and sufficient. -/
theorem tcEft_range_iff {variant : Variant} {x : BlockInput variant.model} {D : F32} {s d : ℚ}
    (hlen : x.products.length = variant.model.nfma)
    (hx : TensorCore.exactDot x = some s) (hD : TensorCore.value32 D = some d) :
    (∃ r b, tcEft variant x D = .ok r ∧ r.bits = some b) ↔ absQ s ≤ maxFinite32 := by
  constructor
  · rintro ⟨r, b, hr, hb⟩
    obtain ⟨r', hr', hb'⟩ := tcEft_correct hlen hx hD
    have he : r' = r := Except.ok.inj (hr'.symm.trans hr)
    subst r'
    exact TensorCore.round32_range (hb'.symm.trans hb)
  · intro h
    obtain ⟨r, b, hr, hb, _⟩ := tcEft_success hlen hx hD h
    exact ⟨r, b, hr, hb⟩


end TensorCore.EFMachine
