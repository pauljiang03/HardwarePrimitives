import MatrixCore.MC.AcceptedDomain

/-! # `correct_rounding`: CDNA 1 and the SFMA

The output is the FP32 value nearest to the exact `Σ a_ℓ b_ℓ + c`, and it is sign-symmetric. -/

namespace MatrixCore

theorem Prepared.exact_eq (x : Prepared) :
    x.exact = sumQ (List.zipWith (fun a b => a.value * b.value) x.a x.b) + x.c.value := by
  unfold Prepared.exact Prepared.p
  congr 1
  generalize x.a = as
  generalize x.b = bs
  induction as generalizing bs with
  | nil => simp
  | cons a as ih =>
    cases bs with
    | nil => simp
    | cons b bs => simp [sumQ, Unpacked.value_mul]

theorem accumulate_correctRounding {P : Model} (hacc : P.accumulation = .correctRounding)
    (hov : P.productOverflow = false) (x : Prepared) : accumulate P x = .ok x.exact := by
  unfold accumulate; simp [hov, hacc]

/-- CDNA 1 and SFMA: an accepted block returns the FP32 value nearest the exact `Σ a_ℓ b_ℓ + c`. -/
theorem correctRounding_nearestEven {P : Model} (hacc : P.accumulation = .correctRounding)
    (hov : P.productOverflow = false) (hs : P.subnormals = true)
    {x : BlockInput P} {t : BlockTrace P} (h : evalBlock x = .ok t) :
    t.sAcc = t.prepared.exact ∧ NearestEven32 t.prepared.exact t.d := by
  obtain ⟨_, _, _, ha, _⟩ := evalBlock_ok h
  rw [accumulate_correctRounding hacc hov] at ha
  have he : t.sAcc = t.prepared.exact := by injection ha with ha; exact ha.symm
  refine ⟨he, ?_⟩
  rw [← he]; exact evalBlock_nearestEven h hs

/-- CDNA 1 and SFMA accept exactly the finite inputs with exact sum below the overflow threshold. -/
theorem correctRounding_success_iff {P : Model} (hacc : P.accumulation = .correctRounding)
    (hov : P.productOverflow = false) (x : BlockInput P) :
    (∃ t, evalBlock x = .ok t) ↔
      x.a.length = P.nfma ∧ x.b.length = P.nfma ∧
        ∃ px, prepare x = some px ∧ absQ px.exact < overflowThreshold32 := by
  rw [evalBlock_success_iff]
  constructor
  · rintro ⟨ha, hb, px, s, hp, hs, hr⟩
    rw [accumulate_correctRounding hacc hov] at hs
    injection hs with hs; subst hs
    exact ⟨ha, hb, px, hp, hr⟩
  · rintro ⟨ha, hb, px, hp, hr⟩
    exact ⟨ha, hb, px, px.exact, hp, accumulate_correctRounding hacc hov px, hr⟩

theorem sfmaF32_nearestEven {x : BlockInput sfmaF32} {t : BlockTrace sfmaF32}
    (h : evalBlock x = .ok t) : NearestEven32 t.prepared.exact t.d :=
  (correctRounding_nearestEven rfl rfl rfl h).2

theorem cdna1F16_nearestEven {x : BlockInput cdna1F16} {t : BlockTrace cdna1F16}
    (h : evalBlock x = .ok t) : NearestEven32 t.prepared.exact t.d :=
  (correctRounding_nearestEven rfl rfl rfl h).2

theorem cdna1BF16_nearestEven {x : BlockInput cdna1BF16} {t : BlockTrace cdna1BF16}
    (h : evalBlock x = .ok t) : NearestEven32 t.prepared.exact t.d :=
  (correctRounding_nearestEven rfl rfl rfl h).2

/-! ## Sign symmetry -/

theorem rneValue_neg (x : ℚ) : rneValue (-x) = -rneValue x := by
  unfold rneValue
  rw [absQ_neg]
  by_cases h : x < 0
  · have : ¬ (-x < 0) := by grind
    simp [h, this]
  · by_cases h0 : x = 0
    · subst h0
      simp only [Rat.neg_zero, Rat.lt_irrefl, ↓reduceIte]
      have : rneMagnitude (absQ 0) = 0 := by
        have := rneValue_zero; unfold rneValue at this; simpa using this
      rw [this]; simp
    · have : -x < 0 := by grind
      simp [h, this]

theorem correctRounding_value {P : Model} (hacc : P.accumulation = .correctRounding)
    (hov : P.productOverflow = false) (hs : P.subnormals = true)
    {x : BlockInput P} {t : BlockTrace P} (h : evalBlock x = .ok t) :
    value32 t.d = some (rneValue t.prepared.exact) := by
  obtain ⟨_, _, _, ha, hd⟩ := evalBlock_ok h
  rw [accumulate_correctRounding hacc hov] at ha
  injection ha with ha
  rw [hs] at hd
  rw [ha]
  exact rne32_value (by simpa [fl32_false] using hd)

theorem correctRounding_neg {P : Model} (hacc : P.accumulation = .correctRounding)
    (hov : P.productOverflow = false) (hs : P.subnormals = true)
    {x y : BlockInput P} {t u : BlockTrace P} (hx : evalBlock x = .ok t)
    (hy : evalBlock y = .ok u) (hneg : u.prepared.exact = -t.prepared.exact) :
    value32 u.d = (value32 t.d).map (- ·) := by
  rw [correctRounding_value hacc hov hs hx, correctRounding_value hacc hov hs hy, hneg,
    rneValue_neg]
  rfl

end MatrixCore
