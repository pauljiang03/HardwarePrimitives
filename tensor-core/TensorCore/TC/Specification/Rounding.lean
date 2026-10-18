import TensorCore.TC.Specification.Stages
import TensorCore.Numerics.Binary.CorrectRounding
import TensorCore.Numerics.RoundTrip

/-! The rounding relation selects unique bits, including signed zero, and `round32` satisfies it. -/

namespace TensorCore.IndependentSpec

set_option maxRecDepth 4096

theorem value32_eq (b : BitVec 32) : value32 b = TensorCore.value32 b := by
  unfold value32
  change (decode (layoutOf TensorCore.fp32) b.toNat).map Term.value = _
  rw [decode_eq]
  simp only [Option.map_map]
  rfl

theorem magnitude_eq (x : ℚ) : magnitude x = absQ x := rfl
theorem maxFinite_eq : maxFinite = maxFinite32 := rfl
theorem between_eq (x y : ℚ) : Between x y ↔ Between0 x y := Iff.rfl

private theorem encode32_sign (negative : Bool) (e k : ℤ)
    (he1 : -126 ≤ e) (he2 : e ≤ 127) (hk0 : 0 ≤ k) (hk1 : k < 2 ^ 24) :
    ((encode32 negative e k).toNat / 2147483648 != 0) = negative := by
  rw [encode32_toNat negative e k hk0 hk1 he1 he2]
  cases negative <;> simp only [Bool.false_eq_true, ↓reduceIte, Nat.reducePow]
  all_goals split <;> simp <;> omega

theorem round32_sign (x : ℚ) (b : F32) (h : round32 .truncate x = some b) :
    (b.toNat / 2147483648 != 0) = decide (x < 0) := by
  by_cases hz : x = 0
  · subst x
    have hzero : round32 .truncate 0 = some 0 := by decide +kernel
    have hb : b = 0 := by simpa only [hzero, Option.some.injEq] using h.symm
    subst b
    decide
  have hr := round32_range h
  have hm := absQ_pos_of_ne_zero x hz
  obtain ⟨he1, he2, _, _⟩ := normExp_bounds (absQ x) hm hr
  obtain ⟨hk0, hk1, hsub, htop⟩ := roundedSignificand_bounds .truncate (absQ x) hm hr
  have hs := carry_spec _ _ he1 he2 hk0 hk1 hsub htop
  unfold round32 round32Core at h
  rw [if_neg (Rat.not_lt.mpr hr), if_neg hz] at h
  generalize hp : carry (normExp (absQ x)) (roundedSignificand .truncate (absQ x)) = pair at h hs
  rcases pair with ⟨e, k⟩
  dsimp only at h hs
  rw [if_neg (by omega)] at h
  cases Option.some.inj h
  exact encode32_sign _ _ _ hs.1 hs.2.1 hs.2.2.1 hs.2.2.2.1

theorem round32_rounds (x : ℚ) (b : F32) (h : round32 .truncate x = some b) :
    Rounds x b := by
  have hr := round32_range h
  obtain ⟨bits, hb, hc⟩ := roundBinary_truncate_correct TensorCore.fp32 (by decide) x hr
  change round32 .truncate x = some bits at hb
  rw [h] at hb
  cases Option.some.inj hb
  obtain ⟨d, hd, hbetween, hmax⟩ := hc
  refine ⟨round32_sign x b h, d, ?_, hbetween, ?_⟩
  · rw [value32_eq]; exact hd
  · intro other y hy hxy
    rw [value32_eq] at hy
    exact hmax y (value32_finite other y hy) hxy

private theorem zero_bits (b : F32) (h : TensorCore.value32 b = some 0) :
    b.toNat = 0 ∨ b.toNat = 2147483648 := by
  cases hd : decode32 b with
  | none => simp [TensorCore.value32, hd] at h
  | some d =>
    have hv : d.value = 0 := by simpa [TensorCore.value32, hd] using h
    have hs : d.significand = 0 := by
      have hp := pow2_pos (d.exponent - d.mantissaBits)
      unfold Decoded.value at hv
      have hc : (d.significand : ℚ) = 0 := by grind
      exact Rat.intCast_inj.mp (by simpa using hc)
    have hlt := b.isLt
    rcases decode32_fields b d hd with ⟨_, _, rfl⟩ | ⟨_, hm, rfl⟩ | ⟨_, _, rfl⟩
    · omega
    · dsimp only at hs
      split at hs <;> omega
    · dsimp only at hs
      split at hs <;> omega

theorem rounds_unique (x : ℚ) (a b : F32) (ha : Rounds x a) (hb : Rounds x b) : a = b := by
  obtain ⟨hsa, va, hva, hba, hma⟩ := ha
  obtain ⟨hsb, vb, hvb, hbb, hmb⟩ := hb
  have hle := hma b vb hvb hbb
  have hge := hmb a va hva hba
  have hv : va = vb := by
    unfold Between magnitude at *
    grind
  subst vb
  rw [value32_eq] at hva hvb
  by_cases hz : va = 0
  · subst va
    have za := zero_bits a hva
    have zb := zero_bits b hvb
    have hsign := hsa.trans hsb.symm
    apply BitVec.eq_of_toNat_eq
    rcases za with za | za <;> rcases zb with zb | zb <;> simp_all
  · exact value32_injective a b va hva hvb hz

theorem rounds_iff (x : ℚ) (b : F32) (hr : magnitude x ≤ maxFinite) :
    Rounds x b ↔ round32 .truncate x = some b := by
  constructor
  · intro h
    obtain ⟨a, _, ha, _⟩ := round32_finite_exists .truncate x hr
    have hab := rounds_unique x a b (round32_rounds x a ha) h
    rwa [hab] at ha
  · exact round32_rounds x b

/-! ## Round to nearest, ties to even -/

theorem round32_sign_nearestEven (x : ℚ) (b : F32) (h : round32 .nearestEven x = some b) :
    (b.toNat / 2147483648 != 0) = decide (x < 0) := by
  by_cases hz : x = 0
  · subst x
    have hzero : round32 .nearestEven 0 = some 0 := by decide +kernel
    have hb : b = 0 := by simpa only [hzero, Option.some.injEq] using h.symm
    subst b
    decide
  have hr := round32_range h
  have hm := absQ_pos_of_ne_zero x hz
  obtain ⟨he1, he2, _, _⟩ := normExp_bounds (absQ x) hm hr
  obtain ⟨hk0, hk1, hsub, htop⟩ := roundedSignificand_bounds .nearestEven (absQ x) hm hr
  have hs := carry_spec _ _ he1 he2 hk0 hk1 hsub htop
  unfold round32 round32Core at h
  rw [if_neg (Rat.not_lt.mpr hr), if_neg hz] at h
  generalize hp : carry (normExp (absQ x)) (roundedSignificand .nearestEven (absQ x)) = pair at h hs
  rcases pair with ⟨e, k⟩
  dsimp only at h hs
  rw [if_neg (by omega)] at h
  cases Option.some.inj h
  exact encode32_sign _ _ _ hs.1 hs.2.1 hs.2.2.1 hs.2.2.2.1

theorem rneInt_tie_even (t : ℚ) (h : 2 * absQ (t - rneInt t) = 1) : rneInt t % 2 = 0 := by
  have hf := Rat.floor_le t
  have hf' := Rat.lt_floor_add_one t
  unfold rneInt at h ⊢
  split
  · rename_i hc
    rw [if_pos hc] at h
    rcases hc with hc | ⟨_, hodd⟩
    · exfalso
      rw [absQ_of_neg (by push_cast at hf' ⊢; grind)] at h
      push_cast at h; grind
    · omega
  · rename_i hc
    rw [if_neg hc] at h
    rw [absQ_of_nonneg (by grind)] at h
    have : 2 * (t - t.floor) = 1 := by grind
    have : ¬ t.floor % 2 = 1 := fun h' => hc (Or.inr ⟨this, h'⟩)
    omega

theorem binade_unique {m : ℚ} {e e' : ℤ}
    (h : -126 ≤ e ∧ m < pow2 (e + 1) ∧ (e = -126 ∨ pow2 e ≤ m))
    (h' : -126 ≤ e' ∧ m < pow2 (e' + 1) ∧ (e' = -126 ∨ pow2 e' ≤ m)) : e = e' := by
  have key : ∀ {a b : ℤ}, (-126 ≤ a ∧ m < pow2 (a + 1) ∧ (a = -126 ∨ pow2 a ≤ m)) →
      (-126 ≤ b ∧ m < pow2 (b + 1) ∧ (b = -126 ∨ pow2 b ≤ m)) → ¬ a < b := by
    intro a b ha hb hab
    rcases hb.2.2 with hb2 | hb2
    · omega
    · have := pow2_le_of_le (show a + 1 ≤ b by omega)
      have := Std.lt_of_lt_of_le ha.2.1 (Rat.le_trans this hb2)
      grind
  rcases Int.lt_trichotomy e e' with hlt | heq | hgt
  · exact absurd hlt (key h h')
  · exact heq
  · exact absurd hgt (key h' h)

theorem nearestEven_int_unique {t : ℚ} {k k' : ℤ}
    (h1 : 2 * absQ (t - k) ≤ 1) (h2 : 2 * absQ (t - k) = 1 → k % 2 = 0)
    (h1' : 2 * absQ (t - k') ≤ 1) (h2' : 2 * absQ (t - k') = 1 → k' % 2 = 0) : k = k' := by
  have a1 := (absQ_le_iff (t - k) (1 / 2)).mp (by grind)
  have a1' := (absQ_le_iff (t - k') (1 / 2)).mp (by grind)
  have hd1 : k - k' ≤ 1 := by
    have : ((k - k' : ℤ) : ℚ) ≤ 1 := by push_cast; grind
    exact_mod_cast this
  have hd2 : k' - k ≤ 1 := by
    have : ((k' - k : ℤ) : ℚ) ≤ 1 := by push_cast; grind
    exact_mod_cast this
  rcases Int.lt_trichotomy k k' with hlt | heq | hgt
  · have hk' : k' = k + 1 := by omega
    subst hk'
    push_cast at a1'
    have ha : 2 * absQ (t - k) = 1 := by rw [absQ_of_nonneg (by grind)]; grind
    have hb : 2 * absQ (t - ((k + 1 : ℤ) : ℚ)) = 1 := by
      rw [absQ_of_neg (by push_cast; grind)]; push_cast; grind
    have := h2 ha; have := h2' hb; omega
  · exact heq
  · have hk : k = k' + 1 := by omega
    subst hk
    push_cast at a1
    have ha : 2 * absQ (t - k') = 1 := by rw [absQ_of_nonneg (by grind)]; grind
    have hb : 2 * absQ (t - ((k' + 1 : ℤ) : ℚ)) = 1 := by
      rw [absQ_of_neg (by push_cast; grind)]; push_cast; grind
    have := h2' ha; have := h2 hb; omega

theorem round32_nearestEven_rounds (x : ℚ) (b : F32) (h : round32 .nearestEven x = some b) :
    RoundsNearestEven x b := by
  refine ⟨round32_sign_nearestEven x b h, ?_⟩
  by_cases hz : x = 0
  · subst x
    have hb : b = 0 := by
      have h0 : round32 .nearestEven 0 = some 0 := by decide +kernel
      rw [h0] at h; exact (Option.some.inj h).symm
    subst hb
    refine ⟨-126, 0, Int.le_refl _, by decide +kernel, Or.inl rfl, by decide +kernel,
      fun h => by decide +kernel, by decide +kernel⟩
  · obtain ⟨b', hb', hv, _, _⟩ := round32_nonzero_spec .nearestEven x hz (round32_range h)
    rw [h] at hb'
    cases Option.some.inj hb'
    have hm := absQ_pos_of_ne_zero x hz
    obtain ⟨he1, _, he3, he4⟩ := normExp_bounds (absQ x) hm (round32_range h)
    refine ⟨normExp (absQ x), rneInt (absQ x / pow2 (normExp (absQ x) - 23)), he1, he3, he4.symm,
      rneInt_dist_le_half _, rneInt_tie_even _, ?_⟩
    rw [value32_eq, hv]
    congr 1
    show signedRounded .nearestEven x = _
    unfold signedRounded magnitudeRounded roundedSignificand roundSignificand
    change _ = (if x < 0 then -1 else 1) * _ * pow2 (normExp (absQ x) - 23)
    split <;> grind

theorem roundsNearestEven_unique (x : ℚ) (a b : F32) (ha : RoundsNearestEven x a)
    (hb : RoundsNearestEven x b) : a = b := by
  obtain ⟨hsa, e, k, he1, he2, he3, hk1, hk2, hva⟩ := ha
  obtain ⟨hsb, e', k', he1', he2', he3', hk1', hk2', hvb⟩ := hb
  have hee : e = e' := binade_unique (m := absQ x) ⟨he1, he2, he3⟩ ⟨he1', he2', he3'⟩
  subst hee
  have hkk : k = k' := nearestEven_int_unique hk1 hk2 hk1' hk2'
  subst hkk
  rw [value32_eq] at hva hvb
  generalize (if x < 0 then -1 else 1) * (k : ℚ) * (2 : ℚ) ^ (e - 23) = v at hva hvb
  by_cases hz : v = 0
  · subst v
    have za := zero_bits a hva
    have zb := zero_bits b hvb
    have hsign := hsa.trans hsb.symm
    apply BitVec.eq_of_toNat_eq
    rcases za with za | za <;> rcases zb with zb | zb <;> simp_all
  · exact value32_injective a b v hva hvb hz

/-- FP32 rounding to nearest, ties to even, is the specified relation on the finite range. -/
theorem roundsNearestEven_iff (x : ℚ) (b : F32) (hr : magnitude x ≤ maxFinite) :
    RoundsNearestEven x b ↔ round32 .nearestEven x = some b := by
  constructor
  · intro h
    obtain ⟨a, _, ha, _⟩ := round32_finite_exists .nearestEven x hr
    have hab := roundsNearestEven_unique x a b (round32_nearestEven_rounds x a ha) h
    rwa [hab] at ha
  · exact round32_nearestEven_rounds x b

end TensorCore.IndependentSpec
