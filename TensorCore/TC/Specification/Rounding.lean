import TensorCore.TC.Specification.Stages
import TensorCore.Numerics.Binary.CorrectRounding
import TensorCore.Numerics.RoundTrip

/-! The ordering-based final-rounding relation selects unique *bits*, including signed zero, and the executable converter satisfies it throughout its finite domain. -/

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

end TensorCore.IndependentSpec
