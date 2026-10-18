import TensorCore.TC.ErrorBounds
import TensorCore.TC.AcceptedDomain
import TensorCore.Numerics.RoundTrip

/-! # Block outputs with fewer than 23 mantissa bits

The error bound for every block-output width, including the 13-bit output of the FP8 block FMAs of
Ada and Hopper. -/

namespace TensorCore

/-- The magnitude of an FP32 word without its sign bit, in units of `2^-149`. -/
def coeff32 (r : ℕ) : ℕ :=
  if r / 2 ^ 23 = 0 then r % 2 ^ 23 else (2 ^ 23 + r % 2 ^ 23) * 2 ^ (r / 2 ^ 23 - 1)

theorem coeff32_lt_binade (r : ℕ) : coeff32 r < 2 ^ 23 * 2 ^ (r / 2 ^ 23) := by
  unfold coeff32
  have hm : r % 2 ^ 23 < 2 ^ 23 := Nat.mod_lt _ (Nat.two_pow_pos 23)
  split
  · rename_i h; rw [h]; simpa using hm
  · rename_i h
    have hp : 2 ^ (r / 2 ^ 23) = 2 ^ (r / 2 ^ 23 - 1) * 2 := by
      rw [← Nat.pow_succ]; congr 1; omega
    rw [hp]
    have hx := Nat.two_pow_pos (r / 2 ^ 23 - 1)
    generalize 2 ^ (r / 2 ^ 23 - 1) = x at hx ⊢
    have : (2 ^ 23 + r % 2 ^ 23) * x < (2 ^ 23 + 2 ^ 23) * x :=
      Nat.mul_lt_mul_of_pos_right (by omega) hx
    simp only [Nat.reducePow] at this ⊢
    omega

theorem coeff32_ge_binade (r : ℕ) (h : r / 2 ^ 23 ≠ 0) :
    2 ^ 23 * 2 ^ (r / 2 ^ 23 - 1) ≤ coeff32 r := by
  unfold coeff32
  rw [if_neg h]
  exact Nat.mul_le_mul_right _ (by omega)

theorem coeff32_lt_of_lt {r r' : ℕ} (h : r < r') : coeff32 r < coeff32 r' := by
  have hE : r / 2 ^ 23 ≤ r' / 2 ^ 23 := Nat.div_le_div_right (Nat.le_of_lt h)
  rcases Nat.lt_or_eq_of_le hE with hlt | heq
  · have h1 := coeff32_lt_binade r
    have h2 := coeff32_ge_binade r' (by omega)
    have h3 : 2 ^ 23 * 2 ^ (r / 2 ^ 23) ≤ 2 ^ 23 * 2 ^ (r' / 2 ^ 23 - 1) :=
      Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by decide) (by omega))
    omega
  · have hm : r % 2 ^ 23 < r' % 2 ^ 23 := by
      have := Nat.div_add_mod r (2 ^ 23)
      have := Nat.div_add_mod r' (2 ^ 23)
      rw [heq] at *
      omega
    unfold coeff32
    rw [heq]
    split
    · exact hm
    · exact Nat.mul_lt_mul_of_pos_right (by omega) (Nat.two_pow_pos _)

theorem coeff32_le_of_le {r r' : ℕ} (h : r ≤ r') : coeff32 r ≤ coeff32 r' := by
  rcases Nat.lt_or_eq_of_le h with h | rfl
  · exact Nat.le_of_lt (coeff32_lt_of_lt h)
  · exact Nat.le_refl _

theorem le_of_coeff32_le {r r' : ℕ} (h : coeff32 r ≤ coeff32 r') : r ≤ r' := by
  apply Nat.le_of_not_lt
  intro hlt
  have := coeff32_lt_of_lt hlt
  omega

/-- The sign of an FP32 word: `1` or `−1`. -/
def signQ32 (n : ℕ) : ℚ := if n / 2 ^ 31 = 0 then 1 else -1

/-- The value of a finite FP32 word is `±coeff32 r · 2^-149`. -/
theorem decode32_value_coeff {w : F32} {d : Decoded} (h : decode32 w = some d) :
    d.value = signQ32 w.toNat * (coeff32 (w.toNat % 2 ^ 31) : ℚ) * pow2 (-149) := by
  have hlt := w.isLt
  have hE : (w.toNat % 2 ^ 31) / 2 ^ 23 = w.toNat / 8388608 % 256 := by
    change _ < 4294967296 at hlt; omega
  have hM : (w.toNat % 2 ^ 31) % 2 ^ 23 = w.toNat % 8388608 := by
    change _ < 4294967296 at hlt; omega
  rcases decode32_fields w d h with ⟨h1, h2, rfl⟩ | ⟨h1, h2, rfl⟩ | ⟨h1, h2, rfl⟩
  · have hc : coeff32 (w.toNat % 2 ^ 31) = 0 := by
      unfold coeff32; rw [hE, hM, if_pos h1, h2]
    simp [Decoded.value, hc]
  · have hc : coeff32 (w.toNat % 2 ^ 31) = w.toNat % 8388608 := by
      unfold coeff32; rw [hE, hM, if_pos h1]
    rw [hc]
    unfold Decoded.value signQ32
    by_cases hs : w.toNat / 2 ^ 31 = 0
    · simp only [hs, ↓reduceIte, Rat.one_mul]
      rfl
    · have hb : (w.toNat / 2147483648 != 0) = true := by
        simp only [Nat.reducePow] at hs; simp [hs]
      simp only [hb, hs, ↓reduceIte, Rat.intCast_neg, Rat.intCast_natCast, Rat.neg_mul,
        Rat.one_mul]
      rfl
  · have hne : w.toNat / 8388608 % 256 ≠ 0 := by omega
    have hc : coeff32 (w.toNat % 2 ^ 31) =
        (8388608 + w.toNat % 8388608) * 2 ^ (w.toNat / 8388608 % 256 - 1) := by
      unfold coeff32; rw [hE, hM, if_neg hne]
    rw [hc]
    have hp : pow2 (((w.toNat / 8388608 % 256 : ℕ) : ℤ) - 127 - 23) =
        (((2 ^ (w.toNat / 8388608 % 256 - 1)) : ℕ) : ℚ) * pow2 (-149) := by
      rw [← pow2_natCast, ← pow2_add]
      congr 1
      omega
    unfold Decoded.value signQ32
    rw [hp, Rat.natCast_mul]
    by_cases hs : w.toNat / 2 ^ 31 = 0
    · have hb : (w.toNat / 2147483648 != 0) = false := by
        simp only [Nat.reducePow] at hs; simp [hs]
      simp only [hb, Bool.false_eq_true, ↓reduceIte, Rat.intCast_natCast, Rat.mul_assoc]
      rw [if_pos hs, Rat.one_mul]
    · have hb : (w.toNat / 2147483648 != 0) = true := by
        simp only [Nat.reducePow] at hs; simp [hs]
      simp only [hb, hs, ↓reduceIte, Rat.intCast_neg, Rat.intCast_natCast, Rat.neg_mul,
        Rat.one_mul]
      simp only [Rat.mul_assoc]

theorem pow2_outputUlpExponent (w : F32) :
    pow2 (outputUlpExponent w) =
      (((if (w.toNat % 2 ^ 31) / 2 ^ 23 = 0 then 1 else 2 ^ ((w.toNat % 2 ^ 31) / 2 ^ 23 - 1)) : ℕ) : ℚ) *
        pow2 (-149) := by
  have hlt := w.isLt
  have hE : (w.toNat % 2 ^ 31) / 2 ^ 23 = w.toNat / 2 ^ 23 % 2 ^ 8 := by
    change _ < 4294967296 at hlt; omega
  unfold outputUlpExponent emin32
  rw [hE]
  split
  · rename_i h
    rw [h, show ((1 : ℕ) : ℚ) = 1 from rfl, Rat.one_mul]
    congr 1
  · rename_i h
    rw [← pow2_natCast, ← pow2_add]
    congr 1
    omega

/-! ## Clearing low mantissa bits -/

theorem truncateMantissa32_parts (m : ℕ) (w : F32) :
    (truncateMantissa32 m w).toNat / 2 ^ 31 = w.toNat / 2 ^ 31 ∧
    (truncateMantissa32 m w).toNat % 2 ^ 31 = (w.toNat % 2 ^ 31) / 2 ^ (23 - m) * 2 ^ (23 - m) := by
  rw [truncateMantissa32_toNat]
  generalize hk : 23 - m = k
  have hk23 : k ≤ 23 := by omega
  have hlt := w.isLt
  change w.toNat < 2 ^ 32 at hlt
  generalize w.toNat = n at hlt ⊢
  have hd : 2 ^ 31 = 2 ^ k * 2 ^ (31 - k) := by rw [← Nat.pow_add]; congr 1; omega
  have hpos : 0 < 2 ^ k := Nat.two_pow_pos k
  obtain ⟨q, r, hr, rfl⟩ : ∃ q r, r < 2 ^ 31 ∧ n = 2 ^ 31 * q + r :=
    ⟨n / 2 ^ 31, n % 2 ^ 31, Nat.mod_lt _ (Nat.two_pow_pos 31), (Nat.div_add_mod n _).symm⟩
  have hsplit : (2 ^ 31 * q + r) / 2 ^ k * 2 ^ k = 2 ^ 31 * q + r / 2 ^ k * 2 ^ k := by
    rw [hd, Nat.mul_assoc, Nat.add_comm, Nat.add_mul_div_left _ _ hpos, Nat.add_mul, Nat.add_comm]
    congr 1
    rw [Nat.mul_comm (2 ^ (31 - k) * q), Nat.mul_comm]
  have hle : r / 2 ^ k * 2 ^ k ≤ r := Nat.div_mul_le_self r _
  rw [hsplit]
  have hr' : r / 2 ^ k * 2 ^ k < 2 ^ 31 := Nat.lt_of_le_of_lt hle hr
  have hmodr : (2 ^ 31 * q + r) % 2 ^ 31 = r := by
    simp only [Nat.reducePow] at hr ⊢; omega
  have hdivr : (2 ^ 31 * q + r) / 2 ^ 31 = q := by
    simp only [Nat.reducePow] at hr ⊢; omega
  rw [hmodr, hdivr]
  generalize r / 2 ^ k * 2 ^ k = X at hr' ⊢
  simp only [Nat.reducePow] at hr hr' ⊢
  omega

theorem div_binade_of_clear (r k : ℕ) (hk : k ≤ 23) :
    (r / 2 ^ k * 2 ^ k) / 2 ^ 23 = r / 2 ^ 23 := by
  have hd : 2 ^ 23 = 2 ^ k * 2 ^ (23 - k) := by rw [← Nat.pow_add]; congr 1; omega
  rw [hd, ← Nat.div_div_eq_div_mul, ← Nat.div_div_eq_div_mul, Nat.mul_div_cancel _ (Nat.two_pow_pos k)]

theorem coeff32_clear_le (r k : ℕ) : coeff32 (r / 2 ^ k * 2 ^ k) ≤ coeff32 r :=
  coeff32_le_of_le (Nat.div_mul_le_self r _)

theorem coeff32_clear_sub (r k : ℕ) (hk : k ≤ 23) :
    coeff32 r - coeff32 (r / 2 ^ k * 2 ^ k) + (if r / 2 ^ 23 = 0 then 1 else 2 ^ (r / 2 ^ 23 - 1)) ≤
      2 ^ k * (if r / 2 ^ 23 = 0 then 1 else 2 ^ (r / 2 ^ 23 - 1)) := by
  have hE := div_binade_of_clear r k hk
  have hm : (r / 2 ^ k * 2 ^ k) % 2 ^ 23 = r % 2 ^ 23 / 2 ^ k * 2 ^ k := by
    have hd : 2 ^ 23 = 2 ^ k * 2 ^ (23 - k) := by rw [← Nat.pow_add]; congr 1; omega
    have h1 := Nat.div_add_mod r (2 ^ 23)
    have h2 := Nat.div_add_mod (r % 2 ^ 23) (2 ^ k)
    have h3 := Nat.div_add_mod r (2 ^ k)
    have hmm : r % 2 ^ 23 % 2 ^ k = r % 2 ^ k := Nat.mod_mod_of_dvd r ⟨2 ^ (23 - k), hd⟩
    have hlt : r % 2 ^ 23 / 2 ^ k * 2 ^ k < 2 ^ 23 :=
      Nat.lt_of_le_of_lt (Nat.div_mul_le_self _ _) (Nat.mod_lt _ (Nat.two_pow_pos 23))
    have heq : r / 2 ^ k * 2 ^ k = 2 ^ 23 * (r / 2 ^ 23) + r % 2 ^ 23 / 2 ^ k * 2 ^ k := by
      rw [Nat.mul_comm (r / 2 ^ k), Nat.mul_comm (r % 2 ^ 23 / 2 ^ k)]
      rw [hmm] at h2
      generalize 2 ^ k * (r / 2 ^ k) = X at h3 ⊢
      generalize 2 ^ k * (r % 2 ^ 23 / 2 ^ k) = Y at h2 ⊢
      omega
    rw [heq, Nat.mul_add_mod, Nat.mod_eq_of_lt hlt]
  have hlow : r % 2 ^ 23 - r % 2 ^ 23 / 2 ^ k * 2 ^ k + 1 ≤ 2 ^ k := by
    have h4 := Nat.div_add_mod (r % 2 ^ 23) (2 ^ k)
    have h5 := Nat.mod_lt (r % 2 ^ 23) (Nat.two_pow_pos k)
    rw [Nat.mul_comm (r % 2 ^ 23 / 2 ^ k)]
    generalize 2 ^ k * (r % 2 ^ 23 / 2 ^ k) = Y at h4 ⊢
    omega
  have hle : r % 2 ^ 23 / 2 ^ k * 2 ^ k ≤ r % 2 ^ 23 := Nat.div_mul_le_self _ _
  unfold coeff32
  rw [hE, hm]
  split
  · omega
  · rename_i h
    rw [← Nat.mul_sub_right_distrib]
    have hs : 2 ^ 23 + r % 2 ^ 23 - (2 ^ 23 + r % 2 ^ 23 / 2 ^ k * 2 ^ k) =
        r % 2 ^ 23 - r % 2 ^ 23 / 2 ^ k * 2 ^ k := by omega
    rw [hs]
    have := Nat.mul_le_mul_right (2 ^ (r / 2 ^ 23 - 1)) hlow
    rw [Nat.add_mul, Nat.one_mul] at this
    exact this

theorem coeff32_le_clear {ry r k : ℕ} (hy : ry % 2 ^ k = 0) (h : coeff32 ry ≤ coeff32 r) :
    coeff32 ry ≤ coeff32 (r / 2 ^ k * 2 ^ k) := by
  apply coeff32_le_of_le
  have hle := le_of_coeff32_le h
  have hy' : ry = ry / 2 ^ k * 2 ^ k := by
    have := Nat.div_add_mod ry (2 ^ k)
    rw [hy, Nat.add_zero] at this
    rw [Nat.mul_comm]; exact this.symm
  rw [hy']
  exact Nat.mul_le_mul_right _ (Nat.div_le_div_right hle)

theorem zeroBits_of_value (b : F32) (h : value32 b = some 0) :
    b.toNat = 0 ∨ b.toNat = 2147483648 := by
  cases hd : decode32 b with
  | none => simp [value32, hd] at h
  | some d =>
    have hv : d.value = 0 := by simpa [value32, hd] using h
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

theorem sign32_abs (n : ℕ) (c : ℕ) (u : ℚ) (hu : 0 < u) :
    absQ (signQ32 n * (c : ℚ) * u) = (c : ℚ) * u := by
  have hc : (0 : ℚ) ≤ (c : ℚ) * u := Rat.mul_nonneg (Rat.natCast_nonneg) (Rat.le_of_lt hu)
  unfold signQ32
  split
  · rw [Rat.one_mul]; exact absQ_of_nonneg hc
  · rw [Rat.neg_mul, Rat.one_mul, Rat.neg_mul, absQ_neg]; exact absQ_of_nonneg hc

theorem truncateMantissa32_values {m : ℕ} {w : F32} {v : ℚ} (h : value32 w = some v) :
    ∃ v', value32 (truncateMantissa32 m w) = some v' ∧
      v = signQ32 w.toNat * (coeff32 (w.toNat % 2 ^ 31) : ℚ) * pow2 (-149) ∧
      v' = signQ32 w.toNat *
        (coeff32 ((w.toNat % 2 ^ 31) / 2 ^ (23 - m) * 2 ^ (23 - m)) : ℚ) * pow2 (-149) := by
  cases hd : decode32 w with
  | none => simp [value32, hd] at h
  | some d =>
    have hv : v = d.value := by simpa [value32, hd] using h.symm
    have hs := decode32_truncateMantissa32 (m := m) (w := w) (by simp [hd])
    cases hd' : decode32 (truncateMantissa32 m w) with
    | none => simp [hd'] at hs
    | some d' =>
      obtain ⟨hsg, hr⟩ := truncateMantissa32_parts m w
      refine ⟨d'.value, by simp [value32, hd'], ?_, ?_⟩
      · rw [hv]; exact decode32_value_coeff hd
      · rw [decode32_value_coeff hd', hr]
        unfold signQ32
        rw [hsg]

/-- The value with cleared low bits lies between zero and the original value. -/
theorem truncateMantissa32_between {m : ℕ} {w : F32} {v v' : ℚ} (h : value32 w = some v)
    (h' : value32 (truncateMantissa32 m w) = some v') :
    (0 ≤ v → 0 ≤ v' ∧ v' ≤ v) ∧ (v ≤ 0 → v ≤ v' ∧ v' ≤ 0) := by
  obtain ⟨v'', h'', hv, hv'⟩ := truncateMantissa32_values (m := m) h
  rw [h'] at h''
  cases Option.some.inj h''
  have hle := coeff32_clear_le (w.toNat % 2 ^ 31) (23 - m)
  have hle' : (coeff32 ((w.toNat % 2 ^ 31) / 2 ^ (23 - m) * 2 ^ (23 - m)) : ℚ) ≤
      (coeff32 (w.toNat % 2 ^ 31) : ℚ) := Rat.natCast_le_natCast.mpr hle
  have hu := pow2_pos (-149)
  have h0 : (0 : ℚ) ≤ (coeff32 ((w.toNat % 2 ^ 31) / 2 ^ (23 - m) * 2 ^ (23 - m)) : ℚ) :=
    Rat.natCast_nonneg
  rw [hv, hv']
  unfold signQ32
  split
  · simp only [Rat.one_mul]
    have := Rat.mul_le_mul_of_nonneg_right hle' (Rat.le_of_lt hu)
    have := Rat.mul_nonneg h0 (Rat.le_of_lt hu)
    constructor
    · intro _; exact ⟨by assumption, by assumption⟩
    · intro hn
      have hz : (coeff32 (w.toNat % 2 ^ 31) : ℚ) * pow2 (-149) = 0 := by grind
      constructor <;> grind
  · simp only [Rat.neg_mul, Rat.one_mul]
    have := Rat.mul_le_mul_of_nonneg_right hle' (Rat.le_of_lt hu)
    have := Rat.mul_nonneg h0 (Rat.le_of_lt hu)
    constructor
    · intro hn
      have hz : (coeff32 (w.toNat % 2 ^ 31) : ℚ) * pow2 (-149) = 0 := by grind
      constructor <;> grind
    · intro _; constructor <;> grind

/-- The value with cleared low bits is within `2^(23 − m) − 1` units in the last place. -/
theorem truncateMantissa32_sub_le {m : ℕ} {w : F32} {v v' : ℚ} (h : value32 w = some v)
    (h' : value32 (truncateMantissa32 m w) = some v') :
    absQ (v - v') + pow2 (outputUlpExponent w) ≤
      pow2 (outputUlpExponent w + ((23 - m : ℕ) : ℤ)) := by
  obtain ⟨v'', h'', hv, hv'⟩ := truncateMantissa32_values (m := m) h
  rw [h'] at h''
  cases Option.some.inj h''
  generalize hr : w.toNat % 2 ^ 31 = r at hv hv'
  generalize hk : 23 - m = k at hv hv'
  have hk23 : k ≤ 23 := by omega
  have hsub := coeff32_clear_sub r k hk23
  have hle := coeff32_clear_le r k
  generalize hC : coeff32 r = C at hsub hle hv
  generalize hC' : coeff32 (r / 2 ^ k * 2 ^ k) = C' at hsub hle hv'
  have hd : absQ (v - v') = ((C : ℚ) - (C' : ℚ)) * pow2 (-149) := by
    have hle' : (C' : ℚ) ≤ (C : ℚ) := Rat.natCast_le_natCast.mpr hle
    have hnn : (0 : ℚ) ≤ ((C : ℚ) - (C' : ℚ)) * pow2 (-149) :=
      Rat.mul_nonneg (by grind) (Rat.le_of_lt (pow2_pos _))
    rw [hv, hv']
    unfold signQ32
    split
    · rw [show (1 : ℚ) * C * pow2 (-149) - 1 * C' * pow2 (-149) = (C - C') * pow2 (-149) by grind]
      exact absQ_of_nonneg hnn
    · rw [show (-1 : ℚ) * C * pow2 (-149) - -1 * C' * pow2 (-149) = -((C - C') * pow2 (-149)) by
        grind, absQ_neg]
      exact absQ_of_nonneg hnn
  rw [hd, pow2_add, pow2_natCast, pow2_outputUlpExponent, hr]
  generalize hU : (if r / 2 ^ 23 = 0 then 1 else 2 ^ (r / 2 ^ 23 - 1) : ℕ) = U at hsub ⊢
  have hsub' : C + U ≤ 2 ^ k * U + C' := by omega
  have hq : ((C + U : ℕ) : ℚ) ≤ ((2 ^ k * U + C' : ℕ) : ℚ) := Rat.natCast_le_natCast.mpr hsub'
  rw [Rat.natCast_add, Rat.natCast_add, Rat.natCast_mul] at hq
  have hu := pow2_pos (-149)
  have := Rat.mul_le_mul_of_nonneg_right hq (Rat.le_of_lt hu)
  grind

/-- Maximality: a word with low `23 − m` bits clear and magnitude at most `|v|` is at most `|v'|`. -/
theorem truncateMantissa32_max {m : ℕ} {w y : F32} {v v' vy : ℚ} (h : value32 w = some v)
    (h' : value32 (truncateMantissa32 m w) = some v') (hy : value32 y = some vy)
    (hlow : y.toNat % 2 ^ (23 - m) = 0) (hle : absQ vy ≤ absQ v) : absQ vy ≤ absQ v' := by
  obtain ⟨v'', h'', hv, hv'⟩ := truncateMantissa32_values (m := m) h
  rw [h'] at h''
  cases Option.some.inj h''
  cases hdy : decode32 y with
  | none => simp [value32, hdy] at hy
  | some dy =>
    have hvy : vy = dy.value := by simpa [value32, hdy] using hy.symm
    have hcy := decode32_value_coeff hdy
    have hu := pow2_pos (-149)
    rw [hvy, hcy, sign32_abs _ _ _ hu] at hle ⊢
    rw [hv, sign32_abs _ _ _ hu] at hle
    rw [hv', sign32_abs _ _ _ hu]
    have hc : coeff32 (y.toNat % 2 ^ 31) ≤ coeff32 (w.toNat % 2 ^ 31) := by
      have := Rat.le_of_mul_le_mul_right hle hu
      exact Rat.natCast_le_natCast.mp this
    have hk : 23 - m ≤ 31 := by omega
    have hy0 : (y.toNat % 2 ^ 31) % 2 ^ (23 - m) = 0 := by
      rw [Nat.mod_mod_of_dvd _ ⟨2 ^ (31 - (23 - m)), by rw [← Nat.pow_add]; congr 1; omega⟩]
      exact hlow
    have := coeff32_le_clear hy0 hc
    exact Rat.mul_le_mul_of_nonneg_right (Rat.natCast_le_natCast.mpr this) (Rat.le_of_lt hu)

theorem outputUlpExponent_truncateMantissa32 (m : ℕ) (w : F32) :
    outputUlpExponent (truncateMantissa32 m w) = outputUlpExponent w := by
  unfold outputUlpExponent
  rw [truncateMantissa32_div]

/-! ## The error bound for any block-output width -/

/-- Model error below (terms) · (grid step) + `2^(23 − m)` FP32 ulps, for `m` output mantissa bits. -/
theorem evalPrepared_error_bound_any {b : PreparedBlock} {t : BlockTrace}
    (h : evalPrepared b = .ok t) :
    absQ (t.block.exactDot - t.output.value) <
      (t.block.terms.length : ℚ) * pow2 t.block.alignGridExponent +
        pow2 (outputUlpExponent t.output.bits + ((23 - b.model.outputMantissaBits : ℕ) : ℤ)) := by
  have hb := evalPrepared_block h
  obtain ⟨bits, hr, ht⟩ := evalPrepared_output_mantissa h
  have hrange := round32_range hr
  obtain ⟨bits', d, hb', hd⟩ := round32_finite_exists .truncate _ hrange
  rw [hr] at hb'
  cases Option.some.inj hb'
  have hv0 : value32 bits = some d.value := by simp [value32, hd]
  have hvt : value32 t.output.bits = some t.output.value := by
    simp [value32, t.output.valid, Finite32.value]
  rw [ht] at hvt
  have hout := output_residual_bound b.accumulator bits d.value hrange hr hv0
  have hsub := truncateMantissa32_sub_le (m := b.model.outputMantissaBits) hv0 hvt
  have halign := block_alignment_bound b
  have hid := block_residual_identity b t.output.value
  unfold PreparedBlock.extractReference at hid
  rw [ht, outputUlpExponent_truncateMantissa32, hb]
  have he : b.exactDot - t.output.value =
      ((b.accumulator - d.value) + (d.value - t.output.value)) + sumQ b.alignmentResiduals := by
    grind
  rw [he]
  have t1 := absQ_add_le ((b.accumulator - d.value) + (d.value - t.output.value))
    (sumQ b.alignmentResiduals)
  have t2 := absQ_add_le (b.accumulator - d.value) (d.value - t.output.value)
  grind

theorem evalBlock_error_bound_any {p : Model} {x : BlockInput p} {t : BlockTrace}
    (h : evalBlock x = .ok t) :
    absQ (t.block.exactDot - t.output.value) <
      (t.block.terms.length : ℚ) * pow2 t.block.alignGridExponent +
        pow2 (outputUlpExponent t.output.bits + ((23 - p.outputMantissaBits : ℕ) : ℤ)) := by
  have := evalPrepared_error_bound_any (evalBlock_evalPrepared h)
  rwa [evalBlock_model h] at this

/-- Ada and Hopper FP8: (terms) · (grid step) + `2^10` FP32 ulps, one ulp of the 14-bit significand. -/
theorem fp8_error_bound {p : Model} (hp : p.outputMantissaBits = 13) {x : BlockInput p}
    {t : BlockTrace} (h : evalBlock x = .ok t) :
    absQ (t.block.exactDot - t.output.value) <
      (t.block.terms.length : ℚ) * pow2 t.block.alignGridExponent +
        pow2 (outputUlpExponent t.output.bits + 10) := by
  have := evalBlock_error_bound_any h
  rwa [hp] at this

end TensorCore
