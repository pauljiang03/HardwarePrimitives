import OzakiMC.Exactness

/-! # The matrix core as a matrix multiplier for the Ozaki schemes

`mcMultiplier P` evaluates an integer dot product on the matrix-core model `P`: it writes
each integer with `MatrixCore`'s exact encoder `encodeExact`, and runs `dotBits` (zero padding to
whole blocks of `N_FMA`, each block's `d` the next block's `c`) from `c = +0`.

* `encodeExact_int`: a format with `emin ≤ 0` and `p + 1 ≤ emax` (`p` stored mantissa bits)
  encodes every integer of magnitude at most `2^(p+1)`; XF32 operands, read by truncating a
  binary32 word to ten mantissa bits, keep every integer of magnitude at most `2^11`
  (`xf32_encodesInts`).
* `mcMultiplier_exactOn`: on an exact configuration (`ExactConfig`), the matrix multiplier is exact
  on `b`-bit vectors whose products total at most `2^24` in magnitude. -/

open MatrixCore

namespace Ozaki.MC

/-! ## The bits of a packed word -/

theorem pack_toNat (f : Format) (neg : Bool) (E M : ℕ) (hE : E < 2 ^ f.exponentBits)
    (hM : M < 2 ^ f.mantissaBits) :
    (f.pack neg E M).toNat =
      M + 2 ^ f.mantissaBits * (E + 2 ^ f.exponentBits * (if neg then 1 else 0)) := by
  unfold Format.pack
  rw [BitVec.toNat_ofNat]
  have hw : 2 ^ f.width = 2 * (2 ^ f.mantissaBits * 2 ^ f.exponentBits) := by
    unfold Format.width
    rw [← Nat.pow_add, ← Nat.pow_succ']
    congr 1; omega
  rw [hw, Nat.pow_add]
  have hP := Nat.two_pow_pos f.mantissaBits
  generalize 2 ^ f.mantissaBits = P at *
  generalize 2 ^ f.exponentBits = Q at *
  have hEP : E * P + M < P * Q := by
    calc E * P + M < E * P + P := by omega
      _ = (E + 1) * P := by rw [Nat.succ_mul]
      _ ≤ Q * P := Nat.mul_le_mul_right P hE
      _ = P * Q := Nat.mul_comm Q P
  cases neg
  · simp only [Bool.false_eq_true, ↓reduceIte, Nat.zero_add, Nat.mul_zero, Nat.add_zero]
    rw [Nat.mod_eq_of_lt (by omega)]
    rw [Nat.mul_comm P E]; omega
  · simp only [↓reduceIte, Nat.mul_one]
    rw [Nat.mod_eq_of_lt (by omega)]
    rw [Nat.mul_add, Nat.mul_comm P E]; omega

theorem decodeNat_pack_fields (f : Format) (neg : Bool) (E M : ℕ) (hE : E < 2 ^ f.exponentBits)
    (hM : M < 2 ^ f.mantissaBits) :
    (f.pack neg E M).toNat % 2 ^ f.mantissaBits = M ∧
      (f.pack neg E M).toNat / 2 ^ f.mantissaBits % 2 ^ f.exponentBits = E ∧
      ((f.pack neg E M).toNat / 2 ^ (f.mantissaBits + f.exponentBits) % 2 == 1) = neg := by
  rw [pack_toNat f neg E M hE hM, Nat.pow_add]
  have hP := Nat.two_pow_pos f.mantissaBits
  have hQ := Nat.two_pow_pos f.exponentBits
  generalize 2 ^ f.mantissaBits = P at *
  generalize 2 ^ f.exponentBits = Q at *
  have h1 : (M + P * (E + Q * (if neg then 1 else 0))) / P = E + Q * (if neg then 1 else 0) := by
    rw [Nat.add_mul_div_left _ _ hP, Nat.div_eq_of_lt hM, Nat.zero_add]
  refine ⟨?_, ?_, ?_⟩
  · rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hM]
  · rw [h1, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hE]
  · rw [← Nat.div_div_eq_div_mul, h1, Nat.add_mul_div_left _ _ hQ, Nat.div_eq_of_lt hE,
      Nat.zero_add]
    cases neg <;> rfl

/-- Decoding a packed normal word returns its fields. -/
theorem decode_pack (f : Format) (neg : Bool) (E M : ℕ) (hE0 : E ≠ 0)
    (hE : E < 2 ^ f.exponentBits) (hEt : f.specials = .ieee → E ≠ 2 ^ f.exponentBits - 1)
    (hM : M < 2 ^ f.mantissaBits) :
    f.decode (f.pack neg E M) =
      .finite ⟨neg, 2 ^ f.mantissaBits + M, (E : ℤ) - f.bias, f.mantissaBits⟩ := by
  obtain ⟨h1, h2, h3⟩ := decodeNat_pack_fields f neg E M hE hM
  unfold Format.decode Format.decodeNat
  simp only [h1, h2, h3]
  cases hs : f.specials
  · simp only [hEt hs, ↓reduceIte, Format.unpackFields, hE0]
  · simp only [hE0, false_and, and_false, ↓reduceIte, Format.unpackFields]

/-! ## Encoding integers -/

/-- A nonzero integer `n` with exponent `L = ⌊log₂ n⌋ ≤ p + 1` has the normal significand
`n / 2^(L−p)`, an integer in `[2^p, 2^(p+1))`. -/
theorem int_significand (p : ℕ) {n : ℕ} (hn : 1 ≤ n) (hle : n ≤ 2 ^ (p + 1)) :
    let L := log2Floor (n : ℚ)
    0 ≤ L ∧ L ≤ p + 1 ∧
      ∃ m : ℕ, (n : ℚ) / pow2 (L - p) = (m : ℚ) ∧ 2 ^ p ≤ m ∧ m < 2 ^ (p + 1) := by
  intro L
  have hpos : (0 : ℚ) < (n : ℚ) := by exact_mod_cast hn
  obtain ⟨hlo, hhi⟩ := log2Floor_spec hpos
  have hL0 : 0 ≤ L := by
    apply Classical.byContradiction; intro h
    have := pow2_le_of_le (show L + 1 ≤ 0 by omega)
    rw [pow2_zero] at this
    have : (1 : ℚ) ≤ (n : ℚ) := by exact_mod_cast hn
    grind
  have hnp : (n : ℚ) ≤ pow2 ((p + 1 : ℕ) : ℤ) := by rw [pow2_natCast]; exact_mod_cast hle
  have hL1 : L ≤ p + 1 := by
    have := pow2_le_iff.mp (Rat.le_trans hlo hnp); omega
  refine ⟨hL0, hL1, ?_⟩
  have hq := pow2_pos (L - p)
  -- bounds of the scaled value
  have hb1 : pow2 p ≤ (n : ℚ) / pow2 (L - p) := by
    apply le_div_of_mul_le hq
    rw [← pow2_add, show (p : ℤ) + (L - p) = L by omega]; exact hlo
  have hb2 : (n : ℚ) / pow2 (L - p) < pow2 ((p + 1 : ℕ) : ℤ) := by
    rw [Rat.div_lt_iff hq, ← pow2_add, show ((p + 1 : ℕ) : ℤ) + (L - p) = L + 1 by omega]
    exact hhi
  by_cases hcase : L ≤ p
  · -- `n · 2^(p − L)` is an integer
    have hk : (n : ℚ) / pow2 (L - p) = ((n * 2 ^ (p - L).toNat : ℕ) : ℚ) := by
      rw [div_pow2, Rat.natCast_mul, ← pow2_natCast, show (((p - L).toNat : ℕ) : ℤ) = -(L - p) by
        omega]
    refine ⟨n * 2 ^ (p - L).toNat, hk, ?_, ?_⟩
    · rw [hk, pow2_natCast] at hb1; exact_mod_cast hb1
    · rw [hk, pow2_natCast] at hb2; exact_mod_cast hb2
  · -- `L = p + 1`: `n = 2^(p+1)` and the significand is `2^p`
    have hLe : L = p + 1 := by omega
    have hn2 : (n : ℚ) = pow2 ((p + 1 : ℕ) : ℤ) := by
      apply Rat.le_antisymm hnp
      rw [show ((p + 1 : ℕ) : ℤ) = L by omega]; exact hlo
    have hk : (n : ℚ) / pow2 (L - p) = ((2 ^ p : ℕ) : ℚ) := by
      rw [hn2, ← pow2_sub, show ((p + 1 : ℕ) : ℤ) - (L - p) = p by omega, pow2_natCast]
    refine ⟨2 ^ p, hk, Nat.le_refl _, Nat.pow_lt_pow_right (by decide) (by omega)⟩

/-- **Exact encoding.** A format with `emin ≤ 0` and `p + 1 ≤ emax` encodes every integer of
magnitude at most `2^(p+1)` as a normal word (or `+0`) whose value it is. -/
theorem encodeExact_int (f : Format) (hmin : f.emin ≤ 0)
    (hmax : (f.mantissaBits : ℤ) + 1 ≤ f.emax) (hE2 : 2 ≤ f.exponentBits) {z : ℤ}
    (hz : z.natAbs ≤ 2 ^ (f.mantissaBits + 1)) :
    ∃ w, f.encodeExact (z : ℚ) = some w ∧ ∃ u, f.decode w = .finite u ∧ u.value = z ∧
      (z ≠ 0 → 2 ^ u.t ≤ u.m ∧ u.t = f.mantissaBits ∧
        (u.m : ℚ) * pow2 (u.e - u.t) = absQ (z : ℚ) ∧ u.e = log2Floor (absQ (z : ℚ))) := by
  have hQ : 4 ≤ 2 ^ f.exponentBits := by
    have := Nat.pow_le_pow_right (show 0 < 2 by decide) hE2; simpa using this
  by_cases hz0 : z = 0
  · -- `+0`
    subst hz0
    have hd : f.decode 0 = .finite (f.unpackFields false 0 0) := by
      show f.decodeNat (0 : BitVec f.width).toNat = _
      have h0 : (0 : BitVec f.width).toNat = 0 := by simp
      rw [h0]
      unfold Format.decodeNat
      simp only [Nat.zero_mod, Nat.zero_div]
      cases f.specials
      · simp only [show (0 : ℕ) ≠ 2 ^ f.exponentBits - 1 by omega, ↓reduceIte]
        rfl
      · simp
    refine ⟨0, by simp [Format.encodeExact], f.unpackFields false 0 0, hd, ?_, by simp⟩
    simp [Format.unpackFields, Unpacked.value]
  · -- a nonzero integer: normal word with significand `|z| / 2^(L − p)`
    have hn : 1 ≤ z.natAbs := by omega
    obtain ⟨hL0, hL1, m, hm, hm1, hm2⟩ := int_significand f.mantissaBits hn hz
    have ha : absQ (z : ℚ) = ((z.natAbs : ℕ) : ℚ) := absQ_intCast z
    generalize hL : log2Floor ((z.natAbs : ℕ) : ℚ) = L at hL0 hL1 hm
    have he : max L f.emin = L := by omega
    have hzq : (z : ℚ) ≠ 0 := fun h => hz0 (Rat.intCast_inj.mp (by rw [h]; rfl))
    have hbias : 1 ≤ f.bias := by unfold Format.emin at hmin; omega
    have hEb : (L + f.bias).toNat < 2 ^ f.exponentBits := by
      unfold Format.emax at hmax
      split at hmax <;> omega
    have hEt : f.specials = .ieee → (L + f.bias).toNat ≠ 2 ^ f.exponentBits - 1 := by
      intro hs
      unfold Format.emax at hmax
      rw [hs] at hmax
      simp only at hmax
      omega
    have hMm : m % 2 ^ f.mantissaBits = m - 2 ^ f.mantissaBits := by
      rw [Nat.pow_succ] at hm2
      rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
    have hdec := decode_pack f (decide ((z : ℚ) < 0)) (L + f.bias).toNat (m % 2 ^ f.mantissaBits)
      (by omega) hEb hEt (Nat.mod_lt _ (Nat.two_pow_pos _))
    have hfields : (⟨decide ((z : ℚ) < 0), 2 ^ f.mantissaBits + m % 2 ^ f.mantissaBits,
        ((L + f.bias).toNat : ℤ) - f.bias, f.mantissaBits⟩ : Unpacked) =
        ⟨decide ((z : ℚ) < 0), m, L, f.mantissaBits⟩ := by
      congr 1
      · omega
      · omega
    rw [hfields] at hdec
    have hval : (⟨decide ((z : ℚ) < 0), m, L, f.mantissaBits⟩ : Unpacked).value = z := by
      have hmn : (m : ℚ) * pow2 (L - f.mantissaBits) = ((z.natAbs : ℕ) : ℚ) := by
        rw [← hm, Rat.div_mul_cancel (pow2_ne_zero _)]
      unfold Unpacked.value
      simp only
      by_cases hneg : (z : ℚ) < 0
      · simp only [hneg, decide_true, ↓reduceIte, Rat.neg_mul, hmn]
        have : z < 0 := by
          have := Rat.intCast_lt_intCast (a := z) (b := 0); simp at this; exact this.mp hneg
        rw [← Rat.intCast_natCast, show ((z.natAbs : ℕ) : ℤ) = -z by omega, Rat.intCast_neg,
          Rat.neg_neg]
      · simp only [hneg, decide_false, Bool.false_eq_true, ↓reduceIte, hmn]
        have : 0 ≤ z := by
          have := Rat.intCast_lt_intCast (a := z) (b := 0); simp at this
          exact Int.not_lt.mp fun h => hneg (this.mpr h)
        rw [← Rat.intCast_natCast, show ((z.natAbs : ℕ) : ℤ) = z by omega]
    refine ⟨f.pack (decide ((z : ℚ) < 0)) (L + f.bias).toNat (m % 2 ^ f.mantissaBits), ?_,
      ⟨decide ((z : ℚ) < 0), m, L, f.mantissaBits⟩, hdec, hval, fun _ => ⟨hm1, rfl, ?_, ?_⟩⟩
    · unfold Format.encodeExact
      simp only [hzq, ↓reduceIte, ha, hL, he, hm, Rat.den_natCast, ne_eq, not_true_eq_false,
        Rat.num_natCast, Int.toNat_natCast, show ¬ m < 2 ^ f.mantissaBits by omega, hdec,
        Datum.toFinite, Option.map_some, hval]
    · simp only
      rw [ha, ← hm, Rat.div_mul_cancel (pow2_ne_zero _)]
    · simp only; rw [ha, hL]

/-- `encodeExact` writes every integer of magnitude at most `2^b` as a word that reads back as
it. -/
def EncodesInts (i : InputFormat) (b : ℕ) : Prop :=
  ∀ z : ℤ, z.natAbs ≤ 2 ^ b →
    ∃ w, i.encodeExact (z : ℚ) = some w ∧ IntWord i w ∧ i.wordValue w = z

/-- A packed format with `emin ≤ 0` and `p + 1 ≤ emax` holds every integer of magnitude at most
`2^(p+1)`. -/
theorem packed_encodesInts (f : Format) (hmin : f.emin ≤ 0)
    (hmax : (f.mantissaBits : ℤ) + 1 ≤ f.emax) (hE2 : 2 ≤ f.exponentBits) {b : ℕ}
    (hb : b ≤ f.mantissaBits + 1) : EncodesInts (.packed f) b := by
  intro z hz
  obtain ⟨w, hw, u, hu, hv, _⟩ := encodeExact_int f hmin hmax hE2
    (Nat.le_trans hz (Nat.pow_le_pow_right (by decide) hb))
  have hr : (InputFormat.read (.packed f) w).toFinite = some u := by
    show (f.decode w).toFinite = some u; rw [hu]; rfl
  exact ⟨w, hw, ⟨u, hr, z, hv⟩, by rw [wordValue_of_read hr, hv]⟩

/-- XF32 operands keep every integer of magnitude at most `2^11`: its binary32 significand ends in
at least thirteen zero bits, which the truncation to ten mantissa bits drops. -/
theorem xf32_encodesInts : EncodesInts .xf32 11 := by
  intro z hz
  obtain ⟨w, hw, u, hu, hv, hn⟩ := encodeExact_int fp32 (by decide) (by decide) (by decide)
    (Nat.le_trans hz (by decide))
  have hr : (InputFormat.read .xf32 w).toFinite = some (InputFormat.truncateXF32 u) := by
    show (match fp32.decode w with
      | .finite x => Datum.finite (InputFormat.truncateXF32 x) | d => d).toFinite = _
    rw [hu]; rfl
  -- the significand is a multiple of `2^13`
  have hdiv : u.m % 2 ^ 13 = 0 := by
    by_cases hz0 : z = 0
    · have : u.m = 0 := (Unpacked.value_eq_zero_iff u).mp (by rw [hv, hz0]; rfl)
      rw [this]
    · obtain ⟨_, ht, hmv, he⟩ := hn hz0
      have ht23 : u.t = 23 := ht
      rw [ht23] at hmv
      have ha : absQ (z : ℚ) = ((z.natAbs : ℕ) : ℚ) := absQ_intCast z
      have hpos : (0 : ℚ) < ((z.natAbs : ℕ) : ℚ) := by
        have : 1 ≤ z.natAbs := by omega
        exact_mod_cast this
      have hlo := (log2Floor_spec hpos).1
      rw [← ha, ← he] at hlo
      have hle : ((z.natAbs : ℕ) : ℚ) ≤ pow2 11 := by
        rw [show (11 : ℤ) = ((11 : ℕ) : ℤ) from rfl, pow2_natCast]; exact_mod_cast hz
      rw [← ha] at hle
      have hL : u.e ≤ 11 := pow2_le_iff.mp (Rat.le_trans hlo hle)
      -- `m = |z| · 2^(23 − e)`
      have hm : u.m = z.natAbs * 2 ^ (23 - u.e).toNat := by
        have h1 : (u.m : ℚ) = ((z.natAbs * 2 ^ (23 - u.e).toNat : ℕ) : ℚ) := by
          rw [Rat.natCast_mul, ← pow2_natCast, show (((23 - u.e).toNat : ℕ) : ℤ) = 23 - u.e by
            omega, ← ha, ← hmv, Rat.mul_assoc, ← pow2_add,
            show u.e - ((23 : ℕ) : ℤ) + (23 - u.e) = 0 by omega, pow2_zero, Rat.mul_one]
        exact_mod_cast h1
      by_cases hL10 : u.e ≤ 10
      · rw [hm, show (23 - u.e).toNat = 13 + (10 - u.e).toNat by omega, Nat.pow_add,
          ← Nat.mul_assoc, Nat.mul_comm _ (2 ^ 13), Nat.mul_assoc]
        exact Nat.mul_mod_right _ _
      · have hn11 : z.natAbs = 2 ^ 11 := by
          have h2 : pow2 11 ≤ ((z.natAbs : ℕ) : ℚ) := by
            rw [← ha]; exact Rat.le_trans (pow2_le_of_le (by omega)) hlo
          rw [show (11 : ℤ) = ((11 : ℕ) : ℤ) from rfl, pow2_natCast] at h2
          have := Rat.natCast_le_natCast.mp h2
          omega
        rw [hm, hn11, show (23 - u.e).toNat = 12 by omega]
  have hval : (InputFormat.truncateXF32 u).value = u.value := by
    unfold InputFormat.truncateXF32 Unpacked.value
    simp only
    have hm : ((u.m / 2 ^ 13 : ℕ) : ℚ) * pow2 13 = (u.m : ℚ) := by
      rw [show (13 : ℤ) = ((13 : ℕ) : ℤ) from rfl, pow2_natCast, ← Rat.natCast_mul]
      congr 1; omega
    have ht : u.t = 23 := by
      by_cases hz0 : z = 0
      · obtain ⟨ht, _⟩ := decode32_finite_fields hu; exact ht
      · exact (hn hz0).2.1
    rw [ht]
    have hsplit : pow2 (u.e - ((10 : ℕ) : ℤ)) = pow2 13 * pow2 (u.e - ((23 : ℕ) : ℤ)) := by
      rw [← pow2_add]; congr 1; omega
    rw [hsplit]
    cases u.negative <;> simp only [Bool.false_eq_true, ↓reduceIte, Rat.neg_mul] <;>
      rw [← Rat.mul_assoc, hm]
  exact ⟨w, hw, ⟨_, hr, z, by rw [hval, hv]⟩, by rw [wordValue_of_read hr, hval, hv]⟩

/-! ## The matrix multiplier -/

/-- **The matrix core as a matrix multiplier for the Ozaki schemes.** Encode the integers exactly,
and evaluate the inner product with `dotBits` from `c = +0`. -/
def mcMultiplier (P : Model) : MatrixMultiplier := fun x y => do
  let a ← x.mapM fun z : ℤ => P.a.encodeExact (z : ℚ)
  let b ← y.mapM fun z : ℤ => P.b.encodeExact (z : ℚ)
  match dotBits P a b 0 with
  | .ok d => value32 d
  | .error _ => none

theorem encodeExact_zero (i : InputFormat) : i.encodeExact ((0 : ℤ) : ℚ) = some 0 := by
  cases i <;> simp [InputFormat.encodeExact, Format.encodeExact] <;> rfl

theorem intWord_zero {i : InputFormat} {b : ℕ} (h : EncodesInts i b) : IntWord i 0 := by
  obtain ⟨w, hw, hint, _⟩ := h 0 (by simp)
  rw [encodeExact_zero] at hw
  cases hw; exact hint

/-- Products and product magnitudes of encoded integer vectors. -/
theorem encoded_products {P : Model} (Ea : ℤ → P.a.Word) (Eb : ℤ → P.b.Word) :
    ∀ (x y : List ℤ), (∀ z ∈ x, P.a.wordValue (Ea z) = z) → (∀ z ∈ y, P.b.wordValue (Eb z) = z) →
      exactProducts P (x.map Ea) (y.map Eb) = (dotZ x y : ℚ) ∧
        wordDotAbs P (x.map Ea) (y.map Eb) = (dotAbs x y : ℚ)
  | [], _, _, _ => ⟨by simp [exactProducts, sumQ], by simp [wordDotAbs, sumQ]⟩
  | _ :: _, [], _, _ => ⟨by simp [exactProducts, sumQ], by simp [wordDotAbs, sumQ]⟩
  | a :: x, c :: y, hx, hy => by
    obtain ⟨h1, h2⟩ := encoded_products Ea Eb x y (fun z hz => hx z (by simp [hz]))
      (fun z hz => hy z (by simp [hz]))
    unfold exactProducts at h1 ⊢; unfold wordDotAbs at h2 ⊢
    simp only [List.map_cons, List.zipWith_cons_cons, sumQ, h1, h2, hx a (by simp),
      hy c (by simp), dotZ_cons, dotAbs_cons, Rat.intCast_add, Rat.intCast_mul, Rat.natCast_add]
    simp [← Rat.intCast_mul, absQ_intCast]

/-- **Exact matrix multiplier.** On an exact configuration whose operand formats hold every `b`-bit
integer, the matrix core is exact on `b`-bit integer vectors whose products total at most `2^24`
in magnitude. -/
theorem mcMultiplier_exactOn {P : Model} {b : ℕ} (hP : ExactConfig P) (hfa : smallSubnormals P.a)
    (hfb : smallSubnormals P.b) (hn : 0 < P.nfma) (hea : EncodesInts P.a b)
    (heb : EncodesInts P.b b) : (mcMultiplier P).ExactOn b (2 ^ 24) := by
  intro x y hlen hx hy hbound
  let Ea : ℤ → P.a.Word := fun z => (P.a.encodeExact (z : ℚ)).getD 0
  let Eb : ℤ → P.b.Word := fun z => (P.b.encodeExact (z : ℚ)).getD 0
  have hEa : ∀ z ∈ x, P.a.encodeExact (z : ℚ) = some (Ea z) ∧ IntWord P.a (Ea z) ∧
      P.a.wordValue (Ea z) = z := by
    intro z hz
    obtain ⟨w, hw, hi, hv⟩ := hea z (hx z hz)
    have : Ea z = w := by simp [Ea, hw]
    rw [this]; exact ⟨hw, hi, hv⟩
  have hEb : ∀ z ∈ y, P.b.encodeExact (z : ℚ) = some (Eb z) ∧ IntWord P.b (Eb z) ∧
      P.b.wordValue (Eb z) = z := by
    intro z hz
    obtain ⟨w, hw, hi, hv⟩ := heb z (hy z hz)
    have : Eb z = w := by simp [Eb, hw]
    rw [this]; exact ⟨hw, hi, hv⟩
  have hmx : x.mapM (fun z : ℤ => P.a.encodeExact (z : ℚ)) = some (x.map Ea) :=
    mapM_eq_some_map fun z hz => (hEa z hz).1
  have hmy : y.mapM (fun z : ℤ => P.b.encodeExact (z : ℚ)) = some (y.map Eb) :=
    mapM_eq_some_map fun z hz => (hEb z hz).1
  obtain ⟨hprod, hbud⟩ := encoded_products Ea Eb x y (fun z hz => (hEa z hz).2.2)
    (fun z hz => (hEb z hz).2.2)
  have hc : value32 (0 : F32) = some ((0 : ℤ) : ℚ) := by rw [Rat.intCast_zero]; exact value32_zero
  obtain ⟨d, hd, hv⟩ := dotBits_int (a := x.map Ea) (b := y.map Eb) hP hfa hfb hn
    (intWord_zero hea) (intWord_zero heb) (by simp [hlen])
    (fun w hw => by obtain ⟨z, hz, rfl⟩ := List.mem_map.mp hw; exact (hEa z hz).2.1)
    (fun w hw => by obtain ⟨z, hz, rfl⟩ := List.mem_map.mp hw; exact (hEb z hz).2.1) hc (by
      rw [hbud, Rat.intCast_zero, show absQ (0 : ℚ) = 0 from rfl]
      have : ((dotAbs x y : ℕ) : ℚ) ≤ ((2 ^ 24 : ℕ) : ℚ) := Rat.natCast_le_natCast.mpr hbound
      rw [show (24 : ℤ) = ((24 : ℕ) : ℤ) from rfl, pow2_natCast]
      grind)
  unfold mcMultiplier
  simp only [hmx, hmy, Option.bind_eq_bind, Option.bind_some, hd]
  rw [hv, hprod, Rat.intCast_zero]
  congr 1; grind

end Ozaki.MC
