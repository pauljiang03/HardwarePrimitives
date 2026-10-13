import OzakiTC.ADPIEEE
import OzakiTC.IEEEBounded
import Ozaki.IEEEWords

/-! # The integer word decoder agrees with TensorCore's

`Ozaki.decodeWord` reads a stored word with integer operations on its fields. For every binary
format of TensorCore (`Format`: stored significand bits, exponent bits, bias) and every word, it
classifies the word as TensorCore's `classifyNat` does and gives the same value and sign
(`decodeWord_classifyNat`); in particular, on binary64 words it is the decoder of the ADP routine
with special values (`decodeWord_binary64`), so `crIEEEWord`'s special-case detection on stored
words is the specification's. `tcOzaki1CRIDW_eq` runs correctly rounded FP64 Ozaki-I in integers on
binary64 words with every step, special cases included, in integer arithmetic. -/

open TensorCore

namespace Ozaki.TC

/-- The `WordFormat` of a TensorCore format. -/
def wordFormatOf (f : Format) : WordFormat := ⟨f.mantissaBits, f.exponentBits, f.bias⟩

theorem wordFormatOf_fp64 : wordFormatOf fp64 = WordFormat.binary64 := rfl
theorem wordFormatOf_fp32 : wordFormatOf fp32 = WordFormat.binary32 := rfl

/-- The IEEE datum TensorCore's classification gives a word. -/
def classifyFVal : Classification → FVal
  | .nan => .nan
  | .infinity s => .inf s
  | .zero s => .fin ⟨0, s⟩
  | .subnormal d => .fin ⟨d.value, decide (d.significand < 0)⟩
  | .normal d => .fin ⟨d.value, decide (d.significand < 0)⟩

theorem sign_bit_eq {x : ℕ} (hx : x < 2) : (x % 2 == 1) = (x != 0) := by
  rcases (show x = 0 ∨ x = 1 by omega) with rfl | rfl <;> rfl

/-- The sign of `±m · 2^e` is the sign bit when `m > 0`. -/
theorem sign_of_signed {sg : Bool} {m : ℕ} (hm : 0 < m) :
    decide ((if sg = true then -(m : ℤ) else (m : ℤ)) < 0) = sg := by
  cases sg <;> simp <;> omega

theorem signed_ne_zero {sg : Bool} {m : ℕ} (hm : m ≠ 0) :
    (if sg = true then -(m : ℤ) else (m : ℤ)) ≠ 0 := by
  cases sg <;> simp <;> omega

theorem width_div_lt (f : Format) {n : ℕ} (hn : n < 2 ^ f.width) :
    n / 2 ^ (f.mantissaBits + f.exponentBits) < 2 := by
  have h2 : 2 ^ f.width = 2 ^ (f.mantissaBits + f.exponentBits) * 2 := by
    unfold Format.width; rw [← Nat.pow_succ]; congr 1; omega
  exact Nat.div_lt_of_lt_mul (h2 ▸ hn)

/-- **The integer decoder classifies every word as TensorCore does**, with the same value and sign. -/
theorem decodeWord_classifyNat (f : Format) {n : ℕ} (hn : n < 2 ^ f.width) :
    (decodeWord (wordFormatOf f) n).toFVal = classifyFVal (classifyNat f n) := by
  have hsg := sign_bit_eq (width_div_lt f hn)
  unfold decodeWord wordFields classifyNat wordFormatOf
  simp only [hsg]
  generalize (n / 2 ^ (f.mantissaBits + f.exponentBits) != 0) = sg
  generalize n / 2 ^ f.mantissaBits % 2 ^ f.exponentBits = E
  generalize n % 2 ^ f.mantissaBits = M
  by_cases h1 : E = 2 ^ f.exponentBits - 1
  · rw [if_pos h1, if_pos h1]
    by_cases h2 : M = 0
    · rw [if_pos h2, if_pos h2]; rfl
    · rw [if_neg h2, if_neg h2]; rfl
  · rw [if_neg h1, if_neg h1]
    by_cases h3 : E = 0
    · rw [if_pos h3, if_pos h3]
      by_cases h2 : M = 0
      · rw [if_pos h2]
        subst h2
        simp [IDatum.toFVal, classifyFVal, toSigned, entryVal, signedSig]
      · rw [if_neg h2]
        simp only [IDatum.toFVal, classifyFVal, toSigned, Decoded.value, entryVal, signedSig,
          pow2_eq]
        rw [sign_of_signed (Nat.pos_of_ne_zero h2)]
    · rw [if_neg h3, if_neg h3]
      simp only [IDatum.toFVal, classifyFVal, toSigned, Decoded.value, entryVal, signedSig, pow2_eq]
      rw [sign_of_signed (Nat.add_pos_left (Nat.two_pow_pos _) _)]

/-- The finite classes of TensorCore's classification have a nonzero significand. -/
theorem classify_significand_ne_zero {f : Format} {n : ℕ} {d : Decoded}
    (h : classifyNat f n = .subnormal d ∨ classifyNat f n = .normal d) : d.significand ≠ 0 := by
  unfold classifyNat at h
  simp only at h
  generalize (n / 2 ^ (f.mantissaBits + f.exponentBits) != 0) = sg at h
  generalize n / 2 ^ f.mantissaBits % 2 ^ f.exponentBits = E at h
  generalize n % 2 ^ f.mantissaBits = M at h
  by_cases h1 : E = 2 ^ f.exponentBits - 1
  · rw [if_pos h1] at h
    split at h <;> simp at h
  · rw [if_neg h1] at h
    by_cases h3 : E = 0
    · rw [if_pos h3] at h
      by_cases h2 : M = 0
      · rw [if_pos h2] at h; simp at h
      · rw [if_neg h2] at h
        rcases h with h | h <;> cases h
        exact signed_ne_zero h2
    · rw [if_neg h3] at h
      rcases h with h | h <;> cases h
      exact signed_ne_zero (Nat.ne_of_gt (Nat.add_pos_left (Nat.two_pow_pos _) _))

theorem value_sign {d : Decoded} (h : d.significand ≠ 0) :
    d.value ≠ 0 ∧ decide (d.value < 0) = decide (d.significand < 0) := by
  unfold Decoded.value
  have hp := pow2_pos (d.unnormalizedExp - d.mantissaBits)
  generalize pow2 (d.unnormalizedExp - d.mantissaBits) = P at hp
  refine ⟨?_, ?_⟩
  · intro h0
    rcases Rat.mul_eq_zero.mp h0 with h0 | h0
    · exact h (by exact_mod_cast h0)
    · exact absurd h0 (Rat.ne_of_gt hp)
  · by_cases hn : d.significand < 0
    · have : (d.significand : ℚ) < 0 := by exact_mod_cast hn
      have := Rat.mul_lt_mul_of_pos_right this hp
      rw [Rat.zero_mul] at this
      simp [this, hn]
    · have : (0 : ℚ) ≤ d.significand := by exact_mod_cast (Int.not_lt.mp hn)
      have := Rat.mul_nonneg this (Rat.le_of_lt hp)
      simp [hn, Rat.not_lt.mpr this]

/-- **On binary64 words the integer decoder is the ADP routine's decoder.** -/
theorem decodeWord_binary64 (w : BitVec 64) :
    (decodeWord .binary64 w.toNat).toFVal = decodeF64 w := by
  rw [← wordFormatOf_fp64, decodeWord_classifyNat fp64 w.isLt]
  unfold decodeF64 value64 binaryValue classify
  cases hc : classifyNat fp64 w.toNat with
  | nan =>
    obtain ⟨h0, _⟩ := classify64_nan hc
    simp [classifyFVal, Classification.finite, h0]
  | infinity m =>
    obtain ⟨h0, hsgn⟩ := classify64_infinity w.isLt hc
    simp [classifyFVal, Classification.finite, h0, signBit64, hsgn]
  | zero m =>
    have : m = signBit64 w := by
      unfold classifyNat at hc
      dsimp only [fp64] at hc
      have hlt : w.toNat / 2 ^ 63 < 2 := by have := w.isLt; omega
      split at hc
      · split at hc <;> cases hc
      · split at hc
        · split at hc
          · cases hc
            unfold signBit64
            rcases (show w.toNat / 2 ^ 63 = 0 ∨ w.toNat / 2 ^ 63 = 1 by omega) with h | h <;>
              simp [h]
          · cases hc
        · cases hc
    subst this
    simp [classifyFVal, Classification.finite, Decoded.value]
  | subnormal d =>
    obtain ⟨h1, h2⟩ := value_sign (classify_significand_ne_zero (Or.inl hc))
    simp only [classifyFVal, Classification.finite, Option.map_some, if_neg h1, h2]
  | normal d =>
    obtain ⟨h1, h2⟩ := value_sign (classify_significand_ne_zero (Or.inr hc))
    simp only [classifyFVal, Classification.finite, Option.map_some, if_neg h1, h2]

/-- **On binary32 words the integer decoder is TensorCore's.** -/
theorem decodeWord_binary32 (w : BitVec 32) :
    (decodeWord .binary32 w.toNat).toFVal = classifyFVal (classify fp32 w) := by
  rw [← wordFormatOf_fp32]; exact decodeWord_classifyNat fp32 w.isLt

/-- The class of a TensorCore classification. -/
def classWord : Classification → WordClass
  | .zero _ => .zero
  | .subnormal _ => .subnormal
  | .normal _ => .normal
  | .infinity _ => .inf
  | .nan => .nan

/-- **The integer classification of a word is TensorCore's.** -/
theorem wordClass_classifyNat (f : Format) (n : ℕ) :
    wordClass (wordFormatOf f) n = classWord (classifyNat f n) := by
  unfold wordClass wordFields classifyNat wordFormatOf
  simp only
  generalize (n / 2 ^ (f.mantissaBits + f.exponentBits) != 0) = sg
  generalize n / 2 ^ f.mantissaBits % 2 ^ f.exponentBits = E
  generalize n % 2 ^ f.mantissaBits = M
  by_cases h1 : E = 2 ^ f.exponentBits - 1
  · rw [if_pos h1, if_pos h1]
    by_cases h2 : M = 0
    · rw [if_pos h2, if_pos h2]; rfl
    · rw [if_neg h2, if_neg h2]; rfl
  · rw [if_neg h1, if_neg h1]
    by_cases h3 : E = 0
    · rw [if_pos h3, if_pos h3]
      by_cases h2 : M = 0
      · rw [if_pos h2, if_pos h2]; rfl
      · rw [if_neg h2, if_neg h2]; rfl
    · rw [if_neg h3, if_neg h3]; rfl

theorem decodeWord_inFormat64 (w : ℕ) : (decodeWord .binary64 w).InFormat 53 (-1022) 1023 :=
  decodeWord_inFormat .binary64 (by decide) w

theorem decodeWord_inFormat32 (w : ℕ) : (decodeWord .binary32 w).InFormat 24 (-126) 127 :=
  decodeWord_inFormat .binary32 (by decide) w

/-- **Correctly rounded FP64 Ozaki-I on binary64 words, every step in integer arithmetic**: the
words decoded by integer operations, the special cases decided on the stored data, the finite
entries through the integer scheme with the integer sign oracle; the result meets the IEEE
specification on the words as the ADP routine decodes them. -/
theorem tcOzaki1CRIDW_eq {p : Model} {b : ℕ} (hmult : (tcMultiplier p).ExactOn b (2 ^ 24))
    (hb : 2 * b ≤ 24) (W : ℕ) (ss : List ℕ) {smax : ℕ} (hsmax : 2098 < smax * (b + 1))
    {ws vs : List (BitVec 64)} (hlen : ws.length = vs.length) :
    crIEEEWord .binary64 (tcOzaki1CRID p b W ss smax)
        (fun x y => (exactSignI (tcSplitK p b) b smax x y).getD 0)
        (ws.map BitVec.toNat) (vs.map BitVec.toNat) =
      dotIEEE 53 (-1022) 1023 (ws.map decodeF64) (vs.map decodeF64) := by
  unfold crIEEEWord
  rw [crIEEEIW_eq]
  have h := tcOzaki1CRIDI_eq hmult hb W ss hsmax
    (xs := (ws.map BitVec.toNat).map (decodeWord .binary64))
    (ys := (vs.map BitVec.toNat).map (decodeWord .binary64))
    (fun a ha => by obtain ⟨w, _, rfl⟩ := List.mem_map.mp ha; exact decodeWord_inFormat64 w)
    (fun a ha => by obtain ⟨w, _, rfl⟩ := List.mem_map.mp ha; exact decodeWord_inFormat64 w)
    (by simp [hlen])
  unfold tcOzaki1CRIDI at h
  rw [h]
  simp only [List.map_map]
  congr 1 <;> apply List.map_congr_left <;> intro w _ <;> exact decodeWord_binary64 w

/-! ## Examples, checked by the kernel -/

/-- `Inf · (−0)`: NaN, decided by integer operations on the words. -/
example : crIEEEWord .binary64 (tcOzaki1CRID v100F16F32 11 96 [5, 6] 175)
    (fun x y => (exactSignI (tcSplitK v100F16F32 11) 11 175 x y).getD 0)
    [0x7FF0000000000000, 0x3FF0000000000000] [0x8000000000000000, 0x4000000000000000] = .nan := by
  decide +kernel

/-- `1 · 2 + (−0) · 3 = 2` on binary64 words. -/
example : crIEEEWord .binary64 (tcOzaki1CRID v100F16F32 11 96 [5, 6] 175)
    (fun x y => (exactSignI (tcSplitK v100F16F32 11) 11 175 x y).getD 0)
    [0x3FF0000000000000, 0x8000000000000000] [0x4000000000000000, 0x4008000000000000] =
      .fin ⟨2, false⟩ := by
  decide +kernel

end Ozaki.TC
