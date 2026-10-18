import OzakiMC.IEEEBounded
import Ozaki.IEEEWords

/-! # The integer word decoder agrees with MatrixCore's

`Ozaki.decodeWord` reads a stored word with integer operations on its fields. For every format of
MatrixCore with IEEE special values (binary32, binary16, bfloat16, the 19-bit format) and every
word, it gives the datum MatrixCore's `decodeNat` gives: the same infinity or NaN, and for a finite
word the same value and sign bit (`decodeWord_decodeNat`). On binary32 words it is MatrixCore's
binary32 decoding (`decodeWord_binary32`, `decodeWord_value32`). `mcOzaki1CRILW_eq` runs correctly
rounded binary32 Ozaki-I in integers on binary32 words on a Matrix Core variant, with every step,
special cases included, in integer arithmetic. -/

open MatrixCore

namespace Ozaki.MC

/-- The `WordFormat` of a MatrixCore format. -/
def wordFormatOf (f : Format) : WordFormat := ⟨f.mantissaBits, f.exponentBits, f.bias⟩

theorem wordFormatOf_binary32 : wordFormatOf fp32 = WordFormat.binary32 := rfl

/-- The IEEE datum MatrixCore's decoding gives a word. -/
def datumFVal : Datum → FVal
  | .nan => .nan
  | .infinity s => .inf s
  | .finite x => .fin ⟨x.value, x.negative⟩

/-- **The integer decoder is MatrixCore's**, on every format with IEEE special values and every
word. -/
theorem decodeWord_decodeNat (f : Format) (hf : f.specials = .ieee) (n : ℕ) :
    (decodeWord (wordFormatOf f) n).toFVal = datumFVal (f.decodeNat n) := by
  unfold decodeWord wordFields Format.decodeNat wordFormatOf
  rw [hf]
  simp only
  generalize (n / 2 ^ (f.mantissaBits + f.exponentBits) % 2 == 1) = sg
  generalize n / 2 ^ f.mantissaBits % 2 ^ f.exponentBits = E
  generalize n % 2 ^ f.mantissaBits = M
  have he : f.emin - (f.mantissaBits : ℤ) = 1 - f.bias - f.mantissaBits := by
    unfold Format.emin; omega
  by_cases hE : E = 2 ^ f.exponentBits - 1
  · rw [if_pos hE, if_pos hE]
    by_cases hM : M = 0
    · rw [if_pos hM, if_pos hM]; rfl
    · rw [if_neg hM, if_neg hM]; rfl
  · rw [if_neg hE, if_neg hE]
    unfold Format.unpackFields
    by_cases h0 : E = 0
    · rw [if_pos h0, if_pos h0]
      cases sg <;> simp [IDatum.toFVal, toSigned, signedSig, datumFVal, Unpacked.value,
        entryVal, pow2, he, Rat.intCast_natCast]
    · rw [if_neg h0, if_neg h0]
      cases sg <;> simp [IDatum.toFVal, toSigned, signedSig, datumFVal, Unpacked.value,
        entryVal, pow2, Rat.intCast_natCast]

/-- On binary32 words the integer decoder is MatrixCore's binary32 decoding. -/
theorem decodeWord_binary32 (w : F32) :
    (decodeWord .binary32 w.toNat).toFVal = datumFVal (fp32.decode w) :=
  decodeWord_decodeNat fp32 rfl w.toNat

/-- A word MatrixCore decodes to a finite value decodes to that value. -/
theorem decodeWord_value32 {w : F32} {v : ℚ} (h : value32 w = some v) :
    ∃ n, (decodeWord .binary32 w.toNat).toFVal = .fin ⟨v, n⟩ := by
  rw [decodeWord_binary32]
  unfold value32 at h
  cases hd : fp32.decode w with
  | finite x =>
    rw [hd] at h
    simp only [Datum.toFinite, Option.map_some, Option.some.injEq] at h
    exact ⟨x.negative, by rw [← h]; rfl⟩
  | infinity s => rw [hd] at h; simp [Datum.toFinite] at h
  | nan => rw [hd] at h; simp [Datum.toFinite] at h

theorem decodeWord_inFormat32 (w : ℕ) : (decodeWord .binary32 w).InFormat 24 (-126) 127 :=
  decodeWord_inFormat .binary32 (by decide) w

/-- **Correctly rounded binary32 Ozaki-I on binary32 words on a Matrix Core variant, every step in
integer arithmetic**: the words decoded by integer operations, the special cases decided on the
stored data, the finite entries through the integer scheme with the integer sign oracle; the
result meets the IEEE specification on the words as MatrixCore decodes them. -/
theorem mcOzaki1CRILW_eq {P : Model} {b : ℕ} (hP : ExactMultiplier P b) (hb : 2 * b ≤ 24) (W : ℕ)
    (ss : List ℕ) {smax : ℕ} (hsmax : 277 < smax * (b + 1)) {ws vs : List F32}
    (hlen : ws.length = vs.length) :
    crIEEEWord .binary32 (mcOzaki1CRIL P b W ss smax)
        (fun x y => (exactSignI (mcSplitK P b) b smax x y).getD 0)
        (ws.map BitVec.toNat) (vs.map BitVec.toNat) =
      dotIEEE 24 (-126) 127 (ws.map fun w => datumFVal (fp32.decode w))
        (vs.map fun w => datumFVal (fp32.decode w)) := by
  unfold crIEEEWord
  rw [crIEEEIW_eq]
  have h := mcOzaki1CRILI_eq hP hb W ss hsmax
    (xs := (ws.map BitVec.toNat).map (decodeWord .binary32))
    (ys := (vs.map BitVec.toNat).map (decodeWord .binary32))
    (fun a ha => by obtain ⟨w, _, rfl⟩ := List.mem_map.mp ha; exact decodeWord_inFormat32 w)
    (fun a ha => by obtain ⟨w, _, rfl⟩ := List.mem_map.mp ha; exact decodeWord_inFormat32 w)
    (by simp [hlen])
  unfold mcOzaki1CRILI at h
  rw [h]
  simp only [List.map_map]
  congr 1 <;> apply List.map_congr_left <;> intro w _ <;> exact decodeWord_binary32 w

/-! ## Examples, checked by the kernel -/

/-- `Inf · (−0)`: NaN, decided by integer operations on binary32 words, on CDNA 3 fp16 blocks. -/
example : crIEEEWord .binary32 (mcOzaki1CRIL cdna3F16 11 96 [3, 4] 24)
    (fun x y => (exactSignI (mcSplitK cdna3F16 11) 11 24 x y).getD 0)
    [0x7F800000, 0x3F800000] [0x80000000, 0x40000000] = .nan := by
  decide +kernel

/-- `1 · 2 + (−0) · 3 = 2` on binary32 words. -/
example : crIEEEWord .binary32 (mcOzaki1CRIL cdna3F16 11 96 [3, 4] 24)
    (fun x y => (exactSignI (mcSplitK cdna3F16 11) 11 24 x y).getD 0)
    [0x3F800000, 0x80000000] [0x40000000, 0x40400000] = .fin ⟨2, false⟩ := by
  decide +kernel

/-- `(−0) · 1 + 0 · (−1)`: every product is `−0`, so the result is `−0`. -/
example : crIEEEWord .binary32 (mcOzaki1CRIL cdna3F16 11 96 [3, 4] 24)
    (fun x y => (exactSignI (mcSplitK cdna3F16 11) 11 24 x y).getD 0)
    [0x80000000, 0x00000000] [0x3F800000, 0xBF800000] = .fin ⟨0, true⟩ := by
  decide +kernel

end Ozaki.MC
