import OzakiTC.Scaling

/-! # The lemmas about the Z3 models' matrix multiplier, on the Tensor Core model

The Z3 models' matrix multiplier takes fp16 operands, widens them to binary32, multiplies and adds
in binary32, and proves three lemmas about it (Ozaki-I `[Z.2]`, `[Z.3]`, `[Z.4]`; Ozaki-II `[Z.1]`,
`[Z.2]`, `[Z.3]`), with runtime checks `[E.1]`–`[E.4]`. The same facts, for every input:

* `fp16_encodes_int` (`I:[Z.2]`, `II:[Z.1]`, `[E.1]`, `[E.2]`): every integer of magnitude at most
  `2^11` is an fp16 word whose value is that integer;
* `fp16_encodes_residue` (`II:[S2.1]`): so is every symmetric residue modulo `m ≤ 4096`;
* `fp16_product_finiteValue32`, `fp16_product_exact` (`I:[Z.3]`, `II:[Z.2]`, `[E.3]`): the product
  of two finite fp16 values is a binary32 value, so a binary32 multiplication of them is exact;
* `fp32Add_int_exact` (`I:[Z.4]`, `II:[Z.3]`, `[E.4]`): a binary32 addition of integers whose sum is
  at most `2^24` is exact.

The Tensor Core itself multiplies exactly and adds a whole block FMA exactly before one rounding
(`evalBlock_int`, `runBlocks_int`); these lemmas are about the Z3 models' matrix multiplier, stated
with TC-EFT's formats and roundings. -/

open TensorCore

namespace Ozaki.TC

/-- **fp16 holds every `11`-bit integer** (`I:[Z.2]`, `II:[Z.1]`): the matrix multiplier's fp16
encoding of an integer `|z| ≤ 2^11` succeeds and decodes to `z`, so widening it is exact (`[E.1]`,
`[E.2]`). -/
theorem fp16_encodes_int {z : ℤ} (hz : z.natAbs ≤ 2 ^ 11) :
    ∃ w, encodeInt fp16 z = some w ∧ ∃ d, (classify fp16 w).finite = some d ∧ d.value = z :=
  encodeInt_spec (by decide) (by decide) (by decide) (Nat.le_trans hz (by decide))

/-- **Residues are fp16 words** (`II:[S2.1]`): a symmetric residue modulo `0 < m ≤ 4096`. -/
theorem fp16_encodes_residue (z : ℤ) {m : ℕ} (hm : 0 < m) (hm' : m ≤ 4096) :
    ∃ w, encodeInt fp16 (symMod z m) = some w ∧
      ∃ d, (classify fp16 w).finite = some d ∧ d.value = symMod z m :=
  fp16_encodes_int (by have := natAbs_symMod_le z hm; omega)

/-- **The product of two fp16 values is a binary32 value** (`I:[Z.3]`, `II:[Z.2]`): coefficients
below `2^11` give a product coefficient below `2^22`, on a grid between `2^-48` and `2^10`. -/
theorem fp16_product_finiteValue32 {a b : ℚ} (ha : fp16.FiniteValue a) (hb : fp16.FiniteValue b) :
    FiniteValue32 (a * b) := by
  obtain ⟨ka, ea, ha1, ha2, hka, rfl⟩ := ha
  obtain ⟨kb, eb, hb1, hb2, hkb, rfl⟩ := hb
  have hm : fp16.mantissaBits = 10 := by decide
  have hmin : fp16.emin = -14 := by decide
  have hmax : fp16.emax = 15 := by decide
  rw [hm] at hka hkb ⊢
  rw [hmin] at ha1 hb1
  rw [hmax] at ha2 hb2
  have hk : (ka * kb).natAbs < 2 ^ 24 := by
    rw [Int.natAbs_mul]
    have : ka.natAbs * kb.natAbs < 2 ^ 11 * 2 ^ 11 := Nat.mul_lt_mul'' hka hkb
    omega
  have := grid_finiteValue32 (ka * kb) (ea - 10 + (eb - 10)) (by omega) (by omega) hk
  have e : (ka : ℚ) * pow2 (ea - ((10 : ℕ) : ℤ)) * ((kb : ℚ) * pow2 (eb - ((10 : ℕ) : ℤ))) =
      ((ka * kb : ℤ) : ℚ) * pow2 (ea - 10 + (eb - 10)) := by
    rw [pow2_eq, pow2_eq, pow2_eq, two_pow_add, Rat.intCast_mul]
    have : ((10 : ℕ) : ℤ) = 10 := rfl
    rw [this]
    grind
  rw [e]; exact this

/-- **A binary32 multiplication of fp16 values is exact** (`[E.3]`). -/
theorem fp16_product_exact {a b : ℚ} (ha : fp16.FiniteValue a) (hb : fp16.FiniteValue b) :
    round32Value (a * b) = some (a * b) :=
  round32Value_of_finite (fp16_product_finiteValue32 ha hb)

/-- **Integer additions within `2^24` are exact in binary32** (`I:[Z.4]`, `II:[Z.3]`, `[E.4]`): the
Z3 accumulation step `|x| ≤ 3 · 2^22`, `|y| ≤ 2^22` is the case `k = 4`. -/
theorem fp32Add_int_exact (a c : ℤ) (h : (a + c).natAbs ≤ 2 ^ 24) :
    fp32Add (a : ℚ) (c : ℚ) = some ((a : ℚ) + c) := by
  apply fp32Add_exact
  have := int_finiteValue32 (a + c) h
  rwa [Rat.intCast_add] at this

end Ozaki.TC
