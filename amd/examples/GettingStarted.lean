import MatrixCore

/-! # Getting started

A block evaluation, the same words on three architectures, and the main theorems. -/

open MatrixCore

namespace MatrixCoreExamples.GettingStarted

/-- Four fp16 products `1 · 1` (`0x3C00 = 1`) and `c = 0` on CDNA 1. -/
def ones : BlockInput cdna1F16 := ⟨List.replicate 4 0x3C00, List.replicate 4 0x3C00, 0⟩

#eval blockBits ones

/-- The result is the binary32 encoding of `4`. -/
example : blockBits ones = .ok 0x40800000 := by decide +kernel

/-! ## One input, three generations

`c = 0` and the fp16 products `1, s, s, 0` with `s = 2^-23 + 2^-24` (`0x0E00 · 0x1000`):

* CDNA 1 adds exactly: `1 + 2s = 1 + 2^-22 + 2^-23`;
* CDNA 2 rounds each pair: `fl{fl{1 + s} + fl{s + 0}} = 1 + 2^-21`;
* CDNA 3 aligns the products with 24 mantissa bits, where `s` is exact: `1 + 2^-22 + 2^-23`.

`c = 1, p₁ = 2^-24 + 2^-32` (`0x0C04 · 0x0C00`) separates CDNA 3: RD of `S_acc` to 31
mantissa bits drops `2^-32`, and RNE then ties to `1`, while CDNA 1 and CDNA 2 give
`1 + 2^-23`. -/

/-- `a` and `b` of the products `1, s, s, 0`. -/
def as : List (BitVec 16) := [0x3C00, 0x0E00, 0x0E00, 0]
def bs : List (BitVec 16) := [0x3C00, 0x1000, 0x1000, 0]

def onCDNA1 : Except ModelError F32 := blockBits (P := cdna1F16) ⟨as, bs, 0⟩
def onCDNA2 : Except ModelError F32 := blockBits (P := cdna2F16) ⟨as, bs, 0⟩
/-- CDNA 3 has `N_FMA = 8`; the remaining products are zero. -/
def onCDNA3 : Except ModelError F32 :=
  blockBits (P := cdna3F16) ⟨as ++ List.replicate 4 0, bs ++ List.replicate 4 0, 0⟩

#eval (onCDNA1.map value32, onCDNA2.map value32, onCDNA3.map value32)

/-- `0x3F800003 = 1 + 3·2^-23`, `0x3F800004 = 1 + 2^-21`. -/
example : onCDNA1 = .ok 0x3F800003 ∧ onCDNA2 = .ok 0x3F800004 ∧ onCDNA3 = .ok 0x3F800003 := by
  decide +kernel

example : blockBits (P := cdna1F16) ⟨[0x0C04, 0, 0, 0], [0x0C00, 0, 0, 0], 0x3F800000⟩ = .ok 0x3F800001 ∧
    blockBits (P := cdna2F16) ⟨[0x0C04, 0, 0, 0], [0x0C00, 0, 0, 0], 0x3F800000⟩ = .ok 0x3F800001 ∧
    blockBits (P := cdna3F16) ⟨0x0C04 :: List.replicate 7 0, 0x0C00 :: List.replicate 7 0, 0x3F800000⟩ =
      .ok 0x3F800000 := by
  decide +kernel

/-! ## Theorems -/

/-- CDNA 1 is correctly rounded: the output is the binary32 value nearest to the exact
`Σ a_ℓ b_ℓ + c`, ties to even. -/
example {x : BlockInput cdna1F16} {t : BlockTrace cdna1F16} (h : evalBlock x = .ok t) :
    NearestEven32 t.prepared.exact t.d :=
  cdna1F16_nearestEven h

/-- The implementation agrees with the independent transcription of Algorithm 1 on every input. -/
example (x : BlockInput cdna3F16) (w : F32) :
    blockBits x = .ok w ↔ Spec.Result Spec.cdna3F16 (x.a.map BitVec.toNat) (x.b.map BitVec.toNat) x.c w :=
  Spec.supported_eq_spec_cdna3F16 x w

/-- The hardware-level observation reports a finite word exactly when the model accepts. -/
example (x : BlockInput cdna2F16) (d : F32) : blockOutcome x = some (.finite d) ↔ blockBits x = .ok d :=
  blockOutcome_finite_iff x d

end MatrixCoreExamples.GettingStarted
