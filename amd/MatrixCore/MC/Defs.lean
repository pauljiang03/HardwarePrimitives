import MatrixCore.Numerics

/-! # Matrix-core feature parameters

A `Model` records the numerical features of one block of `N_FMA` products, following the paper's
feature comparison table. -/

namespace MatrixCore

/-- The four configurations of the generalized matrix-multiplier model. -/
inductive Accumulation where
  /-- `correct_rounding`: the exact sum `Σ p_ℓ + c` and one final RNE (CDNA 1, SFMA). -/
  | correctRounding
  /-- `pair_wise_sum`: FP32 products, then `fl{c + fl{fl{p₁ + p₂} + fl{p₃ + p₄}}}` (CDNA 2). -/
  | pairWiseSum
  /-- `global_alignment` with late `c` (CDNA 3 FP16, BF16, XF32; Algorithm 1). -/
  | globalAlignment
  /-- `odd_even_grouping` with late `c` (CDNA 3 FP8; Algorithm 2). -/
  | oddEvenGrouping
  deriving Repr, DecidableEq

/-- The alignment `align(c, S_{p_i,sum})` of `c` and the product sum. -/
structure LateAlignment where
  /-- `s_c` shifted right by `e_max − e_c` and RD to this many mantissa bits. -/
  cMantissaBits : ℕ := 24
  /-- `S_{p_i,sum}` shifted right by `e_c − e_max` and RD to this many mantissa bits. -/
  sumMantissaBits : ℕ := 32
  /-- `S_acc` normalized and RD to this many mantissa bits, only when `S_{p_i,sum}` was shifted. -/
  accMantissaBits : ℕ := 31
  /-- FP8: once `e_max − e_c` exceeds this shift, `s'_c = 0` (truncation instead of RD). -/
  cCutoff : Option ℕ := none
  deriving Repr, DecidableEq

/-- Numerical features of one MFMA block. -/
structure Model where
  a : InputFormat
  b : InputFormat
  /-- `N_FMA`: products per multi-term addition (group size of a pairwise sum). -/
  nfma : ℕ
  accumulation : Accumulation
  /-- Padding bits: aligned products keep `23 + padding` mantissa bits. -/
  padding : ℕ := 1
  /-- `e_{c=0}`: exponent of `c` when `c = 0`; `none` is `−∞` (a zero `c` is discarded). -/
  cZeroExp : Option ℤ := some (-126)
  late : LateAlignment := {}
  /-- Subnormal support; otherwise inputs and every `fl{·}` result are flushed to zero (CDNA 2). -/
  subnormals : Bool := true
  /-- A product with `|p_ℓ| ≥ 2^128` overflows before accumulation. -/
  productOverflow : Bool := false
  deriving Repr, DecidableEq

/-- Product alignment `(integer bits, mantissa bits)` of the feature table. -/
def Model.productAlignment (P : Model) : ℕ × Option ℕ :=
  match P.accumulation with
  | .correctRounding => (1, none)
  | .pairWiseSum => (1, some 23)
  | .globalAlignment | .oddEvenGrouping => (2, some (23 + P.padding))

/-- Whether `c` is added after the product accumulation (late) or within it (early). -/
def Model.lateC (P : Model) : Bool :=
  match P.accumulation with
  | .globalAlignment | .oddEvenGrouping => true
  | _ => false

end MatrixCore
