import MatrixCore.Numerics

/-! # Matrix-core feature parameters

An MFMA instruction computes `D = AB + C`; every element is the inner product of Eq. (1),
`d = Σ_{ℓ=1}^{k} a_ℓ b_ℓ + c = Σ_{ℓ=1}^{k} p_ℓ + c`, evaluated in blocks of `N_FMA` products.
A `Model` records the numerical features of one block, following the rows of the paper's
feature comparison table:

* input formats of `a` and `b` (`c` and `d` are binary32);
* `N_FMA`, the number of products in one multi-term addition;
* product alignment `(2, 23 + padding)`: the integer bits and the mantissa bits kept after
  alignment, the 23-bit mantissa plus `padding` padding bits (`n_eab` in the paper);
* `e_{c=0}`: the exponent given to `c = 0`;
* late addition of `c`, and `align(c, S_{p_i,sum}) = (24, 32, RD)`;
* the final rounding (RNE on every CDNA variant);
* `|p_i|` overflow at `2^128`;
* subnormal support in input and output.

The accumulation itself is one of the four architectural configurations of the paper's
generalized model. -/

namespace MatrixCore

/-- The four configurations of the generalized matrix-multiplier model. -/
inductive Accumulation where
  /-- `correct_rounding`: products in full precision, the exact sum `Σ p_ℓ + c`, and one final
  RNE (Kulisch accumulator; CDNA 1, and every SFMA step). -/
  | correctRounding
  /-- `pair_wise_sum`: products converted to binary32, then
  `fl{c + fl{fl{p₁ + p₂} + fl{p₃ + p₄}}}`, a balanced pairwise sum over `N_FMA` products
  (CDNA 2). -/
  | pairWiseSum
  /-- `global_alignment` with late `c` (CDNA 3 fp16, bf16, tf19; Algorithm 1). -/
  | globalAlignment
  /-- `odd_even_grouping`: odd- and even-indexed products aligned and accumulated separately,
  then combined, then late `c` (CDNA 3 binary8; Algorithm 2). -/
  | oddEvenGrouping
  deriving Repr, DecidableEq

/-- Two-operand alignment between `c` and the product sum (`align(c, S_{p_i,sum})`). -/
structure LateAlignment where
  /-- `s_c` shifted right by `e_max − e_c` and RD to this many mantissa bits. -/
  cMantissaBits : ℕ := 24
  /-- `S_{p_i,sum}` shifted right by `e_c − e_max` and RD to this many mantissa bits. -/
  sumMantissaBits : ℕ := 32
  /-- `S_acc` normalized (subnormal-aware) and RD to this many mantissa bits; applied only
  when `S_{p_i,sum}` was shifted. -/
  accMantissaBits : ℕ := 31
  /-- binary8: once `e_max − e_c` exceeds this shift, `s'_c = 0` (truncation instead of RD). -/
  cCutoff : Option ℕ := none
  deriving Repr, DecidableEq

/-- Numerical features of one MFMA block. -/
structure Model where
  /-- Input format of `a`. -/
  a : InputFormat
  /-- Input format of `b`. -/
  b : InputFormat
  /-- `N_FMA`: products per multi-term addition (group size of a pairwise sum). -/
  nfma : ℕ
  accumulation : Accumulation
  /-- The padding bits: product significands are aligned to `e_max` and truncated to
  `23 + padding` mantissa bits. -/
  padding : ℕ := 1
  /-- `e_{c=0}`: exponent of `c` when `c = 0`; `none` is `−∞` (a zero `c` is discarded). -/
  cZeroExp : Option ℤ := some (-126)
  late : LateAlignment := {}
  /-- Subnormals supported in input and output; otherwise they are flushed to zero in the
  inputs and after every `fl{·}` (CDNA 2 pairwise sums). -/
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
