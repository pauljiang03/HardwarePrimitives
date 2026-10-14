# Tests

`lake build` builds the `MatrixCoreTests` library, so every check below runs on every build. The
regressions are `example`s proved by kernel evaluation (`decide +kernel`) of the same definitions
the proofs use.

## The paper's test vectors

[Paper/CDNA1.lean](MatrixCoreTests/Paper/CDNA1.lean), [CDNA2.lean](MatrixCoreTests/Paper/CDNA2.lean)
and [CDNA3.lean](MatrixCoreTests/Paper/CDNA3.lean) contain every test vector of the paper's
Section 4, in order, each with the output the paper reports for the hardware. Parameterized
families (for example `j = 24 … 32`) are checked for every listed value.

Inputs are written by decoded value. [Support.lean](MatrixCoreTests/Support.lean) encodes each
value exactly or returns `none`, so an input a format cannot represent fails the test instead of
being rounded silently. A product written by value, `p`, is formed from normal operands
`a · b = p` with `e_a + e_b = ⌊log₂|p|⌋`; where the paper names the operands (for example
`a₁ = b₁ = 1.5`), the test uses them.

Where a vector of the paper cannot be formed in the stated format or disagrees with the paper's
own Algorithm 1, the test says so next to it; [paper notes](../docs/paper-notes.md) lists these.

## Formats and special values

[Formats.lean](MatrixCoreTests/Formats.lean) checks the extreme words of every Table 1 format,
the FNUZ conventions, XF32 truncation, ties and the binary32 overflow threshold.
[Special.lean](MatrixCoreTests/Special.lean) checks infinities and NaN, including products that
overflow when `c` is already infinite, as in a chained inner product.

## Fixed-width accumulation

[Machine.lean](MatrixCoreTests/Machine.lean) shows that the proved register widths are needed:
eight fp16 products just below 4 give the model's output in a 30-bit register and wrap in a
29-bit one; sixteen fp8 products fit 30 bits per odd/even group but need 31 once combined.

## Chained blocks

[Chain.lean](MatrixCoreTests/Chain.lean) uses the contracts as a downstream proof would: from one
accepted inner product it derives that every CDNA 1 block rounds to nearest and every CDNA 3 block
gives the same trace in 30-bit registers, and it evaluates a two-block run.

## Output error bounds

[ErrorBounds.lean](MatrixCoreTests/ErrorBounds.lean) evaluates the actual error `exact − d` and the
proved bound on the paper's examples: on CDNA 1 a tie meets the bound exactly; on CDNA 2 and
CDNA 3 the error lies within it. It also derives inner-product error bounds from the contracts.

## Monotonicity, inner products and `D = AB + C`

[Monotonicity.lean](MatrixCoreTests/Monotonicity.lean) runs the TC-EFT paper's non-monotonicity
construction (lowering `c` from `1` to `1 − 2^-24` with small products) on CDNA 1, 2 and 3: the
lower `c` does not give a larger output, as `evalBlock_c_monotone` proves for every input. The
counterparts in the products are in the library itself: kernel-checked pairs on CDNA 2 and CDNA 3
where a larger product gives a smaller output (`MatrixCore/MC/ProductMonotonicity.lean`).
[InnerProduct.lean](MatrixCoreTests/InnerProduct.lean) checks an exact inner product over two
blocks, a `2 × 2` `D = AB + C` with an infinite `c`, and the CDNA 3 bound from the inputs alone.

## Differential testing

`scripts/matlab_diff.py` compares the model with the authors' MATLAB models on random inputs;
see [differential testing](../docs/differential.md).

## Trust audit

[Audit.lean](MatrixCoreTests/Audit.lean) prints, during the build:

* `spec_independence_audit`: the specification's declarations depend only on the standard
  library and the notation module;
* `axiom_audit`: every theorem in `MatrixCore` uses only `propext`, `Classical.choice` and
  `Quot.sound`;
* `negative_control`: the independence check detects a declaration that uses the implementation.

## Adding a vector

```lean
import MatrixCoreTests.Support

open MatrixCore MatrixCoreTests

-- CDNA 3 bf16: c = 0, p₁ = 2^-150, p₂ = 2^-153: aligned to e_c = −126 and rounded down to
-- 31 mantissa bits, S_acc = 2^-150 + 2^-153 rounds up to 2^-149.
example : observeP cdna3BF16 [p2 (-150), p2 (-153)] (0 : ℚ) = some (.v (p2 (-149))) := by
  decide +kernel
```
