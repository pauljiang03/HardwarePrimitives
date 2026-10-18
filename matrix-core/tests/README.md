# Tests

`MatrixCoreTests` is built by `lake build`, so every check runs on every
build. The regressions are `example`s proven by kernel evaluation of the same
definitions the proofs use.

| Module | Contents |
| --- | --- |
| [`Paper/`](MatrixCoreTests/Paper) | Every test vector of the paper's Section 4 for CDNA 1, 2 and 3, with the output reported for the hardware |
| [`Formats.lean`](MatrixCoreTests/Formats.lean), [`Special.lean`](MatrixCoreTests/Special.lean) | Extreme words of every format, FNUZ conventions, XF32, infinities and NaN |
| [`Machine.lean`](MatrixCoreTests/Machine.lean) | The fixed-width register widths, and inputs that wrap one bit narrower |
| [`ErrorBounds.lean`](MatrixCoreTests/ErrorBounds.lean) | The actual error against the proven bound on the paper's examples |
| [`Monotonicity.lean`](MatrixCoreTests/Monotonicity.lean), [`ProductProperties.lean`](MatrixCoreTests/ProductProperties.lean) | Monotonicity in `c`, non-monotonicity in the products and its threshold, correct rounding without alignment loss |
| [`Chain.lean`](MatrixCoreTests/Chain.lean), [`InnerProduct.lean`](MatrixCoreTests/InnerProduct.lean) | Contracts used downstream, inner products and `D = AB + C` |
| [`EFT.lean`](MatrixCoreTests/EFT.lean) | The MC-EFT correction on each generation and on inner products, the condition on the inputs, and the 576-bit register version |
| [`Audit.lean`](MatrixCoreTests/Audit.lean) | Standard axioms only; independence of the specification, with a negative control |

Inputs are written by decoded value and encoded exactly
([`Support.lean`](MatrixCoreTests/Support.lean)), so an input a format cannot
represent fails the test instead of being rounded. Where a paper vector cannot
be formed in its stated format, or disagrees with the paper's Algorithm 1, the
test says so; [the paper notes](../docs/paper-notes.md) list these cases.

## Adding a vector

```lean
import MatrixCoreTests.Support

open MatrixCore MatrixCoreTests

-- CDNA 3 BF16: c = 0, p₁ = 2^-150, p₂ = 2^-153: aligned to e_c = −126 and rounded down to
-- 31 mantissa bits, S_acc = 2^-150 + 2^-153 rounds up to 2^-149.
example : observeP cdna3BF16 [p2 (-150), p2 (-153)] (0 : ℚ) = some (.v (p2 (-149))) := by
  decide +kernel
```
