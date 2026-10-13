# The tensor-core block model

The model evaluates one block FMA: K exact products plus an FP32 accumulator input C, added in a single multi-term addition. The model of each named variant specifies its numerical features: the FMA size K, the number p of extra alignment bits, an optional minimum alignment exponent, and the input format (FP16, BF16, or packed TF32). Every model in this chapter uses the FP32 output format.

## Follow one block

| Stage | Executable definitions | Mathematical role |
| --- | --- | --- |
| Decode | `prepare`, `prepareProducts`, `Model.decode` | Decode finite words and preserve unnormalized exponent/mantissa metadata |
| Multiply | `unnormalizedMul`, `PreparedBlock.terms` | Form exact products and keep them in denormalized form, with the sum of the input exponents |
| Select grid | `PreparedBlock.alignExp`, `alignGridExponent` | Take the largest exponent of a nonzero term, raise it to the minimum alignment exponent, and subtract the fractional bits kept after alignment |
| Align | `truncBits`, `PreparedBlock.alignedBits` | Truncate each term's magnitude onto the common grid, keeping its sign |
| Accumulate | `PreparedBlock.accumulator` | Sum the retained aligned bits exactly |
| Normalize and round | `evalPrepared`, `round32 .truncate` | Normalize the exact accumulator and truncate it to finite FP32 |
| Explain loss | `alignmentResiduals`, `BlockTrace.residual` | Account for alignment loss and final-rounding loss |

Start with [Block.lean](../../TensorCore/TC/Block.lean), then follow [StageResiduals.lean](../../TensorCore/TC/StageResiduals.lean) and [ErrorBounds.lean](../../TensorCore/TC/ErrorBounds.lean). The [independent specification](../../TensorCore/TC/Specification/Defs.lean) uses separate mathematical definitions; its bridge proves equality of encoded results.

The exponent of a product kept in denormalized form (its unnormalized exponent, the sum of the input exponents) matters even when two factorizations have the same product value. Normalizing the exact products instead can change the alignment grid and the answer. Zero terms do not choose the largest exponent; nonzero subnormal inputs keep their format's subnormal exponent.

For the FP32 output format, alignment keeps `F = 23 + p` fractional bits. The selected variants are:

| Variant | FMA size K | Extra alignment bits p | Minimum alignment exponent |
| --- | ---: | ---: | ---: |
| V100 FP16 | 4 | 0 | none |
| A100 FP16 / BF16 | 8 | 1 | -132 |
| H100 FP16 / BF16 | 16 | 2 | -133 |
| A100 TF32 | 4 | 1 | -132 |
| H100 TF32 WMMA | 4 | 2 | -133 |
| H100 TF32 MMA | 8 | 2 | -133 |

The generic model constructors also permit other FMA sizes, numbers of extra alignment bits, and minimum alignment exponents. The model contract states its width, range, and format premises explicitly; choosing a parameter does not establish physical GPU correspondence.

## Read the contracts

```lean
import TensorCore.TC

open TensorCore

#check evalBlock_success_iff
#check model_contract
#check evalBlock_machinePrefix
#check evalBlock_error_bound
#check IndependentSpec.supported_eq_spec
```

`evalBlock_success_iff` characterizes the accepted input domain. `model_contract` states arithmetic and accumulator-width guarantees under explicit hypotheses. `evalBlock_machinePrefix` relates fixed-width accumulation to exact accumulation when the capacity assumptions hold. `evalBlock_error_bound` accounts for alignment loss and final rounding to FP32 loss. For every encoded input of a supported variant, `supported_eq_spec` proves that the evaluator and independent specification agree on the output or rejection.

The finite model rejects nonfinite operands, wrong numbers of products, and exact accumulators larger in magnitude than `maxFinite32`. Exact zero is canonicalized to +0; negative nonzero underflow may produce -0. The `tc_features` interface accepts TF32 register words with thirteen zero low bits; the paper EFT interface accepts packed 19-bit TF32 words.

[CanonicalInvocation.lean](../../examples/CanonicalInvocation.lean) combines a concrete Hopper calculation with a theorem relating fixed-width and exact accumulation. Hardware checks compare the software model's outputs with recorded GPU measurements.

Next: [execute non-monotonicity](03-non-monotonicity.md).
