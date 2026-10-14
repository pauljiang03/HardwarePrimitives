# The tensor-core block model

The model evaluates one block FMA: K exact products plus an FP32 accumulator input C, added in a single multi-term addition. The model of each named variant specifies its numerical features: the FMA size K, the number p of padding bits (`n_eab` in *Accurate Models*), an optional minimum alignment exponent, the input format (FP16, BF16, packed TF32, E5M2, or E4M3 in a 9-bit layout), and the mantissa bits of the block output. Every model in this chapter has FP32 C and output; the block output keeps all 23 mantissa bits except on the FP8 block FMAs of Ada and Hopper, which truncate it to a 13-bit mantissa.

## Follow one block

| Stage | Executable definitions | Mathematical role |
| --- | --- | --- |
| Decode | `prepare`, `prepareProducts`, `Model.decode` | Decode finite words and preserve exponent/mantissa metadata |
| Multiply | `denormalizedMul`, `PreparedBlock.terms` | Form exact products and keep them in denormalized form, with the sum of the input exponents |
| Select grid | `PreparedBlock.alignExp`, `alignGridExponent` | Take the largest exponent of a nonzero term, raise it to the minimum alignment exponent, and subtract the mantissa bits kept after alignment |
| Align | `truncBits`, `PreparedBlock.alignedBits` | Truncate each term's magnitude onto the common grid, keeping its sign |
| Accumulate | `PreparedBlock.accumulator` | Sum the retained aligned bits exactly |
| Normalize and round | `evalPrepared`, `round32 .truncate`, `truncateMantissa32` | Normalize the exact accumulator, truncate it to finite FP32, then to the block output's mantissa bits |
| Explain loss | `alignmentResiduals`, `BlockTrace.residual` | Account for alignment loss and final-rounding loss |

Start with [Block.lean](../../TensorCore/TC/Block.lean), then follow [StageResiduals.lean](../../TensorCore/TC/StageResiduals.lean) and [ErrorBounds.lean](../../TensorCore/TC/ErrorBounds.lean). The [independent specification](../../TensorCore/TC/Specification/Defs.lean) uses separate mathematical definitions; its bridge proves equality of encoded results.

The exponent of a product kept in denormalized form (its exponent, the sum of the input exponents) matters even when two factorizations have the same product value. Normalizing the exact products instead can change the alignment grid and the answer. Zero terms do not choose the largest exponent; nonzero subnormal inputs keep their format's subnormal exponent.

For the FP32 output format, alignment keeps `F = 23 + p` mantissa bits. The selected variants are:

| Variant | FMA size K | Padding bits p | Minimum alignment exponent |
| --- | ---: | ---: | ---: |
| V100 FP16 | 4 | 0 | none |
| A100 FP16 / BF16 | 8 | 1 | -132 |
| H100 FP16 / BF16 | 16 | 2 | -133 |
| A100 TF32 | 4 | 1 | -132 |
| H100 TF32 WMMA | 4 | 2 | -133 |
| H100 TF32 MMA | 8 | 2 | -133 |

Ada (RTX 1000 Ada, L40S) uses the A100 models (`adaF16F32` is `ampereF16F32`, and so on), H200 the H100 models, and B200 the H100 models (`blackwellF16F32`, …), as in *Accurate Models*, Table 3. Its FP8 rows, in [GPUs.lean](../../TensorCore/TC/GPUs.lean), have no minimum alignment exponent:

| FP8 variant (E4M3, E5M2) | FMA size K | Mantissa bits after alignment F | Block output mantissa bits |
| --- | ---: | ---: | ---: |
| Ada, L40S (`mma.sync`) | 16 | 13, ten fewer than FP32 | 13 |
| H100, H200 (`wgmma`) | 32 | 13, ten fewer than FP32 | 13 |
| B200 (`tcgen05.mma`) | 32 | 25, with 2 padding bits | 23 |

E4M3 is the variant without infinities (largest value 448, NaN only at `S.1111.111`); the model takes it in the `e4m3x` layout, whose decoding `e4m3_decode_widen` proves identical on all 256 words. `Model.dot` chains block FMAs over longer inner products, and `Model.dotThenAdd` adds C after them in binary32 with round-to-nearest-even, as the recorded B200 FP8 outputs do.

The generic model constructors also permit other FMA sizes, numbers of padding bits, and minimum alignment exponents. The model contract states its width, range, and format premises explicitly; choosing a parameter does not establish physical GPU correspondence.

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

`evalBlock_success_iff` characterizes the accepted input domain. `model_contract` states arithmetic and accumulator-width guarantees under explicit hypotheses. `evalBlock_machinePrefix` relates fixed-width accumulation to exact accumulation when the capacity assumptions hold. `evalBlock_error_bound` accounts for alignment loss and final rounding to FP32 loss, for a binary32 block output. For every encoded input of a supported variant, `supported_eq_spec` proves that the evaluator and independent specification agree on the output or rejection.

The finite model rejects nonfinite operands, wrong numbers of products, and exact accumulators larger in magnitude than `maxFinite32`. Exact zero is canonicalized to +0; negative nonzero underflow may produce -0. The `tc_features` interface accepts TF32 register words with thirteen zero low bits; the paper EFT interface accepts packed 19-bit TF32 words.

[CanonicalInvocation.lean](../../examples/CanonicalInvocation.lean) combines a concrete Hopper calculation with a theorem relating fixed-width and exact accumulation. Hardware checks compare the software model's outputs with recorded GPU measurements.

Next: [execute non-monotonicity](03-non-monotonicity.md).
