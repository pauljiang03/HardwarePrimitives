# Tensor-core theory reference

The main [README](../README.md) explains the two implementations and validation commands.
The [guide](README.md), [What is proven](../TensorCore/THEOREMS.md), and [test walkthrough](../tests/README.md) provide the reading path.

## Executable interfaces

```sh
./tc doctor --json
./tc build
./tc audit
./tc check
./tc trace 3e00 3d00 3e00 3d00 3e00 3d00 3e00 3d00 3f7fffff
./tc eft data/examples/eft.txt
```

`tc_trace` accepts eight FP16 hexadecimal words and one FP32 accumulator word, without `0x` prefixes. `--file FILE` reads one block per line; `--round-file FILE` reads rational numerator/denominator pairs.

`tc_features --file FILE` reads commands such as `canonical K PADDING EALIGNMIN a0 b0 ... c`, `bf16 K PADDING EALIGNMIN ...`, `tf32 K PADDING EALIGNMIN ...`, `block MODEL ...`, `decode FORMAT WORD`, and `round FORMAT NUM DEN`. The replay commands `dot MODEL a0 b0 ... c` and `dot-then-add MODEL ...` evaluate a named model (`ada-f16`, `hopper-bf16`, `blackwell-tf32-wmma`, `ada-e4m3`, `hopper-e5m2`, `blackwell-e4m3`, …) on any number of products by recursive summation of block FMAs, the second adding `c` after them in binary32 with round-to-nearest-even; `chain DESCRIPTOR ...` does the same with an invocation descriptor (`ada-e4m3`, `blackwell-e5m2-then-add`, …). `model-dot FORMAT K F EALIGNMIN M c a0 b0 ...` runs `Model.dot` on a model given by its parameters (input format `fp16`, `bf16`, `tf32`, `e4m3` or `e5m2`, FMA size, mantissa bits after alignment, minimum alignment exponent or `none`, block-output mantissa bits), and `mma-sync e4m3|e5m2 k c a0 b0 ...` runs the FP8 `mma.sync` model of H100, H200 and B200 (`mmaSyncFP8Dot`) with instructions of `k` products. FP8 words are 8-bit encodings; `decode` also accepts `e4m3` and `e5m2`. K is the FMA size, PADDING the number of padding bits, and EALIGNMIN the minimum alignment exponent (an integer or `none`). Words are unsigned decimal encodings. Feature TF32 inputs are 32-bit register words with thirteen zero low bits.

`tc_eft_reference FILE` reads `block FORMAT K PADDING EALIGNMIN a0 b0 ... c D`, `round NUM DEN`, and `family p K j`. FORMAT is `fp16`, `bf16`, or packed 19-bit `tf32`; EALIGNMIN is an integer or `none`.

`tc_bounded_eft FILE` reads `block VARIANT a0 b0 ... c D` or `round SIGNED_COEFFICIENT`. The variants are `v100-fp16`, `a100-fp16`, `h100-fp16`, `a100-bf16`, `h100-bf16`, `a100-tf32`, `h100-tf32-wmma`, and `h100-tf32-mma`. The integer rounding command uses the bounded backend's `2^-272` grid.

`tc_lean_eft_check` reads JSON Lines on stdin. To compare the bounded scalar fold with native Lean FP32 addition for accumulator `0.0` and a single term `1.0`, send this encoded request:

```json
{"acc":0,"terms":[1065353216]}
```

Both returned results decode to FP32 `1.0`. A block request has a `profile` field naming the variant, operand arrays `a` and `b`, and encoded `c` and `D`. It compares both complete bounded EFT executions.

## Proof contracts

[What is proven](../TensorCore/THEOREMS.md) lists the public results and their premises.

Identifiers beginning `inputGrid_` concern the TC-EFT paper's input-based precondition (17), a sufficient condition for the scalar predicate. The scalar predicate is an executable sufficient condition that uses the lowest bit actually set in the low parts as its grid. Chosen-grid theorems also permit other valid common grids.

The model rejects nonfinite operands, wrong product counts, and exact accumulators whose magnitude exceeds the maximum finite FP32 value. Exact arithmetic zero is +0; negative nonzero underflow retains its sign. EFT extraction accepts any finite D, whether or not it is the TC model's output. The bounded backend returns the same bits as the reference algorithm; its fallback branch tag may differ.

## Source layout

| Directory | Contents |
| --- | --- |
| `TensorCore/Numerics` | Bit encodings, exact arithmetic, finite rounding, scalar sums |
| `TensorCore/TC` | Base TC model, the models of the variants, independent specification, width/refinement, error and non-monotonicity theory |
| `TensorCore/EFT` | Extraction, scalar preconditions, and reference EFT |
| `TensorCore/Kernels/Datapath` | Bitvector Tensor Core datapath and its equality with the model |
| `TensorCore/Kernels/EFT` | Bounded workspace operations and EFT refinement |
| `tests/TensorCoreTests` | Separate regression modules and trust checks |
| `TensorCore/Scalar` | Scalar proof dependencies for native EFT tests |
| `Main`, `examples` | Compiled adapters and executable Lean tests |
| `scripts` | Trust audits and model/EFT validation |
| `vendor`, `data` | Pinned paper oracles, recorded hardware inputs/outputs, and regression cases |
| `floatlib-port` | Independent FloatLib model, proofs, and associated tests |

[What is proven](../TensorCore/THEOREMS.md) · [Trust and style](style.md)
