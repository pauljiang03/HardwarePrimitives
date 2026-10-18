---
title: 6. Variants and their numerical features
description: How the Tensor Core variants of V100 to B200, FP8 included, are parameterized, and the general InvocationSpec interface.
---

The pipeline is the same on every GPU. Architectures differ only in a few
numerical features, and a `Model` collects them:

```lean
structure Model where
  input : Format                -- input format: FP16, BF16, tf19, e5m2, or e4m3x
  nfma : ℕ                      -- K, the FMA size N_FMA
  alignMantissaBits : ℤ         -- F = 23 + p
  eAlignMin : Option ℤ          -- the minimum alignment exponent e_align^min
  outputMantissaBits : ℕ := 23  -- mantissa bits of the block output (23: FP32)
```

## The supported variants

All of them have FP32 `C` and FP32 output. The parameters follow Table 3 of
*Accurate Models* (Khattak and Mikaitis). These eight parameter sets are also
those of the newer GPUs: Ada (RTX 1000 Ada, L40S) has A100's FP16, BF16 and
TF32 features, and H200 and B200 have H100's.

| Variant | Lean model | Input | K (N_FMA) | Padding bits p (F = 23 + p) | e_align^min |
| --- | --- | --- | ---: | ---: | ---: |
| V100 FP16 | `v100F16F32` | FP16 | 4 | 0 | none |
| A100 FP16 | `ampereF16F32` | FP16 | 8 | 1 | −132 |
| A100 BF16 | `a100BF16F32` | BF16 | 8 | 1 | −132 |
| A100 TF32 | `a100TF32F32` | TF32 | 4 | 1 | −132 |
| H100 FP16 | `hopperF16F32` | FP16 | 16 | 2 | −133 |
| H100 BF16 | `hopperBF16F32` | BF16 | 16 | 2 | −133 |
| H100 TF32 (WMMA) | `hopperTF32WmmaF32` | TF32 | 4 | 2 | −133 |
| H100 TF32 (MMA) | `hopperTF32MmaF32` | TF32 | 8 | 2 | −133 |

| GPU | FP16 | BF16 | TF32 |
| --- | --- | --- | --- |
| Ada, L40S | `adaF16F32` = `ampereF16F32` | `adaBF16F32` = `a100BF16F32` | `adaTF32F32` = `a100TF32F32` |
| H200 | `hopperF16F32` | `hopperBF16F32` | `hopperTF32WmmaF32`, `hopperTF32MmaF32` |
| B200 | `blackwellF16F32` = `hopperF16F32` | `blackwellBF16F32` = `hopperBF16F32` | `blackwellTF32WmmaF32`, `blackwellTF32MmaF32` (= H100's) |

They are built from generic constructors, for example:

```lean
def fp16Fp32Model (K padding : ℕ) (eAlignMin : Option ℤ := none) : Model :=
  ⟨fp16, K, (23 + padding : ℕ), eAlignMin, 23⟩

def ampereF16F32 : Model := fp16Fp32Model 8 1 (some (-132))
def hopperF16F32 : Model := fp16Fp32Model 16 2 (some (-133))
```

Most theorems are stated for **arbitrary** `K`, `p`, and minimum alignment
exponent, and the named models are instances. The error bound and the
independent specification also hold for every block-output width
([`evalBlock_error_bound_any`](https://github.com/pauljiang03/HardwarePrimitives/blob/main/tensor-core/TensorCore/TC/OutputWidth.lean#L405), [`IndependentSpec.evalBlock_eq_specM`](https://github.com/pauljiang03/HardwarePrimitives/blob/main/tensor-core/TensorCore/TC/Specification/OutputWidth.lean#L103)); the
results that need an FP32 block output (block contracts, exact alignment,
non-monotonicity) state it as a hypothesis, `23 ≤ p.outputMantissaBits`. Choosing parameters does not by itself establish that
a GPU behaves that way. That link comes from the
[hardware replay](/HardwarePrimitives/tensor-core/validation/).

The independent specification transcribes the same eight parameter sets on
its own, as `IndependentSpec.parameters`. `supported_parameters` checks with `rfl`
that the two transcriptions match.

## FP8 variants

*Accurate Models* (Table 3) characterizes the FP8 block FMAs of three
architectures, for E4M3 and E5M2 inputs with FP32 `C` and output. All three
truncate, and Table 3 lists no minimum alignment exponent for them:

| GPU | Instruction | Lean models | K (N_FMA) | Mantissa bits after alignment (F) | Block output |
| --- | --- | --- | ---: | ---: | --- |
| Ada, L40S | `mma.sync` (QMMA) | `adaE4M3F32`, `adaE5M2F32` | 16 | 13, ten fewer than FP32 | truncated to a 13-bit mantissa |
| H100, H200 | `wgmma` (QGMMA) | `hopperE4M3F32`, `hopperE5M2F32` | 32 | 13, ten fewer than FP32 | truncated to a 13-bit mantissa |
| B200 | `tcgen05.mma` (UTCQMMA) | `blackwellE4M3F32`, `blackwellE5M2F32` | 32 | 25: 23 plus 2 padding bits | FP32 |
| RTX PRO 6000 | `mma.sync` (QMMA) | `rtxPro6000E4M3F32`, `rtxPro6000E5M2F32` (= B200's) | 32 | 25: 23 plus 2 padding bits | FP32 |

The evidence differs by row. Ada's and L40S's recorded FP8 outputs, from
`mma.sync` with `C`, agree with Ada's block FMA. For Hopper's and B200's block
FMAs with `C` accumulated inside `wgmma` or `tcgen05.mma` there is no recorded
data; the recorded H100 and H200 rows of the toolbox's commit 79143bd agree
with Hopper's block FMA from `C = 0`, and the models agree with the MMA-Sim
simulator on 581,052 cases with a nonzero `C`. The RTX PRO 6000 row rests on
*Accurate Models* and MMA-Sim alone ([hardware validation](/HardwarePrimitives/tensor-core/validation/)).

On Ada and Hopper the block output is truncated to a 13-bit mantissa, as the
*Accurate Models* toolbox's `GEMM.m` sets: the model truncates the FP32
output further, clearing its ten low mantissa bits ([`truncateMantissa32`](https://github.com/pauljiang03/HardwarePrimitives/blob/main/tensor-core/TensorCore/TC/Defs.lean#L26),
[`fp8_output_thirteen_bits`](https://github.com/pauljiang03/HardwarePrimitives/blob/main/tensor-core/TensorCore/TC/GPUs.lean#L73)). Every other variant keeps the default 23.

The two formats decode differently at the top of their range:

- **E5M2** follows IEEE 754: exponent `11111` is infinity (`0x7c`, `0xfc`)
  or NaN, and the largest value is 57344.
- **E4M3** has no infinities: exponent `1111` holds finite values up to 448,
  and its only NaNs are `S.1111.111` (`0x7f`, `0xff`).

The model decodes operands with the IEEE rule, so it takes E4M3 values in a
9-bit layout, `e4m3x`, with one more exponent bit and E4M3's bias. `widenE4M3`
maps each E4M3 word to it, and [`e4m3_decode_widen`](https://github.com/pauljiang03/HardwarePrimitives/blob/main/tensor-core/TensorCore/Numerics/FP8.lean#L31) proves the two decodings
equal on all 256 words, much as `tf32Unpack` maps TF32 register words to the
packed `tf19` layout. The FP8 descriptors decode E4M3 words directly.

The toolbox keeps its default minimum alignment exponents (−132 and −133) for
FP8. They are inactive: with FP8 products and an FP32 `C`, no nonzero term
has an exponent below −126, and [`fp8_eAlignMin_inactive`](https://github.com/pauljiang03/HardwarePrimitives/blob/main/tensor-core/TensorCore/TC/GPUs.lean#L169) proves that either
choice gives the same output word, or the same error, on every input.

Longer inner products use [`Model.dot`](https://github.com/pauljiang03/HardwarePrimitives/blob/main/tensor-core/TensorCore/TC/GPUs.lean#L215), which pads the products with zero pairs
to a multiple of N_FMA and chains the block FMAs through `C`, as the toolbox's
`GEMM.m` does: a row of 32 FP8 products is two block FMAs on Ada and one on
Hopper and Blackwell. [`Model.dotThenAdd`](https://github.com/pauljiang03/HardwarePrimitives/blob/main/tensor-core/TensorCore/TC/GPUs.lean#L253) instead runs the block FMAs from
`C = 0` and adds `C` afterwards in FP32 with round-to-nearest-even. On the
recorded B200 FP8 rows it agrees with the `mma.sync` model below.

### FP8 through `mma.sync`

On H100, H200 and B200 an FP8 `mma.sync` does not run on an FP8 block FMA.
*Accurate Models* (Sections 4.1.6 to 4.1.8) reports that the operands are
converted to FP16 and the instruction runs as FP16 `HMMA.16816` instructions,
with the products split by alternating pairs of positions and `C` added after
the products. [`mmaSyncFP8`](https://github.com/pauljiang03/HardwarePrimitives/blob/main/tensor-core/TensorCore/TC/MmaSyncFP8.lean#L31) models one instruction:

1. every FP8 operand is converted to FP16, exactly ([`e4m3ToF16_exact`](https://github.com/pauljiang03/HardwarePrimitives/blob/main/tensor-core/TensorCore/Numerics/FP8.lean#L91),
   [`e5m2ToF16_exact`](https://github.com/pauljiang03/HardwarePrimitives/blob/main/tensor-core/TensorCore/Numerics/FP8.lean#L106));
2. the products at positions `k mod 4 ∈ {0, 1}` go through one Hopper FP16
   block FMA (`N_FMA = 16`, `F = 25`, `e_align^min = −133`) from `+0`;
3. the products at positions `k mod 4 ∈ {2, 3}` go through a second one, whose
   accumulator input is the first block's output;
4. `C` is added to the second block's output in FP32 with
   round-to-nearest-even.

[`mmaSyncFP8Dot`](https://github.com/pauljiang03/HardwarePrimitives/blob/main/tensor-core/TensorCore/TC/MmaSyncFP8.lean#L39) chains instructions of `k = 32` (or `k = 16`) products
through `C`. The paper does not state that the second block takes the first
block's output, nor the order of the groups; kernel-checked consequences pin
them down:

- the paper's interleaving experiment (E5M2, `1`, `2^-24` and one more
  `2^-24` at position `k`) gives `1 + 2^-23` exactly when `k mod 4 < 2`
  ([`interleave_test_e5m2`](https://github.com/pauljiang03/HardwarePrimitives/blob/main/tensor-core/TensorCore/TC/MmaSyncFP8.lean#L60)); the order with the second group first, and a
  single 32-product block, give `1 + 2^-23` at every position
  ([`interleave_test_reversed`](https://github.com/pauljiang03/HardwarePrimitives/blob/main/tensor-core/TensorCore/TC/MmaSyncFP8.lean#L74), [`interleave_test_single_block`](https://github.com/pauljiang03/HardwarePrimitives/blob/main/tensor-core/TensorCore/TC/MmaSyncFP8.lean#L79));
- `C` added after the products is rounded to nearest, not truncated: one
  input separates the path from a block FMA that holds `C` ([`late_c_witness`](https://github.com/pauljiang03/HardwarePrimitives/blob/main/tensor-core/TensorCore/TC/MmaSyncFP8.lean#L87));
- on a recorded B200 E5M2 row the model returns the recorded word, while two
  independent FP16 blocks added in FP32 return the next word
  ([`separate_groups_excluded`](https://github.com/pauljiang03/HardwarePrimitives/blob/main/tensor-core/TensorCore/TC/MmaSyncFP8.lean#L111)).

The recorded B200 FP8 rows and the H100 and H200 FP8 outputs of the toolbox's
release v0.1 agree with this model bit for bit (30,000 rows with `C`); the
toolbox's FP8 harness, the same file in both, issues `mma.sync`. See [hardware
validation](/HardwarePrimitives/tensor-core/validation/). The RTX PRO 6000 runs FP8 `mma.sync`
as `QMMA.16832` on B200's FP8 block FMA, with `C` inside.

Proven about this model: an error bound
([error bounds](/HardwarePrimitives/tensor-core/properties/error-bounds/#fp8-through-mmasync)),
its correction by TC-EFT ([TC-EFT](/HardwarePrimitives/tensor-core/properties/eft/#fp8-through-mmasync)),
equality with an independent specification ([`TensorCore.IndependentSpec.mmaSyncFP8_eq_spec`](https://github.com/pauljiang03/HardwarePrimitives/blob/main/tensor-core/TensorCore/TC/Specification/MmaSyncFP8Equivalence.lean#L98))
and with a bitvector datapath ([`TensorCore.Datapath.mmaSyncFP8_eq`](https://github.com/pauljiang03/HardwarePrimitives/blob/main/tensor-core/TensorCore/Kernels/Datapath/MmaSyncFP8.lean#L24)).

Not modeled: FP4 and FP6, and the Blackwell instructions *Accurate Models*
does not characterize.

## Beyond one block: `InvocationSpec`

[`InvocationSpec`](https://github.com/pauljiang03/HardwarePrimitives/blob/main/tensor-core/TensorCore/TC/Invocation.lean#L21)
is a more general description of a Tensor Core invocation. Models embed
into it, and it can express variations the basic model cannot:

```lean
inductive CPlacement where
  | early                                   -- early accumulation: C is aligned with the products
  | late (stages : List RoundingStage)     -- late accumulation: products rounded first, then C added exactly

inductive AccumulationKind where
  | aligned (alignMantissaBits : ℕ) (eAlignMin : Option ℤ) (cPlacement : CPlacement)
  | fused                                          -- exact single-product FMA (e.g. FP64 DMMA)

structure InvocationSpec where
  input : OperandEncoding        -- includes TF32's 32-bit register words
  cFormat : Format
  nfma : ℕ
  accumulation : AccumulationKind
  intermediate : List RoundingStage := []
  output : RoundingStage       -- output format and rounding direction
```

- `Model.toInvocation` embeds a model as an aligned invocation with early
  accumulation of `C` and FP32 truncation, and the compatibility theorems show the
  results are equal.
- `fp64Fma mode` models an FP64 DMMA as a **fused** operation: one
  correctly rounded result in any of four directions (`fp64Fma_correct`).
  `fp64FmaBits` gives its output with the IEEE 754 sign for an exactly
  zero result.
- Output stages may use any well-formed format and rounding direction. Each
  is proven correct (`evalInvocation_output_nearestEven`,
  `..._truncate`, `..._towardNegative`, `..._towardPositive`).

The headline theorems concern the eight aligned FP32-output variants of the
first table, and so Ada, H200 and B200; the hardware validation covers those
and the FP8 variants. The FP8 variants are also invocation descriptors
(`adaE4M3Invocation`, …), with the 13-bit block output as a truncation stage
to a format with 13 mantissa bits and the B200 recording convention as a late
accumulator input (`blackwellE4M3ThenAddInvocation`). The general interface is
there for experimenting with other configurations.
