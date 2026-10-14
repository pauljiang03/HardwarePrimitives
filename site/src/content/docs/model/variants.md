---
title: 6. Variants and their numerical features
description: How the Tensor Core variants of V100 to B200, FP8 included, are parameterized, and the general InvocationSpec interface.
---

The pipeline is the same on every GPU. Architectures differ only in a few
numerical features, and a `Model` collects them:

```lean
structure Model where
  input : Format          -- input format: fp16, bf16, tf19, e5m2, or e4m3x
  nfma : ℕ                -- K, the FMA size N_FMA
  alignFracBits : ℤ       -- F = 23 + p
  eAlignMin : Option ℤ    -- the minimum alignment exponent e_align^min
  outputFracBits : ℕ := 23  -- fraction bits of the block output (23: binary32)
```

## The supported variants

All of them have FP32 `C` and FP32 output. The parameters follow Table 3 of
*Accurate Models* (Khattak and Mikaitis). These eight parameter sets are also
those of the newer GPUs: Ada (RTX 1000 Ada, L40S) has A100's FP16, BF16 and
TF32 features, and H200 and B200 have H100's.

| Variant | Lean model | Input | K (N_FMA) | p = n_eab (F = 23 + p) | e_align^min |
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
def fp16Fp32Model (K neab : ℕ) (eAlignMin : Option ℤ := none) : Model :=
  ⟨fp16, K, (23 + neab : ℕ), eAlignMin, 23⟩

def ampereF16F32 : Model := fp16Fp32Model 8 1 (some (-132))
def hopperF16F32 : Model := fp16Fp32Model 16 2 (some (-133))
```

Most theorems are stated for **arbitrary** `K`, `p`, and minimum alignment
exponent, and the named models are instances. Those that need a binary32
block output state it as a hypothesis, `23 ≤ p.outputFracBits`. Choosing parameters does not by itself establish that
a GPU behaves that way. That link comes from the
[hardware replay](/MMAlgebra/model/validation/).

The independent specification transcribes the same eight parameter sets on
its own, as `IndependentSpec.parameters`. `supported_parameters` checks with `rfl`
that the two transcriptions match.

## FP8 variants

*Accurate Models* (Table 3) characterizes the FP8 block FMAs of three
architectures, for E4M3 and E5M2 inputs with FP32 `C` and output. All three
truncate, and Table 3 lists no minimum alignment exponent for them:

| GPU | Instruction | Lean models | K (N_FMA) | p (F = 23 + p) | Block output |
| --- | --- | --- | ---: | ---: | --- |
| Ada, L40S | `mma.sync` (QMMA) | `adaE4M3F32`, `adaE5M2F32` | 16 | −10 (13 fraction bits) | 13 fraction bits |
| H100, H200 | `wgmma` (QGMMA) | `hopperE4M3F32`, `hopperE5M2F32` | 32 | −10 (13 fraction bits) | 13 fraction bits |
| B200 | `tcgen05.mma` (UTCQMMA) | `blackwellE4M3F32`, `blackwellE5M2F32` | 32 | 2 (25 fraction bits) | binary32 |

On Ada and Hopper the block output keeps 13 fraction bits, as the *Accurate
Models* toolbox's `GEMM.m` sets for `p < 0`: the model truncates the binary32
output further, clearing its ten low fraction bits ([`truncateFraction32`](https://github.com/pauljiang03/MMAlgebra/blob/main/TensorCore/TC/Defs.lean#L30),
[`fp8_output_thirteen_bits`](https://github.com/pauljiang03/MMAlgebra/blob/main/TensorCore/TC/GPUs.lean#L97)). Every other variant keeps the default 23.

The two formats decode differently at the top of their range:

- **E5M2** follows IEEE 754: exponent `11111` is infinity (`0x7c`, `0xfc`)
  or NaN, and the largest value is 57344.
- **E4M3** has no infinities: exponent `1111` holds finite values up to 448,
  and its only NaNs are `S.1111.111` (`0x7f`, `0xff`).

The model decodes operands with the IEEE rule, so it takes E4M3 values in a
9-bit layout, `e4m3x`, with one more exponent bit and E4M3's bias. `widenE4M3`
maps each E4M3 word to it, and [`e4m3_decode_widen`](https://github.com/pauljiang03/MMAlgebra/blob/main/TensorCore/Numerics/FP8.lean#L43) proves the two decodings
equal on all 256 words, much as `tf32Unpack` maps TF32 register words to the
packed `tf19` layout. The FP8 descriptors decode E4M3 words directly.

The toolbox keeps its default minimum alignment exponents (−132 and −133) for
FP8. They are inactive: with FP8 products and a binary32 `C`, no nonzero term
has an exponent below −126, and [`fp8_eAlignMin_inactive`](https://github.com/pauljiang03/MMAlgebra/blob/main/TensorCore/TC/GPUs.lean#L199) proves that either
choice gives the same output word, or the same error, on every input.

Longer inner products use [`Model.dot`](https://github.com/pauljiang03/MMAlgebra/blob/main/TensorCore/TC/GPUs.lean#L248), which pads the products with zero pairs
to a multiple of N_FMA and chains the block FMAs through `C`, as the toolbox's
`GEMM.m` does: a row of 32 FP8 products is two block FMAs on Ada and one on
Hopper and Blackwell. [`Model.dotThenAdd`](https://github.com/pauljiang03/MMAlgebra/blob/main/TensorCore/TC/GPUs.lean#L288) instead runs the block FMAs from
`C = 0` and adds `C` afterwards in binary32 with round-to-nearest-even; that
is how the recorded B200 FP8 outputs add `C` (see [hardware
validation](/MMAlgebra/model/validation/)).

Not modeled: FP4 and FP6, the FP8 `mma.sync` path of H100 and H200 (FP8
converted to FP16 for HMMA, with `C` added late), and the Blackwell
instructions *Accurate Models* does not characterize.

## Beyond one block: `InvocationSpec`

[`InvocationSpec`](https://github.com/pauljiang03/MMAlgebra/blob/main/TensorCore/TC/Invocation.lean#L21)
is a more general description of a Tensor Core invocation. Models embed
into it, and it can express variations the basic model cannot:

```lean
inductive CPlacement where
  | early                                   -- early accumulation: C is aligned with the products
  | late (stages : List RoundingStage)     -- late accumulation: products rounded first, then C added exactly

inductive AccumulationKind where
  | aligned (alignFracBits : ℕ) (eAlignMin : Option ℤ) (cPlacement : CPlacement)
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
- `binary64Fma mode` models an FP64 DMMA as a **fused** operation: one
  correctly rounded result in any of four directions (`binary64Fma_correct`).
  `binary64FmaBits` gives its output with the IEEE 754 sign for an exactly
  zero result.
- Output stages may use any well-formed format and rounding direction. Each
  is proved correct (`evalInvocation_output_nearestEven`,
  `..._truncate`, `..._towardNegative`, `..._towardPositive`).

The headline theorems concern the eight aligned FP32-output variants of the
first table, and so Ada, H200 and B200; the hardware validation covers those
and the FP8 variants. The FP8 variants are also invocation descriptors
(`adaE4M3Invocation`, …), with the 13-bit block output as a truncation stage
to a format with 13 fraction bits and the B200 recording convention as a late
accumulator input (`blackwellE4M3ThenAddInvocation`). The general interface is
there for experimenting with other configurations.
