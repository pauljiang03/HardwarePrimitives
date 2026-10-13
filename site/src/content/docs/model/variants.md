---
title: 6. Variants and their numerical features
description: How the V100, A100, and H100 Tensor Core variants are parameterized, and the general InvocationSpec interface.
---

The pipeline is the same on every GPU. Architectures differ only in a few
numerical features, and a `Model` collects them:

```lean
structure Model where
  input : Format          -- input format: fp16, bf16, or tf19
  nfma : ℕ                -- K, the FMA size N_FMA
  alignFracBits : ℤ       -- F = 23 + p
  eAlignMin : Option ℤ    -- the minimum alignment exponent e_align^min
```

## The supported variants

All of them have FP32 `C` and FP32 output. The parameters follow Table 3 of
*Accurate Models* (Khattak and Mikaitis).

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

They are built from generic constructors, for example:

```lean
def fp16Fp32Model (K neab : ℕ) (eAlignMin : Option ℤ := none) : Model :=
  ⟨fp16, K, (23 + neab : ℕ), eAlignMin⟩

def ampereF16F32 : Model := fp16Fp32Model 8 1 (some (-132))
def hopperF16F32 : Model := fp16Fp32Model 16 2 (some (-133))
```

Most theorems are stated for **arbitrary** `K`, `p`, and minimum alignment
exponent, and the named models are instances. Choosing parameters does not by itself establish that
a GPU behaves that way. That link comes from the
[hardware replay](/TC-EFT/model/validation/).

The independent specification transcribes the same eight parameter sets on
its own, as `IndependentSpec.parameters`. `supported_parameters` checks with `rfl`
that the two transcriptions match.

## Beyond one block: `InvocationSpec`

[`InvocationSpec`](https://github.com/pauljiang03/TC-EFT/blob/main/TensorCore/TC/Invocation.lean#L21)
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

The headline theorems and the hardware validation concern the eight aligned
FP32-output variants in the table. The general interface is there for
experimenting with other configurations.
