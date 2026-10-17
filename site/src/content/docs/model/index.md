---
title: The model at a glance
description: How the Tensor Core model turns encoded Tensor Core inputs into an FP32 output word in Lean, end to end.
---

This section explains how Tensor Core arithmetic is represented in Lean. It
covers the data types, every stage of `evalBlock`, the numerical features of
each GPU variant, and how the model is tied to an independent specification and to
GPU measurements.

## The hardware behavior being modeled

One Tensor Core *block FMA* computes

```text
D = C + a₁·b₁ + a₂·b₂ + … + a_K·b_K
```

where `aᵢ, bᵢ` are FP16, BF16, or TF32 words, `C` is an FP32 word, `D` is an
FP32 word, and the FMA size `K` (4, 8, or 16) depends on the GPU and the input format.
Khattak and Mikaitis (*[Accurate Models of NVIDIA Tensor
Cores](https://arxiv.org/html/2512.07004v4)*) found that NVIDIA hardware does **not** round this sum
once, the way a fused dot product would. It does the following:

1. Forms each product **exactly**, without normalizing the significand.
2. Finds the **largest exponent** among the nonzero terms (including `C`),
   raised to the **minimum alignment exponent** where the architecture has one.
3. **Aligns** every term to a fixed-point grid `F` bits below that exponent,
   and **truncates** any bits below the grid.
4. **Adds** the aligned bits exactly, in a single multi-term addition.
5. **Normalizes** the sum to FP32 and **truncates** it: bits beyond FP32's 24
   significant bits are dropped.

The Lean model implements these five steps directly.

## The pipeline in Lean

<div class="pipeline">
  <a href="/HardwarePrimitives/model/formats/"><span class="n">01 · prepare</span><span class="t">Decode</span><span class="d"><code>BlockInput p</code> → <code>PreparedBlock</code></span></a>
  <a href="/HardwarePrimitives/model/products/"><span class="n">02 · denormalizedMul</span><span class="t">Multiply</span><span class="d"><code>Decoded × Decoded</code> → <code>DenormalizedProduct</code></span></a>
  <a href="/HardwarePrimitives/model/alignment/"><span class="n">03 · alignExp, truncBits</span><span class="t">Align</span><span class="d">grid <code>2^(η − F)</code>, truncate</span></a>
  <a href="/HardwarePrimitives/model/accumulation/"><span class="n">04 · accumulator</span><span class="t">Accumulate</span><span class="d">exact <code>Σ bits · 2^(η−F)</code></span></a>
  <a href="/HardwarePrimitives/model/normalization/"><span class="n">05 · round32</span><span class="t">Normalize &amp; round</span><span class="d">truncate → <code>F32</code></span></a>
</div>

The whole model is about 120 lines, in
[`TensorCore/TC/Block.lean`](https://github.com/pauljiang03/HardwarePrimitives/blob/main/TensorCore/TC/Block.lean).
These are its definitions, unchanged apart from omitted comments:

```lean
structure Model where
  input : Format                -- input format: fp16, bf16, tf19 (packed TF32), e5m2, e4m3x
  nfma : ℕ                      -- K, the FMA size N_FMA
  alignMantissaBits : ℤ         -- F = 23 + p, mantissa bits kept after alignment
  eAlignMin : Option ℤ          -- the minimum alignment exponent, if any
  outputMantissaBits : ℕ := 23  -- mantissa bits of the block output

structure BlockInput (p : Model) where
  products : List (p.Word × p.Word)   -- encoded (aᵢ, bᵢ) pairs
  c : F32                             -- encoded FP32 accumulator input

def PreparedBlock.terms (b : PreparedBlock) : List DenormalizedProduct :=
  ⟨b.c.significand, b.c.exponent, b.c.mantissaBits⟩ ::
    b.products.map fun (a, b) => denormalizedMul a b

def PreparedBlock.alignExp (b : PreparedBlock) : Option ℤ :=
  b.model.applyEAlignMin (maxTermExp b.terms)

def PreparedBlock.alignGridExponent (b : PreparedBlock) : ℤ :=
  b.alignExp.getD 0 - b.model.alignMantissaBits

def PreparedBlock.alignedBits (b : PreparedBlock) : List ℤ :=
  b.terms.map fun t => truncBits t.value b.alignGridExponent

def PreparedBlock.accumulator (b : PreparedBlock) : ℚ :=
  (sumZ b.alignedBits : ℚ) * pow2 b.alignGridExponent

def evalPrepared (b : PreparedBlock) : Except ModelError BlockTrace :=
  match round32 .truncate b.accumulator with
  | none => .error .accumulatorOutOfRange
  | some bits => match finite32 (truncateMantissa32 b.model.outputMantissaBits bits) with
    | none => .error .nonfiniteOutput
    | some d => .ok ⟨b, d⟩

def evalBlock {p : Model} (x : BlockInput p) : Except ModelError BlockTrace :=
  if x.products.length != p.nfma then .error .wrongProductCount
  else match prepare x with
    | none => .error .nonfiniteInput
    | some b => evalPrepared b
```

### Names used in the code

| Lean name | Meaning | In *Accurate Models* / its MATLAB code |
| --- | --- | --- |
| `significand` | The significand bits, hidden bit included, with the sign | significand (`a_sig`, `prod_sig`) |
| `exponent` | Exponent as the hardware sees it. For an input, its unbiased exponent (minimum normal exponent for subnormals). For a product, the sum of the input exponents: the product stays in denormalized form. | "sum of exponents"; products "remain denormalised" (`prod_exp`) |
| `mantissaBits` | Mantissa width: how many low bits of the significand lie after the binary point. For a format or an input value, the stored mantissa width (10 for FP16). For a product, the sum of both inputs' widths (20 for FP16 × FP16). value = `significand · 2^(exponent − mantissaBits)` | mantissa bits (`manBits`) |
| `DenormalizedProduct`, `denormalizedMul` | An exact product kept in that denormalized form | `prod_sig`, `prod_exp` with `denorm_prd` |
| `alignExp` (η) | Alignment exponent: largest `exponent` of a nonzero term, raised to the minimum alignment exponent | maximum exponent, "capped from below" by `e_align^min` |
| `alignMantissaBits` (F) | Mantissa bits each term keeps after alignment, counted below the alignment exponent: `23 + p` | 23 + `n_eab` |
| `alignGridExponent` | Exponent of the alignment grid step, `η − F` | |
| `outputUlpExponent` | Exponent of one unit in the last place of the FP32 output | |
| `outputMantissaBits` | Mantissa bits of the block output: 23 (binary32), or 13 on the FP8 block FMAs of Ada and Hopper | `NoManBitsOut` |

Three design choices run through the model:

- **Exact arithmetic everywhere.** Values are `ℤ` and `ℚ`. Neither Lean's
  `Float` nor a floating-point library is used. The only lossy steps are the
  two the hardware performs: the alignment truncation (`truncBits`) and the
  final rounding (`round32 .truncate`, then `truncateMantissa32` to the block
  output's mantissa bits, which changes nothing for a binary32 output).
- **Bits in, bits out.** Inputs are `BitVec` words and the output is an
  `F32 = BitVec 32`. Theorems can therefore state facts about exact bit
  patterns, including signed zero.
- **Failure is explicit.** `evalBlock` returns `Except ModelError BlockTrace`.
  It rejects inputs with the wrong number of products, NaN or infinity
  operands, and sums that overflow FP32. The proved theorem
  [`evalBlock_success_iff`](https://github.com/pauljiang03/HardwarePrimitives/blob/main/TensorCore/TC/AcceptedDomain.lean#L37)
  gives the exact accepted domain, so no input is rejected silently.

## A worked trace

Here is the V100 model (`K = 4`, `F = 23`, no minimum alignment exponent) with four FP16 products
`2^-12 × 2^-12`, run for two values of `C`:

| Stage | `C = 1.0` (`0x3f800000`) | `C = 1 − 2^-24` (`0x3f7fffff`) |
| --- | --- | --- |
| Decode `C` | `1.000…0` (24 bits) × `2^0` | `1.111…1` (24 ones) × `2^-1` |
| Each product | value `2^-24`, exponent `−24` | same |
| `η` = largest exponent | `0` | `−1` |
| Grid `2^(η − F)` | `2^-23` | `2^-24` |
| Bits of `C` kept | all 24 | all 24 |
| Each product's single bit at `2^-24` | below the grid: dropped | on the grid: kept |
| Accumulator | `1` | `1 + 3·2^-24` |
| Truncate to FP32 | `1.0` | `1 + 2^-23` |

The smaller `C` moves the grid one bit lower, so the four products survive
alignment and the output **increases**. This is the
[non-monotonicity](/HardwarePrimitives/properties/non-monotonicity/) that the library
proves in general. Both rows can be checked in Lean:

```lean
import TensorCore.TC

open TensorCore

def before : BlockInput v100F16F32 := ⟨List.replicate 4 (0x0c00, 0x0c00), 0x3f800000⟩
def after  : BlockInput v100F16F32 := ⟨List.replicate 4 (0x0c00, 0x0c00), 0x3f7fffff⟩

example : ((evalBlock before).toOption.map fun t => t.output.bits) = some 0x3f800000 ∧
          ((evalBlock after).toOption.map  fun t => t.output.bits) = some 0x3f800001 := by
  decide +kernel
```

## Reading on

Each stage has its own page:

1. [Formats and decoding](/HardwarePrimitives/model/formats/): IEEE classification, exponents, subnormals, TF32 packing.
2. [Exact products in denormalized form](/HardwarePrimitives/model/products/): why products are not normalized.
3. [Alignment](/HardwarePrimitives/model/alignment/): `η`, the minimum alignment exponent, the grid, and truncation.
4. [Accumulation](/HardwarePrimitives/model/accumulation/): the exact sum and fixed-width registers.
5. [Normalization and final rounding](/HardwarePrimitives/model/normalization/): `round32`, range, signed zero.
6. [Variants and their numerical features](/HardwarePrimitives/model/variants/): the models of V100 to B200, FP8 included, and the general `InvocationSpec`.
7. [Instructions and chaining](/HardwarePrimitives/model/instructions/): instructions made of several block FMAs, and passing `C` between them.
8. [Independent specification](/HardwarePrimitives/model/specification/): `IndependentSpec` (a transcription of *Accurate Models*) and the equality proof.
9. [Bitvector datapath](/HardwarePrimitives/model/datapath/): the model in fixed-width registers, proved to give the same output word.
10. [Hardware validation](/HardwarePrimitives/model/validation/): replay of GPU measurements.

The AMD matrix cores have a model of their own, with round-to-nearest output
and late addition of `c`: see [the AMD model at a glance](/HardwarePrimitives/amd/).
