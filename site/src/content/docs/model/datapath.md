---
title: 9. Bitvector datapath
description: A second implementation of the model in fixed-width bitvector registers, and the proof that it returns the same output word as evalBlock on every input.
---

`evalBlock` works on exact integers and rationals. That makes it a clear
definition to prove things about, but it does not say how wide the hardware's
registers need to be. The bitvector datapath, `Datapath.evalBlock`,
computes the same block FMA with **bitvector operations only**, in registers
whose widths come from the model. Lean proves it returns the same FP32
word as `evalBlock`, or the same error, for **every** input on all eight
supported GPU variants.

The integer model is still the definition that all other theorems are about.
The datapath is a second implementation next to it.

## Register widths

The widths follow from the model: the 23 FP32 fractional bits, the `p` extra
alignment bits, and the FMA size `K`.

| Register | Width | Why |
| --- | --- | --- |
| Product significand | 24 bits | an 11-bit × 11-bit product is below `2^22` |
| Exponents | 9 bits | see [exponents](#exponents) below |
| Output exponent field | 8 bits | the FP32 exponent field |
| Aligned term | `F + 2 = 25 + p` bits | two integer bits (the implicit bit and a second bit for a product in denormalized form) and `F = 23 + p` fractional bits |
| Accumulator | `F + 2 + c` magnitude bits and a sign bit, two's complement | `c = ⌊log₂ K⌋ + 1` extra carry bits, so the `K + 1` terms cannot overflow |

| Variant | `F` | `K` | Accumulator |
| --- | --- | --- | --- |
| V100 FP16 | 23 | 4 | 28 bits + sign |
| A100 FP16, BF16 | 24 | 8 | 30 bits + sign |
| A100 TF32 | 24 | 4 | 29 bits + sign |
| H100 FP16, BF16 | 25 | 16 | 32 bits + sign |
| H100 TF32 (wmma) | 25 | 4 | 30 bits + sign |
| H100 TF32 (mma) | 25 | 8 | 31 bits + sign |

The **implicit bit** is the leading 1 of a significand `1.xxx`; multiplying
two implicit bits puts a 1 in the same place. The **second integer bit**
sits above it: a product of two significands below 2 can reach `11.xxx`, just
under 4, and the hardware keeps the product in denormalized form, so the carry
stays in the register. `C` and subnormal products never use the second integer
bit.

The magnitude widths for A100 and H100 FP16 are the adder widths *Accurate
Models* gives (§4.1.2 and §4.1.6): `26 + ⌈log₂ 9⌉ = 30` and `27 + 5 = 32`.
The paper keeps the sign separately; here it is the two's complement sign bit.

### Exponents

FP32 has an 8-bit exponent field, and the output word uses exactly that. The
exponents before the output need 9 bits:

- The alignment exponent can be as low as the minimum alignment exponent,
  −133 on H100, and as high
  as 127 from `C` alone. That is 261 values, more than 8 bits can hold.
- Product exponents span more: two BF16 inputs near the maximum give 254.

The datapath stores an input's exponent biased by 128, so a
product's exponent, the sum of two, is biased by 256, as is `C`'s. Every
exponent fits in 9 bits. Normalization compares exponents before it
subtracts, so no intermediate value leaves 9 bits either. *Accurate Models*
does not give the hardware's exponent register widths; 9 bits is the least
its reported ranges allow.

*Accurate Models* writes a subnormal input with its normalized exponent, so it
reports product exponents down to −266 for BF16 and −272 for TF32. The model
here writes the same subnormal with exponent −126 and no hidden bit, so the
same product has exponent −252. The values are identical; only
the bookkeeping differs.

## The stages

[`TensorCore/Kernels/Datapath/Defs.lean`](https://github.com/pauljiang03/TC-EFT/blob/main/TensorCore/Kernels/Datapath/Defs.lean)
follows the same five steps as the model:

1. **Decode.** Bit-field extraction gives the sign, the significand with its
   hidden bit, and a 9-bit biased exponent. Zeros and subnormals are handled
   by the field values; an all-ones exponent field rejects the input.
2. **Multiply.** The significands are multiplied in a 24-bit register and the
   biased exponents are added. Nothing is normalized.
3. **Align.** A fold keeps the largest exponent of a nonzero term, starting
   from the model's minimum alignment exponent. Each significand is shifted left to put `F` bits
   after the binary point, then right by the gap to the largest exponent. The
   right shift drops the bits below the grid, which is the truncation.
4. **Accumulate.** The aligned terms are negated where needed and added in the
   two's complement accumulator.
5. **Normalize and truncate.** A leading-zero count gives the position of the
   leading one. Comparing it with the alignment exponent decides whether the
   result overflows, is normal, or is subnormal. The FP32 exponent field is
   computed for a normal result and is 1 for a subnormal. A shift keeps the
   top 24 bits and drops the rest. The result is out of range when the
   exponent field would reach 255, or when it is 254 with all 24 kept bits
   set and some dropped bit nonzero. Otherwise the sign, exponent field and
   mantissa are packed into the output word.

```lean
def evalBlock (variant : Variant) (x : BlockInput variant.model) : Except ModelError F32 := do
  if x.products.length != variant.model.nfma then throw .wrongProductCount
  let some c := decodeC x.c | throw .nonfiniteInput
  let some ps := x.products.mapM (decodeTerm variant) | throw .nonfiniteInput
  let ts := c :: ps
  let e := alignExp variant ts
  let some bits := normalize (accumulate variant e ts) e (alignBits variant) | throw .accumulatorOutOfRange
  return bits
```

## The equality theorem

```lean
theorem evalBlock_eq (variant : Variant) (x : BlockInput variant.model) :
    Datapath.evalBlock variant x = (TensorCore.evalBlock x).map (·.output.bits)
```

This holds for every input, including every rejection. The proof follows
the stages:

| Stage | Lean result | What it shows |
| --- | --- | --- |
| Decode | [`Datapath.decodeInput_asDecoded`](https://github.com/pauljiang03/TC-EFT/blob/main/TensorCore/Kernels/Datapath/Decode.lean#L48), [`Datapath.decodeC_spec`](https://github.com/pauljiang03/TC-EFT/blob/main/TensorCore/Kernels/Datapath/Decode.lean#L97) | each decoder gives the model's decoded value |
| Multiply | [`Datapath.product_spec`](https://github.com/pauljiang03/TC-EFT/blob/main/TensorCore/Kernels/Datapath/Correctness.lean#L17) | each product register denotes the model's product in denormalized form |
| Alignment exponent | [`Datapath.alignFold_spec`](https://github.com/pauljiang03/TC-EFT/blob/main/TensorCore/Kernels/Datapath/Align.lean#L141) | the fold is the maximum over nonzero terms, raised to the minimum alignment exponent |
| Align | [`Datapath.Term.truncBits_eq`](https://github.com/pauljiang03/TC-EFT/blob/main/TensorCore/Kernels/Datapath/Align.lean#L49) | each aligned register holds the model's `truncBits` |
| Accumulate | [`Datapath.accumulate_toInt`](https://github.com/pauljiang03/TC-EFT/blob/main/TensorCore/Kernels/Datapath/Align.lean#L126), [`Datapath.accumulator_eq`](https://github.com/pauljiang03/TC-EFT/blob/main/TensorCore/Kernels/Datapath/Correctness.lean#L121) | the accumulator's signed value is the model's exact sum; it never overflows |
| Normalize and truncate | [`Datapath.normalize_eq`](https://github.com/pauljiang03/TC-EFT/blob/main/TensorCore/Kernels/Datapath/Normalize.lean#L182) | the bitvector normalizer is `round32 .truncate`, bit for bit |

[`Normalize.lean`](https://github.com/pauljiang03/TC-EFT/blob/main/TensorCore/Kernels/Datapath/Normalize.lean)
proves `normalize_eq` for any accumulator width from 24 to 64 bits, so it
does not depend on the model.

## What the equality covers

- **Every output bit and every error.** The sign of zero, subnormal outputs,
  out-of-range sums, and which error is reported all match.
- **The output word, not the trace.** `evalBlock` also returns intermediate
  values such as the aligned bits and residuals; the datapath returns only
  the word. Each stage is still proved to match internally.
- **The eight supported variants.** `evalBlock` is defined for any model; the
  datapath covers V100 FP16, A100 FP16/BF16/TF32 and H100 FP16/BF16/TF32
  (both TF32 modes). The FP64 DMMA variant has no datapath.
- **The definitions are bitvectors; the proof is not.** The equivalence is
  proved by reading registers as integers (`toNat`, `toInt`), so one proof
  covers every input and every register width.

Because the output words are equal, every theorem about `evalBlock`'s output
(the error bound, non-monotonicity, the accepted inputs, agreement with the
independent specification) holds for the datapath too.

## Comparison with the SMT model of Valpey et al.

Valpey et al., [*An SMT Formalization of Mixed-Precision Matrix
Multiplication: Modeling Three Generations of Tensor
Cores*](https://arxiv.org/abs/2502.15999), model the same pipeline in SMT
bitvectors: exact products, alignment to the largest exponent with the
shifted-out bits discarded, carry bits for the sum, no intermediate
normalization, and a final truncation.

| | SMT model | This datapath |
| --- | --- | --- |
| Products | exact, in the SMT floating-point theory | exact, bitvector multiplication |
| Extra alignment bits | none on Volta/Turing, one on Ampere | `p` = 0, 1, 2 on V100, A100, H100 |
| Extra carry bits | ⌈log₂ N⌉ for N terms | ⌊log₂ K⌋ + 1 for K products and C: 3, 4, 5 |
| Use | solver queries for discriminating inputs, then GPU runs | executable definition with proofs over every input |
| Coverage | FP16 inputs on Volta, Turing, Ampere, including FP16 output | FP16, BF16, TF32 inputs with FP32 output on V100, A100, H100, including minimum alignment exponents and subnormals |

The SMT model answers one query at a time and some queries time out (the
Ampere carry-bit query ran for 6 hours). Here the carry-bit width is proved
sufficient for every input. The datapath could also be used for solver
queries on one fixed model, through Lean's `bv_decide`.

## Tests

[`tests/TensorCoreTests/TC/Datapath.lean`](https://github.com/pauljiang03/TC-EFT/blob/main/tests/TensorCoreTests/TC/Datapath.lean)
checks concrete words with the kernel: four products of one, products lost
below the grid, an out-of-range sum, a subnormal output, a negative sum that
truncates to −0, and both input errors.
