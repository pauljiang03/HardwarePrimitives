---
title: Tensor Cores and Matrix Cores compared
description: Single theorems that compare the NVIDIA and AMD models, and show that the correction does not depend on the vendor.
---

The Tensor Core and Matrix Core libraries model different hardware, each with
its own numerics. The
[`cross-vendor/`](https://github.com/pauljiang03/HardwarePrimitives/tree/main/cross-vendor)
project imports both and states each comparison as one theorem. The two
libraries can be imported into the same file because each scopes its `ℕ`,
`ℤ` and `ℚ` notation to its own namespace.

## The same words, the same values, the same rounding

The libraries decode words with separate definitions. On every word of an
IEEE layout they give the same value, or both reject it
([`CrossVendor.decode_value`](https://github.com/pauljiang03/HardwarePrimitives/blob/main/cross-vendor/CrossVendor/Formats.lean#L43)). In particular this holds for every FP32, FP16
and BF16 word ([`CrossVendor.value32_eq`](https://github.com/pauljiang03/HardwarePrimitives/blob/main/cross-vendor/CrossVendor/Formats.lean#L68), [`CrossVendor.fp16_value_eq`](https://github.com/pauljiang03/HardwarePrimitives/blob/main/cross-vendor/CrossVendor/Formats.lean#L72),
[`CrossVendor.bf16_value_eq`](https://github.com/pauljiang03/HardwarePrimitives/blob/main/cross-vendor/CrossVendor/Formats.lean#L78)).

Their round-to-nearest-even functions are also separate. Up to the largest
finite FP32 magnitude, both round every rational to the same word
([`CrossVendor.round32_eq_rne32`](https://github.com/pauljiang03/HardwarePrimitives/blob/main/cross-vendor/CrossVendor/Rounding.lean#L33)). Above it they differ: the Tensor Core
library returns no word, while the Matrix Core library rounds values below
`2^128 − 2^103` down to the largest finite word.

## The correction does not depend on the vendor

A Tensor Core block and a Matrix Core block with the same exact sum `S` can
give different outputs. If `S` is in the FP32 range, TC-EFT and MC-EFT both
return a word, and the same one: `S` rounded to nearest even. Each runs from
any finite `D`, such as its own block's output
([`CrossVendor.corrections_agree`](https://github.com/pauljiang03/HardwarePrimitives/blob/main/cross-vendor/CrossVendor/Correction.lean#L93)).

For the same operand words this needs no assumption beyond finite inputs and
the range of `S`:

- FP16 on A100 and CDNA 3, eight products ([`CrossVendor.fp16_ampere_cdna3`](https://github.com/pauljiang03/HardwarePrimitives/blob/main/cross-vendor/CrossVendor/Correction.lean#L136));
- FP16 on V100 and CDNA 1, four products ([`CrossVendor.fp16_volta_cdna1`](https://github.com/pauljiang03/HardwarePrimitives/blob/main/cross-vendor/CrossVendor/Correction.lean#L148));
- BF16 on A100 and CDNA 3, eight products ([`CrossVendor.bf16_ampere_cdna3`](https://github.com/pauljiang03/HardwarePrimitives/blob/main/cross-vendor/CrossVendor/Correction.lean#L160)).

## The comparison, row by row

| | NVIDIA Tensor Core | AMD Matrix Core | Lean |
| --- | --- | --- | --- |
| Final rounding | truncation to FP32 | round to nearest even | [`CrossVendor.final_rounding`](https://github.com/pauljiang03/HardwarePrimitives/blob/main/cross-vendor/CrossVendor/Comparison.lean#L23) |
| Monotone in `C` / `c` | no | yes, on every configuration | [`CrossVendor.accumulator_monotonicity`](https://github.com/pauljiang03/HardwarePrimitives/blob/main/cross-vendor/CrossVendor/Comparison.lean#L44) |
| Monotone in the products | no | SFMA and CDNA 1 yes; CDNA 2 and CDNA 3 no | [`CrossVendor.product_monotonicity`](https://github.com/pauljiang03/HardwarePrimitives/blob/main/cross-vendor/CrossVendor/Comparison.lean#L86) |
| Product order | only the multiset matters | CDNA 1 and CDNA 3 Algorithm 1 only the multiset; CDNA 2 and CDNA 3 FP8 the positions | [`CrossVendor.product_order`](https://github.com/pauljiang03/HardwarePrimitives/blob/main/cross-vendor/CrossVendor/Comparison.lean#L112) |

**Final rounding.** Take `c = 1` and one FP16 product
`2^-12 · 1.5·2^-12 = 3·2^-25`, with seven zero products. The exact sum is
`1 + 3·2^-25`. A100 truncates to `1`, and CDNA 3 rounds to nearest,
`1 + 2^-23`. From each block's own output, TC-EFT and MC-EFT return the same
word, `1 + 2^-23`.

**Monotonicity in `C` and `c`.** On H100, take sixteen products
`2^-13 · 2^-13 = 2^-26`. With `C = 1` the products fall below the alignment
grid and the output is `1`. With `C` one FP32 step below `1` they stay on the
grid, and the output is `1 + 2^-23`. On every Matrix Core configuration of
the paper, a larger `c` never gives a smaller output.

**Monotonicity in the products.** On V100 and on CDNA 3, raise a lead product
from `2^-9 − 2^-29` (normal operands, exponent `−10`) to `2^-9`
(`2^-24 · 2^15`, a subnormal operand, exponent `1`), next to products
`2^-24`. The alignment grid coarsens and those products are lost, so the
exact sum rises while the output falls. On CDNA 2, a product that rises from
`2^-14` to `(1 − 2^-10)·2^-13` has a subnormal operand, which is flushed to
zero. On CDNA 1 and the SFMA no such pair of inputs exists.

**Product order.** A Tensor Core block aligns every term to the largest
exponent and adds the truncated terms exactly, so permuting its products
changes neither whether it succeeds nor its output, on every model
([`TensorCore.evalBlock_perm`](https://github.com/pauljiang03/HardwarePrimitives/blob/main/tensor-core/TensorCore/TC/ProductOrder.lean#L60)). CDNA 1, the SFMA and CDNA 3 Algorithm 1 also
depend on the products only as a multiset. CDNA 2's pairwise sum depends on
positions. On CDNA 3 FP8, a permutation of the 16 slots preserves every output
exactly when it preserves the parity of each slot.

## Checks

```sh
cd cross-vendor
python3 scripts/check.py     # build, axiom audit, documentation blocks
EXPORTER=… CHECKER=… bash scripts/conleche.sh
```

The audit checks that every `CrossVendor` theorem uses only `propext`,
`Classical.choice` and `Quot.sound`. Con-leche re-checks every declaration of
the project, with the parts of both libraries it uses.
