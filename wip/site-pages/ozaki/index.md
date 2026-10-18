---
title: The Ozaki schemes at a glance
description: What the Ozaki schemes do, what the Lean development proves about them on the Tensor Core and AMD matrix-core models, and where to read each proof.
---

The Ozaki schemes compute a high-precision matrix product on a low-precision
matrix multiplier. They turn the inputs into small integers, which the matrix
multiplier multiplies exactly, and combine the exact integer results. The
[`ozaki/`](https://github.com/pauljiang03/HardwarePrimitives/tree/main/wip/ozaki) project
formalizes three of them in Lean on this repository's NVIDIA Tensor Core model
and on the AMD matrix-core model in `amd/`, following a set of bit-precise Z3
models of the schemes. Every theorem uses only Lean's standard axioms, and
every named declaration is re-checked by
[con-leche](https://github.com/leanprover/con-leche), an independent Lean
checker proven never to accept a proof of `False`.

| Scheme | Idea | Read |
| --- | --- | --- |
| **Ozaki-I** (Ozaki, Ogita, Oishi and Rump, 2012) | Cut every input into slices of small integers, multiply slice pairs on the matrix multiplier, add the scaled products. | [Ozaki-I, proven end to end](/HardwarePrimitives/ozaki/ozaki-1/) |
| **Ozaki-II** (Ozaki, Uchino and Imamura, 2025) | Scale the inputs to integers, multiply them modulo a few moduli on the matrix multiplier, rebuild the product with the Chinese remainder theorem. | [Ozaki-II, proven end to end](/HardwarePrimitives/ozaki/ozaki-2/) |
| **ADP and ESC** (Schwarz et al., NVIDIA, 2025) | Ozaki-I on INT8 matrix multipliers for FP64, with a slice count chosen from the inputs' exponent spread and a fallback to native FP64. | [ADP and ESC](/HardwarePrimitives/ozaki/adp/) |

Two pages cut across the schemes: [correct rounding](/HardwarePrimitives/ozaki/correct-rounding/)
for all three, and [what the hardware semantics give](/HardwarePrimitives/ozaki/hardware/).
[Related work and novelty](/HardwarePrimitives/ozaki/literature/) places the work in the
literature.

## What is proven

- **The matrix multiplier is exact, from the hardware model.** Every scheme
  assumes that the matrix multiplier multiplies its small integers exactly.
  Lean proves this on all eight NVIDIA variants and on the AMD SFMA and the
  CDNA 1, 2 and 3 fp16, bf16 and XF32 variants,
  from the bit-level models, with the exact condition, cancellation included.
- **Error bounds** for Ozaki-I and Ozaki-II, including the sharpest published
  ones that apply, and a Grade-A bound `|C − AB| ≤ (4k + 1) 2^-53 |A||B|` for
  ADP's whole routine on normal inputs, and on all inputs with one added
  guardrail; the paper establishes Grade A by experiment.
- **Dot products of any length** (split-K), **full block FMAs on A100 and
  H100** by a second pass through `C`, and **FP64 emulation** on fp16, bf16 and tf32
  Tensor Cores and on AMD matrix cores, with the cheapest exact configuration
  per GPU.
- **Correct rounding.** Each scheme has a variant that returns the round to
  nearest even of the exact product for every input, with the same result on
  both vendors: Ziv's rounding test checks whether the scheme's proven error
  interval rounds to one value, the scheme refines if not, and it ends with an
  exact fallback on the matrix multiplier.
  The whole pipeline runs in integer registers, with one theorem bounding
  every register, none depending on the inputs' exponents.
- **IEEE special values.** `±Inf` on overflow, NaN and infinite inputs, and
  signed zeros, for every correctly rounded scheme, native GEMM, plain Ozaki-I
  and Ozaki-II, and ADP, whose Inf and NaN results match the Z3 model's.

## Findings

- A full block FMA of `11`-bit slice products on A100 or H100 can exceed the
  exactness bound `2^24`; NVIDIA truncates and AMD rounds to nearest, so they give
  different wrong answers.
- ADP as described in its paper, and formalized here following the Z3 model,
  can return a wrong result, even of the wrong sign, on subnormal inputs; the
  Z3 model fails its own final-rounding check on the same input. One added
  guardrail fixes it. Shipping cuBLAS is not modeled; it passes an
  independent underflow test (Demmel et al., 2026).
- ADP with the Z3 model's "skip zeros" policy, run without the model's
  assertion, returns `0` for a nonzero entry on one of the model's own inputs.
- On A100 and H100, `10`-bit slices that fill a block FMA are the cheapest
  exact configuration; a second pass through `C` is exact but costs more than
  the extra slice. For FP64, Ozaki-II needs `1.4×` to `2×` fewer block FMAs
  than Ozaki-I on every variant.
- At realistic sizes the rounding test saves about 40 % of the products on
  the matrix multiplier on well-conditioned data; ill-conditioned products
  need a deeper list of slice counts, and low-precision inputs are cheaper
  with the exact fallback directly.
- On the Z3 test matrices, Ozaki-I's configuration (`4` slices) is correctly
  rounded on every entry and Ozaki-II's (`P = 22`) on none.

## Not covered

FP8 variants; INT8 hardware semantics, out of scope for now on both vendors
([issue #2](https://github.com/pauljiang03/HardwarePrimitives/issues/2)), so ADP runs on
an idealized INT8 matrix multiplier; and a GPU implementation. The theorems are about the
models; that GPUs behave like them rests on the models'
[validation](/HardwarePrimitives/tensor-core/validation/). The full list, with every Lean name,
is in
[`ozaki/THEOREMS.md`](https://github.com/pauljiang03/HardwarePrimitives/blob/main/wip/ozaki/THEOREMS.md).
