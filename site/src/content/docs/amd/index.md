---
title: The AMD model at a glance
description: How Matrix-Core models the MFMA instructions of AMD CDNA 1, 2 and 3 GPUs in Lean, and how they differ from NVIDIA Tensor Cores.
---

Matrix-Core is a Lean library about the arithmetic of AMD matrix cores: the
MFMA instructions of the CDNA 1, CDNA 2 and CDNA 3 GPUs. It follows Khattak,
Mikaitis and Graziani, *[Accurate Models of AMD Matrix
Cores](https://arxiv.org/abs/2609.14845)* (arXiv 2609.14845), and uses that
paper's notation throughout. As on the Tensor Core side, the executable
calculations and the proofs use the same definitions.

It lives in the
[`amd/`](https://github.com/pauljiang03/MMAlgebra/tree/main/amd) folder as a
standalone Lake project, with its own numerical foundation: it does not depend
on the Tensor Core library, and the two cannot be imported into the same file.
The [Ozaki schemes](/MMAlgebra/ozaki/) are proved on both.

## The hardware behavior being modeled

One MFMA block computes

```text
d = Σ_{ℓ=1}^{N_FMA} a_ℓ b_ℓ + c
```

with binary32 `c` and `d`. Longer inner products chain blocks, each block's
`d` becoming the next block's `c`. The paper describes four configurations
for how a block accumulates, the constructors of [`MatrixCore.Accumulation`](https://github.com/pauljiang03/MMAlgebra/blob/main/amd/MatrixCore/MC/Defs.lean#L25):

| Architecture | Inputs | Configuration | `N_FMA` |
| --- | --- | --- | --- |
| CDNA 1, 2, 3 | fp32 | SFMA: `correct_rounding`, one product per step | 1 |
| CDNA 1 (MI100) | fp16 / bf16 | `correct_rounding`: exact sum, one round to nearest even | 4 / 2 |
| CDNA 2 (MI210, MI250) | fp16 / bf16 / bf16 `_1k` | `pair_wise_sum`, subnormals flushed | 4 / 2 / 4 |
| CDNA 3 (MI300A, MI300X) | fp16 / bf16 / XF32 | `global_alignment` with late `c` (Algorithm 1) | 8 / 8 / 4 |
| CDNA 3 | fp8 E4M3 / E5M2 FNUZ, any mix | `odd_even_grouping` (Algorithm 2) | 16 |

Every variant ends with `d = fl{S_acc}`: the accumulated value `S_acc`,
normalized and rounded to nearest even in binary32. What differs is how
`S_acc` is formed.

## How it differs from a Tensor Core

| | NVIDIA Tensor Core | AMD matrix core |
| --- | --- | --- |
| Final rounding | truncation to FP32 | round to nearest even (`fl{·}`) |
| Alignment | every term, `C` included, to the largest exponent | CDNA 3: the products to their largest exponent; `c` added late |
| Monotone in `C` / `c` | no: a smaller `C` can move the grid and raise the output | yes, on every configuration ([`MatrixCore.evalBlock_c_monotone`](https://github.com/pauljiang03/MMAlgebra/blob/main/amd/MatrixCore/MC/Monotonicity.lean#L633)) |
| Monotone in the products | no | SFMA and CDNA 1 yes; CDNA 2 and CDNA 3 no ([`MatrixCore.cdna3F16_nonmonotonic`](https://github.com/pauljiang03/MMAlgebra/blob/main/amd/MatrixCore/MC/ProductMonotonicity.lean#L164)) |
| Product order | — | CDNA 1 and CDNA 3 Algorithm 1 depend only on the multiset; CDNA 2 and CDNA 3 binary8 depend on positions |

On CDNA 3 a product with a subnormal operand has a small value but a large
exponent sum `e_a + e_b`, so raising it slightly can raise the alignment
exponent and truncate the other products by more than it gains. The library
proves this and gives kernel-checked counterexamples on every input format.

## A first calculation

Four fp16 products `1 · 1` (`0x3C00 = 1`) with `c = 0` on CDNA 1:

```lean
import MatrixCore

open MatrixCore

def ones : BlockInput cdna1F16 := ⟨List.replicate 4 0x3C00, List.replicate 4 0x3C00, 0⟩

#eval blockBits ones

example : blockBits ones = .ok 0x40800000 := by decide +kernel
```

The result is the binary32 encoding of `4`. The same words give different
results on the three architectures; the example file
[`GettingStarted.lean`](https://github.com/pauljiang03/MMAlgebra/blob/main/amd/examples/GettingStarted.lean)
shows one such input.

## What is and is not claimed

The proofs concern the model. That the hardware behaves like it rests on the
paper's experiments, which the regression suite replays: every test vector of
the paper's Section 4 is a kernel-checked regression that reproduces the
output the paper reports for the hardware. No recorded hardware vectors for
AMD GPUs are published, so the suite uses the paper's explicit vectors. See
[validation](/MMAlgebra/amd/validation/) and [scope and
limits](/MMAlgebra/amd/scope/).

## Reading on

1. [Getting started](/MMAlgebra/amd/getting-started/): build, evaluate a block, read the results.
2. [Notation and formats](/MMAlgebra/amd/notation/): every symbol of the paper and its Lean name.
3. [The three architectures](/MMAlgebra/amd/architectures/): CDNA 1, 2 and 3, block by block.
4. [Independent specification](/MMAlgebra/amd/specification/): a second transcription of the paper, proved equal to the model.
5. [What is proved](/MMAlgebra/amd/theorems/): error bounds, monotonicity, contracts and chaining.
6. [Validation](/MMAlgebra/amd/validation/): the paper's vectors, the MATLAB models and a FloatLib implementation.
