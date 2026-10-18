---
title: Overview
description: What Hardware Primitives models, what it proves, and how the parts fit together.
---

Hardware Primitives is a Lean 4 development about the arithmetic of GPU matrix
multipliers: what the block FMAs of NVIDIA Tensor Cores and AMD Matrix Cores
actually compute, on every generation whose arithmetic has been characterized,
and what software built on them can rely on. Executable calculations and
correctness proofs use the same definitions. For each vendor there is a model
and a set of proven properties:

1. **NVIDIA Tensor Cores.** [Models of the block
   FMAs](/HardwarePrimitives/tensor-core/) from Volta to Blackwell (V100, A100, Ada
   and L40S, H100, H200 and B200) for FP16, BF16 and TF32, the FP8 block FMAs
   of Ada, Hopper and Blackwell, and the FP8 `mma.sync` paths of Hopper, B200
   and the RTX PRO 6000. Their [properties](/HardwarePrimitives/tensor-core/properties/error-bounds/)
   are error bounds, non-monotonicity and TC-EFT.
2. **AMD Matrix Cores.** [Models of the MFMA
   instructions](/HardwarePrimitives/matrix-core/) of CDNA 1, 2 and 3 and of the
   sequential FMA, for FP16, BF16, XF32 and FP8. Their
   properties, one page per generation ([CDNA 1](/HardwarePrimitives/matrix-core/properties/cdna1/),
   [CDNA 2](/HardwarePrimitives/matrix-core/properties/cdna2/),
   [CDNA 3](/HardwarePrimitives/matrix-core/properties/cdna3/)), are error bounds,
   monotonicity, correct rounding and the dependence on the order of the
   products, and [MC-EFT](/HardwarePrimitives/matrix-core/properties/eft/), TC-EFT
   carried over to every generation.

## The Tensor Core model

A Tensor Core instruction computes `D = C + Σ aᵢ·bᵢ` with block FMAs, each of
which adds a small number of low-precision products in a single multi-term
addition. It is **not** an IEEE fused dot product. The products are exact,
but before the hardware adds them it aligns their significands relative to
the largest exponent in the block, and it truncates the bits below that
grid. The sum is then truncated to FP32. Because of this, the output
can be less accurate than the input precision suggests, and it can be
**non-monotone**: making `C` smaller can make `D` larger.

This part has three layers:

1. **[A model of the Tensor Core](/HardwarePrimitives/tensor-core/).** An executable function,
   `evalBlock`, maps encoded input words to an FP32 output word for one block
   FMA. It follows the hardware model of Khattak and Mikaitis,
   *[Accurate Models of NVIDIA Tensor Cores](https://arxiv.org/html/2512.07004v4)*,
   and uses exact integers and rationals throughout. It does not rely on
   floating-point hardware or rounding libraries.
2. **[Properties of that model](/HardwarePrimitives/tensor-core/properties/error-bounds/).** Proven
   facts: the accepted input domain, an error bound split into alignment loss
   and final-rounding loss, exactness of fixed-width accumulators, and a
   characterization of non-monotonicity.
3. **[TC-EFT](/HardwarePrimitives/tensor-core/properties/eft/).** An error-free transformation that
   takes the encoded inputs and any finite FP32 output `D`, recovers what
   alignment discarded, and returns the correctly rounded exact sum when its
   preconditions hold. There is a reference version and a bounded 576-bit
   workspace version, and they are proven to agree.

The AMD model of the MFMA instructions of CDNA 1, 2 and 3 is a separate
library; see [the AMD model at a glance](/HardwarePrimitives/matrix-core/).

## Why a Lean model?

Floating-point behavior that a vendor does not document is usually studied by
probing hardware and fitting a model to the results. That gives a model, but
not a reason to trust conclusions drawn from it. Here the model is a Lean
definition, so:

- **It runs.** `#eval evalBlock x` returns bits, and the native executables in
  `Main/` drive large comparison suites.
- **It can be proven about.** Error bounds, non-monotonicity thresholds, and
  EFT correctness are Lean theorems about the *same* definition that the tests
  execute.
- **It is cross-checked.** An [independent
  specification](/HardwarePrimitives/tensor-core/specification/), written from *Accurate Models* without
  importing the implementation, is proven to agree with `evalBlock` on every
  encoded input. A [bitvector datapath](/HardwarePrimitives/tensor-core/datapath/) with
  fixed-width registers, and a second implementation built on
  [FloatLib](/HardwarePrimitives/proofs/floatlib/), are also proven equivalent.
- **It is validated.** Recorded GPU outputs are [replayed bit for
  bit](/HardwarePrimitives/tensor-core/validation/).

## Two papers

The site cites two papers, and always names which one it means:

- ***Accurate Models***: Khattak and Mikaitis,
  [*Accurate Models of NVIDIA Tensor Cores*](https://arxiv.org/html/2512.07004v4)
  (arXiv 2512.07004v4). The source of the **Tensor Core model**: the
  alignment, truncation and rounding behavior, the per-GPU parameters
  (Table 3), and the recorded GPU validation vectors. The Lean
  specification `IndependentSpec` is a transcription of this paper.
- **The TC-EFT paper**: *TC-EFT: Characterizing and Correcting Tensor Core
  Arithmetic* (manuscript). The source of the **worst-case error and non-monotonicity
  results** (Section III) and the **TC-EFT algorithm** (Section IV,
  Algorithm 1). Theorem, lemma and equation numbers such as Theorem III.4,
  Lemma IV.2 and inequality (17) refer to this paper, and
  `check_tc_eft_paper.py` replays its validation suites. In Lean, the algorithm is
  named `tcEft` (for example `tcEftEncoded` and `EFMachine.tcEft`).

Lean declaration names describe what each result states rather than citing a
paper number. Docstrings give the corresponding paper reference where there is
one.

## A first calculation

```lean
import TensorCore.TC

open TensorCore

-- Four FP16 products 1.0 × 1.0 with C = +0 on the V100 model.
def ones : BlockInput v100F16F32 :=
  ⟨List.replicate 4 (0x3c00, 0x3c00), 0⟩

#eval (evalBlock ones).map fun t => t.output.bits.toNat

-- The kernel checks the exact output word: FP32 4.0.
example : ((evalBlock ones).toOption.map fun t => t.output.bits) =
    some 0x40800000 := by decide +kernel
```

## What is and is not claimed

The proofs are about the **formal model**, under each theorem's stated
hypotheses. The link from the model to real GPUs comes from replaying
recorded measurements and from *Accurate Models*, which the definitions follow.
It is evidence, not a proof. The variants run from Volta to Blackwell (V100,
A100, Ada, H100, H200, B200) with FP16, BF16 or TF32 inputs, and on Ada,
Hopper and Blackwell also with FP8 (E4M3, E5M2) inputs; all have FP32 `C` and
output. See [Modeling scope and
limits](/HardwarePrimitives/tensor-core/scope/) and [What is tested](/HardwarePrimitives/proofs/tested/).

## Start exploring

- [The model at a glance](/HardwarePrimitives/tensor-core/): the whole pipeline on one page.
- [The AMD model at a glance](/HardwarePrimitives/matrix-core/): the Matrix Core model of CDNA 1, 2 and 3.
- [Quick start](/HardwarePrimitives/quick-start/): build the project and run the examples.
- [Properties of Tensor Cores](/HardwarePrimitives/tensor-core/properties/error-bounds/): error bounds, non-monotonicity and TC-EFT.
- [What is proven](/HardwarePrimitives/proofs/theorems/): the headline results and where they live.
- [Source on GitHub](https://github.com/pauljiang03/HardwarePrimitives).
