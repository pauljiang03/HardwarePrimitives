---
title: Overview
description: What TC-EFT models, what it proves, and how the parts fit together.
---

TC-EFT is a Lean 4 library about the arithmetic of NVIDIA Tensor Cores (TCs).
A Tensor Core instruction computes `D = C + Σ aᵢ·bᵢ` over a small group of
low-precision products. It is **not** an IEEE fused dot product. The products
are exact, but before the hardware adds them it aligns them to a common grid
fixed by the largest exponent in the group, and it discards bits below that
grid. The sum is then truncated to FP32. Because of this, the output
can be less accurate than the input precision suggests, and it can be
**non-monotone**: making `C` smaller can make `D` larger.

The library has three layers:

1. **[A model of the Tensor Core](/TC-EFT/model/).** An executable function,
   `evalBlock`, maps encoded input words to an FP32 output word for one group
   of products. It follows the hardware model of Khattak and Mikaitis,
   *[Accurate Models of NVIDIA Tensor Cores](https://arxiv.org/html/2512.07004v4)*,
   and uses exact integers and rationals throughout. It does not rely on
   floating-point hardware or rounding libraries.
2. **[Properties of that model](/TC-EFT/properties/error-bounds/).** Proved
   facts: the accepted input domain, an error bound split into alignment loss
   and final-rounding loss, exactness of fixed-width accumulators, and a
   characterization of non-monotonicity.
3. **[TC-EFT](/TC-EFT/properties/eft/).** An error-free transformation that
   takes the encoded inputs and any finite FP32 output `D`, recovers what
   alignment discarded, and returns the correctly rounded exact sum when its
   preconditions hold. There is a reference version and a bounded 576-bit
   workspace version, and they are proved to agree.

The same repository also models **AMD matrix cores**, the MFMA instructions
of CDNA 1, 2 and 3, in a separate library; see [the AMD model at a
glance](/TC-EFT/amd/). The [Ozaki schemes](/TC-EFT/ozaki/) are proved on both.

## Why a Lean model?

Floating-point behavior that a vendor does not document is usually studied by
probing hardware and fitting a model to the results. That gives a model, but
not a reason to trust conclusions drawn from it. Here the model is a Lean
definition, so:

- **It runs.** `#eval evalBlock x` returns bits, and the native executables in
  `Main/` drive large comparison suites.
- **It can be proved about.** Error bounds, non-monotonicity thresholds, and
  EFT correctness are Lean theorems about the *same* definition that the tests
  execute.
- **It is cross-checked.** An [independent
  specification](/TC-EFT/model/specification/), written from *Accurate Models* without
  importing the implementation, is proved to agree with `evalBlock` on every
  encoded input. A [bitvector datapath](/TC-EFT/model/datapath/) with
  fixed-width registers, and a second implementation built on
  [FloatLib](/TC-EFT/proofs/floatlib/), are also proved equivalent.
- **It is validated.** Recorded GPU outputs are [replayed bit for
  bit](/TC-EFT/model/validation/).

## Two papers

The site cites two papers, and always names which one it means:

- ***Accurate Models***: Khattak and Mikaitis,
  [*Accurate Models of NVIDIA Tensor Cores*](https://arxiv.org/html/2512.07004v4)
  (arXiv 2512.07004v4). The source of the **Tensor Core model**: the
  alignment, truncation and rounding behavior, the per-GPU parameters
  (Table 3), and the recorded GPU validation vectors. The Lean
  specification `IndependentSpec` is a transcription of this paper.
- **The TC-EFT paper**: *TC-EFT: Characterizing and Correcting Tensor Core
  Arithmetic* (under submission). The source of the **worst-case error and non-monotonicity
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

-- Four FP16 products 1.0 × 1.0 with C = +0 on the V100 profile.
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
It is evidence, not a proof. The supported paths have FP16, BF16, or TF32
operands and FP32 `C` and output. See [Modeling scope and
limits](/TC-EFT/model/scope/) and [What is tested](/TC-EFT/proofs/tested/).

## Start exploring

- [The model at a glance](/TC-EFT/model/): the whole pipeline on one page.
- [The AMD model at a glance](/TC-EFT/amd/): the matrix-core model of CDNA 1, 2 and 3.
- [Quick start](/TC-EFT/quick-start/): build the project and run the examples.
- [What is proven](/TC-EFT/proofs/theorems/): the headline results and where they live.
- [Source on GitHub](https://github.com/pauljiang03/TC-EFT).
