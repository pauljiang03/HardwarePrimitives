---
title: Project status
description: What MMAlgebra can do today, how it is checked, what is not done yet, and what could come next.
---

MMAlgebra is a Lean 4 development about the arithmetic of GPU matrix multipliers and the
software built on them. It has three parts:

- **hardware semantics**: models of NVIDIA Tensor Cores and AMD matrix cores, and their
  properties;
- **emulation**: the Ozaki schemes, proved on those models;
- **schedules**: an algebra of reduction schedules that decides when two ways of computing a
  matrix product give the same bits.

This page summarizes all three: what each can do today, how it is checked, what is not done,
and what could come next.

## What it can do today

### Hardware semantics

**Executable models with FP32 output**, which map input words to output words:

| Vendor | Architectures and paths | Input formats |
| --- | --- | --- |
| NVIDIA Tensor Cores | V100; A100; Ada and L40S (A100's arithmetic); H100 and H200; B200 (Hopper's arithmetic for FP16, BF16 and TF32) | FP16, BF16, TF32 |
| NVIDIA Tensor Cores, FP8 block FMAs | Ada, Hopper (`wgmma`) and B200 (`tcgen05.mma`) | E4M3, E5M2 |
| NVIDIA Tensor Cores, FP8 `mma.sync` | H100, H200 and B200 (FP16 path with interleaving); RTX PRO 6000 | E4M3, E5M2 |
| AMD matrix cores | CDNA 1, 2 and 3, and the sequential FMA of FP32 inputs | FP16, BF16 (incl. `_1k`), XF32, FP8 (E4M3 and E5M2 FNUZ, any mix) |

The models are described on [the model at a glance](/MMAlgebra/model/) and
[the AMD model at a glance](/MMAlgebra/amd/).

**Proved properties.**

- Per-block error bounds, for every block-output width.
- An exact characterization of a family of non-monotonic Tensor Core inputs.
- TC-EFT: the correctly rounded sum of a Tensor Core block FMA, with a 576-bit exact fallback.
- When small integers are added exactly, and the two-pass recovery of full block FMAs.
- AMD's monotonicity in `c`, and the cases where it fails in the products.
- The CDNA 3 FP8 parity law.

**Cross-checks proved in Lean.** Each model equals an independent specification. The Tensor Core
model also equals a bitvector datapath, and a second implementation on FloatLib.

### Emulation

- Ozaki-I, Ozaki-II and NVIDIA's ADP (on an idealized INT8 matrix multiplier) are proved
  against the exactness of the models.
- Correctly rounded variants use a rounding test with an exact fallback on the matrix multiplier.
- The integer pipelines have proved register widths, and IEEE special values are handled.
- Every schedule within the exactness bound is an exact matrix multiplier, so the Ozaki schemes
  give the same bits under every split-K or stream-K schedule.

See [the Ozaki schemes](/MMAlgebra/ozaki/).

### Schedules

The laws of each architecture's reduction algebra:

| Algebra | Architectures |
| --- | --- |
| Rigid | NVIDIA FP16/BF16/TF32, CDNA 3, the sequential FMA, Blackwell FP8 |
| Correctly rounded nodes | CDNA 1 |
| Summation trees | CDNA 2 |
| Rigid with truncation nodes | Ada and Hopper FP8 |
| Parity-rigid | CDNA 3 FP8 |

On top of the laws:

- **Completeness.** Terms with different normal forms differ on some input; see the coverage
  below.
- **Separating inputs.** Every pair of inequivalent schedules has an input that separates them.
- **Divergence bounds.** How far apart two schedules can be, with shared work not counted.
- **The exact region.** Where every schedule agrees.
- **Pinned and anchored accumulation.** These make every schedule agree on truncating hardware,
  across vendors.

See [Schedules](/MMAlgebra/schedules/).

## How it is checked

| Check | Status |
| --- | --- |
| `lake build` (248 targets) | passes, no Lean warnings |
| Axiom audit | only `propext`, `Classical.choice`, `Quot.sound`; no `sorry` |
| Model = independent specification | proved for all inputs on every model, for every block-output width (FP8 included) |
| Model = bitvector datapath | proved for all inputs on the 8 FP16/BF16/TF32 variants and the 6 FP8 block FMAs |
| Recorded GPU vectors | 35,000 rows of V100, A100 and H100; 125,000 rows of Ada, L40S, H100, H200 and B200 (FP16, BF16, TF32, E4M3, E5M2); 20,000 H100 and H200 FP8 rows of toolbox release v0.1. 0 mismatches |
| MMA-Sim cross-check | 850,000 cases on 31 instructions (581,052 identical with a nonzero `C`) and 80,000 FP8 `mma.sync` cases, 0 mismatches |
| AMD vectors and MATLAB models | every published test vector; 600,000 random inner products plus targeted ones; 90,000 FP8 inner products against MMA-Sim's CDNA 3 semantics, 0 mismatches |
| Software oracle cases | 715 blocks, 2,918 rounding cases, 2,033 feature cases, 0 mismatches |
| FloatLib equivalence | proved; 115,029 + 668,944 comparison cases, 0 mismatches |
| Independent proof checker | every declaration of the four libraries accepted |

## What is not done

**Formal gaps in the schedule algebra.**

- **Completeness not yet proved:**
  - terms with additions on Ada, Hopper and CDNA 3 FP8 (an addition can leave more than 13
    mantissa bits, so the normal form needs truncation nodes above additions);
  - CDNA 2 BF16;
  - CDNA 1 BF16 terms.

  These are checked by enumeration.
- **Products below the binary32 grid.** On the BF16/TF32 Tensor Cores, the sequential FMA and
  CDNA 3 BF16/XF32, completeness for terms is proved only on inputs whose products are
  multiples of `2^-149`, because a block can then return `−0`. TF32 and XF32 terms off that
  grid are not covered at all.
- **Only one direction proved.** Several chain results prove completeness without the matching
  soundness statement.
- **Laws that are only tested:** `[x] ⊕ [y] = [x y]` on CDNA 2, the zero-product law on AMD, and
  the negation symmetry.
- **The decision procedure** is a Python prototype, not a verified procedure.
- **Divergence bounds** are proved for the FP16 models, not for BF16, TF32 or FP8.
- **Pinned accumulation** is proved for chains on CDNA 3, not for split-K or general schedules.
  The algorithm's grid choice and its error bound are not proved end to end.
- **Cross-vendor statements.** `TensorCore` and `MatrixCore` cannot be imported together, so
  every statement that compares the two vendors is two theorems.

**Model gaps.**

- **Special values inside a block FMA.** The models reject infinities and NaNs in a block and a
  binary32 overflow, where MMA-Sim returns `±∞`.
- **FP16-output modes** of the Tensor Cores are not modeled.
- **Formats and architectures without a published characterization:** FP4, FP6, the Blackwell
  instructions that *Accurate Models* does not characterize, and AMD CDNA 4. INT8 is out of
  scope.
- **The FP8 `mma.sync` path** of Hopper and B200 follows the structure that *Accurate Models*
  describes. The recorded rows do not separate it from a single block followed by `c`; the
  paper's interleaving experiment does, and that is a kernel-checked theorem.

**Hardware coverage.**

- **Not exercised by any recorded GPU row:**
  - active minimum alignment exponents;
  - subnormal and zero operands;
  - wide-exponent BF16/TF32 inputs;
  - the H100 TF32 variant with FMA size 8;
  - E4M3's top binade.
- **FP8 with a nonzero `C` inside `wgmma` or `tcgen05.mma`.** No recorded row covers it; the
  evidence there is the MMA-Sim cross-check, a simulator.
- **AMD.** No recorded hardware outputs are published; the AMD models rest on the published
  test vectors and on two simulators.

**Emulation.** The width theorems do not check comparisons, bit lengths or shift amounts. The
ADP zero policy is characterized up to about one value of `D`. Further items are on
[the Ozaki theorem list](https://github.com/pauljiang03/MMAlgebra/blob/main/ozaki/THEOREMS.md#not-proved).

**TC-EFT.** The paper's input-based precondition (17) derives five of the nine conditions of
the fast-path check for FP32; the other four depend on the particular sum and remain
assumptions.

## What could come next

**Without hardware:**

- **Single cross-vendor theorems.** Make `TensorCore` and `MatrixCore` importable together, so
  that each comparison between NVIDIA and AMD is one statement.
- **Completeness everywhere.** FP8 terms with truncation nodes and parity groups, the BF16
  variants, and products below the binary32 grid.
- **The tested laws and the remaining divergence bounds**, in Lean.
- **Special values and FP16 outputs.** Infinities and NaNs inside block FMAs, and the FP16-output
  modes.
- **A verified decision procedure**, with a certificate for equivalence and a separating input
  for inequivalence.
- **Pinned accumulation end to end**, including its error bound.

**With hardware:**

- **Run the existing tests on GPUs:**
  - the 140-case targeted validation suite;
  - the separating inputs of the schedule algebra;
  - pinned accumulation;
  - FP8 with a nonzero `C` inside `wgmma` and `tcgen05.mma`;
  - the AMD matrix cores, including one FP8 instruction that swaps two products between an odd
    and an even slot to confirm the parity law.
- **New architectures.** Model CDNA 4, Rubin and the FP4/FP6 paths once their arithmetic is
  characterized.

**Building on the algebra:** a front end for Triton or PTX that extracts each output entry's
reduction term from a compiled kernel. It could then check which autotuning configurations give
identical bits, and whether a kernel's results depend on the batch size.
