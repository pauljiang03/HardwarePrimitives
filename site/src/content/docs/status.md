---
title: Project status
description: What Hardware Primitives can do today, how it is checked, what is not done yet, and what could come next.
---

Hardware Primitives is a Lean 4 development about the arithmetic of GPU matrix multipliers:
models of the block FMAs of NVIDIA Tensor Cores and AMD Matrix Cores, and their proven
properties. This page summarizes what it can do today, how it is checked, what is not done, and
what could come next. Work in progress that builds on the models is kept in the repository's
`wip/` folder and is not covered here.

## What it can do today

**Executable models with FP32 output**, which map input words to output words:

| Vendor | Architectures and paths | Input formats |
| --- | --- | --- |
| NVIDIA Tensor Cores | V100; A100; Ada and L40S (A100's arithmetic); H100 and H200; B200 (Hopper's arithmetic for FP16, BF16 and TF32) | FP16, BF16, TF32 |
| NVIDIA Tensor Cores, FP8 block FMAs | Ada, Hopper (`wgmma`) and B200 (`tcgen05.mma`) | E4M3, E5M2 |
| NVIDIA Tensor Cores, FP8 `mma.sync` | H100, H200 and B200 (FP16 path with interleaving); RTX PRO 6000 | E4M3, E5M2 |
| AMD Matrix Cores | CDNA 1, 2 and 3, and the sequential FMA of FP32 inputs | FP16, BF16 (incl. `_1k`), XF32, FP8 (E4M3 and E5M2 FNUZ, any mix) |

The models are described on [the model at a glance](/HardwarePrimitives/tensor-core/) and
[the AMD model at a glance](/HardwarePrimitives/matrix-core/).

**Proven properties of the Tensor Core models.**

- Per-block error bounds, for every block-output width.
- When alignment loses nothing, so that a block FMA adds its products exactly.
- An exact characterization of a family of non-monotonic inputs.
- TC-EFT: the correctly rounded sum of a block FMA, with a 576-bit exact fallback.

**Proven properties of the Matrix Core models**, per generation:

- **All:** per-block error bounds, also from the inputs alone, monotonicity in `c`, and the
  [MC-EFT correction](/HardwarePrimitives/matrix-core/properties/eft/) of a block or an inner
  product from its output, with its fast path from the inputs alone and a 576-bit register
  version.
- **CDNA 1 and the SFMA:** correct rounding, monotonicity in every product, and independence of
  the order of the products.
- **CDNA 2:** non-monotonicity in the products only through flushing; correct rounding when every
  intermediate rounding is exact.
- **CDNA 3:** monotonicity in the products while the alignment exponents are unchanged, necessary
  and sufficient conditions for an output decrease, a non-monotone family with an exact threshold,
  correct rounding when alignment loses nothing, fixed-width accumulation, and the FP8 parity law
  (proven in `wip/mmalgebra`, which builds on the model).

**Cross-checks proven in Lean.** Each model equals an independent specification. The Tensor Core
model also equals a bitvector datapath, and a second implementation on FloatLib.

## How it is checked

| Check | Status |
| --- | --- |
| `lake build` (248 targets) | passes, no Lean warnings |
| Axiom audit | only `propext`, `Classical.choice`, `Quot.sound`; no `sorry` |
| Model = independent specification | proven for all inputs on every model, for every block-output width (FP8 included) |
| Model = bitvector datapath | proven for all inputs on the 8 FP16/BF16/TF32 variants and the 6 FP8 block FMAs |
| Recorded GPU vectors | 35,000 rows of V100, A100 and H100; 125,000 rows of Ada, L40S, H100, H200 and B200 (FP16, BF16, TF32, E4M3, E5M2); 20,000 H100 and H200 FP8 rows of toolbox release v0.1. 0 mismatches |
| MMA-Sim cross-check | 850,000 cases on 31 instructions (581,052 identical with a nonzero `C`) and 80,000 FP8 `mma.sync` cases, 0 mismatches |
| AMD vectors and MATLAB models | every published test vector; 600,000 random inner products plus targeted ones; 90,000 FP8 inner products against MMA-Sim's CDNA 3 semantics, 0 mismatches |
| Software oracle cases | 715 blocks, 2,918 rounding cases, 2,033 feature cases, 0 mismatches |
| FloatLib equivalence | proven; 115,029 + 668,944 comparison cases, 0 mismatches |
| Independent proof checker | every declaration of `TensorCore`, `MatrixCore` and their tests accepted on 2026-10-18 (169,059 and 167,239) |

## What is not done

**Model gaps.**

- **Special values inside a block FMA.** The models reject infinities and NaNs in a block and a
  FP32 overflow, where MMA-Sim returns `±∞`.
- **FP16-output modes** of the Tensor Cores are not modeled.
- **Formats and architectures without a published characterization:** FP4, FP6, the Blackwell
  instructions that *Accurate Models* does not characterize, and AMD CDNA 4. INT8 is out of
  scope.
- **The FP8 `mma.sync` path** of Hopper and B200 follows the structure that *Accurate Models*
  describes. The recorded rows do not separate it from a single block followed by `c`; the
  paper's interleaving experiment does, and that is a kernel-checked theorem.
- **Cross-vendor statements.** `TensorCore` and `MatrixCore` cannot be imported together, so
  every statement that compares the two vendors is two theorems.

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

**TC-EFT and MC-EFT.** On Tensor Cores, the paper's input-based precondition (17) derives five
of the nine conditions of the fast-path check for FP32; the other four depend on the particular
sum and remain assumptions. On Matrix Cores the condition on the inputs derives every condition,
but it uses the exact sum and an error bound, and it is sufficient, not necessary. For inner
products it takes a given error bound.

## What could come next

**Without hardware:**

- **Single cross-vendor theorems.** Make `TensorCore` and `MatrixCore` importable together, so
  that each comparison between NVIDIA and AMD is one statement.
- **Special values and FP16 outputs.** Infinities and NaNs inside block FMAs, and the FP16-output
  modes.

**With hardware:**

- **Run the models against GPUs where no recording exists:**
  - the inputs that no recorded row exercises (listed above);
  - FP8 with a nonzero `C` inside `wgmma` and `tcgen05.mma`;
  - the AMD Matrix Cores, including one FP8 instruction that swaps two products between an odd
    and an even slot to confirm the parity law.
- **New architectures.** Model CDNA 4, Rubin and the FP4/FP6 paths once their arithmetic is
  characterized.
