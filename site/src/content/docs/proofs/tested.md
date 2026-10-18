---
title: What is tested
description: What is tested rather than proven, what is trusted, and what is assumed.
---

This page separates what Lean proves from what is only tested, trusted, or
assumed. The proven results themselves are listed on
[What is proven](/HardwarePrimitives/proofs/theorems/).

## Proven in Lean

All model properties, EFT correctness, and refinement results, under the
hypotheses stated in each theorem (see [What is
proven](/HardwarePrimitives/proofs/theorems/)). The development uses no `sorry` and no
custom axioms. `scripts/check_axioms.py` audits every public theorem under
the `TensorCore` namespace and allows only `propext`, `Classical.choice`, and
`Quot.sound`. The recorded run audited 1,543 theorem roots. The AMD test
library audits every theorem of `MatrixCore` the same way (824 theorems).

The declarations are also re-checked outside Lean's kernel by
[con-leche](https://github.com/leanprover/con-leche), an external checker
proved never to accept a proof of `False`. On 2026-10-13, at revision
`3b37939` in `--verified` mode, it accepted every declaration of `TensorCore`
and its tests (168,810, including Lean's own library) and of the AMD model
`MatrixCore` and its tests (166,049); the `MatrixCore` theorems added since
have not been re-checked. Lean does not record `example`s as declarations, so the kernel-evaluated regression examples are checked by Lean's kernel only.

## Tested, not proved

- **Agreement with GPUs**: on the recorded measurements only (35,000 rows of
  V100, A100 and H100; 125,000 rows of Ada, L40S, H100, H200 and B200 with
  FP16, BF16, TF32, E4M3 and E5M2 inputs; 20,000 H100 and H200 FP8 rows of
  the toolbox's release v0.1), with the
  [coverage gaps](/HardwarePrimitives/model/validation/#what-the-rows-dont-cover) noted
  there.
- **The accumulator input of the recorded FP8 outputs**: Ada and L40S
  accumulate `C` in the block FMA; the H100 and H200 outputs of commit 79143bd
  agree with `C = 0`; the B200 outputs and the H100 and H200 outputs of
  release v0.1, recorded with the toolbox's `mma.sync` harness, agree with the
  FP8 `mma.sync` model, which adds `C` after two FP16 block FMAs. A nonzero
  `C` inside `wgmma` or `tcgen05.mma` has no recorded data.
- **Agreement with MMA-Sim**: a simulator, not hardware. 850,000 cases on 31
  instructions of V100 to B200 and the RTX PRO 6000 (581,052 identical with a
  nonzero `C`, `wgmma` and `tcgen05.mma` included) and 80,000 FP8 `mma.sync`
  cases composed from MMA-Sim's FP16 `mma.sync`, 0 mismatches
  ([details](/HardwarePrimitives/model/validation/#cross-check-against-mma-sim)).
- **FP8 decoding**: proved for every E4M3 and E5M2 word in Lean, and also
  compared with an independent Python decoder on all 512 words.
- **Agreement with Python oracles**: exact-rational reimplementations of
  the same *Accurate Models* semantics.
- **Agreement of the AMD model with the hardware**: through the paper's test
  vectors, each a kernel-checked regression reproducing the output the paper
  reports for the hardware; differential testing against the authors' MATLAB
  models (600,000 random inner products, and 20,000 targeted FP8 ones);
  and 90,000 FP8 inner products against MMA-Sim's CDNA 3 semantics. No
  recorded AMD hardware outputs are published
  ([details](/HardwarePrimitives/amd/validation/)).
- **Native Float32**: `tcEftWithLean_eq` is proved against Lean's float
  *model*. That the compiled `Float32` addition matches the model is checked
  by `check_lean_eft.py`, not proved.

## Trusted

- The Lean kernel, and for `#eval` and the `tc_*` executables, Lean's
  compiler and runtime.
- The Python harnesses that compare outputs. Their pass/fail rests largely on
  `assert`; every script refuses to run under `python -O` or `PYTHONOPTIMIZE`.
- The authenticity of the vendored measurement files. They are pinned by
  SHA-256 in [`vendor/SOURCES.json`](https://github.com/pauljiang03/HardwarePrimitives/blob/main/vendor/SOURCES.json)
  and in [`vendor/matlab-tensor-core-79143bd/SOURCES.json`](https://github.com/pauljiang03/HardwarePrimitives/blob/main/vendor/matlab-tensor-core-79143bd/SOURCES.json)
  but cannot be independently re-measured without GPUs.

## Assumed

That the *Accurate Models* model, and therefore this one, matches hardware in the
regions the recorded data does not exercise: active minimum alignment exponents,
subnormal and zero operands, wide-exponent BF16/TF32 inputs, the H100 TF32
K = 8 MMA variant, a nonzero `C` inside the FP8 block FMA of Hopper and B200,
and E4M3's top binade. For the AMD model: that *Accurate Models of AMD Matrix
Cores*, and therefore this model, matches the hardware beyond the paper's test
vectors.
