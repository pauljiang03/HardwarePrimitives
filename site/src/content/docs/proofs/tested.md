---
title: What is tested
description: What is tested rather than proven, what is trusted, and what is assumed.
---

This page separates what Lean proves from what is only tested, trusted, or
assumed. The proven results themselves are listed on
[What is proven](/TC-EFT/proofs/theorems/).

## Proven in Lean

All model properties, EFT correctness, and refinement results, under the
hypotheses stated in each theorem (see [What is
proven](/TC-EFT/proofs/theorems/)). The development uses no `sorry` and no
custom axioms. `scripts/check_axioms.py` audits every public theorem under
the `TensorCore` namespace and allows only `propext`, `Classical.choice`, and
`Quot.sound`. The recorded run audited 1,375 theorem roots.

Every named declaration is also re-checked outside Lean's kernel by
[con-leche](https://github.com/leanprover/con-leche), an external checker
proved never to accept a proof of `False`. On 2026-10-12, at revision
`3b37939` in `--verified` mode, it accepted every declaration of `TensorCore`
and its tests (168,717, including Lean's own library), of the AMD model
`MatrixCore` and its tests (166,049), and of the Ozaki libraries with their
tests (175,760 and 171,967). Lean does not record `example`s as declarations,
so the kernel-evaluated regression examples are checked by Lean's kernel only.

## Tested, not proved

- **Agreement with GPUs**: on the 35,000 recorded measurements only, with the
  [coverage gaps](/TC-EFT/model/validation/#what-the-rows-dont-cover) noted
  there.
- **Agreement with Python oracles**: exact-rational reimplementations of
  the same *Accurate Models* semantics.
- **Native Float32**: `tcEftWithLean_eq` is proved against Lean's float
  *model*. That the compiled `Float32` addition matches the model is checked
  by `check_lean_eft.py`, not proved.

## Trusted

- The Lean kernel, and for `#eval` and the `tc_*` executables, Lean's
  compiler and runtime.
- The Python harnesses that compare outputs. Their pass/fail rests largely on
  `assert`; every script refuses to run under `python -O` or `PYTHONOPTIMIZE`.
- The authenticity of the vendored measurement files. They are pinned by
  SHA-256 in [`vendor/SOURCES.json`](https://github.com/pauljiang03/TC-EFT/blob/main/vendor/SOURCES.json)
  but cannot be independently re-measured without GPUs.

## Assumed

That the *Accurate Models* model, and therefore this one, matches hardware in the
regions the recorded data does not exercise: active minimum alignment exponents,
subnormal and zero operands, wide-exponent BF16/TF32 inputs, and the H100 TF32
K = 8 MMA variant.
