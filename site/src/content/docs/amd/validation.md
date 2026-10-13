---
title: 6. Validation
description: How the AMD model is tied to hardware - the paper's test vectors as kernel-checked regressions, differential testing against the authors' MATLAB models, and a second implementation on FloatLib proved equivalent.
---

The proofs connect the model to an independent specification. Its link to
the hardware comes from three checks.

## The paper's test vectors

Every test vector of the paper's Section 4, for CDNA 1, 2 and 3 and the fp32,
fp16, bf16, bf16 `_1k`, XF32 and fp8 variants, is a regression proved by kernel
evaluation that reproduces the output the paper reports for the hardware
([`tests/MatrixCoreTests/Paper/`](https://github.com/pauljiang03/TC-EFT/tree/main/amd/tests/MatrixCoreTests/Paper)).
Parameterized families, such as `j = 24 … 32`, are checked for every listed
value. Inputs are written by decoded value and encoded exactly, so an input a
format cannot represent fails the test instead of being rounded silently.

Where a vector cannot be formed in the stated format, or where the paper's
prose and its Algorithm 1 disagree, the test records which it follows and why
([paper notes](https://github.com/pauljiang03/TC-EFT/blob/main/amd/docs/paper-notes.md)).
For example, the paper's fp16 cancellation test `c = 2^10, p₁ = −p₂ = 2^35`
cannot be formed from fp16 operands, whose products are below `2^32`, so the
suite runs it with bf16, which the paper says behaves identically.

No recorded hardware vectors for AMD GPUs are published, so unlike the
[Tensor Core validation](/TC-EFT/model/validation/) the suite uses the paper's
explicit vectors rather than bulk measurements.

## Differential testing against the MATLAB models

[`scripts/matlab_diff.py`](https://github.com/pauljiang03/TC-EFT/blob/main/amd/scripts/matlab_diff.py)
compares the Lean model with the authors' MATLAB matrix-core models, run in
GNU Octave, on random inputs sampled as in the paper's Section 5 (normal,
subnormal and uniform random bits) and on the paper's targeted vectors.
The Lean side is `mc_eval`, which prints the observed result of an inner
product for given words.

On 600,000 random inner products across all ten models, the two agree once
two special-value lines and one unread flag in the MATLAB code are corrected.
The two remaining differences are two of the paper's bf16 vectors that test
the subnormal-aware normalization, where the Lean model returns the outputs
the paper reports for the hardware. The MATLAB models have no fp32 SFMA and
no mixed fp8 formats, so those variants are compared through the paper's
vectors only. The method and the per-model counts are in
[`amd/docs/differential.md`](https://github.com/pauljiang03/TC-EFT/blob/main/amd/docs/differential.md).

## A second implementation on FloatLib

[`amd/floatlib-port/`](https://github.com/pauljiang03/TC-EFT/tree/main/amd/floatlib-port)
reimplements the model on [FloatLib](https://github.com/lean-dojo/FloatLib)
instead of Matrix-Core's own numerics, as a separate Lake project with
mathlib. Lean proves that, for every model and any input words, a block of
the FloatLib implementation gives the same observation as the model (finite
word, infinity or NaN), and an inner product of any length the same as
`dotOutcome`. Every model's contract and the chaining theorems hold for the
FloatLib implementation too. It follows the layout of the
[Tensor Core FloatLib cross-check](/TC-EFT/proofs/floatlib/).

## Running the checks

```sh
cd amd
lake build                    # library, paper regressions, audit
python3 scripts/check.py      # clean build, examples, documentation blocks
python3 scripts/matlab_diff.py --cases 20000 --seed 1   # needs GNU Octave
```
